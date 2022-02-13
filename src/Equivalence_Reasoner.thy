section \<open>Introduction\<close>

text \<open>
  Isabelle's Simplifier is a powerful tool for reasoning using term rewriting, with rewrite rules
  given as equations. While this is more than sufficient in many cases, there are situations where
  it would be great if automated rewriting could be done using mere equivalences as rewrite rules.
  The automated equivalence reasoner described herein makes this possible.

  Of course, rewriting based on equivalences is generally not sound. However, there are situations
  where it is indeed valid. For example, if the goal is \<^term>\<open>R x y\<close> where \<^term>\<open>R\<close> is known to be an
  equivalence relation, it is okay to use a fact \<^term>\<open>R x x'\<close> as a rewrite rule to turn that goal
  into \<^term>\<open>R x' y\<close>. A more complex example would be that of a goal \<^term>\<open>R (f x) y\<close> where \<^term>\<open>R\<close>
  is a congruence with respect to~\<^term>\<open>f\<close>. This goal can be safely turned into \<^term>\<open>R (f x') y\<close>.

  The facilities of the equivalence reasoner go even beyond these kinds of rewriting, making it a
  versatile tool for automated reasoning with equivalences. In particular, it is able to
  automatically turn a given rewrite rule \<^term>\<open>S x x'\<close> into a rewrite rule \<^term>\<open>R x x'\<close> if \<^term>\<open>S\<close>
  is known to be included in~\<^term>\<open>R\<close>, thus making the former rule usable for goals that involve
  \<^term>\<open>R\<close> instead of~\<^term>\<open>S\<close>.
\<close>

section \<open>Usage\<close>

text \<open>
  The equivalence reasoner attempts to prove statements of the form \<open>R _ _\<close> where \<^term>\<open>R\<close> is an
  equivalence relation. In the simplest case, it uses facts of the form \<open>R _ _\<close> as rewrite rules for
  repeatedly replacing the first and the second argument of~\<^term>\<open>R\<close> in the statement to prove. If
  both arguments become equal this way, it discharges the now trivial goal. Beyond this core
  functionality the equivalence reasoner has the following features:

    \<^item> Rewrite rules can use relations other than~\<^term>\<open>R\<close> as long as these relations are
      subrelations of~\<^term>\<open>R\<close>. It is not necessary for them to be equivalence relations themselves.

    \<^item> Rewriting can happen not only directly under the top-level~\<^term>\<open>R\<close>, but also further down
      under an additional stack of function applications, as long as the functions in this stack are
      compatible with~\<^term>\<open>R\<close>. For example, both occurrences of~\<^term>\<open>x\<close> in \<^term>\<open>R (f x (g x)) y\<close>
      can be replaced if \<^term>\<open>f\<close>~and~\<^term>\<open>g\<close> are compatible with~\<^term>\<open>R\<close>, and the first, if just
      \<^term>\<open>f\<close> is.

    \<^item> Rewrite rules can be conditional, that is, have the shape \<open>P\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> S t\<^sub>1 t\<^sub>2\<close>. The
      additional conditions \<^term>\<open>P\<^sub>1\<close> to~\<^term>\<open>P\<^sub>n\<close> must be solvable by the Simplifier.

  The equivalence reasoner offers its services via two proof methods:

    \<^item> The \<^theory_text>\<open>equivalence\<close> method attempts to prove the given equivalence statement and fails if it is
      unable to complete the proof.

    \<^item> The \<^theory_text>\<open>try_equivalence\<close> method attempts to prove the given equivalence statement, but does not
      fail if it is unable to complete the proof, but succeeds, leaving behind an intermediate goal
      it managed to reach. It is intended for debugging.

  Beware that the equivalence reasoner transforms the goal in non-trivial ways before performing the
  actual rewriting. The intermediate goals that \<^theory_text>\<open>try_equivalence\<close> leaves behind when being
  unsuccessful expose these transformations. As a result, such an intermediate goal is typically
  harder to comprehend than the original goal, and a follow-up invocation of the equivalence
  reasoner will almost certainly fail, even when using a different configuration. For details about
  the transformations the equivalence reasoner performs see Section~\ref{implementation}.

  Apart from their different names, both equivalence reasoner methods share the same interface. The
  syntax of invocations of these two methods and of underlying constructs is as follows:
  \<^rail>\<open>
    invocation:
      (@@{theory_text equivalence} | @@{theory_text try_equivalence}) (argument*);
    argument:
      (named_theorem | @@{theory_text simplification}) @@{theory_text \<open>:\<close>} thms;
    named_theorem:
      @@{theory_text equivalence} | @@{theory_text inclusion} | @@{theory_text compatibility}
  \<close>
  Both methods operate solely on the first subgoal and receive their input in the following way:

    \<^item> The equivalence to be proved is given as the goal conclusion. It must have the form \<open>R _ _\<close>
      where \<^term>\<open>R\<close> is known to the equivalence reasoner as an equivalence relation. If it does not
      have this form, the proof method fails.

    \<^item> Rewrite rules can be provided as premises, chained facts, or a mix of both. All premises and
      chained facts that are not valid rewrite rules are ignored.

    \<^item> The named theorem \<^theory_text>\<open>equivalence\<close> contains the fact \<^term>\<open>equivp R\<close> for every~\<^term>\<open>R\<close> that the
      equivalence reasoner shall recognize as an equivalence relation.

      Like with every named theorem, facts can be added to \<^theory_text>\<open>equivalence\<close> by applying an attribute
      named \<^theory_text>\<open>equivalence\<close> to them. Furthermore, additional facts can be provided for a particular
      method invocation by adding \<^theory_text>\<open>equivalence:\<close> followed by these facts to the method call.

      All facts that are not of the form \<open>equivp _\<close> are ignored, whether they have been added to the
      named theorem using the \<^theory_text>\<open>equivalence\<close> attribute or passed as method arguments.

    \<^item> The named theorem \<^theory_text>\<open>inclusion\<close> contains facts of the shape \<open>T \<le> U\<close> where \<^term>\<open>T\<close>~and~\<^term>\<open>U\<close>
      are relations. A rewrite rule that uses a relation~\<^term>\<open>S\<close> is considered valid for rewriting
      in an equivalence that uses an equivalence relation~\<^term>\<open>R\<close> exactly if the statement \<open>S \<le> R\<close>
      can be derived from the given inclusions using only reflexivity and transitivity of \<open>(\<le>)\<close> for
      relations.

      Analogously to \<^theory_text>\<open>equivalence\<close>, \<^theory_text>\<open>inclusion\<close> can be extended by attribute application and
      augmented via method arguments, and all facts that are not of the appropriate form are ignored.

    \<^item> The named theorem \<^theory_text>\<open>compatibility\<close> contains facts that establish compatibility of certain
      functions with certain equivalence relations. We call these facts compatibility rules. The
      compatibility of an \<^term>\<open>n\<close>-ary function~\<^term>\<open>f\<close> with an equivalence relation~\<^term>\<open>R\<close> is
      usually expressed using the statement
      \<open>\<And>x\<^sub>1 \<dots> x\<^sub>n y\<^sub>1 \<dots> y\<^sub>n. R x\<^sub>1 y\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> R x\<^sub>n y\<^sub>n \<Longrightarrow> R (f x\<^sub>1 \<dots> x\<^sub>n) (f y\<^sub>1 \<dots> y\<^sub>n)\<close>. However, the
      equivalence reasoner expects this compatibility to be stated as
      \<open>\<And>x\<^sub>1 \<dots> x\<^sub>n. R (f x\<^sub>1 \<dots> x\<^sub>n) (f (canonical R x\<^sub>1) \<dots> (canonical R x\<^sub>n))\<close>. This formulation uses
      certain constructs introduced by the equivalence reasoner:

        \<^item> A term \<^term>\<open>canonical R x\<close> denotes a value that is equivalent to~\<^term>\<open>x\<close> with respect
          to~\<^term>\<open>R\<close> and serves as a canonical form of all values that are equivalent to~\<^term>\<open>x\<close>.
          The term \<^term>\<open>canonical R x\<close> is an abbreviation for \<open>representative [x]\<^bsub>R\<^esub>\<close>.

        \<^item> A term \<open>[x]\<^bsub>R\<^esub>\<close> denotes the equivalence class of~\<^term>\<open>x\<close> with respect to~\<^term>\<open>R\<close>.

        \<^item> A term \<^term>\<open>representative X\<close> denotes an unspecified element of the equivalence
          class~\<^term>\<open>X\<close>.

      The equivalence reasoner does not insist on compatibility rules having precisely the format
      described above, but only requires them to be equivalences. As a result, compatibility rules
      can be used to trigger behavior more complex than just the application of actual
      compatibilities. To see exactly how the equivalence handler uses compatibility rules, turn
      to Section~\ref{implementation}.

      Analogously to \<^theory_text>\<open>equivalence\<close> and \<^theory_text>\<open>inclusion\<close>, \<^theory_text>\<open>compatibility\<close> can be extended by attribute
      application and augmented via method arguments. All facts that are not of the form \<open>R _ _\<close>
      where \<^term>\<open>R\<close> is the equivalence relation of the conclusion are ignored.

    \<^item> Simplification rules for solving conditions arising from the application of conditional
      rewrite rules can be provided by adding them to the method invocation preceded by
      \<^theory_text>\<open>simplification:\<close>. Simplification of conditions does not use any simplification rules beyond
      those explicitly provided.
\<close>

section \<open>Implementation\<close>

text_raw \<open>\label{implementation}\<close>

theory Equivalence_Reasoner
imports
  Main
  "HOL-Eisbach.Eisbach"
begin

text \<open>
  We declare the named theorems \<^theory_text>\<open>equivalence\<close>, \<^theory_text>\<open>inclusion\<close>, and \<^theory_text>\<open>compatibility\<close>.
\<close>

named_theorems equivalence and inclusion and compatibility

text \<open>
  We implement the \<^theory_text>\<open>equivalence\<close> method.
\<close>

method equivalence declares equivalence inclusion compatibility = (
  \<comment> \<open>Insert a dummy premise into the first subgoal to guarantee the subsequent match to succeed:\<close>
  insert TrueI;
  \<comment> \<open>Excavate the premises of the first subgoal and use them to solve the remaining goal:\<close>
  match premises in prems [thin]: _ (multi, cut) \<Rightarrow> \<open>
    \<comment> \<open>Block direct access to the chained facts and solve the goal:\<close>
    use nothing in \<open>
      \<comment> \<open>Solve the goal via intuitionistic proof search:\<close>
      iprover
        intro!:
          equivalence [THEN equivp_reflp]
        intro:
          equivalence [THEN equivp_symp]
          equivalence [THEN equivp_transp]
          inclusion [THEN predicate2D]
          compatibility
          method_facts
          prems
    \<close>
  \<close>
)

text \<open>
  This concludes the implementation of the equivalence reasoner.
\<close>

end
