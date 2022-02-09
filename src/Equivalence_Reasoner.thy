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
  "HOL-Eisbach.Eisbach_Tools"
    \<comment>\<open>Besides Eisbach, we use the @{attribute uncurry} attribute from the Eisbach tools.\<close>
begin

context begin

text \<open>
  We start with defining what an equivalence class, a representative, and a canonical form are.
\<close>

definition equivalence_class :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" (\<open>[_]\<^bsub>_\<^esub>\<close>) where
  "[x]\<^bsub>R\<^esub> = {y. R x y}"

definition representative :: "'a set \<Rightarrow> 'a" where
  "representative X = (SOME x. x \<in> X)"

abbreviation canonical :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "canonical R x \<equiv> representative [x]\<^bsub>R\<^esub>"

text \<open>
  The key idea of our implementation is to turn equivalences into equalities of equivalence classes
  and solve the resulting goals using the Simplifier. The translation from equivalences to
  equalities that are ready for simplification works as follows:

    \<^item> First, each equivalence \<^term>\<open>R t\<^sub>1 t\<^sub>2\<close> is turned into \<^term>\<open>[t\<^sub>1]\<^bsub>R\<^esub> = [t\<^sub>2]\<^bsub>R\<^esub>\<close>.

    \<^item> Second, each equivalence class construction \<^term>\<open>[t\<^sub>1]\<^bsub>R\<^esub>\<close> for which there is a compatibility
      rule \<^term>\<open>R t\<^sub>1 t\<^sub>2\<close> is turned into \<^term>\<open>[t\<^sub>2]\<^bsub>R\<^esub>\<close>. This is done repeatedly until no such
      replacement is possible anymore.

  Both of these steps involve converting equivalences into equalities of equivalence classes: the
  first step converts subterms of the goal, the second step converts compatibility rules, generating
  rewrite rules that perform the described replacement. We prove a lemma that enables such
  conversions.
\<close>

lemma equivalence_is_equivalence_class_equality:
  assumes "equivp R"
  shows "R x y \<longleftrightarrow> [x]\<^bsub>R\<^esub> = [y]\<^bsub>R\<^esub>"
  using assms
  unfolding equivp_def and equivalence_class_def
  by auto

text \<open>
  Actually, performing the second of the above steps will typically result in endless looping. To
  see why, consider the compatibility rule \<^term>\<open>\<And>x. R (f x) (f (canonical R x))\<close>, which is
  probably one of the simplest of its kind. Let us assume the first of the above steps has produced
  a subterm \<^term>\<open>[f (f x)]\<^bsub>R\<^esub>\<close>. We want the second step to turn this subterm first into
  \<^term>\<open>[f (canonical R (f x))]\<^bsub>R\<^esub>\<close> and further into \<^term>\<open>[f (canonical R (f (canonical R x)))]\<^bsub>R\<^esub>\<close>.
  These translations are surely possible (the second one uses the fact that \<^term>\<open>canonical R (f x)\<close>
  is shorthand for \<^term>\<open>representative [f x]\<^bsub>R\<^esub>\<close> and thus contains another equivalence class
  construction). However, they are not the only ones that can be performed, as the compatibility
  rule permits the replacement of any subterm of the form \<open>[f _]\<^bsub>R\<^esub>\<close> by another subterm of this
  form, making it possible to perform further such replacements \<^emph>\<open>ad infinitum\<close>.

  We solve this problem by letting the replacement subterms use an alternative equivalence class
  constructor \<^term>\<open>frozen_equivalence_class\<close> instead of the standard one. The constant
  \<^term>\<open>frozen_equivalence_class\<close> equals \<^const>\<open>equivalence_class\<close>, but its use makes rewrite rules
  that require \<^const>\<open>equivalence_class\<close> unapplicable. With this correction in place, the second
  step turns \<^term>\<open>[f (f x)]\<^bsub>R\<^esub>\<close> into \<^term>\<open>frozen_equivalence_class (f (canonical R (f x))) R\<close> and
  this further into
  \<^term>\<open>frozen_equivalence_class (f (representative (frozen_equivalence_class (f (canonical R x)) R))) R\<close>.
  From there, no further translations are possible.
\<close>

private definition frozen_equivalence_class :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" where
  "frozen_equivalence_class = equivalence_class"

private lemma equivalence_is_right_frozen_equivalence_class_equality:
  assumes "equivp R"
  shows "R x y \<longleftrightarrow> [x]\<^bsub>R\<^esub> = frozen_equivalence_class y R"
  unfolding frozen_equivalence_class_def
  using equivalence_is_equivalence_class_equality [OF assms] .

text \<open>
  We introduce a helper method \<^theory_text>\<open>generate_relax_inclusions\<close> that takes a set of inclusions and a
  relation~\<^term>\<open>R\<close> and computes the set of all inclusions that can be derived from the inclusions
  in the given set using only reflexivity and transitivity and furthermore have the form \<open>_ \<le> R\<close>.
  The inclusions in the resulting set are called relax inclusions, since they are supposed to be fed
  into the \<^theory_text>\<open>relax\<close> method defined below.

  The \<^theory_text>\<open>generate_relax_inclusions\<close> method does not receive its input inclusions via a fact argument,
  but as goal premises. This is because it needs to iterate over them, and the only possible way to
  do that in Eisbach seems to involve removing them one by one, which in turn seems to be possible
  only if storing them as premises (premises can be removed via the @{attribute thin} attribute).

  The \<^theory_text>\<open>generate_relax_inclusions\<close> method considers only those premises that are of the shape
  \<^term>\<open>S \<le> T\<close> where \<^term>\<open>S\<close>~and~\<^term>\<open>T\<close> have the same type as~\<^term>\<open>R\<close>. It drops all other
  premises.

  Output inclusions are delivered as the premises of the resulting goal, since methods can
  communicate information to their callers only via the goal state.

  To iterate through the input inclusions, the \<^theory_text>\<open>generate_relax_inclusions\<close> method recursively
  invokes itself. Since it already uses the goal premises for storing the shrinking set of input
  inclusions, it stores the growing set of output inclusions in a fact argument \<^theory_text>\<open>accumulator\<close>,
  which is amended at each recursive invocation. Users of the method should not specify this
  argument, so that the method starts with \<^theory_text>\<open>accumulator\<close> being the empty fact list.
\<close>

private method generate_relax_inclusions for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" uses accumulator = (
  \<comment> \<open>Pick an input inclusion of the form \<open>_ \<le> R\<close>, called a base inclusion, and process it:\<close>
  match premises in base [thin]: "S \<le> R" (cut) for S \<Rightarrow> \<open>
    \<comment> \<open>If the base inclusion is extendable, add its extensions to the set of input inclusions:\<close>
    (
      \<comment> \<open>Add the extensions of the base inclusion to the set of input inclusions:\<close>
      match premises in extensions [thin]: "_ \<le> S" (multi, cut) \<Rightarrow> \<open>
        insert extensions [THEN order_trans, OF base]
      \<close>
    )?,
    \<comment> \<open>Continue with the base inclusion added to the set of output inclusions:\<close>
    generate_relax_inclusions R accumulator: accumulator base
  \<close> |
  \<comment> \<open>Remove all unused input inclusions and invalid premises:\<close>
  (match premises in leftover [thin]: _ (multi, cut) \<Rightarrow> \<open>succeed\<close>)?,
  \<comment> \<open>Add \<^term>\<open>R \<le> R\<close> to the set of output inclusions and return the result:\<close>
  insert accumulator order_refl [of R]
)

text \<open>
  We introduce a helper method \<^theory_text>\<open>relax\<close> that takes a set of inclusions and a set of rewrite rules
  and turns each rewrite rule of the shape \<open>P\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> S t\<^sub>1 t\<^sub>2\<close> for which \<^term>\<open>S \<le> R\<close> is
  among the given inclusions into \<open>P\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> R t\<^sub>1 t\<^sub>2\<close>, ignoring all other facts from the
  set of rewrite rules. It receives the inclusions as goal premises and delivers the output rewrite
  rules as the premises of the resulting goal.

  The \<^theory_text>\<open>relax\<close> method recursively invokes itself. It removes the inclusions one by one from the goal
  and collects the output rewrite rules in a fact argument \<^theory_text>\<open>accumulator\<close>. As with
  @{method generate_relax_inclusions}, users of \<^theory_text>\<open>relax\<close> should not specify the \<^theory_text>\<open>accumulator\<close>
  argument, so that the method starts with \<^theory_text>\<open>accumulator\<close> being the empty fact list.
\<close>

private method relax uses rewrite_rules accumulator = (
  \<comment> \<open>Pick an inclusion and use it to process the rewrite rules that fit it:\<close>
  match premises in inclusion [thin]: "S \<le> _" (cut) for S :: "'a \<Rightarrow> 'a \<Rightarrow> bool" \<Rightarrow> \<open>
    \<comment> \<open>Move all remaining premises back into the goal\<^footnote>\<open>See \<^url>\<open>https://github.com/input-output-hk/equivalence-reasoner/issues/24\<close> for the reason of that.\<close>:\<close>
    (match premises in remaining [thin]: _ (multi, cut) \<Rightarrow> \<open>insert remaining\<close>)?,
    \<comment> \<open>Get the rewrite rules that fit the inclusion and process them:\<close>
    match rewrite_rules [THEN TrueE [rotated], uncurry] in
      current_rewrite_rules_mangled: "_ \<Longrightarrow> S _ _" (multi, cut) \<Rightarrow> \<open>
        \<comment> \<open>Continue with the relaxed rewrite rules added to the set of output rewrite rules:\<close>
        relax
          rewrite_rules:
            rewrite_rules
          accumulator:
            accumulator
            current_rewrite_rules_mangled
              [curry, rotated -1, OF TrueI, THEN inclusion [THEN predicate2D]]
      \<close> |
    \<comment> \<open>Continue with the set of output rewrite rules unchanged:\<close>
    relax
      rewrite_rules: rewrite_rules
      accumulator: accumulator
  \<close> |
  \<comment> \<open>Return the set of output rewrite rules:\<close>
  insert accumulator
)

text \<open>
  We declare the named theorems \<^theory_text>\<open>equivalence\<close>, \<^theory_text>\<open>inclusion\<close>, and \<^theory_text>\<open>compatibility\<close>.
\<close>

named_theorems equivalence and inclusion and compatibility

text \<open>
  We implement the \<^theory_text>\<open>try_equivalence\<close> method.
\<close>

method try_equivalence uses simplification declares equivalence inclusion compatibility = (
  \<comment> \<open>Try to solve the first subgoal:\<close>
  match conclusion in _ \<Rightarrow> \<open>
    \<comment> \<open>Turn all chained facts into goal premises and try to solve the resulting goal:\<close>
    -, use nothing in \<open>
      \<comment> \<open>Get the equivalence relation of the conclusion and preprocess the goal based on it:\<close>
      match equivalence in current_equivalence: "equivp R" for R \<Rightarrow> \<open>
        \<comment> \<open>Make sure the equivalence relation is the one of the conclusion (if it is not, backtrack):\<close>
        match conclusion in "R _ _"  (cut) \<Rightarrow> \<open>succeed\<close>,
        \<comment> \<open>If any premises exist, relax all premises that can be relaxed and drop all others:\<close>
        (
          \<comment> \<open>Relax all premises that can be relaxed and drop all others:\<close>
          match premises in rewrite_rules [thin]: _ (multi, cut) \<Rightarrow> \<open>
            insert inclusion,
            generate_relax_inclusions R,
            relax rewrite_rules: rewrite_rules
          \<close>
        )?,
        \<comment> \<open>Turn equivalences into equalities of equivalence class constructions:\<close>
        simp (no_asm_use) only: current_equivalence [THEN equivalence_is_equivalence_class_equality],
        \<comment> \<open>If compatibility rules for~\<^term>\<open>R\<close> exist and are applicable to the goal, apply them:\<close>
        (
          match compatibility in current_compatibilities: "R _ _" (multi, cut) \<Rightarrow> \<open>
            unfold
              current_compatibilities
                [simplified
                  current_equivalence [THEN equivalence_is_right_frozen_equivalence_class_equality]
                ]
          \<close>,
          unfold frozen_equivalence_class_def
        )?
      \<close>,
      \<comment> \<open>Simplify the conclusion, using the premises and the given simplification rules:\<close>
      (simp (no_asm_simp) only: simplification)?
    \<close>
  \<close>
)

text \<open>
  Finally, we implement the \<^theory_text>\<open>equivalence\<close> method.

  We introduce the arguments \<^theory_text>\<open>equivalence\<close>, \<^theory_text>\<open>inclusion\<close>, and \<^theory_text>\<open>compatibility\<close> as fact arguments
  instead of declaration arguments. This is because \<^theory_text>\<open>equivalence\<close> invokes
  @{method try_equivalence}, which expects to receive only additions to the named theorems and
  augments the named theorems with those. If \<^theory_text>\<open>equivalence\<close> would already augment the named
  theorems, the fact lists that @{method try_equivalence} ultimately uses would contain the facts
  from the unaugmented named theorems twice.
\<close>

method equivalence uses equivalence inclusion compatibility simplification = (
  \<comment> \<open>Invoke @{method try_equivalence}:\<close>
  try_equivalence
    equivalence: equivalence
    inclusion: inclusion
    compatibility: compatibility
    simplification: simplification;
  \<comment> \<open>Fail (only done if @{method try_equivalence} has left a goal, because of the \<^theory_text>\<open>;\<close>-combinator):\<close>
  fail
)

text \<open>
  This concludes the implementation of the equivalence reasoner.
\<close>

end

end
