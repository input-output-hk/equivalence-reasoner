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

    \<^item> Rewrite rules can be conditional, that is, have the shape \<open>P\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> S x y\<close>. The
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

  Both equivalence reasoner methods share the same interface, which has the following appearance:

    \<^item> The equivalence to be proved is given as the goal conclusion. It must have the form \<open>R _ _\<close>
      where \<^term>\<open>R\<close> is known to the equivalence reasoner as an equivalence relation. If it does not
      have this form, the proof method fails.

    \<^item> Rewrite rules can be provided as premises, chained facts, or a mix of both. All premises and
      chained facts that are not valid rewrite rules are ignored.

    \<^item> There is a named theorem \<^theory_text>\<open>equivalence\<close> that contains the fact \<^term>\<open>equivp R\<close> for
      every~\<^term>\<open>R\<close> that the equivalence reasoner shall recognize as an equivalence relation.

      Like with every named theorem, facts can be added to \<^theory_text>\<open>equivalence\<close> by applying an attribute
      named \<^theory_text>\<open>equivalence\<close> to them. Furthermore, additional facts can be provided for a particular
      method invocation by adding \<^theory_text>\<open>equivalence:\<close> followed by these facts to the method call.

      All facts that are not of the form \<open>equivp _\<close> are ignored, whether they have been added to the
      named theorem using the \<^theory_text>\<open>equivalence\<close> attribute or passed as method arguments.

    \<^item> There is a named theorem \<^theory_text>\<open>inclusion\<close> that contains facts of the shape \<open>T \<le> U\<close> where
      \<^term>\<open>T\<close>~and~\<^term>\<open>U\<close> are relations. A rewrite rule that uses a relation~\<^term>\<open>S\<close> is considered
      valid for rewriting an equivalence that uses an equivalence relation~\<^term>\<open>R\<close> exactly if the
      statement \<open>S \<le> R\<close> can be derived from the given inclusions using only reflexivity and
      transitivity of \<open>(\<le>)\<close> for relations.

      Like with \<^theory_text>\<open>equivalence\<close>, \<^theory_text>\<open>inclusion\<close> can be augmented via method arguments, and all facts
      that are not of the appropriate form are ignored.

    \<^item> There is a named theorem \<^theory_text>\<open>compatibility\<close> that contains facts that establish compatibility of
      certain functions with certain equivalence relations. We call these facts compatibility rules.
      The compatibility of an \<^term>\<open>n\<close>-ary function~\<^term>\<open>f\<close> with an equivalence relation~\<^term>\<open>R\<close> is
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

      Like with \<^theory_text>\<open>equivalence\<close> and \<^theory_text>\<open>inclusion\<close>, \<^theory_text>\<open>compatibility\<close> can be augmented via method
      arguments. All facts that are not of the form \<open>R _ _\<close> where \<^term>\<open>R\<close> is the equivalence
      relation of the conclusion are ignored.

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

    \<^item> First, each equivalence \<^term>\<open>R x y\<close> is turned into \<^term>\<open>[x]\<^bsub>R\<^esub> = [y]\<^bsub>R\<^esub>\<close>.

    \<^item> Second, each equivalence class construction \<^term>\<open>[x]\<^bsub>R\<^esub>\<close> for which there is a compatibility
      rule \<^term>\<open>R x y\<close> is turned into \<^term>\<open>[y]\<^bsub>R\<^esub>\<close>. This is done repeatedly until no such
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

definition frozen_equivalence_class :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" where
  "frozen_equivalence_class = equivalence_class"

lemma equivalence_is_right_frozen_equivalence_class_equality:
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

method generate_relax_inclusions for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" uses accumulator = (
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
  We introduce a helper method \<^theory_text>\<open>relax\<close> that takes a set of inclusions and turns all goal premises
  of the shape \<open>P\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> S x y\<close> for which \<^term>\<open>S \<le> R\<close> is among the given inclusions into
  \<open>P\<^sub>1 \<Longrightarrow> \<cdots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> R x y\<close>, while dropping all other premises.

  The \<^theory_text>\<open>relax\<close> method recursively invokes itself. It removes the input premises one by one from the
  goal and collects the output premises in a fact argument \<^theory_text>\<open>accumulator\<close>. As with
  @{method generate_relax_inclusions}, users of \<^theory_text>\<open>relax\<close> should not specify the \<^theory_text>\<open>accumulator\<close>
  argument, so that the method starts with \<^theory_text>\<open>accumulator\<close> being the empty fact list.
\<close>

method relax uses inclusions accumulator = (
  \<comment> \<open>Pick a premise and process it:\<close>
  match premises in premise [thin]: _ (cut) \<Rightarrow> \<open>
    \<comment> \<open>Move all remaining premises back into the goal (see \#24 for the reason of that):\<close>
    (match premises in remaining [thin]: _ (multi, cut) \<Rightarrow> \<open>insert remaining\<close>)?,
    \<comment> \<open>Get the inclusion that fits the premise and process the premise using it:\<close>
    match inclusions in inclusion: "S \<le> _" for S :: "'a \<Rightarrow> 'a \<Rightarrow> bool" \<Rightarrow> \<open>
      \<comment> \<open>Make sure the inclusion fits the premise (if it does not, backtrack):\<close>
      match premise [uncurry] in
        "S _ _" (cut) \<Rightarrow> \<open>succeed\<close> \<bar>
        "_ \<Longrightarrow> S _ _" (cut) \<Rightarrow> \<open>succeed\<close>,
      \<comment> \<open>Continue with the relaxed premise added to the set of output premises:\<close>
      match ("()") in "()" \<Rightarrow> \<open>
        relax
          inclusions: inclusions
          accumulator: accumulator premise [THEN inclusion [THEN predicate2D]]
      \<close>
    \<close> |
    \<comment> \<open>Continue with the set of output premises unchanged:\<close>
    relax
      inclusions: inclusions
      accumulator: accumulator
  \<close> |
  \<comment> \<open>Return the set of output premises:\<close>
  insert accumulator
)

text \<open>
  We introduce a helper method \<^theory_text>\<open>raw_equivalence\<close> that essentially works like \<^theory_text>\<open>try_equivalence\<close>.
  The only difference is that \<^theory_text>\<open>raw_equivalence\<close> does not use the named theorems \<^theory_text>\<open>equivalence\<close>,
  \<^theory_text>\<open>inclusion\<close>, and \<^theory_text>\<open>compatibility\<close>, but receives the respective fact lists as fact arguments. This
  enables us to use \<^theory_text>\<open>raw_equivalence\<close> in the implementation of the \<^theory_text>\<open>equivalence\<close> method. If
  \<^theory_text>\<open>equivalence\<close> would invoke \<^theory_text>\<open>try_equivalence\<close> instead of \<^theory_text>\<open>raw_equivalence\<close>, the facts that come
  from the unaugmented named theorems \<^theory_text>\<open>equivalence\<close>, \<^theory_text>\<open>inclusion\<close>, and \<^theory_text>\<open>compatibility\<close> would be
  duplicated: \<^theory_text>\<open>equivalence\<close> would augment all named theorems with the corresponding declaration
  arguments and could only use the resulting fact lists in its invocation of \<^theory_text>\<open>try_equivalence\<close>,
  which would augment the named theorems with these fact lists.
\<close>

method raw_equivalence uses equivalence inclusion compatibility simplification = (
  \<comment> \<open>Turn all chained facts into goal premises and try to solve the resulting goal:\<close>
  -, use nothing in \<open>
    \<comment> \<open>Get the equivalence relation that is used by the conclusion and perform relaxation using it:\<close>
    match equivalence in current_equivalence: "equivp R" for R \<Rightarrow> \<open>
      \<comment> \<open>Make sure the equivalence relation is used by the conclusion (if it is not, backtrack):\<close>
      match conclusion in "R _ _"  (cut) \<Rightarrow> \<open>succeed\<close>,
      \<comment> \<open>If any premises exist, relax all premises that can be relaxed and drop all others:\<close>
      (
        \<comment> \<open>Relax all premises that can be relaxed and drop all others:\<close>
        match premises in original_premises [thin]: _ (multi, cut) \<Rightarrow> \<open>
          insert inclusion,
          generate_relax_inclusions R,
          match premises in relax_inclusions [thin]: _ (multi, cut) \<Rightarrow> \<open>
            insert original_premises,
            relax inclusions: relax_inclusions
          \<close>
        \<close>
      )?
    \<close>,
    \<comment> \<open>Turn equivalences into equalities, taking compatibility rules into account:\<close>
    simp (no_asm_use) only:
      equivalence
        [THEN equivalence_is_equivalence_class_equality]
      compatibility
        [simplified equivalence [THEN equivalence_is_right_frozen_equivalence_class_equality]],
    \<comment> \<open>Unfreeze all frozen equivalence class constructions:\<close>
    (unfold frozen_equivalence_class_def)?,
    \<comment> \<open>Simplify the conclusion, using the premises and the given simplification rules:\<close>
    (simp (no_asm_simp) only: simplification)?
  \<close>
)

text \<open>
  We declare the named theorems \<^theory_text>\<open>equivalence\<close>, \<^theory_text>\<open>inclusion\<close>, and \<^theory_text>\<open>compatibility\<close>.
\<close>

named_theorems equivalence and inclusion and compatibility

text \<open>
  Finally, we implement the methods we offer to the user.
\<close>

method try_equivalence uses simplification declares equivalence inclusion compatibility = (
  \<comment> \<open>Invoke @{method raw_equivalence} with the augmented named theorems and the simplification rules:\<close>
  raw_equivalence
    equivalence: equivalence
    inclusion: inclusion
    compatibility: compatibility
    simplification: simplification
)

method equivalence uses simplification declares equivalence inclusion compatibility = (
  \<comment> \<open>Invoke @{method raw_equivalence} with the augmented named theorems and the simplification rules:\<close>
  raw_equivalence
    equivalence: equivalence
    inclusion: inclusion
    compatibility: compatibility
    simplification: simplification;
  \<comment> \<open>Fail (only done if @{method raw_equivalence} left a goal, because of the \<^theory_text>\<open>;\<close>-combinator):\<close>
  fail
)

text \<open>
  This concludes the implementation of the equivalence reasoner.
\<close>

end
