theory Equivalence_Reasoner
imports
  Main
  "HOL-Eisbach.Eisbach_Tools"
begin

definition equivalence_class :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" (\<open>[_]\<^bsub>_\<^esub>\<close>) where
  "[x]\<^bsub>R\<^esub> = {y. R x y}"

definition frozen_equivalence_class :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" where
  "frozen_equivalence_class = equivalence_class"

lemma equivalence_is_equivalence_class_equality:
  assumes "equivp R"
  shows "R x y \<longleftrightarrow> [x]\<^bsub>R\<^esub> = [y]\<^bsub>R\<^esub>"
  using assms
  unfolding equivp_def and equivalence_class_def
  by auto

lemma equivalence_is_right_frozen_equivalence_class_equality:
  assumes "equivp R"
  shows "R x y \<longleftrightarrow> [x]\<^bsub>R\<^esub> = frozen_equivalence_class y R"
  unfolding frozen_equivalence_class_def
  using equivalence_is_equivalence_class_equality [OF assms] .

definition representative :: "'a set \<Rightarrow> 'a" where
  "representative X = (SOME x. x \<in> X)"

abbreviation canonical :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "canonical R x \<equiv> representative [x]\<^bsub>R\<^esub>"

method generate_relax_inclusions for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" uses processed = (
  match premises in first [thin]: "S \<le> R" (cut) for S \<Rightarrow> \<open>
    (
      match premises in second [thin]: "_ \<le> S" (multi, cut) \<Rightarrow> \<open>
        insert second [THEN order_trans, OF first]
      \<close>
    )?,
    generate_relax_inclusions R processed: processed first
  \<close> |
  (match premises in unused [thin]: _ (multi, cut) \<Rightarrow> \<open>succeed\<close>)?,
  insert processed order_refl [of R]
)

method relax uses inclusions processed = (
  match premises in first [thin]: _ (cut) \<Rightarrow> \<open>
    match inclusions in inclusion: "S \<le> _" for S :: "'a \<Rightarrow> 'a \<Rightarrow> bool" \<Rightarrow> \<open>
      match first in
        "S _ _" (cut) \<Rightarrow> \<open>succeed\<close> \<bar>
        _ [uncurry]: "_ \<Longrightarrow> S _ _" (cut) \<Rightarrow> \<open>succeed\<close>,
      relax
        inclusions: inclusions
        processed: processed first [THEN inclusion [THEN predicate2D]]
    \<close> |
    relax
      inclusions: inclusions
      processed: processed
  \<close> |
  insert processed
)

method raw_equivalence uses equivalence inclusion compatibility simplification = (
  -, use nothing in \<open>
    match equivalence in current_equivalence: "equivp R" for R \<Rightarrow> \<open>
      match conclusion in "R _ _"  (cut) \<Rightarrow> \<open>succeed\<close>,
      (
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
    simp (no_asm_use) only:
      equivalence
        [THEN equivalence_is_equivalence_class_equality]
      compatibility
        [simplified equivalence [THEN equivalence_is_right_frozen_equivalence_class_equality]],
    (unfold frozen_equivalence_class_def)?,
    (simp (no_asm_simp) only: simplification)?
  \<close>
)

named_theorems equivalence and inclusion and compatibility

method try_equivalence uses simplification declares equivalence inclusion compatibility = (
  raw_equivalence
    equivalence: equivalence
    inclusion: inclusion
    compatibility: compatibility
    simplification: simplification
)

method equivalence uses simplification declares equivalence inclusion compatibility = (
  raw_equivalence
    equivalence: equivalence
    inclusion: inclusion
    compatibility: compatibility
    simplification: simplification;
  fail
)

end
