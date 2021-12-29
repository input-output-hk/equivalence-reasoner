text_raw \<open>\appendix\<close>

section \<open>Usage Example\<close>

theory "Equivalence_Reasoner-Usage_Example"
imports
  Equivalence_Reasoner
  "HOL-Library.Extended_Nonnegative_Real"
begin

subsection \<open>Extended Reals\<close>

setup_lifting type_definition_ennreal

function extended_exp :: "ereal \<Rightarrow> ennreal" where
  "extended_exp (-\<infinity>) = 0" |
  "extended_exp x = exp x" for x :: real |
  "extended_exp \<infinity> = \<infinity>"
  by (erule ereal_cases, simp_all)
  termination by standard+

function extended_ln :: "ennreal \<Rightarrow> ereal" where
  "extended_ln 0 = -\<infinity>" |
  "extended_ln x = ln x" if "x > 0" for x :: real |
  "extended_ln \<infinity> = \<infinity>"
  by (rule ennreal_cases, force, simp_all)
  termination by standard+

lemma extended_exp_of_sum:
  assumes "x \<noteq> \<infinity>" and "y \<noteq> \<infinity>"
  shows "extended_exp (x + y) = extended_exp x * extended_exp y"
  using assms
  by
    (cases x rule: extended_exp.cases; cases y rule: extended_exp.cases)
    (simp_all add: exp_add ennreal_mult)

lemma extended_ln_of_product:
  assumes "x \<noteq> \<infinity>" and "y \<noteq> \<infinity>"
  shows "extended_ln (x * y) = extended_ln x + extended_ln y"
  using assms
  by
    (cases x rule: extended_ln.cases; cases y rule: extended_ln.cases)
    (simp_all add: ln_mult ennreal_mult [symmetric])

lemma extended_ln_after_extended_exp:
  shows "extended_ln (extended_exp x) = x"
  by (cases x rule: extended_exp.cases) (simp_all del: infinity_ennreal_def)

lemma extended_exp_after_extended_ln:
  shows "extended_exp (extended_ln x) = x"
  by (cases x rule: extended_ln.cases) (simp_all del: infinity_ennreal_def)

lemma extended_exp_surjectivity:
  shows "surj extended_exp"
  using extended_exp_after_extended_ln
  by (rule surjI)

lemma extended_ln_surjectivity:
  shows "surj extended_ln"
  using extended_ln_after_extended_exp
  by (rule surjI)

lemma extended_exp_monotonicity:
  shows "mono extended_exp"
proof
  fix x y :: ereal
  assume "x \<le> y"
  then show "extended_exp x \<le> extended_exp y"
    by (cases x rule: extended_exp.cases; cases y rule: extended_exp.cases) simp_all
qed

lemma extended_ln_monotonicity:
  shows "mono extended_ln"
proof
  fix x y :: ennreal
  assume "x \<le> y"
  then show "extended_ln x \<le> extended_ln y"
    by
      (cases x rule: extended_ln.cases; cases y rule: extended_ln.cases)
      (
        (simp_all del: infinity_ennreal_def)[7],
        metis ennreal_less_top infinity_ennreal_def not_le,
        simp
      )
qed

lemma extended_exp_continuity:
  shows "continuous_on UNIV extended_exp"
  by
    (rule continuous_onI_mono)
    (simp add: extended_exp_surjectivity, rule extended_exp_monotonicity [THEN monoD])

lemma extended_ln_continuity:
  shows "continuous_on UNIV extended_ln"
  by
    (rule continuous_onI_mono)
    (simp add: extended_ln_surjectivity, rule extended_ln_monotonicity [THEN monoD])

end
