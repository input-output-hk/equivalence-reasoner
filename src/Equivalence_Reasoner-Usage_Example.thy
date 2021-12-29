text_raw \<open>\appendix\<close>

section \<open>Usage Example\<close>

theory "Equivalence_Reasoner-Usage_Example"
imports
  Equivalence_Reasoner
  "HOL-Analysis.Extended_Real_Limits"
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

subsection \<open>Positive Reals\<close>

typedef positive_real = "{x :: real. x > 0}"
  using zero_less_one
  by blast

setup_lifting type_definition_positive_real

instantiation positive_real :: comm_semiring
begin

lift_definition plus_positive_real :: "positive_real \<Rightarrow> positive_real \<Rightarrow> positive_real"
  is "(+)"
  using add_pos_pos .

lift_definition times_positive_real :: "positive_real \<Rightarrow> positive_real \<Rightarrow> positive_real"
  is "(*)"
  using mult_pos_pos .

instance by (standard; transfer) (simp_all add: algebra_simps)

end

instantiation positive_real :: comm_monoid_mult
begin

lift_definition one_positive_real :: positive_real
  is 1
  using zero_less_one .

instance by (standard; transfer) simp

end

instantiation positive_real :: inverse
begin

lift_definition divide_positive_real :: "positive_real \<Rightarrow> positive_real \<Rightarrow> positive_real"
  is "(/)"
  using divide_pos_pos .

lift_definition inverse_positive_real :: "positive_real \<Rightarrow> positive_real"
  is inverse
  using positive_imp_inverse_positive .

instance ..

end

instantiation positive_real :: unbounded_dense_linorder
begin

lift_definition less_eq_positive_real :: "positive_real \<Rightarrow> positive_real \<Rightarrow> bool"
  is "(\<le>)" .

lift_definition less_positive_real :: "positive_real \<Rightarrow> positive_real \<Rightarrow> bool"
  is "(<)" .

instance proof ((standard; transfer), unfold bex_simps(6))
  show "\<exists>z > 0. x < z \<and> z < y" if "x > 0" and "x < y" for x y :: real
  proof
    show "(x + y) / 2 > 0 \<and> x < (x + y) / 2 \<and> (x + y) / 2 < y"
      using that
      by simp
  qed
next
  show "\<exists>y > 0. y > x" if "x > 0" for x :: real
    using gt_ex and that
    by (iprover intro: less_trans)
next
  show "\<exists>y > 0. y < x" if "x > 0" for x :: real
    using dense [OF that] .
qed auto

end

lift_definition extended_non_negative_real :: "positive_real \<Rightarrow> ennreal"
  is ennreal .

lemma extended_non_negative_real_is_finite:
  shows "extended_non_negative_real x \<noteq> \<infinity>"
  by transfer simp

lemma extended_non_negative_real_of_product:
  shows "
    extended_non_negative_real (x * y)
    =
    extended_non_negative_real x * extended_non_negative_real y"
  by transfer (simp only: ennreal_mult)

subsection \<open>Sequences of Positive Reals\<close>

typedef sequence = "UNIV :: (nat \<Rightarrow> positive_real) set"
  by simp

setup_lifting type_definition_sequence

instantiation sequence :: comm_semiring
begin

lift_definition plus_sequence :: "sequence \<Rightarrow> sequence \<Rightarrow> sequence"
  is "\<lambda>X Y. \<lambda>i. X i + Y i" .

lift_definition times_sequence :: "sequence \<Rightarrow> sequence \<Rightarrow> sequence"
  is "\<lambda>X Y. \<lambda>i. X i * Y i" .

instance by (standard; transfer) (simp_all add: algebra_simps)

end

instantiation sequence :: comm_monoid_mult
begin

lift_definition one_sequence :: sequence
  is "\<lambda>_. 1" .

instance by (standard; transfer) simp

end

instantiation sequence :: inverse
begin

lift_definition divide_sequence :: "sequence \<Rightarrow> sequence \<Rightarrow> sequence"
  is "\<lambda>X Y. \<lambda>i. X i / Y i" .

lift_definition inverse_sequence :: "sequence \<Rightarrow> sequence"
  is "\<lambda>X. \<lambda>i. inverse (X i)" .

instance ..

end

instantiation sequence :: dense_order
begin

lift_definition less_eq_sequence :: "sequence \<Rightarrow> sequence \<Rightarrow> bool"
  is "(\<le>)" .

lift_definition less_sequence :: "sequence \<Rightarrow> sequence \<Rightarrow> bool"
  is "(<)" .

instance proof (standard; transfer)
  show "\<exists>Z > X. Z < Y" if "X < Y" for X Y Z :: "nat \<Rightarrow> positive_real"
  proof -
    from \<open>X < Y\<close> obtain i where "X i < Y i"
      by (metis leD le_funI leI)
    then obtain z where "X i < z" and "z < Y i"
      using dense
      by blast
    with \<open>X < Y\<close> have "X < X(i := z)" and "X(i := z) < Y"
      by (auto simp add: less_le_not_le le_fun_def)
    then show ?thesis
      by iprover
  qed
qed (simp_all add: less_le_not_le)

end

lift_definition limit_superior :: "sequence \<Rightarrow> ennreal"
  is "\<lambda>X. limsup (\<lambda>i. extended_non_negative_real (X i))" .

lemma limit_superior_of_product:
  assumes "limit_superior X \<noteq> \<infinity>" and "limit_superior Y \<noteq> \<infinity>"
  shows "limit_superior (X * Y) \<le> limit_superior X * limit_superior Y"
proof -
  note Limsup_after_extended_ln =
    Limsup_compose_continuous_mono [OF extended_ln_continuity extended_ln_monotonicity]
  have raw_thesis:
    "limsup (\<lambda>i. X i * Y i) \<le> limsup X * limsup Y"
    if "\<And>i. X i \<noteq> \<infinity>" and "\<And>i. Y i \<noteq> \<infinity>" and "limsup X \<noteq> \<infinity>" and "limsup Y \<noteq> \<infinity>"
    for X Y :: "nat \<Rightarrow> ennreal"
  proof -
    from that(3-4) have "extended_ln (limsup X) \<noteq> \<infinity>" and "extended_ln (limsup Y) \<noteq> \<infinity>"
      by (metis extended_exp_after_extended_ln extended_exp.simps(3))+
    then have 1: "limsup (\<lambda>i. extended_ln (X i)) \<noteq> \<infinity>" and 2: "limsup (\<lambda>i. extended_ln (Y i)) \<noteq> \<infinity>"
      by (simp_all add: Limsup_after_extended_ln)
    have "limsup (\<lambda>i. X i * Y i) = extended_exp (extended_ln (limsup (\<lambda>i. X i * Y i)))"
      by (simp only: extended_exp_after_extended_ln)
    also have "\<dots> = extended_exp (limsup (\<lambda>i. extended_ln (X i * Y i)))"
      by (simp_all add: Limsup_after_extended_ln)
    also have "\<dots> = extended_exp (limsup (\<lambda>i. extended_ln (X i) + extended_ln (Y i)))"
      using extended_ln_of_product and that(1-2)
      by simp
    also have "\<dots> \<le> extended_exp (limsup (\<lambda>i. extended_ln (X i)) + limsup (\<lambda>i. extended_ln (Y i)))"
      using ereal_limsup_add_mono
      by (rule extended_exp_monotonicity [THEN monoD])
    also have "\<dots> =
      extended_exp (limsup (\<lambda>i. extended_ln (X i))) * extended_exp (limsup (\<lambda>i. extended_ln (Y i)))"
      using extended_exp_of_sum and 1 2
      by simp
    also have "\<dots> = extended_exp (extended_ln (limsup X)) * extended_exp (extended_ln (limsup Y))"
      by (simp_all add: Limsup_after_extended_ln)
    also have "\<dots> = limsup X * limsup Y"
      by (simp only: extended_exp_after_extended_ln)
    finally show ?thesis .
  qed
  from assms show ?thesis
    by
      transfer
      (auto
        simp only: extended_non_negative_real_of_product extended_non_negative_real_is_finite
        intro: raw_thesis
      )
qed

end
