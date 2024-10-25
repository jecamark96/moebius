theory GammaFactor
  imports Complex_Main
begin

definition gamma_factor :: "complex \<Rightarrow> real" ("\<gamma>") where
  "\<gamma> u = (if cmod u < 1 then 
             (1 / sqrt(1 - (cmod u)\<^sup>2))
          else
             0)"

lemma gamma_ok:
  assumes "cmod u < 1"
  shows "1 / sqrt(1 - (norm u)\<^sup>2) \<noteq> 0"
  using assms square_norm_one by force

lemma gamma_factor_increasing:
  fixes t1 t2 ::real
  assumes "0 \<le> t2" "t2 < t1" "t1 < 1"
  shows "\<gamma> t2 < \<gamma> t1" 
proof-
  have d: "cmod t1 = abs t1" "cmod t2 = abs t2"
    using norm_of_real 
    by blast+

  have "\<bar>t2\<bar> * \<bar>t2\<bar> < \<bar>t1\<bar> * \<bar>t1\<bar>"
    by (simp add: assms mult_strict_mono')
  then have "1 - \<bar>t1\<bar> * \<bar>t1\<bar> < 1 - \<bar>t2\<bar> * \<bar>t2\<bar>"
    by auto
  then have "sqrt (1 - \<bar>t1\<bar> * \<bar>t1\<bar>) < sqrt (1 - \<bar>t2\<bar> * \<bar>t2\<bar>)"
    using real_sqrt_less_iff 
    by blast
  then have "1 / sqrt (1 - \<bar>t2\<bar> * \<bar>t2\<bar>) < 1 / sqrt (1 - \<bar>t1\<bar> * \<bar>t1\<bar>)"
    using assms
    by (smt (z3) frac_less2 mult_less_cancel_right2 real_sqrt_gt_zero)

  moreover

  have "cmod t1 < 1" "cmod t2 < 1"
    using assms 
    by force+
  then have "\<gamma> t1 = 1 / sqrt(1 - (abs t1)^2)" "\<gamma> t2 = 1 / sqrt(1 - (abs t2)^2)"
    using assms d gamma_factor_def
    by auto

  ultimately

  show ?thesis
    using d 
    by (metis power2_eq_square)
qed

lemma gamma_factor_increase_reverse:
  fixes t1 t2 :: real
  assumes "t1 \<ge> 0" "t1 < 1" "t2 \<ge> 0" "t2 < 1"
  assumes "\<gamma> t1 > \<gamma> t2"
  shows "t1 > t2"
  using assms
  by (smt (verit, best) gamma_factor_increasing)
  
lemma gamma_factor_u_normu:
  fixes u :: real
  assumes "0 \<le> u" "u \<le> 1"
  shows "\<gamma> u = \<gamma> (cmod u)"
  using gamma_factor_def
  by auto

lemma gamma_factor_positive:
  assumes "cmod u < 1"
  shows "\<gamma> u > 0"
  using assms
  unfolding gamma_factor_def
  by (smt (verit, del_insts) divide_pos_pos norm_ge_zero power2_eq_square power2_nonneg_ge_1_iff real_sqrt_gt_0_iff)


end