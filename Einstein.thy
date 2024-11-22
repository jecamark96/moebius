theory Einstein
  imports Complex_Main GyroGroup GyroVectorSpace GammaFactor HOL.Real_Vector_Spaces
  MobiusGyroGroup MobiusGyroVectorSpace HOL.Transcendental
begin

text \<open>Einstein zero\<close>

definition ozero_e' :: "complex" where
  "ozero_e' = 0"

lift_definition ozero_e :: PoincareDisc  ("0\<^sub>e") is ozero_e'
  unfolding ozero_e'_def
  by simp

lemma ozero_e_ozero_m:
  shows "0\<^sub>e = 0\<^sub>m"
  using ozero_e'_def ozero_e_def ozero_m'_def ozero_m_def 
  by auto

text \<open>Einstein addition\<close>

definition oplus_e' :: "complex \<Rightarrow> complex \<Rightarrow> complex"  where
  "oplus_e' u v = (1 / (1 + inner u v)) *\<^sub>R (u + (1 / \<gamma> u) *\<^sub>R v + ((\<gamma> u / (1 + \<gamma> u)) * (inner u v)) *\<^sub>R u)"

lemma noroplus_m'_e:
  assumes "norm u < 1" "norm v <1"
  shows "norm (oplus_e' u v)^2 =
         1 / (1 + inner u v)^2 * (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - (inner u v)^2))"
proof-
  let ?uv = "inner u v"
  let ?gu = "\<gamma> u / (1 + \<gamma> u)"

  have 1: "norm (oplus_e' u v)^2 = 
           norm (1 / (1 + ?uv))^2 * norm ((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2"  
    by (metis oplus_e'_def norm_scaleR power_mult_distrib real_norm_def)

  have 2: "norm (1 / (1 + ?uv))^2 =  1 / (1 + ?uv)^2"
    by (simp add: power_one_over)

  have "norm((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2 = 
        inner (u + (1 / \<gamma> u) *\<^sub>R v + (?gu * ?uv) *\<^sub>R u) 
              (u + (1 / \<gamma> u) *\<^sub>R v + (?gu * ?uv) *\<^sub>R u)"
    by (simp add: dot_square_norm)
  also have "\<dots> = 
        (norm u)^2 + 
        (norm ((1 / \<gamma> u) *\<^sub>R v))^2 + 
        (norm ((?gu * ?uv) *\<^sub>R u))^2 + 
        2 * inner u ((1 / \<gamma> u) *\<^sub>R v) + 
        2 * inner u ((?gu * ?uv) *\<^sub>R u) +
        2 * inner ((?gu * ?uv) *\<^sub>R u) ((1 / \<gamma> u) *\<^sub>R v)" (is "?lhs = ?a + ?b + ?c + ?d + ?e + ?f")
    by (smt (verit) inner_commute inner_right_distrib power2_norm_eq_inner)
  also have "\<dots> = (norm u)^2 + 
                  1 / (\<gamma> u)^2 * (norm v)^2 + 
                  ?gu^2 * (inner u v)^2 * (norm u)^2 +
                  2 / \<gamma> u * (inner u v) +
                  2 * ?gu * ?uv * (inner u u) +
                  2 * ?gu * ?uv * (1 / \<gamma> u) * (inner u v)"
  proof-
    have "?b = 1 / (\<gamma> u)^2 * (norm v)^2"
      by (simp add: power_divide)
    moreover
    have "?c = ?gu^2 * (inner u v)^2 * (norm u)^2"
      by (simp add: power2_eq_square)
    moreover
    have "?d = 2 / \<gamma> u * (inner u v)"
      using inner_scaleR_right
      by auto
    moreover
    have "?e = 2 * ?gu * ?uv * (inner u u)"
      using inner_scaleR_right
      by auto
    moreover
    have "?f = 2 * ?gu * ?uv * (1 / \<gamma> u) * (inner u v)"
      by force
    ultimately
    show ?thesis
      by presburger
  qed
  also have "\<dots> = 2 * inner u v + (inner u v)^2 + (norm u)^2 + (1 - (norm u)^2) * (norm v)^2"  (is "?a + ?b + ?c + ?d + ?e + ?f = ?rhs")
  proof-
    have "?a + ?b = (norm u)^2 + (1 - (norm u)^2) * (norm v)^2"
      using assms norm_square_gamma_factor
      by auto

    moreover

    have "?d + ?e = 2 * inner u v" (is "?lhs = ?rhs")
    proof-
      have "?e = 2 * (\<gamma> u * (norm u)^2 / (1 + \<gamma> u)) * inner u v"
        by (simp add: dot_square_norm)
      moreover
      have "1 / \<gamma> u + \<gamma> u * (norm u)^2 / (1 + \<gamma> u) = 1"
        using assms(1) gamma_expression_eq_one_1
        by blast
      moreover
      have "?d + 2 * (\<gamma> u * (norm u)^2 / (1 + \<gamma> u)) * inner u v = 2 * inner u v * (1 / \<gamma> u + \<gamma> u * (norm u)^2 / (1 + \<gamma> u))"
        by (simp add: distrib_left)
      ultimately 
      show ?thesis
        by (metis mult.right_neutral)
    qed

    moreover

    have "?c + ?f = (inner u v)^2"
    proof-
      have "?c + ?f = ?gu^2 * (norm u)^2 * (inner u v)^2 + 2 * (1 / \<gamma> u) * ?gu * (inner u v)^2"
        by (simp add: mult.commute mult.left_commute power2_eq_square)
      then have "?c + ?f = ((\<gamma> u / (1 + \<gamma> u))^2 * (norm u)^2 + 2 * (1 / \<gamma> u) * (\<gamma> u / (1 + \<gamma> u))) * (inner u v)^2"
        by (simp add: ring_class.ring_distribs(2))
      moreover
      have "(\<gamma> u / (1 + \<gamma> u))^2 * (norm u)^2 + 2 * (1 / \<gamma> u) * (\<gamma> u / (1 + \<gamma> u)) = 1"
      proof -
        have "\<forall> (x::real) y n. (x / y) ^ n = x ^ n / y ^ n"
          by (simp add: power_divide)
        then show ?thesis
          using gamma_expression_eq_one_2[OF assms(1)]
          by fastforce
      qed
      ultimately
      show ?thesis
        by simp
    qed

    ultimately
    show ?thesis
      by auto
  qed
  also have "\<dots> = ((cmod (u + v))\<^sup>2 - ((cmod u)\<^sup>2 * (cmod v)\<^sup>2 - ?uv\<^sup>2))"
    unfolding dot_square_norm[symmetric]
    by (simp add: inner_commute inner_right_distrib field_simps)
  finally
  have 3: "norm ((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2 =
           norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2)"
    by simp

  show ?thesis
    using 1 2 3
    by simp
qed

lemma gamma_oplus_e':
  assumes "norm u < 1" "norm v < 1"
  shows "1 / sqrt(1 - norm (oplus_e' u v)^2) = \<gamma> u * \<gamma> v * (1 + inner u v)"
proof-
  let ?uv = "inner u v"

  have abs: "abs (1 + ?uv) = 1 + ?uv"
    using abs_inner_lt_1 assms by fastforce

  have "1 - norm (oplus_e' u v)^2 = 
        1 - 1 / (1 + ?uv)^2 * (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2))"
    using assms noroplus_m'_e
    by presburger
  also have "\<dots> = ((1 + ?uv)^2 - (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2))) /
                  (1 + ?uv)^2"
  proof-
    have "?uv \<noteq> -1"
      using abs_inner_lt_1[OF assms]
      by auto
    then have "(1 + ?uv)^2 \<noteq> 0"
      by auto
    then show ?thesis
      by (simp add: diff_divide_distrib)
  qed
  also have "\<dots> = (1 - (norm u)^2 - (norm v)^2 + (norm u)^2 * (norm v)^2) / (1 + ?uv)^2"
  proof-
    have "(1 + ?uv)^2  = 1 + 2*?uv + ?uv^2"
      by (simp add: power2_eq_square field_simps)
    moreover
    have "norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2) = 
         (norm u)^2 + 2*?uv + (norm v)^2 - (norm u)^2*(norm v)^2 + ?uv^2"
      by (smt (z3) dot_norm field_sum_of_halves)
    ultimately
    show ?thesis
      by auto
  qed
  finally have "1 / sqrt (1 - norm (oplus_e' u v)^2) = 
                1 / sqrt((1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2) / (1 + ?uv)^2)"
    by simp
  then have 1: "1 / sqrt (1 - norm (oplus_e' u v)^2) = 
                (1 + ?uv) / sqrt (1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2)"
    using abs
    by (simp add: real_sqrt_divide)

  have "\<gamma> u = 1 / sqrt(1 - (norm u)^2)" "\<gamma> v = 1 / sqrt(1 - (norm v)^2)"
    using assms
    by (metis gamma_factor_def)+
  then have "\<gamma> u * \<gamma> v = (1 / sqrt (1 - (norm u)^2)) * (1 / sqrt (1 - (norm v)^2))"
    by simp
  also have "\<dots> = 1 / sqrt ((1 - (norm u)^2) * (1 - (norm v)^2))"
    by (simp add: real_sqrt_mult)
  finally have 2: "\<gamma> u * \<gamma> v = 1 / sqrt ((1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2))"
    by (simp add: field_simps power2_eq_square)

  show ?thesis
    using 1 2
    by (metis (no_types, lifting) mult_cancel_right1 times_divide_eq_left)
qed

lemma gamma_oplus_e'_not_zero:
  assumes "norm u < 1" "norm v < 1"
  shows "1 / sqrt(1 - norm(oplus_e' u v)^2) \<noteq> 0"
  using assms
  using gamma_oplus_e' gamma_factor_def gamma_factor_nonzero noroplus_m'_e
  by fastforce

lemma oplus_e'_in_unit_disc:
  assumes "norm u < 1" "norm v < 1"
  shows "norm (oplus_e' u v) < 1"
proof-
  let ?uv = "inner u v"
  have "1 + ?uv > 0"
    using abs_inner_lt_1[OF assms]
    by fastforce
  then have "\<gamma> u * \<gamma> v * (1 + inner u v) > 0"
    using gamma_factor_positive[OF assms(1)] 
          gamma_factor_positive[OF assms(2)]
    by fastforce
  then have "0 < sqrt (1 - (cmod (oplus_e' u v))\<^sup>2)"
    using gamma_oplus_e'[OF assms] gamma_oplus_e'_not_zero[OF assms]
    by (metis zero_less_divide_1_iff)
  then have "(norm (oplus_e' u v))^2 < 1"
    using real_sqrt_gt_0_iff
    by simp
  then show ?thesis
    using real_less_rsqrt by force
qed

lemma gamma_factor_oplus_e':
  assumes "norm u < 1" "norm v < 1"
  shows "\<gamma> (oplus_e' u v) = (\<gamma> u) * (\<gamma> v) * (1 + inner u v)"
proof-
  have "\<gamma> (oplus_e' u v) = 1 / sqrt(1 - norm (oplus_e' u v)^2)"
    by (simp add: assms(1) assms(2) oplus_e'_in_unit_disc gamma_factor_def)
  then show ?thesis
    using assms
    using gamma_oplus_e' by force
qed

lift_definition oplus_e :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<oplus>\<^sub>e" 100) is oplus_e'
  by (rule oplus_e'_in_unit_disc)

(* ------------------------------------------------------------------------------------- *)
  
definition ominus_e' :: "complex \<Rightarrow> complex" where
  "ominus_e' v = - v"                                      

lemma ominus_e'_in_unit_disc:
  assumes "norm z < 1"
  shows "norm (ominus_e' z) < 1"
  using assms
  unfolding ominus_e'_def
  by simp

lift_definition ominus_e :: "PoincareDisc \<Rightarrow> PoincareDisc" ("\<ominus>\<^sub>e") is ominus_e'
  using ominus_e'_in_unit_disc by blast

lemma ominus_e_ominus_m:
  shows "\<ominus>\<^sub>e a = \<ominus>\<^sub>m a"
  by (simp add: ominus_e'_def ominus_e_def ominus_m'_def ominus_m_def)

lemma ominus_e_scale:
  shows "k \<otimes> (\<ominus>\<^sub>e u) = \<ominus>\<^sub>e (k \<otimes> u)"
  using ominus_e_ominus_m ominus_m_scale by auto
  
(* ------------------------------------------------------------------------------------- *)

lemma gamma_factor_p_positive:
  shows "\<gamma>\<^sub>p a > 0"
  by transfer (simp add: gamma_factor_positive)

lemma gamma_factor_p_oplus_e:
  shows "\<gamma>\<^sub>p (u \<oplus>\<^sub>e v) = \<gamma>\<^sub>p u * \<gamma>\<^sub>p v * (1 + u \<cdot> v)"
  using gamma_factor_oplus_e' 
  by transfer blast

abbreviation \<gamma>\<^sub>2 :: "complex \<Rightarrow> real" where
  "\<gamma>\<^sub>2 u \<equiv> \<gamma> u / (1 + \<gamma> u)"

lemma norm_square_gamma_half_scale:
  assumes "norm u < 1"
  shows "(norm (\<gamma>\<^sub>2 u *\<^sub>R u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)"
proof-
  have "(norm (\<gamma>\<^sub>2 u *\<^sub>R u))\<^sup>2 = (\<gamma>\<^sub>2 u)\<^sup>2 * (norm u)\<^sup>2"
    by (simp add: power2_eq_square)
  also have "\<dots> = (\<gamma>\<^sub>2 u)\<^sup>2 * ((\<gamma> u)\<^sup>2 - 1) / (\<gamma> u)\<^sup>2"
    using assms
    by (simp add: norm_square_gamma_factor')
  also have "\<dots> = (\<gamma> u)\<^sup>2 / (1 + \<gamma> u)\<^sup>2 * ((\<gamma> u)\<^sup>2 - 1) / (\<gamma> u)\<^sup>2"
    by (simp add: power_divide)
  also have "\<dots> = ((\<gamma> u)\<^sup>2 - 1) / (1 + \<gamma> u)\<^sup>2"
    using assms gamma_factor_positive 
    by fastforce
  also have "\<dots> = (\<gamma> u - 1) * (\<gamma> u + 1) / (1 + \<gamma> u)\<^sup>2"
    by (simp add: power2_eq_square square_diff_one_factored)
  also have "\<dots> = (\<gamma> u - 1) / (1 + \<gamma> u)"
    by (simp add: add.commute power2_eq_square)
  finally
  show ?thesis
    by simp
qed
  
lemma norm_half_square_gamma:
  assumes "norm u < 1"
  shows "(norm (half' u))\<^sup>2 = (\<gamma>\<^sub>2 u)\<^sup>2 * (cmod u)\<^sup>2"
  unfolding half'_def 
  using norm_square_gamma_half_scale assms
  by (smt (verit) divide_pos_pos gamma_factor_positive norm_scaleR power_mult_distrib)

lemma norm_half_square_gamma':
  assumes "cmod u < 1"
  shows "(norm (half' u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)"
  using assms
  using half'_def norm_square_gamma_half_scale
  by auto

lemma inner_half_square_gamma:
  assumes "cmod u < 1" "cmod v < 1"
  shows "inner (half' u) (half' v) = \<gamma>\<^sub>2 u * \<gamma>\<^sub>2 v * inner u v"
  unfolding half'_def scaleR_conv_of_real
  by (metis inner_mult_left inner_mult_right mult.assoc)


lemma iso_me_help1:
  assumes "norm v < 1"
  shows "1 + (\<gamma> v - 1) / (1 + \<gamma> v) = 2 * \<gamma> v / (1 + \<gamma> v)"
proof-
  have "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive
    by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_me_help2:
  assumes "norm v < 1"
  shows "1 - (\<gamma> v - 1) / (1 + \<gamma> v) = 2 / (1 + \<gamma> v)"
proof-
  have "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_me_help3:
  assumes "norm v < 1" "norm u <1"
  shows "1 + ((\<gamma> v - 1) / (1 + \<gamma> v)) * ((\<gamma> u - 1) / (1 + \<gamma> u)) =
         2 * (1 + (\<gamma> u) * (\<gamma> v)) / ((1 + \<gamma> v) * (1 + \<gamma> u))" (is "?lhs = ?rhs")
proof-
  have *: "1 + \<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0"
    using assms gamma_factor_positive by fastforce+
  have "(1 + \<gamma> v) * (1 + \<gamma> u) = 1 + (\<gamma> v) + (\<gamma> u) + (\<gamma> u)*(\<gamma> v)"
    by (simp add: field_simps)
  moreover 
  have "(\<gamma> v - 1) * (\<gamma> u - 1) =  (\<gamma> u)*(\<gamma> v) - (\<gamma> u) - (\<gamma> v) +1"
    by (simp add: field_simps)
  moreover 
  have "?lhs = ((1 + \<gamma> v) * (1 + \<gamma> u) + (\<gamma> u - 1) * (\<gamma> v - 1)) / ((1 + \<gamma> v) * (1 + \<gamma> u))"
    using *
    by (simp add: add_divide_distrib)
  ultimately show ?thesis 
    by (simp add: mult.commute)
qed

lemma half'_oplus_e':
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "half' (oplus_e' u v) = 
         \<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u)"
proof-
  have "half' (oplus_e' u v) = 
       \<gamma> u * \<gamma> v * (1 + inner u v) / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) *
       ((1 / (1 + inner u v)) * (u + (1 / \<gamma> u)*v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u))"
    unfolding half'_def
    unfolding gamma_factor_oplus_e'[OF assms] scaleR_conv_of_real
    unfolding oplus_e'_def scaleR_conv_of_real
    by simp
  then show ?thesis
    using assms
    by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) gamma_oplus_e' gamma_oplus_e'_not_zero inner_mult_left' inner_real_def mult.commute mult_eq_0_iff nonzero_mult_divide_mult_cancel_right2 of_real_1 of_real_divide of_real_mult real_inner_1_right times_divide_times_eq)
qed

lemma oplus_m'_half':
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "oplus_m' (half' u) (half' v) =
        (\<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1)) * 
        (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u)"
proof-
  have *: "\<gamma> u \<noteq> 0" "\<gamma> v \<noteq> 0" "1 + \<gamma> u \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce+

  let ?den = "(1 + \<gamma> v) * (1 + \<gamma> u)"
  let ?DEN = "\<gamma> u * \<gamma> v * (1 + inner u v) + 1"
  let ?NOM = "u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u"

  have **: "cmod (half' u) < 1" "cmod (half' v) < 1"
    using assms
    by (metis eq_onp_same_args half.rsp rel_fun_eq_onp_rel)+
  then have "oplus_m' (half' u) (half' v) = oplus_m'_alternative (half' u) (half' v)"
    by (simp add: oplus_m'_alternative)
  also have "\<dots> = ((2 * \<gamma>\<^sub>2 v + 2 * \<gamma>\<^sub>2 v * \<gamma>\<^sub>2 u * inner u v) * \<gamma>\<^sub>2 u * u  +  2 * \<gamma> v / ?den * v) /
                  (2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den)"
  proof-
    have "(1 + 2 * inner (half' u) (half' v) + (norm (half' v))\<^sup>2) *\<^sub>R (half' u) = 
          (2 * \<gamma>\<^sub>2 v + 2 * \<gamma> v * \<gamma> u / ?den * inner u v) * \<gamma>\<^sub>2 u * u"
    proof-
      have *: "half' u = (\<gamma> u / (1 + \<gamma> u)) * u"
        by (simp add: half'_def scaleR_conv_of_real)
  
      have "1 + 2 * inner (half' u) (half' v) + (cmod (half' v))\<^sup>2 = 
            1 + 2 * (\<gamma>\<^sub>2 u * \<gamma>\<^sub>2 v * inner u v) + (\<gamma>\<^sub>2 v)\<^sup>2 * (cmod v)\<^sup>2"
        using inner_half_square_gamma norm_half_square_gamma assms
        by simp
      also have "\<dots> = 2 * \<gamma> v / (1 + \<gamma> v) + 2 * \<gamma> v * \<gamma> u / ?den * inner u v"
        using assms norm_half_square_gamma norm_square_gamma_half_scale[OF assms(2)] iso_me_help1[OF assms(2)] half'_def
        by (smt (verit, best) add_divide_distrib distrib_left inner_commute inner_left_distrib inner_real_def times_divide_times_eq)
      finally
      show ?thesis
        using *
        by (simp add: of_real_def)
    qed
    moreover
    have "(1 - (norm (half' u))\<^sup>2) *\<^sub>R (half' v) = 
          2 * (\<gamma> v) / ?den * v"
      using iso_me_help2 norm_half_square_gamma' assms
      by (simp add: half'_def mult.assoc scaleR_conv_of_real)
    moreover
    have"1 + 2 * inner (half' u) (half' v) + (cmod (half' u))\<^sup>2 * (cmod (half' v))\<^sup>2 =
         2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den"
      using assms inner_half_square_gamma iso_me_help3 norm_half_square_gamma'
      by (simp add: field_simps)
    ultimately
    show ?thesis
       unfolding oplus_m'_alternative_def
       by (simp add: mult.commute)
  qed
  also have "\<dots> = (2 * \<gamma> v * \<gamma> u * u + 2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v * v) / 
                  (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v))"
  proof-
    have "1 / ?den \<noteq> 0"
      using *
      by simp
    moreover 
    have "(2 * \<gamma>\<^sub>2 v + 2 * \<gamma>\<^sub>2 v * \<gamma>\<^sub>2 u * inner u v) * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v / ?den * v =
           (1 / ?den) * (2 * \<gamma> v * \<gamma> u * u + 2 * \<gamma> v * \<gamma> u * inner u v * \<gamma>\<^sub>2 u * u + 2 * \<gamma> v * v)"
      by (simp add: mult.commute ring_class.ring_distribs(1))
    moreover 
    have "2 * \<gamma> u * \<gamma> v * inner u v / ?den + 2 * (1 + \<gamma> u * \<gamma> v) / ?den =
          (1 / ?den) * (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v))"
      by argo
    ultimately 
    show ?thesis
      by (smt (verit, ccfv_threshold) divide_divide_eq_left' division_ring_divide_zero eq_divide_eq inner_commute inner_real_def mult_eq_0_iff mult_eq_0_iff nonzero_mult_divide_mult_cancel_left nonzero_mult_divide_mult_cancel_left numeral_One of_real_1 of_real_1 of_real_divide of_real_inner_1 of_real_mult one_divide_eq_0_iff real_inner_1_right times_divide_times_eq)
  qed
  also have "\<dots> = 2 * (\<gamma> v * \<gamma> u * u + \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u) * u + \<gamma> v * v) / (2 * ?DEN)"
    by (simp add: field_simps)
  also have "\<dots> = (\<gamma> v * \<gamma> u * u + \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u) * u + \<gamma> v * v) / ?DEN"
    by (metis (no_types, opaque_lifting) nonzero_mult_divide_mult_cancel_left of_real_mult of_real_numeral zero_neq_numeral)
  also have "\<dots> = ((\<gamma> v * \<gamma> u) * u + (\<gamma> v * \<gamma> u) * (inner u v * \<gamma> u / (1 + \<gamma> u) * u) + (\<gamma> u * \<gamma> v) * (v / \<gamma> u)) / ?DEN"
    using \<open>\<gamma> u \<noteq> 0\<close>
    by simp
  also have "\<dots> = (\<gamma> v * \<gamma> u) * ?NOM / ?DEN"
  proof-
    have "(\<gamma> v * \<gamma> u) * u + (\<gamma> v * \<gamma> u) * (inner u v * \<gamma> u / (1 + \<gamma> u) * u) + (\<gamma> u * \<gamma> v) * (v / \<gamma> u) = (\<gamma> v * \<gamma> u) * ?NOM"
      by (simp add: field_simps)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    by simp
qed


lemma iso_me_oplus:
  shows "(1/2) \<otimes> (u \<oplus>\<^sub>e v) = ((1/2) \<otimes> u) \<oplus>\<^sub>m ((1/2) \<otimes> v)"
proof transfer
  fix u v
  assume *: "cmod u < 1" "cmod v < 1"
  have "otimes' (1 / 2) (oplus_e' u v) = half' (oplus_e' u v)"
    using half'[of "oplus_e' u v"] *
    unfolding otimes'_def
    using oplus_e'_in_unit_disc 
    by blast
  moreover
  have "otimes' (1 / 2) u = half' u" "otimes' (1 / 2) v = half' v"
    using half' *
    by auto
  moreover
  have "half' (oplus_e' u v) = oplus_m' (half' u) (half' v)"
    using * half'_oplus_e'[OF *] oplus_m'_half'[OF *]
    by simp
  ultimately
  show "otimes' (1 / 2) (oplus_e' u v) = oplus_m' (otimes' (1 / 2) u) (otimes' (1 / 2) v)"
    by simp
qed

lemma oplus_e_oplus_m:
  shows "u \<oplus>\<^sub>e v = 2 \<otimes> ((1/2) \<otimes> u \<oplus>\<^sub>m (1/2) \<otimes> v)"
  by (metis half iso_me_oplus otimes_2_half)

(* ---------------------------------------------------------------------------------------------- *)

definition gyr\<^sub>e::"PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
 "gyr\<^sub>e u v w = \<ominus>\<^sub>e (u \<oplus>\<^sub>e v) \<oplus>\<^sub>e (u \<oplus>\<^sub>e (v \<oplus>\<^sub>e w))"

lemma iso_me_gyr:
  shows "(1/2) \<otimes> gyr\<^sub>e u v w = gyr\<^sub>m ((1/2) \<otimes> u) ((1/2) \<otimes> v) ((1/2) \<otimes> w)"
  unfolding gyr\<^sub>e_def Mobius_gyrogroup.gyr_def
  using iso_me_oplus ominus_e_ominus_m ominus_e_scale
  by presburger

lemma gyr_e_gyr_m:
  shows "gyr\<^sub>e u v w = 2 \<otimes> gyr\<^sub>m ((1/2) \<otimes> u) ((1/2) \<otimes> v) ((1/2) \<otimes> w)"
  by (metis iso_me_gyr half otimes_2_half)

(* ---------------------------------------------------------------------------------------------- *)
lemma e_left_id:
  shows "0\<^sub>e \<oplus>\<^sub>e u = u"
  using Mobius_gyrovector_space.double_half Mobius_gyrovector_space.times_zero ozero_e_ozero_m gyrozero_PoincareDisc_def oplus_e_oplus_m
  by force

lemma e_inv:
  shows "\<ominus>\<^sub>e a \<oplus>\<^sub>e a = 0\<^sub>e"
  using ominus_e_ominus_m ominus_e_scale ozero_e_ozero_m oplus_e_oplus_m otimes_2_oplus_m 
  by auto

lemma gyr_e_left_loop:
  shows "gyr\<^sub>e a b = gyr\<^sub>e (a \<oplus>\<^sub>e b) b"
  using gyr_m_left_loop gyr_e_gyr_m iso_me_oplus
  by presburger

lemma gyr_e_left_assoc:
  shows "a \<oplus>\<^sub>e (b \<oplus>\<^sub>e z) = (a \<oplus>\<^sub>e b) \<oplus>\<^sub>e gyr\<^sub>e a b z"
(*
  using e_gyr_m_gyr iso_moplus_e_oplus_e_m iso_moplus_e m_gyro_left_assoc 
  by simp
*)
proof-
  let ?a = "(1/2) \<otimes> a" and ?b = "(1/2) \<otimes> b" and ?z = "(1/2) \<otimes> z"
  have "a \<oplus>\<^sub>e (b \<oplus>\<^sub>e z) = 2 \<otimes> (?a \<oplus>\<^sub>m (?b \<oplus>\<^sub>m ?z))"
    using iso_me_oplus oplus_e_oplus_m by simp
  also have "\<dots> = 2 \<otimes> ((?a \<oplus>\<^sub>m ?b) \<oplus>\<^sub>m gyr\<^sub>m ?a ?b ?z)"
    using gyr_m_left_assoc by simp
  also have "\<dots> = 2 \<otimes> (((1/2) \<otimes> (a \<oplus>\<^sub>e b)) \<oplus>\<^sub>m gyr\<^sub>m ?a ?b ?z)"
    using iso_me_oplus by simp
  also have "\<dots> = 2 \<otimes> (((1/2) \<otimes> (a \<oplus>\<^sub>e b)) \<oplus>\<^sub>m (1/2) \<otimes> gyr\<^sub>e a b z)"
    using iso_me_gyr by simp
  finally show ?thesis
    using oplus_e_oplus_m by simp
qed

lemma gyr_e_commute:
  shows  "a \<oplus>\<^sub>e b = gyr\<^sub>e a b (b \<oplus>\<^sub>e a)"
  by (metis gyr_e_gyr_m iso_me_oplus oplus_e_oplus_m gyr_m_commute)

lemma gyr_e_distrib:
  shows "gyr\<^sub>e a b (a' \<oplus>\<^sub>e b') = gyr\<^sub>e a b a' \<oplus>\<^sub>e gyr\<^sub>e a b b'"
  using gyr_e_gyr_m iso_me_gyr iso_me_oplus oplus_e_oplus_m
  by force

lemma gyr_e_inv:
  "gyr\<^sub>e a b (gyr\<^sub>e b a z) = z"
  by (metis iso_me_gyr half gyr_m_inv otimes_2_half)

lemma gyr_e_bij:
  shows "bij (gyr\<^sub>e a b)"
  by (metis bijI gyr_e_inv inj_def surjI)
  
interpretation Einstein_gyrogroup: gyrogroup ozero_e oplus_e ominus_e gyr\<^sub>e
proof
  fix a
  show "0\<^sub>e \<oplus>\<^sub>e a = a"
    by (simp add: e_left_id)
next
  fix a
  show "\<ominus>\<^sub>e a \<oplus>\<^sub>e a = 0\<^sub>e"
    by (simp add: e_inv)    
next
  fix a b z
  show "a \<oplus>\<^sub>e (b \<oplus>\<^sub>e z) = a \<oplus>\<^sub>e b \<oplus>\<^sub>e gyr\<^sub>e a b z"
    by (simp add: gyr_e_left_assoc)
next
  fix a b
  show "gyr\<^sub>e a b = gyr\<^sub>e (a \<oplus>\<^sub>e b) b"
    using gyr_e_left_loop by auto
next
  fix a b
  show "gyrogroupoid.gyroaut (\<oplus>\<^sub>e) (gyr\<^sub>e a b)"
    unfolding gyrogroupoid.gyroaut_def
  proof safe
    fix a' b'
    show "gyr\<^sub>e a b (a' \<oplus>\<^sub>e b') = gyr\<^sub>e a b a' \<oplus>\<^sub>e gyr\<^sub>e a b b'"
      by (simp add: gyr_e_distrib)
  next
    show "bij (gyr\<^sub>e a b)"
      by (simp add: gyr_e_bij)
  qed
qed

interpretation Einstein_gyrocommutative_gyrogroup: gyrocommutative_gyrogroup ozero_e oplus_e ominus_e gyr\<^sub>e
proof
  fix a b
  show "a \<oplus>\<^sub>e b = gyr\<^sub>e a b (b \<oplus>\<^sub>e a)"
    using gyr_e_commute by auto
qed

lemma otimes_oplus_e_distrib:
  shows "(r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus>\<^sub>e r2 \<otimes> a" 
proof-
  have "r1 \<otimes> a \<oplus>\<^sub>e r2 \<otimes> a =  2 \<otimes> ((1 / 2) \<otimes> (r1 \<otimes> a) \<oplus>\<^sub>m (1 / 2) \<otimes> (r2 \<otimes> a))"
    unfolding oplus_e_oplus_m
    by simp
  also have "\<dots> = 2 \<otimes> ((1/2) \<otimes> ((r1 \<otimes> a) \<oplus>\<^sub>m (r2 \<otimes> a)))"
    using Mobius_gyrovector_space.monodistributive gyroplus_PoincareDisc_def 
    by auto
  also have "\<dots> = 2 \<otimes> ((1/2) \<otimes> ((r1 + r2) \<otimes> a))"
    using otimes_oplus_m_distrib 
    by auto
  finally show ?thesis
    using half otimes_2_half 
    by presburger
qed


lemma half_inner_left: 
  "((1/2) \<otimes> a) \<cdot> b = (\<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a)) * (a \<cdot> b)"
  unfolding half[symmetric]
  by transfer (simp add: half'_def)

lemma half_inner_right:
  "a \<cdot> ((1/2) \<otimes> b) = (\<gamma>\<^sub>p b / (1 + \<gamma>\<^sub>p b)) * (a \<cdot> b)"
  by (metis inner_p.rep_eq half_inner_left inner_commute)

lemma half_inner: 
  "((1/2) \<otimes> a) \<cdot> ((1/2) \<otimes> b) = (\<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a)) * (\<gamma>\<^sub>p b / (1 + \<gamma>\<^sub>p b)) * (a \<cdot> b)"
  using half_inner_left half_inner_right
  by auto

lemma double_inner_left: 
  "(2 \<otimes> a) \<cdot> b = (2*(\<gamma>\<^sub>p a)\<^sup>2 / (2*(\<gamma>\<^sub>p a)\<^sup>2 - 1)) * (a \<cdot> b)"
  unfolding double[symmetric]
  by transfer (simp add: double'_def)

lemma double_inner_right: 
  "a \<cdot> (2 \<otimes> b) = (2*(\<gamma>\<^sub>p b)\<^sup>2 / (2*(\<gamma>\<^sub>p b)\<^sup>2 - 1)) * (a \<cdot> b)"
  by (metis inner_p.rep_eq double_inner_left inner_commute)

lemma double_inner: 
  "(2 \<otimes> a) \<cdot> (2 \<otimes> b) = (2*(\<gamma>\<^sub>p a)\<^sup>2 / (2*(\<gamma>\<^sub>p a)\<^sup>2 - 1)) * (2*(\<gamma>\<^sub>p b)\<^sup>2 / (2*(\<gamma>\<^sub>p b)\<^sup>2 - 1)) * (a \<cdot> b)"
  using double_inner_left double_inner_right
  by auto

lemma double_norm_square:
  shows "2*(\<gamma>\<^sub>p u)\<^sup>2 / (2*(\<gamma>\<^sub>p u)\<^sup>2 - 1) = 2 / (1 + (\<llangle>u\<rrangle>)\<^sup>2)"
  by transfer (simp add: double'_cmod) 

lemma square_norm_half:
  shows "(\<llangle>(1/2) \<otimes> a\<rrangle>)\<^sup>2 = (\<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a))\<^sup>2 * (\<llangle>a\<rrangle>)\<^sup>2"
  by (metis half_inner power2_eq_square square_norm_inner)

lemma double_mgyr_half:
  shows "let m = gyr\<^sub>m ((1/2) \<otimes> u) ((1/2) \<otimes> v) ((1/2) \<otimes> a)
          in 2*(\<gamma>\<^sub>p m)\<^sup>2 / (2*(\<gamma>\<^sub>p m)\<^sup>2 - 1) = (1 + \<gamma>\<^sub>p a) / \<gamma>\<^sub>p a"
proof-
  define m where "m = gyr\<^sub>m ((1/2) \<otimes> u) ((1/2) \<otimes> v) ((1/2) \<otimes> a)"
  have "\<llangle>m\<rrangle> = \<llangle>(1/2) \<otimes> a\<rrangle>"
    unfolding m_def mobius_gyroauto_norm
    by simp

  have "2*(\<gamma>\<^sub>p m)\<^sup>2 / (2*(\<gamma>\<^sub>p m)\<^sup>2 - 1) = 2 / (1 + (\<llangle>m\<rrangle>)\<^sup>2)"
    by (simp add: double_norm_square)
  also have "\<dots> = 2 / (1 + (\<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a))\<^sup>2 * (\<llangle>a\<rrangle>)\<^sup>2)"
    by (simp add: \<open>\<llangle>m\<rrangle> = \<llangle>(1 / 2) \<otimes> a\<rrangle>\<close> square_norm_half)
  also have "\<dots> = 2 / (1 + (\<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a))\<^sup>2 * (1 - 1 / (\<gamma>\<^sub>p a)\<^sup>2))"
    using norm_square_gamma_factor_p
    by auto
  also have "\<dots> = (1 + \<gamma>\<^sub>p a) / \<gamma>\<^sub>p a" (is "?lhs = ?rhs")
  proof-
    have *: "(\<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a))\<^sup>2 = (\<gamma>\<^sub>p a)\<^sup>2 / (1 + \<gamma>\<^sub>p a)\<^sup>2"
      by (simp add: power_divide)
    moreover
    have **: "1 - 1 / (\<gamma>\<^sub>p a)\<^sup>2 = ((\<gamma>\<^sub>p a)\<^sup>2 - 1) / (\<gamma>\<^sub>p a)\<^sup>2"
      using gamma_factor_p_positive[of a]
      by (metis diff_divide_distrib less_numeral_extra(3) right_inverse_eq zero_less_power)
    ultimately
    have "(\<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a))\<^sup>2 * (1 - 1 / (\<gamma>\<^sub>p a)\<^sup>2) = 
          ((\<gamma>\<^sub>p a)\<^sup>2 / (1 + \<gamma>\<^sub>p a)\<^sup>2) * (((\<gamma>\<^sub>p a)\<^sup>2 - 1) / (\<gamma>\<^sub>p a)\<^sup>2)"
      by simp
    also have "\<dots> = ((\<gamma>\<^sub>p a)\<^sup>2 - 1) / (1 + \<gamma>\<^sub>p a)\<^sup>2"
      using gamma_factor_p_positive[of a]
      by simp
    also have "\<dots> = (\<gamma>\<^sub>p a - 1) / (1 + \<gamma>\<^sub>p a)"
      using gamma_factor_p_positive[of a]
      by (simp add: add.commute power2_eq_square square_diff_one_factored)
    finally
    have "?lhs = 2 / (1 + (\<gamma>\<^sub>p a - 1) / (1 + \<gamma>\<^sub>p a))"
      by simp
    also have "\<dots> = 2 / (((1 + \<gamma>\<^sub>p a) + (\<gamma>\<^sub>p a - 1)) / (1 + \<gamma>\<^sub>p a))"
      using gamma_factor_p_positive[of a]
      by (metis add_divide_distrib add_less_same_cancel1 div_0 div_self less_divide_eq_1_neg less_numeral_extra(1) not_one_less_zero)
    also have "\<dots> = 2 / (2 * \<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a))"
      by simp
    also have "\<dots> = ?rhs"
      using gamma_factor_p_positive[of a]
      by (metis divide_divide_eq_right mult_divide_mult_cancel_left_if zero_neq_numeral)
    finally show ?thesis
      .
  qed
  finally show ?thesis
    unfolding m_def Let_def
    by simp
qed

lemma einstein_gyroauto:
  shows "gyr\<^sub>e u v a \<cdot> gyr\<^sub>e u v b = a \<cdot> b"
proof-
  let ?u = "(1/2) \<otimes> u" and ?v = "(1/2) \<otimes> v" and ?a = "(1/2) \<otimes> a" and ?b = "(1/2) \<otimes> b"
  let ?ma = "gyr\<^sub>m ?u ?v ?a" and ?mb = "gyr\<^sub>m ?u ?v ?b"
  let ?A = "2*(\<gamma>\<^sub>p ?ma)\<^sup>2 / (2*(\<gamma>\<^sub>p ?ma)\<^sup>2 - 1)" and ?B = "2*(\<gamma>\<^sub>p ?mb)\<^sup>2 / (2*(\<gamma>\<^sub>p ?mb)\<^sup>2 - 1)"
  let ?A' = "(\<gamma>\<^sub>p a / (1 + \<gamma>\<^sub>p a))" and ?B' = "(\<gamma>\<^sub>p b / (1 + \<gamma>\<^sub>p b))"

  have "gyr\<^sub>e u v a \<cdot> gyr\<^sub>e u v b = 2 \<otimes> ?ma \<cdot> 2 \<otimes> ?mb"
    unfolding gyr_e_gyr_m
    by simp
  also have "\<dots> = ?A * ?B * (?ma \<cdot> ?mb)"
    by (rule double_inner)
  also have "\<dots> = ?A * ?B * (?a \<cdot> ?b)"
    using moebius_gyroauto 
    by presburger
  also have "\<dots> = ?A * ?B * ?A' * ?B' * (a \<cdot> b)"
    using half_inner
    by simp
  also have "\<dots> = a \<cdot> b"
  proof-
    have "\<gamma>\<^sub>p a \<noteq> 0" "1 + \<gamma>\<^sub>p a \<noteq> 0"
      using gamma_factor_p_positive 
      by (smt (verit))+
    then have "?A * ?A' = 1"
      using double_mgyr_half[of u v a] 
      unfolding Let_def
      by simp

    moreover

    have "\<gamma>\<^sub>p b \<noteq> 0" "1 + \<gamma>\<^sub>p b \<noteq> 0"
      using gamma_factor_p_positive 
      by (smt (verit))+
    then have "?B * ?B' = 1"
      using double_mgyr_half[of u v b] 
      unfolding Let_def
      by simp

    ultimately
    show ?thesis
      by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) mult.left_commute mult_cancel_right1)
  qed
  finally
  show ?thesis
    .
qed

lemma norm_double:
  shows "\<llangle>2 \<otimes> a\<rrangle> = \<bar>2*(\<gamma>\<^sub>p a)\<^sup>2 / (2*(\<gamma>\<^sub>p a)\<^sup>2 - 1)\<bar> * \<llangle>a\<rrangle>"
proof-
  have "(\<llangle>2 \<otimes> a\<rrangle>)\<^sup>2 = (2*(\<gamma>\<^sub>p a)\<^sup>2 / (2*(\<gamma>\<^sub>p a)\<^sup>2 - 1))\<^sup>2 * (\<llangle>a\<rrangle>)\<^sup>2"
    by (metis double_inner power2_eq_square square_norm_inner)
  then show ?thesis
    by (metis Mobius_gyrocarrier'.norm_inner real_root_mult real_sqrt_abs sqrt_def square_norm_inner)
qed

lemma einstein_triangle:
  shows "\<llangle>a \<oplus>\<^sub>e b\<rrangle> \<le> \<llangle>(of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>e of_complex (\<llangle>b\<rrangle>))\<rrangle>"
proof-
  let ?a = "(1 / 2) \<otimes> a" and ?b = "(1 / 2) \<otimes> b"
  have "\<llangle>a \<oplus>\<^sub>e b\<rrangle> = \<llangle>2 \<otimes> (?a \<oplus>\<^sub>m ?b)\<rrangle>"
    unfolding oplus_e_oplus_m
    by simp
  also have "\<dots> = \<bar>tanh (2 * artanh (\<llangle>?a \<oplus>\<^sub>m ?b\<rrangle>))\<bar>"
    using norm_scale_tanh by blast
  finally have *: "\<llangle>a \<oplus>\<^sub>e b\<rrangle> = tanh (2 * artanh (\<llangle>?a \<oplus>\<^sub>m ?b\<rrangle>))"
    using tanh_artanh_nonneg norm_lt_one
    using Mobius_gyrocarrier'.norm_inner square_norm_inner 
    by force

  let ?A = "of_complex (\<llangle>a\<rrangle>)" and ?B = "of_complex (\<llangle>b\<rrangle>)"
  let ?A' = "(1/2) \<otimes> ?A" and ?B' = "(1/2) \<otimes> ?B"
  have "\<llangle>(?A \<oplus>\<^sub>e ?B)\<rrangle> = \<llangle>2 \<otimes> (?A' \<oplus>\<^sub>m ?B')\<rrangle>"
    using oplus_e_oplus_m by auto
  also have "\<dots> = \<bar>tanh (2 * artanh (\<llangle>?A' \<oplus>\<^sub>m ?B'\<rrangle>))\<bar>"
    using norm_scale_tanh by blast
  finally have **: "\<llangle>(?A \<oplus>\<^sub>e ?B)\<rrangle> = tanh (2 * artanh (\<llangle>?A' \<oplus>\<^sub>m ?B'\<rrangle>))"
    using tanh_artanh_nonneg norm_lt_one
    using Mobius_gyrocarrier'.norm_inner square_norm_inner 
    by force

  have "of_complex (\<llangle>(1 / 2) \<otimes> a\<rrangle>) = (1 / 2) \<otimes> of_complex (\<llangle>a\<rrangle>)"
       "of_complex (\<llangle>(1 / 2) \<otimes> b\<rrangle>) = (1 / 2) \<otimes> of_complex (\<llangle>b\<rrangle>)"
    using otimes_homogenity[of "1/2" a] otimes_homogenity[of "1/2" b]
    by (smt (verit) Mobius_gyrocarrier'.gyronorm_def Mobius_gyrocarrier'.of_carrier Mobius_gyrocarrier'.to_carrier Mobius_gyrocarrier'.norm_inner divide_eq_0_iff divide_eq_1_iff divide_less_0_1_iff norm_eq_zero norm_lt_one norm_of_real otimes_scale_prop real_sqrt_abs square_norm_inner)+
  then have "\<llangle>?a \<oplus>\<^sub>m ?b\<rrangle> \<le> \<llangle>?A' \<oplus>\<^sub>m ?B'\<rrangle>"
    using mobius_triangle[of ?a ?b]
    by simp

  then show ?thesis
    using * ** tanh_artanh_mono
    using norm_p.rep_eq norm_lt_one
    by auto
qed     

lemma gyr_e_gyrospace2:
  shows "gyr\<^sub>e u v (r \<otimes> a) = r \<otimes> (gyr\<^sub>e u v a)"
  by (metis iso_me_gyr half gyr_m_gyrospace2 otimes_2_half)

lemma gyr_e_gyrospace:
  shows "gyr\<^sub>e (r1 \<otimes> v) (r2 \<otimes> v) = id"
proof-
  have "\<forall> z. gyr\<^sub>e (r1 \<otimes> v) (r2 \<otimes> v) z = z"
    unfolding gyr_e_gyr_m
    using gyr_m_gyrospace[of "(1/2)*r1" v "(1/2)*r2"]
    by (metis Mobius_gyrovector_space.scale_1 eq_id_iff nonzero_mult_div_cancel_left otimes_assoc times_divide_eq_right zero_neq_numeral)
  then show ?thesis
    by auto
qed

end
