theory Einstein
  imports Complex_Main GyroGroup GyroVectorSpace HOL.Real_Vector_Spaces
  MobiusGyroGroup HOL.Transcendental
begin

text \<open>Einstein zero\<close>

definition e_ozero' :: "complex" where
  "e_ozero' = 0"

lift_definition e_ozero :: PoincareDisc  ("0\<^sub>E") is e_ozero'
  unfolding e_ozero'_def
  by simp

lemma e_zero_m_zero:
  shows "0\<^sub>E = 0\<^sub>m"
  using e_ozero'_def e_ozero_def m_ozero'_def m_ozero_def 
  by auto

text \<open>Einstein addition\<close>

definition e_oplus' :: "complex \<Rightarrow> complex \<Rightarrow> complex"  where
  "e_oplus' u v = (1 / (1 + inner u v)) *\<^sub>R (u + (1 / \<gamma> u) *\<^sub>R v + ((\<gamma> u / (1 + \<gamma> u)) * (inner u v)) *\<^sub>R u)"

lemma norm_oplus'_e:
  assumes "norm u < 1" "norm v <1"
  shows "norm (e_oplus' u v)^2 =
         1 / (1 + inner u v)^2 * (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - (inner u v)^2))"
proof-
  let ?uv = "inner u v"
  let ?gu = "\<gamma> u / (1 + \<gamma> u)"

  have 1: "norm (e_oplus' u v)^2 = 
        norm (1 / (1 + ?uv))^2 * norm ((u + ((1 / \<gamma> u) *\<^sub>R v) + (?gu * ?uv) *\<^sub>R u))^2"  
    by (metis e_oplus'_def norm_scaleR power_mult_distrib real_norm_def)

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

lemma gamma_e_oplus':
  assumes "norm u < 1" "norm v < 1"
  shows "1 / sqrt(1 - norm (e_oplus' u v)^2) = \<gamma> u * \<gamma> v * (1 + inner u v)"
proof-
  let ?uv = "inner u v"

  have abs: "abs (1 + ?uv) = 1 + ?uv"
    using abs_inner_lt_1 assms by fastforce

  have "1 - norm (e_oplus' u v)^2 = 
        1 - 1 / (1 + ?uv)^2 * (norm(u+v)^2 - ((norm u)^2 *(norm v)^2 - ?uv^2))"
    using assms norm_oplus'_e
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
  finally have "1 / sqrt (1 - norm (e_oplus' u v)^2) = 
                1 / sqrt((1 - (norm u)^2 - (norm v)^2 + (norm u)^2*(norm v)^2) / (1 + ?uv)^2)"
    by simp
  then have 1: "1 / sqrt (1 - norm (e_oplus' u v)^2) = 
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

lemma gamma_e_oplus'_not_zero:
  assumes "norm u < 1" "norm v < 1"
  shows "1 / sqrt(1 - norm(e_oplus' u v)^2) \<noteq> 0"
  using assms
  using gamma_e_oplus' gamma_factor_def gamma_ok norm_oplus'_e
  by fastforce

lemma e_oplus'_in_unit_disc:
  assumes "norm u < 1" "norm v < 1"
  shows "norm (e_oplus' u v) < 1"
proof-
  let ?uv = "inner u v"
  have abs: "abs (1 + ?uv) = 1 + ?uv"
    using abs_inner_lt_1 assms by fastforce
  then show ?thesis
    using assms
    by (smt (verit, ccfv_SIG) dot_square_norm gamma_factor_def gamma_factor_def gamma_factor_positive gamma_e_oplus' gamma_e_oplus'_not_zero mult_nonneg_nonneg norm_eq_sqrt_inner real_sqrt_gt_0_iff real_sqrt_lt_1_iff zero_less_divide_1_iff)
qed

lemma gamma_factor_e_oplus':
  assumes "norm u < 1" "norm v < 1"
  shows "\<gamma> (e_oplus' u v) = (\<gamma> u) * (\<gamma> v) * (1 + inner u v)"
proof-
  have "\<gamma> (e_oplus' u v) = 1 / sqrt(1 - norm (e_oplus' u v)^2)"
    by (simp add: assms(1) assms(2) e_oplus'_in_unit_disc gamma_factor_def)
  then show ?thesis
    using assms
    using gamma_e_oplus' by force
qed

lift_definition e_oplus :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<oplus>\<^sub>E" 100) is e_oplus'
  by (rule e_oplus'_in_unit_disc)


lemma e_left_id:
  shows "0\<^sub>E \<oplus>\<^sub>E u = u"
  apply transfer
  unfolding e_oplus'_def e_ozero'_def
  by (simp add: gamma_factor_def)

(* ------------------------------------------------------------------------------------- *)
  
definition e_ominus' :: "complex \<Rightarrow> complex" where
  "e_ominus' v = - v"                                      

lemma e_ominus'_in_unit_disc:
  assumes "norm z < 1"
  shows "norm (e_ominus' z) < 1"
  using assms
  unfolding e_ominus'_def
  by simp

lift_definition e_ominus :: "PoincareDisc \<Rightarrow> PoincareDisc" ("\<ominus>\<^sub>E") is e_ominus'
  using e_ominus'_in_unit_disc by blast

lemma e_minus_m_minus:
  shows "\<ominus>\<^sub>E a = \<ominus>\<^sub>m a"
  by (simp add: e_ominus'_def e_ominus_def m_ominus'_def m_ominus_def)

lemma e_minus_scale:
  shows "k \<otimes> (\<ominus>\<^sub>E u) = \<ominus>\<^sub>E (k \<otimes> u)"
  by (metis Moebious_gyrovector_space.scale_minus1 e_minus_m_minus gyroinv_PoincareDisc_def mult.commute otimes_assoc)

(* ------------------------------------------------------------------------------------- *)

lift_definition e_gammma_factor :: "PoincareDisc \<Rightarrow> real" ("\<gamma>\<^sub>E") is gamma_factor
  done

lemma gamma_factorE_positive:
  shows "\<gamma>\<^sub>E a > 0"
  by transfer (simp add: gamma_factor_positive)

lemma gamma_factor_oplus_e:
  shows "\<gamma>\<^sub>E (u \<oplus>\<^sub>E v) = \<gamma>\<^sub>E u * \<gamma>\<^sub>E v * (1 + u \<cdot> v)"
  using gamma_factor_e_oplus' 
  by transfer blast

lemma norm_square_gamma_half:
  assumes "norm v < 1"
  shows "norm ((\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v)^2 = (\<gamma> v - 1) / (\<gamma> v + 1)"
proof-
  have "norm ((\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v)^2 = ((\<gamma> v) / (1 + \<gamma> v))^2 *(norm v)^2"
    by (simp add: power2_eq_square)
  also have "\<dots> = (\<gamma> v / (1 + \<gamma> v))^2 *((\<gamma> v)^2 - 1) / (\<gamma> v)^2"
    using assms
    by (simp add: norm_square_gamma_factor')
  also have "\<dots> = (\<gamma> v)^2 / (1 + \<gamma> v)^2 * ((\<gamma> v)^2 - 1) / (\<gamma> v)^2"
    by (simp add: power_divide)
  also have "\<dots> = ((\<gamma> v)^2 - 1) / (1 + \<gamma> v)^2"
    using assms gamma_factor_positive 
    by fastforce
  also have "\<dots> = (\<gamma> v - 1) * (\<gamma> v + 1) / (1 + \<gamma> v)^2"
    by (simp add: power2_eq_square square_diff_one_factored)
  also have "\<dots> = (\<gamma> v - 1) / (1 + \<gamma> v)"
    by (simp add: add.commute power2_eq_square)
  finally
  show ?thesis
    by simp
qed

lemma  iso_ei_mo_help3:
  assumes "norm v < 1"
  shows "1 + (\<gamma> v - 1) / (1 + \<gamma> v) = 2 * \<gamma> v / (1 + \<gamma> v)"
proof-
  have "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive
    by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_ei_mo_help4:
  assumes "norm v < 1"
  shows "1 - (\<gamma> v - 1) / (1 + \<gamma> v) = 2 / (1 + \<gamma> v)"
proof-
  have "1 + \<gamma> v \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_ei_mo_help5:
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

lemma  iso_ei_mo_help6:
  assumes "norm u < 1" "norm v < 1"
  shows "1 + 2 * (\<gamma> u / (1 + \<gamma> u)) * ((\<gamma> v) / (1 + \<gamma> v)) * inner u v + (norm ((\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v))^2 =
         2 * (\<gamma> v) / (1 + \<gamma> v) + 2 * (\<gamma> v) * (\<gamma> u) / ((1 + \<gamma> v) * (1 + \<gamma> u)) * inner u v"
  using norm_square_gamma_half[OF assms(2)] iso_ei_mo_help3[OF assms(2)]
  by (simp add: add.commute mult.commute mult.left_commute)

lemma  iso_ei_mo_help7:
  assumes "norm u < 1" 
  shows "1 - (norm ((\<gamma> u / (1 + \<gamma> u)) *\<^sub>R u))^2 = 2 / (1 + \<gamma> u)" (is "?lhs = ?rhs")
  using norm_square_gamma_half[OF assms] iso_ei_mo_help4[OF assms]
  by (simp add: add.commute)

lemma  iso_ei_mo_help8:
  assumes "norm u < 1" "norm v < 1"
  shows "1 + (norm ((\<gamma> u / (1 + \<gamma> u)) *\<^sub>R u))^2 * (norm ((\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v))^2 =
         2 * (1 + (\<gamma> u)*(\<gamma> v)) / ((1 + \<gamma> v) * (1 + \<gamma> u))"
  using assms
  by (smt (verit) inner_commute inner_real_def iso_ei_mo_help5 norm_square_gamma_half)

lemma  iso_ei_mo_help8_1:
  assumes "norm u < 1" "norm v < 1"
  shows "1 + ((\<gamma> u - 1) / (1 + \<gamma> u)) * ((\<gamma> v - 1) / (1 + \<gamma> v)) =
         2 * (1 + (\<gamma> u) * (\<gamma> v)) / ((1 + \<gamma> u)*(1 + \<gamma> v))"
  by (metis assms(1) assms(2) iso_ei_mo_help5 mult.commute)

lemma iso_ei_inner_help2:
  shows "to_complex ((1 / 2) \<otimes> u) = 
         (\<gamma> (to_complex u)) / (1 + \<gamma> (to_complex u)) * to_complex u"
  using half half.rep_eq half'_def
  by (simp add: scaleR_conv_of_real)
  
lemma iso_ei_inner_mo_help3:
  assumes "cmod v < 1"
  shows "(cmod (half' v))\<^sup>2 = (\<gamma> v / (1 + \<gamma> v))^2 * (norm v)^2"
  unfolding half'_def 
  using norm_square_gamma_half assms
  by (smt (verit) divide_pos_pos gamma_factor_positive norm_scaleR power_mult_distrib)

lemma iso_ei_inner_mo_help4:
  assumes "cmod u < 1" "cmod v < 1"
  shows "inner (half' u) (half' v) = (\<gamma> u / (1 + \<gamma> u)) * (\<gamma> v / (1 + \<gamma> v)) * (inner u v)"
  unfolding half'_def scaleR_conv_of_real
  by (metis inner_mult_left inner_mult_right mult.assoc)


lemma iso_ei_mo_inner_help6:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "(1 + 2 * inner (half' u) (half' v) + (cmod (half' v))\<^sup>2) *\<^sub>R (half' u) = 
        (2 * \<gamma> v / (1 + \<gamma> v) + 2 * \<gamma> v * \<gamma> u / ((1 + \<gamma> v) * (1 + \<gamma> u)) * inner u v) * (\<gamma> u / (1 + \<gamma> u)) * u"
proof-
  have *: "half' u = (\<gamma> u / (1 + \<gamma> u)) * u"
    by (simp add: half'_def scaleR_conv_of_real)
  
  have "1 + 2 * inner (half' u) (half' v) + (cmod (half' v))\<^sup>2 = 
        1 + 2 * (\<gamma> u / (1 + \<gamma> u) * (\<gamma> v / (1 + \<gamma> v)) * inner u v) + (\<gamma> v / (1 + \<gamma> v))\<^sup>2 * (cmod v)\<^sup>2"
    using iso_ei_inner_mo_help4 iso_ei_inner_mo_help3 assms
    by simp
  also have "\<dots> = (2 * \<gamma> v / (1 + \<gamma> v) + 2 * \<gamma> v * \<gamma> u / ((1 + \<gamma> v) * (1 + \<gamma> u)) * inner u v)"
    using iso_ei_mo_help6[OF assms]
    using assms(2) iso_ei_inner_mo_help3 half'_def by auto
  finally
  show ?thesis
    using *
    by (simp add: of_real_def)
qed

lemma iso_ei_mo_inner_help7_1:
  assumes "cmod u < 1"
  shows "(cmod (half' u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)"
  using assms
  using half'_def norm_square_gamma_half
  by auto

lemma iso_ei_mo_inner_help7:
  fixes u v :: complex
  assumes "cmod u < 1"
  shows "(1 - (cmod (half' u))\<^sup>2) *\<^sub>R (half' v) = 
         2 * (\<gamma> v) / ((1 + \<gamma> v) *(1 + \<gamma> u)) * v"
  using iso_ei_mo_help4 iso_ei_mo_inner_help7_1 assms
  by (simp add: half'_def mult.assoc scaleR_conv_of_real)

lemma iso_ei_mo_inner_help8:
  assumes "cmod u < 1" "cmod v < 1"
  shows "1 + 2 * inner (half' u) (half' v) + (cmod (half' u))\<^sup>2 * (cmod (half' v))\<^sup>2 =
         2 * (\<gamma> u) * (\<gamma> v) * inner u v / ((1 + \<gamma> u) * (1 + \<gamma> v)) + 2 * (1 + (\<gamma> u)*(\<gamma> v)) / ((1 + \<gamma> u) * (1 + \<gamma> v))"
  using assms iso_ei_inner_mo_help4 iso_ei_mo_help8_1 iso_ei_mo_inner_help7_1
  by fastforce


lemma iso_ei_mo_help9:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "m_oplus'_full (half' u) (half' v) = 
         ((2*(\<gamma> v / (1 + \<gamma> v)) + (2*(\<gamma> v / (1 + \<gamma> v)) * (\<gamma> u / (1 + \<gamma> u)) * inner u v)) *
          (\<gamma> u / (1 + \<gamma> u)) * u + 2 * \<gamma> v / ((1 + \<gamma> v) * (1 + \<gamma> u)) * v) /
          (2 * (\<gamma> u) * (\<gamma> v) * inner u v / ((1 + \<gamma> v) * (1 + \<gamma> u)) + 2 * (1 + (\<gamma> u) * (\<gamma> v)) / ((1 + \<gamma> v) * (1 + \<gamma> u)))" (is "?lhs = ?rhs")
  using iso_ei_mo_inner_help8[OF assms]  iso_ei_mo_inner_help7[OF assms(1)] iso_ei_mo_inner_help6[OF assms]
  unfolding m_oplus'_full_def
  by (simp add: mult.commute)

lemma iso_ei_mo_help10:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "half' (e_oplus' u v) = 
         \<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u)"
proof-
  have "half' (e_oplus' u v) = 
       \<gamma> u * \<gamma> v * (1 + inner u v) / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) *
       ((1 / (1 + inner u v)) * (u + (1 / \<gamma> u)*v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u))"
    unfolding half'_def
    unfolding gamma_factor_e_oplus'[OF assms] scaleR_conv_of_real
    unfolding e_oplus'_def scaleR_conv_of_real
    by simp
  then show ?thesis
    using assms
    by (smt (verit, best) ab_semigroup_mult_class.mult_ac(1) gamma_e_oplus' gamma_e_oplus'_not_zero inner_mult_left' inner_real_def mult.commute mult_eq_0_iff nonzero_mult_divide_mult_cancel_right2 of_real_1 of_real_divide of_real_mult real_inner_1_right times_divide_times_eq)
qed

lemma iso_ei_mo_help11:
  fixes u v :: complex
  shows "((2 * (\<gamma> v / (1 + \<gamma> v)) + (2 * (\<gamma> v / (1 + \<gamma> v)) * (\<gamma> u / (1 + \<gamma> u)) * inner u v)) * (\<gamma> u / (1 + \<gamma> u)) * u + 2 * \<gamma> v / ((1 + \<gamma> v) * (1 + \<gamma> u)) * v) =
          1 / ((1 + \<gamma> v) * (1 + \<gamma> u)) * ((2 * \<gamma> v * \<gamma> u * u) + 2 * \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1+ \<gamma> u) * u + 2 * \<gamma> v * v)" (is "?lhs = ?rhs")
proof-
  have "(2 * (\<gamma> v / (1+\<gamma> v)) + (2 * (\<gamma> v / (1 + \<gamma> v)) * (\<gamma> u / (1 + \<gamma> u)) * inner u v)) * (\<gamma> u / (1 + \<gamma> u)) * u = 
        (2 * (\<gamma> v / (1+\<gamma> v))) * (\<gamma> u / (1 + \<gamma> u)) * u + 2 * (\<gamma> v / (1 + \<gamma> v)) * (\<gamma> u / (1 +\<gamma> u)) * inner u v * \<gamma> u / (1 +\<gamma> u) * u"
    by (simp add: mult.commute mult.left_commute ring_class.ring_distribs(1))
  also have "\<dots> =  (1/((1+\<gamma> v)*(1+\<gamma> u))) *((2*(\<gamma> v)*(\<gamma> u) *u) +  (2*(\<gamma> v) *(\<gamma> u)*(inner u v)*(((\<gamma> u) )/(1+(\<gamma> u) ))*u))"
    by (simp add: distrib_left mult.commute mult.left_commute)
  ultimately show ?thesis 
    by (simp add: distrib_left)
qed


lemma iso_ei_mo_help12:
  fixes u v :: complex
  shows "2 * \<gamma> u * \<gamma> v * inner u v / ((1 + \<gamma> v) * (1 + \<gamma> u)) + 2 * (1 + \<gamma> u * \<gamma> v)/ ((1 + \<gamma> v) * (1 + \<gamma> u)) =
         1 / ((1 + \<gamma> v) * (1 + \<gamma> u)) * ((2 * \<gamma> u * \<gamma> v * inner u v) + (2 + 2 * \<gamma> u * \<gamma> v))"
  by argo

lemma iso_ei_mo_help13:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "m_oplus'_full (half' u) (half' v) = 
         ((2 * \<gamma> v * \<gamma> u * u) + 2 * \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u) * u + 2 * \<gamma> v * v) / ((2 * \<gamma> u * \<gamma> v * inner u v) + ((2 + 2 * \<gamma> u * \<gamma> v)))"
proof-
  have "1 + \<gamma> u \<noteq>0" "1 + \<gamma> v \<noteq> 0"
    using  gamma_factor_positive assms by force+
  then have "1 / ((1 + \<gamma> u) * (1 + \<gamma> v)) \<noteq> 0"
    by simp
  moreover 
  have "((2 * (\<gamma> v / (1 + \<gamma> v)) + 2 * (\<gamma> v / (1 + \<gamma> v)) * (\<gamma> u / (1 + \<gamma> u)) * inner u v) * (\<gamma> u / (1 + \<gamma> u))) * u +
    (2 * \<gamma> v / ((1 + \<gamma> v) * (1 + \<gamma> u))) * v =
    (1 / ((1 + \<gamma> v) * (1 + \<gamma> u))) * ((2 * \<gamma> v * \<gamma> u) * u + cor (2 * \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u)) * u + cor (2 * \<gamma> v) * v)"
    using iso_ei_mo_help11 by blast
  moreover 
  have "2 * \<gamma> u * \<gamma> v * inner u v / ((1 + \<gamma> v) * (1 + \<gamma> u)) + 2 * (1 + \<gamma> u * \<gamma> v) / ((1 + \<gamma> v) * (1 + \<gamma> u)) =
    1 / ((1 + \<gamma> v) * (1 + \<gamma> u)) * (2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v))"
    using iso_ei_mo_help12 
    by presburger
  ultimately 
  show ?thesis
    using iso_ei_mo_help9[OF assms]
    by (smt (verit, ccfv_threshold) divide_divide_eq_left' division_ring_divide_zero eq_divide_eq inner_commute inner_real_def mult_eq_0_iff mult_eq_0_iff nonzero_mult_divide_mult_cancel_left nonzero_mult_divide_mult_cancel_left numeral_One of_real_1 of_real_1 of_real_divide of_real_inner_1 of_real_mult one_divide_eq_0_iff real_inner_1_right times_divide_times_eq)
qed

lemma iso_ei_mo_help14:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "m_oplus'_full (half' u) (half' v) =
        (\<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1)) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u)"
proof-
  have "\<gamma> u \<noteq> 0" "\<gamma> v \<noteq> 0"
    using assms gamma_factor_positive 
    by fastforce+
  moreover
  have "(2 * \<gamma> v * \<gamma> u) * u + (2 * \<gamma> v * \<gamma> u * inner u v * \<gamma> u / (1 + \<gamma> u)) * u + (2 * \<gamma> v) * v =
        (2 * \<gamma> v * \<gamma> u) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u)"
    using \<open>\<gamma> u \<noteq> 0\<close> \<open>\<gamma> v \<noteq> 0\<close>
    by (simp add: distrib_left is_num_normalize(1) mult.commute)      
  moreover
  have "2 * \<gamma> u * \<gamma> v * inner u v + (2 + 2 * \<gamma> u * \<gamma> v) = 2 * (\<gamma> u * \<gamma> v * (1 + inner u v) + 1)"
    by (simp add: ring_class.ring_distribs(1))
  moreover 
  have "(2 * \<gamma> v * \<gamma> u) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u) /
        (2 * (\<gamma> u * \<gamma> v * (1 + inner u v) + 1)) =
        (\<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1)) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u) * inner u v) * u)"
  proof -
    have "\<forall>r ra rb. (ra::real) / r = ra * (rb / (rb * r)) \<or> 0 = rb"
      by simp
    then have "(\<gamma> u * (\<gamma> v / ((1 + inner u v) * (\<gamma> u * \<gamma> v) + 1))) * ( u +  v * (1 / \<gamma> u) +  u * (\<gamma> u * (inner u v / (1 + \<gamma> u)))) = (\<gamma> u * (\<gamma> v * (2 / (2 * ((1 + inner u v) * (\<gamma> u * \<gamma> v) + 1))))) * ( u +  v * (1 / \<gamma> u) +  u * (\<gamma> u * (inner u v / (1 + \<gamma> u))))"
      by (metis (no_types) zero_neq_numeral)
    then show ?thesis
      by (simp add: mult.commute)
  qed
  ultimately show ?thesis
    using iso_ei_mo_help13 assms
    by presburger
qed

lemma iso_ei_mo_half:
  shows "(1/2) \<otimes> (u \<oplus>\<^sub>E v) = ((1/2) \<otimes> u \<oplus>\<^sub>m (1/2) \<otimes> v)"
proof transfer
  fix u v
  assume *: "cmod u < 1" "cmod v < 1"
  have "otimes' (1 / 2) (e_oplus' u v) = half' (e_oplus' u v)"
    using half'[of "e_oplus' u v"] *
    unfolding otimes'_def
    using e_oplus'_in_unit_disc 
    by blast
  moreover
  have "otimes' (1 / 2) u = half' u" "otimes' (1 / 2) v = half' v"
    using half' *
    by auto
  moreover
  have **: "cmod (half' u) < 1" "cmod (half' v) < 1"
    using *
    by (metis eq_onp_same_args half.rsp rel_fun_eq_onp_rel)+
  have "half' (e_oplus' u v) = m_oplus' (half' u) (half' v)"
    using * iso_ei_mo_help10[OF *] iso_ei_mo_help14[OF *]
    unfolding m_oplus'_full[OF **, symmetric]
    by simp
  ultimately
  show "otimes' (1 / 2) (e_oplus' u v) = m_oplus' (otimes' (1 / 2) u) (otimes' (1 / 2) v)"
    by simp
qed

lemma iso_ei_mo:
  shows "u \<oplus>\<^sub>E v = 2 \<otimes> ((1/2) \<otimes> u \<oplus>\<^sub>m (1/2) \<otimes> v)"
  by (metis half iso_ei_mo_half two_times_half)

(* ---------------------------------------------------------------------------------------------- *)

definition e_gyr::"PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
    "e_gyr u v w = \<ominus>\<^sub>E(u\<oplus>\<^sub>Ev)\<oplus>\<^sub>E(u \<oplus>\<^sub>E(v \<oplus>\<^sub>E w))"

lemma e_gyr_m_gyr:
  shows "(1/2) \<otimes> e_gyr u v w = m_gyr ((1/2) \<otimes> u) ((1/2) \<otimes> v) ((1/2) \<otimes> w)"
  unfolding e_gyr_def Moebius_gyrogroup.gyr_def
  using iso_ei_mo_half e_minus_m_minus e_minus_scale
  by presburger

lemma e_gyr_m_gyr_two:
  shows "e_gyr u v w = 2 \<otimes> m_gyr ((1/2) \<otimes> u) ((1/2) \<otimes> v) ((1/2) \<otimes> w)"
  by (metis e_gyr_m_gyr half two_times_half)

lemma e_gyr_left_loop:
  shows "e_gyr a b = e_gyr (a \<oplus>\<^sub>E b) b"
  using m_gyr_left_loop e_gyr_m_gyr_two iso_ei_mo_half
  by presburger

(* ---------------------------------------------------------------------------------------------- *)

lemma e_inv:
  shows "\<ominus>\<^sub>E a \<oplus>\<^sub>E a = 0\<^sub>E"
  using e_minus_m_minus e_minus_scale e_zero_m_zero iso_ei_mo times2_m 
  by auto

lemma e_gyro_left_assoc:
  shows "a \<oplus>\<^sub>E (b \<oplus>\<^sub>E z) = (a \<oplus>\<^sub>E b) \<oplus>\<^sub>E e_gyr a b z"
  using e_gyr_m_gyr iso_ei_mo iso_ei_mo_half m_gyro_left_assoc 
  by presburger

lemma e_gyro_commute:
  shows  "a \<oplus>\<^sub>E b = e_gyr a b (b \<oplus>\<^sub>E a)"
  by (metis e_gyr_m_gyr_two iso_ei_mo iso_ei_mo_half m_gyro_commute)

lemma e_gyr_distrib:
  shows "e_gyr a b (a' \<oplus>\<^sub>E b') = e_gyr a b a' \<oplus>\<^sub>E e_gyr a b b'"
  using e_gyr_m_gyr e_gyr_m_gyr_two iso_ei_mo iso_ei_mo_half
  by force

lemma e_gyr_inv:
  "e_gyr a b (e_gyr b a z) = z"
  by (metis e_gyr_m_gyr half m_gyr_inv two_times_half)


lemma e_gyr_bij:
  shows "bij (e_gyr a b)"
  by (metis bijI e_gyr_inv inj_def surjI)
  
interpretation Einstein_gyrogroup: gyrogroup e_ozero e_oplus e_ominus e_gyr
proof
  fix a
  show "0\<^sub>E \<oplus>\<^sub>E a = a"
    by (simp add: e_left_id)
next
  fix a
  show "\<ominus>\<^sub>E a \<oplus>\<^sub>E a = 0\<^sub>E"
    by (simp add: e_inv)    
next
  fix a b z
  show "a \<oplus>\<^sub>E (b \<oplus>\<^sub>E z) = a \<oplus>\<^sub>E b \<oplus>\<^sub>E e_gyr a b z"
    by (simp add: e_gyro_left_assoc)
next
  fix a b
  show "e_gyr a b = e_gyr (a \<oplus>\<^sub>E b) b"
    using e_gyr_left_loop by auto
next
  fix a b
  show "gyrogroup'.gyroaut (\<oplus>\<^sub>E) (e_gyr a b)"
    unfolding gyrogroup'.gyroaut_def
  proof safe
    fix a' b'
    show "e_gyr a b (a' \<oplus>\<^sub>E b') = e_gyr a b a' \<oplus>\<^sub>E e_gyr a b b'"
      by (simp add: e_gyr_distrib)
  next
    show "bij (e_gyr a b)"
      by (simp add: e_gyr_bij)
  qed
qed

interpretation Einstein_gyrocommutative_gyrogroup: gyrocommutative_gyrogroup e_ozero e_oplus e_ominus e_gyr
proof
  fix a b
  show "a \<oplus>\<^sub>E b = e_gyr a b (b \<oplus>\<^sub>E a)"
    using e_gyro_commute by auto
qed

lemma half_inner_left: 
  "((1/2) \<otimes> a) \<cdot> b = (\<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a)) * (a \<cdot> b)"
  unfolding half[symmetric]
  by transfer (simp add: half'_def)

lemma half_inner_right:
  "a \<cdot> ((1/2) \<otimes> b) = (\<gamma>\<^sub>E b / (1 + \<gamma>\<^sub>E b)) * (a \<cdot> b)"
  by (metis inner_p.rep_eq half_inner_left inner_commute)

lemma half_inner: 
  "((1/2) \<otimes> a) \<cdot> ((1/2) \<otimes> b) = (\<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a)) * (\<gamma>\<^sub>E b / (1 + \<gamma>\<^sub>E b)) * (a \<cdot> b)"
  using half_inner_left half_inner_right
  by auto

lemma double_inner_left: 
  "(2 \<otimes> a) \<cdot> b = (2*(\<gamma>\<^sub>E a)\<^sup>2 / (2*(\<gamma>\<^sub>E a)\<^sup>2 - 1)) * (a \<cdot> b)"
  unfolding double[symmetric]
  by transfer (simp add: double'_def)

lemma double_inner_right: 
  "a \<cdot> (2 \<otimes> b) = (2*(\<gamma>\<^sub>E b)\<^sup>2 / (2*(\<gamma>\<^sub>E b)\<^sup>2 - 1)) * (a \<cdot> b)"
  by (metis inner_p.rep_eq double_inner_left inner_commute)

lemma double_inner: 
  "(2 \<otimes> a) \<cdot> (2 \<otimes> b) = (2*(\<gamma>\<^sub>E a)\<^sup>2 / (2*(\<gamma>\<^sub>E a)\<^sup>2 - 1)) * (2*(\<gamma>\<^sub>E b)\<^sup>2 / (2*(\<gamma>\<^sub>E b)\<^sup>2 - 1)) * (a \<cdot> b)"
  using double_inner_left double_inner_right
  by auto

lemma double_norm_square:
  shows "2*(\<gamma>\<^sub>E u)\<^sup>2 / (2*(\<gamma>\<^sub>E u)\<^sup>2 - 1) = 2 / (1 + (\<llangle>u\<rrangle>)\<^sup>2)"
  by transfer (simp add: double'_cmod) 

lemma norm_square_gamma_factorE:
  shows "(\<llangle>u\<rrangle>)\<^sup>2 = 1 - 1 / (\<gamma>\<^sub>E u)\<^sup>2"
  by transfer (simp add: norm_square_gamma_factor)

lemma square_norm_half:
  shows "(\<llangle>(1/2) \<otimes> a\<rrangle>)\<^sup>2 = (\<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a))\<^sup>2 * (\<llangle>a\<rrangle>)\<^sup>2"
  by (metis  half_inner power2_eq_square square_norm_inner)

lemma double_mgyr_half:
  shows "let m = m_gyr ((1/2) \<otimes> u) ((1/2) \<otimes> v) ((1/2) \<otimes> a)
          in 2*(\<gamma>\<^sub>E m)\<^sup>2 / (2*(\<gamma>\<^sub>E m)\<^sup>2 - 1) = (1 + \<gamma>\<^sub>E a) / \<gamma>\<^sub>E a"
proof-
  define m where "m = m_gyr ((1/2) \<otimes> u) ((1/2) \<otimes> v) ((1/2) \<otimes> a)"
  have "\<llangle>m\<rrangle> = \<llangle>(1/2) \<otimes> a\<rrangle>"
    unfolding m_def moebius_gyroauto_norm
    by simp

  have "2*(\<gamma>\<^sub>E m)\<^sup>2 / (2*(\<gamma>\<^sub>E m)\<^sup>2 - 1) = 2 / (1 + (\<llangle>m\<rrangle>)\<^sup>2)"
    by (simp add: double_norm_square)
  also have "\<dots> = 2 / (1 + (\<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a))\<^sup>2 * (\<llangle>a\<rrangle>)\<^sup>2)"
    by (simp add: \<open>\<llangle>m\<rrangle> = \<llangle>(1 / 2) \<otimes> a\<rrangle>\<close> square_norm_half)
  also have "\<dots> = 2 / (1 + (\<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a))\<^sup>2 * (1 - 1 / (\<gamma>\<^sub>E a)\<^sup>2))"
    using norm_square_gamma_factorE
    by auto
  also have "\<dots> = (1 + \<gamma>\<^sub>E a) / \<gamma>\<^sub>E a" (is "?lhs = ?rhs")
  proof-
    have *: "(\<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a))\<^sup>2 = (\<gamma>\<^sub>E a)\<^sup>2 / (1 + \<gamma>\<^sub>E a)\<^sup>2"
      by (simp add: power_divide)
    moreover
    have **: "1 - 1 / (\<gamma>\<^sub>E a)\<^sup>2 = ((\<gamma>\<^sub>E a)\<^sup>2 - 1) / (\<gamma>\<^sub>E a)\<^sup>2"
      using gamma_factorE_positive[of a]
      by (metis diff_divide_distrib less_numeral_extra(3) right_inverse_eq zero_less_power)
    ultimately
    have "(\<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a))\<^sup>2 * (1 - 1 / (\<gamma>\<^sub>E a)\<^sup>2) = 
          ((\<gamma>\<^sub>E a)\<^sup>2 / (1 + \<gamma>\<^sub>E a)\<^sup>2) * (((\<gamma>\<^sub>E a)\<^sup>2 - 1) / (\<gamma>\<^sub>E a)\<^sup>2)"
      by simp
    also have "\<dots> = ((\<gamma>\<^sub>E a)\<^sup>2 - 1) / (1 + \<gamma>\<^sub>E a)\<^sup>2"
      using gamma_factorE_positive[of a]
      by simp
    also have "\<dots> = (\<gamma>\<^sub>E a - 1) / (1 + \<gamma>\<^sub>E a)"
      using gamma_factorE_positive[of a]
      by (simp add: add.commute power2_eq_square square_diff_one_factored)
    finally
    have "?lhs = 2 / (1 + (\<gamma>\<^sub>E a - 1) / (1 + \<gamma>\<^sub>E a))"
      by simp
    also have "\<dots> = 2 / (((1 + \<gamma>\<^sub>E a) + (\<gamma>\<^sub>E a - 1)) / (1 + \<gamma>\<^sub>E a))"
      using gamma_factorE_positive[of a]
      by (metis add_divide_distrib add_less_same_cancel1 div_0 div_self less_divide_eq_1_neg less_numeral_extra(1) not_one_less_zero)
    also have "\<dots> = 2 / (2 * \<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a))"
      by simp
    also have "\<dots> = ?rhs"
      using gamma_factorE_positive[of a]
      by (metis divide_divide_eq_right mult_divide_mult_cancel_left_if zero_neq_numeral)
    finally show ?thesis
      .
  qed
  finally show ?thesis
    unfolding m_def Let_def
    by simp
qed

lemma einstein_gyroauto:
  shows "e_gyr u v a \<cdot> e_gyr u v b = a \<cdot> b"
proof-
  let ?u = "(1/2) \<otimes> u" and ?v = "(1/2) \<otimes> v" and ?a = "(1/2) \<otimes> a" and ?b = "(1/2) \<otimes> b"
  let ?ma = "m_gyr ?u ?v ?a" and ?mb = "m_gyr ?u ?v ?b"
  let ?A = "2*(\<gamma>\<^sub>E ?ma)\<^sup>2 / (2*(\<gamma>\<^sub>E ?ma)\<^sup>2 - 1)" and ?B = "2*(\<gamma>\<^sub>E ?mb)\<^sup>2 / (2*(\<gamma>\<^sub>E ?mb)\<^sup>2 - 1)"
  let ?A' = "(\<gamma>\<^sub>E a / (1 + \<gamma>\<^sub>E a))" and ?B' = "(\<gamma>\<^sub>E b / (1 + \<gamma>\<^sub>E b))"

  have "e_gyr u v a \<cdot> e_gyr u v b = 2 \<otimes> ?ma \<cdot> 2 \<otimes> ?mb"
    unfolding e_gyr_m_gyr_two
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
    have "\<gamma>\<^sub>E a \<noteq> 0" "1 + \<gamma>\<^sub>E a \<noteq> 0"
      using gamma_factorE_positive 
      by (smt (verit))+
    then have "?A * ?A' = 1"
      using double_mgyr_half[of u v a] 
      unfolding Let_def
      by simp

    moreover

    have "\<gamma>\<^sub>E b \<noteq> 0" "1 + \<gamma>\<^sub>E b \<noteq> 0"
      using gamma_factorE_positive 
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

lemma e_otimes_distrib:
  shows "(r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus>\<^sub>E r2 \<otimes> a" 
proof-
  have "r1 \<otimes> a \<oplus>\<^sub>E r2 \<otimes> a =  2 \<otimes> ((1 / 2) \<otimes> (r1 \<otimes> a) \<oplus>\<^sub>m (1 / 2) \<otimes> (r2 \<otimes> a))"
    unfolding iso_ei_mo
    by simp
  also have "\<dots> = 2 \<otimes> ((1/2) \<otimes> ((r1 \<otimes> a) \<oplus>\<^sub>m (r2 \<otimes> a)))"
    using Moebious_gyrovector_space.monodistributive gyroplus_PoincareDisc_def 
    by auto
  also have "\<dots> = 2 \<otimes> ((1/2) \<otimes> ((r1 + r2) \<otimes> a))"
    using otimes_distrib 
    by auto
  finally show ?thesis
    using half two_times_half 
    by presburger
qed

lemma norm_double:
  shows "\<llangle>2 \<otimes> a\<rrangle> = \<bar>2*(\<gamma>\<^sub>E a)\<^sup>2 / (2*(\<gamma>\<^sub>E a)\<^sup>2 - 1)\<bar> * \<llangle>a\<rrangle>"
proof-
  have "(\<llangle>2 \<otimes> a\<rrangle>)\<^sup>2 = (2*(\<gamma>\<^sub>E a)\<^sup>2 / (2*(\<gamma>\<^sub>E a)\<^sup>2 - 1))\<^sup>2 * (\<llangle>a\<rrangle>)\<^sup>2"
    by (metis double_inner power2_eq_square square_norm_inner)
  then show ?thesis
    by (metis Moebius_gyrodom.norm_inner real_root_mult real_sqrt_abs sqrt_def square_norm_inner)
qed

lemma norm_m_scale_tanh: 
  shows "\<llangle>r \<otimes> z\<rrangle> = \<bar>tanh (r * artanh (\<llangle>z\<rrangle>))\<bar>"
proof transfer
  fix r z
  assume "cmod z < 1"
  have "cmod ((otimes'_k r z) * z / cor (cmod z)) = cmod (otimes'_k r z)"
    by (smt (verit) artanh_0 div_by_0 mult_cancel_right1 nonzero_eq_divide_eq norm_divide norm_not_less_zero norm_of_real of_real_0 otimes'_k_tanh tanh_0)
  then show "cmod (otimes' r z) = \<bar>tanh (r * artanh (cmod z))\<bar>"
    unfolding otimes'_def
    using \<open>cmod z < 1\<close> otimes'_k_tanh 
    by auto
qed

lemma einstein_triangle:
  shows "\<llangle>a \<oplus>\<^sub>E b\<rrangle> \<le> \<llangle>(of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>E of_complex (\<llangle>b\<rrangle>))\<rrangle>"
proof-
  let ?a = "(1 / 2) \<otimes> a" and ?b = "(1 / 2) \<otimes> b"
  have "\<llangle>a \<oplus>\<^sub>E b\<rrangle> = \<llangle>2 \<otimes> (?a \<oplus>\<^sub>m ?b)\<rrangle>"
    unfolding iso_ei_mo
    by simp
  also have "\<dots> = \<bar>tanh (2 * artanh (\<llangle>?a \<oplus>\<^sub>m ?b\<rrangle>))\<bar>"
    using norm_m_scale_tanh by blast
  finally have *: "\<llangle>a \<oplus>\<^sub>E b\<rrangle> = tanh (2 * artanh (\<llangle>?a \<oplus>\<^sub>m ?b\<rrangle>))"
    using tanh_artanh_nonneg norm_lt_one
    using Moebius_gyrodom.norm_inner square_norm_inner 
    by force

  let ?A = "of_complex (\<llangle>a\<rrangle>)" and ?B = "of_complex (\<llangle>b\<rrangle>)"
  let ?A' = "(1/2) \<otimes> ?A" and ?B' = "(1/2) \<otimes> ?B"
  have "\<llangle>(?A \<oplus>\<^sub>E ?B)\<rrangle> = \<llangle>2 \<otimes> (?A' \<oplus>\<^sub>m ?B')\<rrangle>"
    using iso_ei_mo by auto
  also have "\<dots> = \<bar>tanh (2 * artanh (\<llangle>?A' \<oplus>\<^sub>m ?B'\<rrangle>))\<bar>"
    using norm_m_scale_tanh by blast
  finally have **: "\<llangle>(?A \<oplus>\<^sub>E ?B)\<rrangle> = tanh (2 * artanh (\<llangle>?A' \<oplus>\<^sub>m ?B'\<rrangle>))"
    using tanh_artanh_nonneg norm_lt_one
    using Moebius_gyrodom.norm_inner square_norm_inner 
    by force

  have "of_complex (\<llangle>(1 / 2) \<otimes> a\<rrangle>) = (1 / 2) \<otimes> of_complex (\<llangle>a\<rrangle>)"
       "of_complex (\<llangle>(1 / 2) \<otimes> b\<rrangle>) = (1 / 2) \<otimes> of_complex (\<llangle>b\<rrangle>)"
    using otimes_homogenity[of "1/2" a] otimes_homogenity[of "1/2" b]
    by (smt (verit) Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.of_dom Moebius_gyrodom'.to_dom Moebius_gyrodom.norm_inner divide_eq_0_iff divide_eq_1_iff divide_less_0_1_iff norm_eq_zero norm_lt_one norm_of_real otimes_scale_prop real_sqrt_abs square_norm_inner)+
  then have "\<llangle>?a \<oplus>\<^sub>m ?b\<rrangle> \<le> \<llangle>?A' \<oplus>\<^sub>m ?B'\<rrangle>"
    using moebius_triangle[of ?a ?b]
    by simp

  then show ?thesis
    using * ** tanh_artanh_mono
    using norm_p.rep_eq norm_lt_one
    by auto    
qed                          

lemma e_gyr_gyrospace2:
  shows "e_gyr u v (r \<otimes> a) = r \<otimes> (e_gyr u v a)"
  by (metis e_gyr_m_gyr half m_gyr_gyrospace2 two_times_half)

lemma e_gyr_gyrospace:
  shows "e_gyr (r1 \<otimes> v) (r2 \<otimes> v) = id"
proof-
  have "\<forall> z. e_gyr (r1 \<otimes> v) (r2 \<otimes> v) z = z"
    unfolding e_gyr_m_gyr_two
    using m_gyr_gyrospace[of "(1/2)*r1" v "(1/2)*r2"]
    by (metis Moebious_gyrovector_space.scale_1 eq_id_iff nonzero_mult_div_cancel_left otimes_assoc times_divide_eq_right zero_neq_numeral)
  then show ?thesis
    by auto
qed

end
