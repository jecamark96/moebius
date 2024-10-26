theory Einstein
  imports Complex_Main GyroGroup GyroVectorSpace HOL.Real_Vector_Spaces
  MobiusGyroGroup HOL.Transcendental
begin

lift_definition e_inner :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> real" (infixl "\<cdot>\<^sub>E" 100) is inner
  done

lemma e_inner_m_inner:
  shows "m_inner z1 z2 = e_inner z1 z2"
  by transfer simp

definition e_ozero' :: "complex" where
  "e_ozero' = 0"

lemma norm_0:
  fixes x :: complex
  assumes "x = 0"
  shows "inner x x = 0"
  using assms 
  by force

lift_definition e_ozero :: PoincareDisc  ("0\<^sub>E") is e_ozero'
  unfolding e_ozero'_def
  using norm_0
  by auto


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
  using e_oplus'_in_unit_disc
  by presburger

(* ------------------------------------------------------------------------------------- *)

lift_definition e_gammma_factor :: "PoincareDisc \<Rightarrow> real" ("\<gamma>\<^sub>E") is gamma_factor
  done


lemma gamma_factor_oplus_e:
  shows "\<gamma>\<^sub>E (u \<oplus>\<^sub>E v) = \<gamma>\<^sub>E u * \<gamma>\<^sub>E v * (1 + u \<cdot>\<^sub>E v)"
  using gamma_factor_e_oplus' 
  by transfer blast

lemma m_left_id:
  shows "0\<^sub>E \<oplus>\<^sub>E u = u"
  apply transfer
  unfolding e_oplus'_def e_ozero'_def
  by (simp add: gamma_factor_def)
  
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

definition e_otimes' :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "e_otimes' r z = m_otimes' r z"

lift_definition e_otimes :: "real \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<otimes>\<^sub>E" 105) is e_otimes'
  using cmod_m_otimes' cmod_m_otimes'_k e_otimes'_def 
  by auto


lemma e_half:
  shows "(1/2) \<otimes>\<^sub>E u = m_half u"
  by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq m_half m_otimes.rep_eq)

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

lemma iso_ei_inner_help:
  fixes a b :: real
  shows "inner (a*x) (b*y) = (a*b)* inner x y"
  by fastforce

lemma iso_ei_inner_help2:
  shows "to_complex ((1 / 2) \<otimes>\<^sub>m u) = 
         (\<gamma> (to_complex u)) / (1 + \<gamma> (to_complex u)) * to_complex u"
  using m_half m_half.rep_eq m_half'_def
  by (simp add: scaleR_conv_of_real)
  
lemma iso_ei_inner_mo_help3:
  assumes "cmod v < 1"
  shows "(cmod (m_half' v))\<^sup>2 = (\<gamma> v / (1 + \<gamma> v))^2 * (norm v)^2"
  unfolding m_half'_def 
  using norm_square_gamma_half assms
  by (smt (verit) divide_pos_pos gamma_factor_positive norm_scaleR power_mult_distrib)


lemma iso_ei_inner_mo_help4:
  assumes "cmod u < 1" "cmod v < 1"
  shows "inner (m_half' u) (m_half' v) = (\<gamma> u / (1 + \<gamma> u)) * (\<gamma> v / (1 + \<gamma> v)) * (inner u v)"
  unfolding m_half'_def scaleR_conv_of_real
  by (metis inner_mult_left inner_mult_right mult.assoc)


lemma iso_ei_mo_inner_help6:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "(1 + 2 * inner (m_half' u) (m_half' v) + (cmod (m_half' v))\<^sup>2) *\<^sub>R (m_half' u) = 
        (2 * \<gamma> v / (1 + \<gamma> v) + 2 * \<gamma> v * \<gamma> u / ((1 + \<gamma> v) * (1 + \<gamma> u)) * inner u v) * (\<gamma> u / (1 + \<gamma> u)) * u"
proof-
  have *: "m_half' u = (\<gamma> u / (1 + \<gamma> u)) * u"
    by (simp add: m_half'_def scaleR_conv_of_real)
  
  have "1 + 2 * inner (m_half' u) (m_half' v) + (cmod (m_half' v))\<^sup>2 = 
        1 + 2 * (\<gamma> u / (1 + \<gamma> u) * (\<gamma> v / (1 + \<gamma> v)) * inner u v) + (\<gamma> v / (1 + \<gamma> v))\<^sup>2 * (cmod v)\<^sup>2"
    using iso_ei_inner_mo_help4 iso_ei_inner_mo_help3 assms
    by simp
  also have "\<dots> = (2 * \<gamma> v / (1 + \<gamma> v) + 2 * \<gamma> v * \<gamma> u / ((1 + \<gamma> v) * (1 + \<gamma> u)) * inner u v)"
    using iso_ei_mo_help6[OF assms]
    using assms(2) iso_ei_inner_mo_help3 m_half'_def by auto
  finally
  show ?thesis
    using *
    by (simp add: of_real_def)
qed

lemma iso_ei_mo_inner_help7_1:
  assumes "cmod u < 1"
  shows "(cmod (m_half' u))\<^sup>2 = (\<gamma> u - 1) / (1 + \<gamma> u)"
  using assms
  using m_half'_def norm_square_gamma_half
  by auto

lemma iso_ei_mo_inner_help7:
  fixes u v :: complex
  assumes "cmod u < 1"
  shows "(1 - (cmod (m_half' u))\<^sup>2) *\<^sub>R (m_half' v) = 
         2 * (\<gamma> v) / ((1 + \<gamma> v) *(1 + \<gamma> u)) * v"
  using iso_ei_mo_help4 iso_ei_mo_inner_help7_1 assms
  by (simp add: m_half'_def mult.assoc scaleR_conv_of_real)

lemma iso_ei_mo_inner_help8:
  assumes "cmod u < 1" "cmod v < 1"
  shows "1 + 2 * inner (m_half' u) (m_half' v) + (cmod (m_half' u))\<^sup>2 * (cmod (m_half' v))\<^sup>2 =
         2 * (\<gamma> u) * (\<gamma> v) * inner u v / ((1 + \<gamma> u) * (1 + \<gamma> v)) + 2 * (1 + (\<gamma> u)*(\<gamma> v)) / ((1 + \<gamma> u) * (1 + \<gamma> v))"
  using assms iso_ei_inner_mo_help4 iso_ei_mo_help8_1 iso_ei_mo_inner_help7_1
  by fastforce


lemma iso_ei_mo_help9:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "m_oplus'_full (m_half' u) (m_half' v) = 
         ((2*(\<gamma> v / (1 + \<gamma> v)) + (2*(\<gamma> v / (1 + \<gamma> v)) * (\<gamma> u / (1 + \<gamma> u)) * inner u v)) *
          (\<gamma> u / (1 + \<gamma> u)) * u + 2 * \<gamma> v / ((1 + \<gamma> v) * (1 + \<gamma> u)) * v) /
          (2 * (\<gamma> u) * (\<gamma> v) * inner u v / ((1 + \<gamma> v) * (1 + \<gamma> u)) + 2 * (1 + (\<gamma> u) * (\<gamma> v)) / ((1 + \<gamma> v) * (1 + \<gamma> u)))" (is "?lhs = ?rhs")
  using iso_ei_mo_inner_help8[OF assms]  iso_ei_mo_inner_help7[OF assms(1)] iso_ei_mo_inner_help6[OF assms]
  unfolding m_oplus'_full_def
  by (simp add: mult.commute)

lemma iso_ei_mo_help10:
  fixes u v :: complex
  assumes "cmod u < 1" "cmod v < 1"
  shows "m_half' (e_oplus' u v) = 
         \<gamma> u * \<gamma> v / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) * (u + (1 / \<gamma> u) * v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u)"
proof-
  have "m_half' (e_oplus' u v) = 
       \<gamma> u * \<gamma> v * (1 + inner u v) / (\<gamma> u * \<gamma> v * (1 + inner u v) + 1) *
       ((1 / (1 + inner u v)) * (u + (1 / \<gamma> u)*v + (\<gamma> u / (1 + \<gamma> u)) * inner u v * u))"
    unfolding m_half'_def
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
  shows "m_oplus'_full (m_half' u) (m_half' v) = 
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
  shows "m_oplus'_full (m_half' u) (m_half' v) =
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

lemma m_half':
  assumes "cmod u < 1"
  shows "m_otimes' (1 / 2) u = m_half' u"
  using assms m_half m_half.rep_eq[of "of_complex u"] m_otimes.rep_eq
  by (simp add: Moebius_gyrodom'.to_dom)

lemma iso_ei_mo_half:
  shows "(1/2) \<otimes>\<^sub>E (u \<oplus>\<^sub>E v) = ((1/2) \<otimes>\<^sub>m u \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>m v)"
proof transfer
  fix u v
  assume *: "cmod u < 1" "cmod v < 1"
  have "e_otimes' (1 / 2) (e_oplus' u v) = m_half' (e_oplus' u v)"
    using m_half'[of "e_oplus' u v"] *
    unfolding e_otimes'_def
    using e_oplus'_in_unit_disc 
    by blast
  moreover
  have "m_otimes' (1 / 2) u = m_half' u" "m_otimes' (1 / 2) v = m_half' v"
    using m_half' *
    by auto
  moreover
  have **: "cmod (m_half' u) < 1" "cmod (m_half' v) < 1"
    using *
    by (metis eq_onp_same_args m_half.rsp rel_fun_eq_onp_rel)+
  have "m_half' (e_oplus' u v) = m_oplus' (m_half' u) (m_half' v)"
    using * iso_ei_mo_help10[OF *] iso_ei_mo_help14[OF *]
    unfolding m_oplus'_full[OF **, symmetric]
    by simp
  ultimately
  show "e_otimes' (1 / 2) (e_oplus' u v) = m_oplus' (m_otimes' (1 / 2) u) (m_otimes' (1 / 2) v)"
    by simp
qed
 
lemma iso_mo_ei_two:
  shows " 2 \<otimes>\<^sub>m ( u \<oplus>\<^sub>m v) =  (2 \<otimes>\<^sub>E u \<oplus>\<^sub>E 2 \<otimes>\<^sub>E v)"
proof-
  have  "(1/2)  \<otimes>\<^sub>E (2 \<otimes>\<^sub>m ( u \<oplus>\<^sub>m v)) =  ( u \<oplus>\<^sub>m v) "
    proof -
      have "\<forall>r ra. (1::real) / ra * r = r / ra"
        by simp
      then show ?thesis
        by (smt (z3) Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom div_self e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq m_otimes_assoc)
    qed
    moreover have "(1/2)  \<otimes>\<^sub>E  (2 \<otimes>\<^sub>E u \<oplus>\<^sub>E 2 \<otimes>\<^sub>E v) = ((1/2) \<otimes>\<^sub>E (2 \<otimes>\<^sub>E u)  \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>E (2\<otimes>\<^sub>E v))"
      using e_otimes'_def e_otimes_def iso_ei_mo_half m_otimes_def by presburger
    moreover have "((1/2) \<otimes>\<^sub>E (2 \<otimes>\<^sub>E u)  \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>E (2\<otimes>\<^sub>E v)) =  ( u \<oplus>\<^sub>m v) "
    proof -
      have "(\<otimes>\<^sub>E) = (\<otimes>\<^sub>m)"
        using e_otimes'_def e_otimes_def m_otimes_def by presburger
      then show ?thesis
        by (smt (z3) Moebious_gyrovector_space.scale_1 div_self m_otimes_assoc times_divide_eq_left times_divide_eq_right)
    qed
    ultimately show ?thesis
      by (metis Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq field_sum_of_halves m_otimes.rep_eq m_otimes_distrib)
qed



definition e_gyr::"PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
    "e_gyr u v w = \<ominus>\<^sub>E(u\<oplus>\<^sub>Ev)\<oplus>\<^sub>E(u \<oplus>\<^sub>E(v \<oplus>\<^sub>E w))"

lemma e_minus_m_minus:
  shows "\<ominus>\<^sub>m a = \<ominus>\<^sub>E a"
  by (simp add: e_ominus'_def e_ominus_def m_ominus'_def m_ominus_def)


lemma e_gamma_minus_plus:
  shows "\<gamma> (Rep_PoincareDisc (\<ominus>\<^sub>E a)) = \<gamma> (Rep_PoincareDisc a)"
proof-
  have "norm (Rep_PoincareDisc (\<ominus>\<^sub>E a)) = norm (Rep_PoincareDisc a)"
    by (simp add: e_ominus'_def e_ominus.rep_eq)
  then show ?thesis 
    using \<open>cmod (Rep_PoincareDisc (\<ominus>\<^sub>E a)) = cmod (Rep_PoincareDisc a)\<close> \<gamma>_def by presburger
qed

lemma rep_abs_inv:
  fixes u::complex
  assumes "norm u <1"
  shows "Rep_PoincareDisc(Abs_PoincareDisc u) = u"
  by (simp add: Moebius_gyrodom'.to_dom assms)
 
lemma e_minus_negative:
  fixes a::"PoincareDisc"
  shows "((1/2) \<otimes>\<^sub>E (\<ominus>\<^sub>E a)) =\<ominus>\<^sub>E ((1/2) \<otimes>\<^sub>E a)"
proof-
  have "((1/2)\<otimes>\<^sub>E (\<ominus>\<^sub>E a)) = Abs_PoincareDisc (cor (\<gamma> (Rep_PoincareDisc (\<ominus>\<^sub>E a))) /
        (1+(\<gamma> (Rep_PoincareDisc (\<ominus>\<^sub>E a)))) * (Rep_PoincareDisc (\<ominus>\<^sub>E a)))"
    using half_times_gamma by blast
  moreover have "\<ominus>\<^sub>E ((1/2) \<otimes>\<^sub>E a) = \<ominus>\<^sub>E( Abs_PoincareDisc (cor (\<gamma> (Rep_PoincareDisc a)) /
        (1+(\<gamma> (Rep_PoincareDisc a))) * (Rep_PoincareDisc  a)))"
    using half_times_gamma by presburger
  moreover have "((1/2)\<otimes>\<^sub>E (\<ominus>\<^sub>E a)) = Abs_PoincareDisc (cor (\<gamma> (Rep_PoincareDisc (a))) /
        (1+(\<gamma> (Rep_PoincareDisc ( a)))) * -1 * (Rep_PoincareDisc (a)))"
    using e_gamma_minus_plus e_ominus'_def e_ominus.rep_eq half_times_gamma by force
  let ?iz = " (Rep_PoincareDisc
       (Abs_PoincareDisc((cor (\<gamma> (Rep_PoincareDisc a)) /
        (1+(\<gamma> (Rep_PoincareDisc a))) * (Rep_PoincareDisc  a)))))"
  let ?iz1 = "Abs_PoincareDisc ((cor (\<gamma> (Rep_PoincareDisc a)) /
        (1+(\<gamma> (Rep_PoincareDisc a))) * (Rep_PoincareDisc  a)))"
  have "\<ominus>\<^sub>E ((1/2) \<otimes>\<^sub>E a) =Abs_PoincareDisc (-1* Rep_PoincareDisc
       (Abs_PoincareDisc
         (cor (\<gamma> (Rep_PoincareDisc a)) /
          cor (1 + \<gamma> (Rep_PoincareDisc a)) *
          Rep_PoincareDisc a)))"
    using  e_ominus'_def[of ?iz] e_ominus.rep_eq[of ?iz1]
    by (metis Moebius_gyrodom'.of_dom calculation(2) mult_minus1)
  moreover have "(-1* Rep_PoincareDisc
       (Abs_PoincareDisc
         (cor (\<gamma> (Rep_PoincareDisc a)) /
          cor (1 + \<gamma> (Rep_PoincareDisc a)) *
          Rep_PoincareDisc a))) = (-1 * (cor (\<gamma> (Rep_PoincareDisc a)) /
          cor (1 + \<gamma> (Rep_PoincareDisc a)) *
          Rep_PoincareDisc a))"
  proof-
    have "norm (Rep_PoincareDisc a) <1"
      using Rep_PoincareDisc by blast
    moreover have "\<gamma> (Rep_PoincareDisc a) = 1/sqrt(1-(norm (Rep_PoincareDisc a))^2)"
      by (metis calculation \<gamma>_def mult_closed norm_power power2_eq_square)
    moreover have "norm ((cor (\<gamma> (Rep_PoincareDisc a)) /
          cor (1 + \<gamma> (Rep_PoincareDisc a)) *
          Rep_PoincareDisc a)) <1"
      by (smt (verit, best) calculation(1) calculation(2) divide_eq_1_iff \<gamma>_def less_divide_eq_1_pos mult_closed norm_divide norm_of_real real_sqrt_gt_zero zero_less_divide_1_iff)    
    ultimately show ?thesis 
      using rep_abs_inv by presburger
  qed
  ultimately show ?thesis
    by (simp add: \<open>(1 / 2) \<otimes>\<^sub>E \<ominus>\<^sub>E a = Abs_PoincareDisc (cor (\<gamma> (Rep_PoincareDisc a)) / cor (1 + \<gamma> (Rep_PoincareDisc a)) * - 1 * Rep_PoincareDisc a)\<close>)
qed


lemma e_gyr_m_gyr:
  shows "(1/2) \<otimes>\<^sub>E e_gyr u v w = m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E w) "
proof-
  have "(1/2) \<otimes>\<^sub>E e_gyr u v w = (1/2) \<otimes>\<^sub>E ( \<ominus>\<^sub>E(u\<oplus>\<^sub>Ev)\<oplus>\<^sub>E(u \<oplus>\<^sub>E(v \<oplus>\<^sub>E w)))"
    using e_gyr_def by auto
  moreover have " (1/2) \<otimes>\<^sub>E  (\<ominus>\<^sub>E(u\<oplus>\<^sub>Ev)\<oplus>\<^sub>E(u \<oplus>\<^sub>E(v \<oplus>\<^sub>E w)))= ((1/2) \<otimes>\<^sub>m (\<ominus>\<^sub>E(u\<oplus>\<^sub>Ev))) \<oplus>\<^sub>m 
        ((1/2) \<otimes>\<^sub>m (u \<oplus>\<^sub>E (v \<oplus>\<^sub>E w)))"
    using iso_ei_mo_half
    by auto
  moreover have "((1/2) \<otimes>\<^sub>m (\<ominus>\<^sub>E(u\<oplus>\<^sub>Ev))) = \<ominus>\<^sub>m ((1/2) \<otimes>\<^sub>m (u\<oplus>\<^sub>Ev))"
    by (metis Einstein.m_left_id Moebius_gyrodom'.of_dom Moebius_gyrogroup.gyro_left_id Moebius_gyrogroup.gyro_left_inv add.inverse_neutral division_ring_divide_zero e_minus_m_minus e_minus_negative e_ominus'_def e_ominus.rep_eq e_ozero'_def e_ozero.rep_eq half_times_gamma iso_ei_mo_half m_otimes'_def m_otimes.rep_eq times_divide_eq_right)
  moreover have " \<ominus>\<^sub>m ((1/2) \<otimes>\<^sub>m (u\<oplus>\<^sub>Ev)) = \<ominus>\<^sub>m ((1/2) \<otimes>\<^sub>m u  \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>m v)"
    by (metis Einstein.m_left_id Moebius_gyrodom'.of_dom Moebius_gyrogroup.gyro_left_id e_ozero'_def e_ozero.rep_eq iso_ei_mo_half m_otimes'_def m_otimes.rep_eq m_ozero'_def m_ozero_def)
  moreover have " ((1/2) \<otimes>\<^sub>m (u \<oplus>\<^sub>E (v \<oplus>\<^sub>E w))) = ((1/2) \<otimes>\<^sub>m u  \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>m (v \<oplus>\<^sub>E w))"
    by (metis Einstein.m_left_id Moebius_gyrodom'.of_dom Moebius_gyrogroup.gyro_left_id e_ozero'_def e_ozero.rep_eq iso_ei_mo_half m_otimes'_def m_otimes.rep_eq m_ozero'_def m_ozero_def)
  moreover have "((1/2) \<otimes>\<^sub>m u  \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>m (v \<oplus>\<^sub>E w)) = ((1/2) \<otimes>\<^sub>m u  \<oplus>\<^sub>m ((1/2) \<otimes>\<^sub>m v  \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>m w))"
    by (metis Einstein.m_left_id Moebius_gyrodom'.of_dom Moebius_gyrogroup.gyro_left_id e_ozero'_def e_ozero.rep_eq iso_ei_mo_half m_otimes'_def m_otimes.rep_eq m_ozero'_def m_ozero_def)
  ultimately show ?thesis 
    by (metis Moebius_gyrogroup.gyro_left_cancel' Moebius_gyrogroup.gyro_translation_2a Rep_PoincareDisc_inject e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq)
qed


lemma m_gyr_e_gyr:
  shows "2 \<otimes>\<^sub>E m_gyr u v w = e_gyr (2 \<otimes>\<^sub>E u) (2 \<otimes>\<^sub>E v) (2 \<otimes>\<^sub>E w) "
  by (smt (z3) Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom div_self divide_divide_eq_right divide_numeral_1 e_gyr_m_gyr e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq m_otimes_assoc times_divide_eq_left)

lemma zeros_equal:
  shows "0\<^sub>E = 0\<^sub>m"
  using e_ozero'_def e_ozero_def m_ozero'_def m_ozero_def by auto
lemma e_inv:
  shows "\<ominus>\<^sub>E a \<oplus>\<^sub>E a = 0\<^sub>E"
proof-
  have "(1/2) \<otimes>\<^sub>E (\<ominus>\<^sub>E a \<oplus>\<^sub>E a) = ((1/2) \<otimes>\<^sub>E ( \<ominus>\<^sub>E a)) \<oplus>\<^sub>m ((1/2)\<otimes>\<^sub>E a)"
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_ei_mo_half m_otimes.rep_eq)
  moreover have "((1/2) \<otimes>\<^sub>E ( \<ominus>\<^sub>E a)) \<oplus>\<^sub>m ((1/2)\<otimes>\<^sub>E a) =  \<ominus>\<^sub>E( ((1/2)\<otimes>\<^sub>E a)) \<oplus>\<^sub>m ((1/2)\<otimes>\<^sub>E a) "
    using e_minus_negative by auto
  moreover have " \<ominus>\<^sub>E( ((1/2)\<otimes>\<^sub>E a)) \<oplus>\<^sub>m ((1/2)\<otimes>\<^sub>E a) = 0\<^sub>m"
    using Moebius_gyrogroup.gyro_left_inv e_minus_m_minus by auto
  ultimately show ?thesis
    using zeros_equal
    by (metis (no_types, opaque_lifting) MobiusGyroGroup.m_left_id Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom divide_divide_eq_right divide_eq_eq_numeral1(1) e_otimes'_def e_otimes.rep_eq eq_divide_eq_1 m_otimes.rep_eq m_otimes_distrib mult_2 zero_neq_numeral)
qed

lemma e_gyro_left_assoc:
  shows "a \<oplus>\<^sub>E (b \<oplus>\<^sub>E z) = (a \<oplus>\<^sub>E b) \<oplus>\<^sub>E e_gyr a b z"
proof-
  have "(1/2) \<otimes>\<^sub>E (a \<oplus>\<^sub>E (b \<oplus>\<^sub>E z)) = ((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m((1/2) \<otimes>\<^sub>E (b \<oplus>\<^sub>E z) )"
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_ei_mo_half m_otimes.rep_eq)
  moreover have " ((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m((1/2) \<otimes>\<^sub>E (b \<oplus>\<^sub>E z)) = ((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m((1/2) \<otimes>\<^sub>E b \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>E z)"
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_ei_mo_half m_otimes.rep_eq)
  moreover have "((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m((1/2) \<otimes>\<^sub>E b \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>E z) = ((1/2) \<otimes>\<^sub>E a \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>E b) \<oplus>\<^sub>m m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>E b) ((1/2) \<otimes>\<^sub>E z)"
    using m_gyro_left_assoc by blast
  moreover have "(1/2)  \<otimes>\<^sub>E ((a \<oplus>\<^sub>E b) \<oplus>\<^sub>E e_gyr a b z) = (1/2)  \<otimes>\<^sub>E (a \<oplus>\<^sub>E b) \<oplus>\<^sub>m (1/2)  \<otimes>\<^sub>E e_gyr a b z "
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_ei_mo_half m_otimes.rep_eq)
  moreover have "(1/2)  \<otimes>\<^sub>E (a \<oplus>\<^sub>E b) \<oplus>\<^sub>m (1/2)  \<otimes>\<^sub>E e_gyr a b z = ((1/2)  \<otimes>\<^sub>E a  \<oplus>\<^sub>m (1/2)  \<otimes>\<^sub>E b)  \<oplus>\<^sub>m  m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>E b) ((1/2) \<otimes>\<^sub>E z)"
      by (metis Moebius_gyrodom'.of_dom e_gyr_m_gyr e_otimes'_def e_otimes.rep_eq iso_ei_mo_half m_otimes.rep_eq)
    moreover have "(1/2) \<otimes>\<^sub>E (a \<oplus>\<^sub>E (b \<oplus>\<^sub>E z)) = (1/2)  \<otimes>\<^sub>E ((a \<oplus>\<^sub>E b) \<oplus>\<^sub>E e_gyr a b z)"
      using calculation(1) calculation(2) calculation(3) calculation(4) calculation(5) by presburger
    ultimately show ?thesis 
      by (metis (no_types, opaque_lifting) Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom divide_eq_eq_numeral1(1) e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq m_otimes_distrib mult.commute mult_2 zero_neq_numeral)
  qed

lemma e_gyr_not_degenerate:
  shows "\<exists> z1 z2. e_gyr a b z1 \<noteq> e_gyr a b z2"
proof-
  obtain z1 z2 :: PoincareDisc where "z1 \<noteq> z2"
    using poincare_disc_two_elems
    by blast
  hence "m_gyr a b z1 \<noteq> m_gyr a b z2"
    by (metis m_gyr_inv)
  hence "2 \<otimes>\<^sub>E m_gyr a b z1 \<noteq> 2 \<otimes>\<^sub>E m_gyr a b z2"
    by (metis (no_types, opaque_lifting) Moebious_gyrovector_space.scale_1 Moebius_gyrocommutative_gyrogroup.gyro_translate_commute divide_eq_eq_numeral1(1) iso_mo_ei_two m_gyro_commute m_otimes_assoc rel_simps(76))
  thus ?thesis
    by (metis (no_types, opaque_lifting) Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom e_gyr_m_gyr e_otimes'_def e_otimes.rep_eq field_sum_of_halves m_gyr_inv m_otimes.rep_eq m_otimes_assoc mult_2)
qed


lemma e_gyro_commute:
  shows  "a \<oplus>\<^sub>E b = e_gyr a b (b \<oplus>\<^sub>E a)"
proof-
  have "(1/2) \<otimes>\<^sub>E (a \<oplus>\<^sub>E b) = (1/2) \<otimes>\<^sub>E a  \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>E b"
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_ei_mo_half m_otimes.rep_eq)
  moreover have "(1/2) \<otimes>\<^sub>E a  \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>E b = m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>E b) ((1/2) \<otimes>\<^sub>E b  \<oplus>\<^sub>m  (1/2) \<otimes>\<^sub>E a)  "
    using m_gyro_commute by auto
  moreover have "(1/2) \<otimes>\<^sub>E ( e_gyr a b (b \<oplus>\<^sub>E a)) = m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>E b) ((1/2) \<otimes>\<^sub>E (b \<oplus>\<^sub>E a))"
    using e_gyr_m_gyr by auto
  moreover have "m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>E b) ((1/2) \<otimes>\<^sub>E (b \<oplus>\<^sub>E a)) = m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>E b) ((1/2) \<otimes>\<^sub>E b  \<oplus>\<^sub>m  (1/2) \<otimes>\<^sub>E a)"
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_ei_mo_half m_otimes.rep_eq)
  moreover have "(1/2) \<otimes>\<^sub>E (a \<oplus>\<^sub>E b)  = (1/2) \<otimes>\<^sub>E ( e_gyr a b (b \<oplus>\<^sub>E a)) "
    using calculation(1) calculation(2) calculation(3) calculation(4) by presburger
  ultimately show ?thesis 
    by (metis (no_types, opaque_lifting) Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom div_self divide_divide_eq_left e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq m_otimes_distrib mult_2 nonzero_mult_divide_mult_cancel_right2 times_divide_eq_right zero_neq_numeral)
qed

lemma m_gyr_left_loop_z:
  shows "\<forall>z. m_gyr a b z = m_gyr (a \<oplus>\<^sub>m b) b z"
  using m_gyr_left_loop by auto

lemma e_gyr_left_loop_z:
  shows "\<forall>z. e_gyr a b z = e_gyr (a \<oplus>\<^sub>E b) b z"
(* shows "2 \<otimes>\<^sub>E m_gyr u v w = e_gyr (2 \<otimes>\<^sub>E u) (2 \<otimes>\<^sub>E v) (2 \<otimes>\<^sub>E w) "*)
proof-
  have "\<forall>z. m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>Eb) z = m_gyr (((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m ((1/2) \<otimes>\<^sub>E b)) ((1/2) \<otimes>\<^sub>E b) z"
    using m_gyr_left_loop_z by auto
 moreover have "\<forall>z. 2  \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>Eb) z =2  \<otimes>\<^sub>E m_gyr (((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m ((1/2) \<otimes>\<^sub>E b)) ((1/2) \<otimes>\<^sub>E b) z"
   by (simp add: calculation)
  moreover have "\<forall>z. 2  \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E a) ((1/2) \<otimes>\<^sub>Eb) z = e_gyr (2 \<otimes>\<^sub>E((1/2) \<otimes>\<^sub>E a)) (2 \<otimes>\<^sub>E((1/2) \<otimes>\<^sub>E b)) ((2 \<otimes>\<^sub>E z))"
    using m_gyr_e_gyr by auto
  moreover have "\<forall>z. e_gyr (2 \<otimes>\<^sub>E((1/2) \<otimes>\<^sub>E a)) (2 \<otimes>\<^sub>E((1/2) \<otimes>\<^sub>E b)) ((2 \<otimes>\<^sub>E z)) =  e_gyr a b ((2 \<otimes>\<^sub>E z))"
    by (smt (verit, ccfv_SIG) Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom div_self e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq m_otimes_assoc mult.commute times_divide_eq_left)
  moreover have "\<forall>z. 2 \<otimes>\<^sub>E m_gyr (((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m ((1/2) \<otimes>\<^sub>E b)) ((1/2) \<otimes>\<^sub>E b) z = e_gyr (2 \<otimes>\<^sub>E (((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m ((1/2) \<otimes>\<^sub>E b))) (2 \<otimes>\<^sub>E  ((1/2) \<otimes>\<^sub>E b) ) (2 \<otimes>\<^sub>E z)"
    using m_gyr_e_gyr by blast
  moreover have "\<forall>z.  e_gyr (2 \<otimes>\<^sub>E (((1/2) \<otimes>\<^sub>E a) \<oplus>\<^sub>m ((1/2) \<otimes>\<^sub>E b))) (2 \<otimes>\<^sub>E  ((1/2) \<otimes>\<^sub>E b) ) (2 \<otimes>\<^sub>E z) =
      e_gyr (2 \<otimes>\<^sub>E (((1/2) \<otimes>\<^sub>E a))  \<oplus>\<^sub>E  2 \<otimes>\<^sub>E (((1/2) \<otimes>\<^sub>E b)))  (2 \<otimes>\<^sub>E  ((1/2) \<otimes>\<^sub>E b) ) (2 \<otimes>\<^sub>E z) "
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_mo_ei_two m_otimes.rep_eq)
  moreover have "\<forall>z.  e_gyr (2 \<otimes>\<^sub>E (((1/2) \<otimes>\<^sub>E a))  \<oplus>\<^sub>E  2 \<otimes>\<^sub>E (((1/2) \<otimes>\<^sub>E b)))  (2 \<otimes>\<^sub>E  ((1/2) \<otimes>\<^sub>E b) ) (2 \<otimes>\<^sub>E z) =
     e_gyr (a  \<oplus>\<^sub>E  b)   b  (2 \<otimes>\<^sub>E z)"
  proof -
    { fix pp :: PoincareDisc
      have "(\<otimes>\<^sub>E) = (\<otimes>\<^sub>m)"
        using e_otimes'_def e_otimes_def m_otimes_def by presburger
      then have "e_gyr (2 \<otimes>\<^sub>E ((1 / 2) \<otimes>\<^sub>E a) \<oplus>\<^sub>E 2 \<otimes>\<^sub>E ((1 / 2) \<otimes>\<^sub>E b)) (2 \<otimes>\<^sub>E ((1 / 2) \<otimes>\<^sub>E b)) (2 \<otimes>\<^sub>E pp) = e_gyr (a \<oplus>\<^sub>E b) b (2 \<otimes>\<^sub>E pp)"
        by (metis Moebious_gyrovector_space.scale_1 field_sum_of_halves m_otimes_assoc mult_2) }
    then show ?thesis
      by blast
  qed
  ultimately show ?thesis
    by (metis Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq field_sum_of_halves m_otimes.rep_eq m_otimes_assoc mult_2)
qed

lemma e_gyr_left_loop:
  shows "e_gyr a b = e_gyr (a \<oplus>\<^sub>E b) b"
  using e_gyr_left_loop_z by presburger

lemma e_gyr_distrib:
  shows "e_gyr a b (a' \<oplus>\<^sub>E b') = e_gyr a b a' \<oplus>\<^sub>E e_gyr a b b'"
proof-
  have "m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b) ((1/2) \<otimes>\<^sub>m a'  \<oplus>\<^sub>m (1/2)\<otimes>\<^sub>m b') =
      m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m a') \<oplus>\<^sub>m
      m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m b') "
    using Moebius_gyrogroup.gyr_distrib by blast
  moreover have "2  \<otimes>\<^sub>m m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b) ((1/2) \<otimes>\<^sub>m a'  \<oplus>\<^sub>m (1/2)\<otimes>\<^sub>m b') =
     2 \<otimes>\<^sub>m( m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m a') \<oplus>\<^sub>m
      m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m b'))"
    using calculation by presburger
  moreover have "  2 \<otimes>\<^sub>m( m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m a') \<oplus>\<^sub>m
      m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m b'))=
       2 \<otimes>\<^sub>m( m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m a')) \<oplus>\<^sub>E 
       2 \<otimes>\<^sub>m( m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m b'))"
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_mo_ei_two m_otimes.rep_eq)
  moreover have "2  \<otimes>\<^sub>m m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b) ((1/2) \<otimes>\<^sub>m a'  \<oplus>\<^sub>m (1/2)\<otimes>\<^sub>m b')
    = e_gyr (2  \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a))  (2  \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m b))  (2  \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a'  \<oplus>\<^sub>m (1/2)\<otimes>\<^sub>m b'))"
    using e_otimes'_def e_otimes_def m_gyr_e_gyr m_otimes_def by presburger
  moreover have "e_gyr (2  \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a))  (2  \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m b))  (2  \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a'  \<oplus>\<^sub>m (1/2)\<otimes>\<^sub>m b'))
    = e_gyr a b (2  \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a'  \<oplus>\<^sub>m (1/2)\<otimes>\<^sub>m b'))"
    by (metis Moebious_gyrovector_space.scale_1 field_sum_of_halves m_otimes_assoc mult_2)
  moreover have "e_gyr a b (2  \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a'  \<oplus>\<^sub>m (1/2)\<otimes>\<^sub>m b')) = e_gyr a b ( a'  \<oplus>\<^sub>E b')"
  proof -
    have "(\<otimes>\<^sub>m) = (\<otimes>\<^sub>E)"
      using e_otimes'_def e_otimes_def m_otimes_def by presburger
    then show ?thesis
      by (metis (no_types) Moebious_gyrovector_space.scale_1 field_sum_of_halves iso_ei_mo_half m_otimes_assoc mult.commute mult_2_right)
  qed
  moreover have "2 \<otimes>\<^sub>m( m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m a')) =
        e_gyr (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a)) (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m b)) (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a'))"
    using  m_gyr_e_gyr
    by (simp add: e_otimes'_def e_otimes_def m_otimes_def)
  moreover have "  e_gyr (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a)) (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m b)) (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a')) =
    e_gyr a b a'"
    by (metis (mono_tags, opaque_lifting) Moebious_gyrovector_space.scale_1 field_sum_of_halves m_otimes_assoc mult.commute mult_2_right)
   moreover have "2 \<otimes>\<^sub>m( m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m b')) =
        e_gyr (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a)) (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m b)) (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m b'))"
    using  m_gyr_e_gyr
    by (simp add: e_otimes'_def e_otimes_def m_otimes_def)
  moreover have "  e_gyr (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m a)) (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m b)) (2 \<otimes>\<^sub>m ((1/2) \<otimes>\<^sub>m b')) =
    e_gyr a b b'"
    by (metis (mono_tags, opaque_lifting) Moebious_gyrovector_space.scale_1 field_sum_of_halves m_otimes_assoc mult.commute mult_2_right)
  moreover have "2 \<otimes>\<^sub>m( m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m a') \<oplus>\<^sub>m
      m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b)  ((1/2) \<otimes>\<^sub>m b')) = e_gyr a b a' \<oplus>\<^sub>E e_gyr a b b'"
    by (simp add: calculation(10) calculation(3) calculation(7) calculation(8) calculation(9))
  moreover have "2  \<otimes>\<^sub>m m_gyr ((1/2) \<otimes>\<^sub>m a) ((1/2) \<otimes>\<^sub>m b) ((1/2) \<otimes>\<^sub>m a'  \<oplus>\<^sub>m (1/2)\<otimes>\<^sub>m b') = 
    e_gyr a b (a' \<oplus>\<^sub>E b')"
    using calculation(4) calculation(5) calculation(6) by presburger
  ultimately show ?thesis
      by presburger
  qed

lemma e_gyr_inv:
  "e_gyr a b (e_gyr b a z) = z"
  by (metis Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom e_gyr_m_gyr e_otimes'_def e_otimes.rep_eq field_sum_of_halves m_gyr_inv m_otimes.rep_eq m_otimes_assoc mult_2)


lemma e_gyr_bij:
  shows "bij (e_gyr a b)"
  by (metis bijI e_gyr_inv inj_def surjI)
  

interpretation Einstein_gyrogroup: gyrogroup e_ozero e_oplus e_ominus e_gyr
proof
  fix a
  show "0\<^sub>E \<oplus>\<^sub>E a = a"
    by (simp add: Einstein.m_left_id)
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


lemma iso_ei_mo:
  shows " u \<oplus>\<^sub>E v = 2 \<otimes>\<^sub>m ((1/2)\<otimes>\<^sub>m u \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>m v)"
  by (metis Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom div_self half_times_gamma iso_ei_inner_help2 iso_ei_mo_half m_otimes_assoc mult.commute times_divide_eq_right zero_neq_numeral)

lift_definition e_norm :: "PoincareDisc \<Rightarrow> real"  ("\<llangle>_\<rrangle>\<^sub>E" [100] 100) is m_norm'
  done

lemma e_gyr_m_gyr2:
  shows "e_gyr u v w = 2 \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E w) "
  by (smt (verit) Moebious_gyrovector_space.scale_1 Moebius_gyrodom'.of_dom div_by_1 div_self divide_divide_eq_right e_gyr_m_gyr e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq m_otimes_assoc times_divide_eq_right)

lemma two_times_gamma_factor:
  shows "2 \<otimes>\<^sub>E u = Abs_PoincareDisc (cor(2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2 -1) * (Rep_PoincareDisc u))"
proof-
  have "(norm (Rep_PoincareDisc u)) =0 \<or> (norm (Rep_PoincareDisc u))\<noteq>0"
    by meson
  moreover {
    assume "(norm (Rep_PoincareDisc u)) =0"
    then have ?thesis 
      by (simp add: e_otimes'_def e_otimes_def m_otimes'_def)
  }
  moreover {
    assume "(norm (Rep_PoincareDisc u)) \<noteq>0"
    then have ?thesis 
    proof-
      let ?iz1 = "(Rep_PoincareDisc u)"
      let ?iz2 = "(2::real)"
      have "(Rep_PoincareDisc u)\<noteq>0"
        using \<open>cmod (Rep_PoincareDisc u) \<noteq> 0\<close> by auto
      moreover have *: "(2::real)\<noteq>0"
        by auto

      moreover have "m_otimes' 2 (Rep_PoincareDisc u) =
     cor (m_otimes'_k 2 (Rep_PoincareDisc u)) *
          (Rep_PoincareDisc u / cor (cmod (Rep_PoincareDisc u)))"
        using calculation(1) m_otimes'_def by presburger
      moreover have "2 \<otimes>\<^sub>E u =Abs_PoincareDisc (( ((1 + cmod (Rep_PoincareDisc u)) powr 2 - (1 - cmod (Rep_PoincareDisc u)) powr 2) /
                     ((1 + cmod (Rep_PoincareDisc u)) powr 2 + (1 - cmod (Rep_PoincareDisc u)) powr 2))  *   (Rep_PoincareDisc u / cor (cmod (Rep_PoincareDisc u))))"
        by (simp add: calculation(3) e_otimes'_def e_otimes_def m_otimes'_k_def)
        
      moreover have "(1 + cmod (Rep_PoincareDisc u)) powr 2 = (1+cmod (Rep_PoincareDisc u))^2"
        by simp
      moreover have "(1 - cmod (Rep_PoincareDisc u)) powr 2 = (1-cmod (Rep_PoincareDisc u))^2"
        using Rep_PoincareDisc less_eq_real_def by force

      moreover have "(1+cmod (Rep_PoincareDisc u))^2 - (1-cmod (Rep_PoincareDisc u))^2
      =  4*cmod(Rep_PoincareDisc u)"
        by (smt (verit, ccfv_SIG) bin_square help1 power2_diff)
      moreover have "(1+cmod (Rep_PoincareDisc u))^2 + (1-cmod (Rep_PoincareDisc u))^2
      = 2 + 2*cmod(Rep_PoincareDisc u)^2"
        by (simp add: power2_diff power2_sum)

      moreover have " 4*cmod(Rep_PoincareDisc u) / (2 + 2*cmod(Rep_PoincareDisc u)^2)
        * (Rep_PoincareDisc u) / (cmod (Rep_PoincareDisc u)) =
        2*(Rep_PoincareDisc u)/(1+cmod(Rep_PoincareDisc u)^2)"
      proof-
        have "cmod (Rep_PoincareDisc u) \<noteq>0"
          using \<open>cmod (Rep_PoincareDisc u) \<noteq> 0\<close> by auto
        moreover have "2+2*cmod(Rep_PoincareDisc u)^2 = 2*(1+cmod(Rep_PoincareDisc u)^2)"
          by auto
        moreover have "4*cmod(Rep_PoincareDisc u) = 2 * (2*cmod(Rep_PoincareDisc u))"
          by simp
        moreover have "4*cmod(Rep_PoincareDisc u) / (2 + 2*cmod(Rep_PoincareDisc u)^2) =
        (2*cmod(Rep_PoincareDisc u))/ (1+cmod(Rep_PoincareDisc u)^2)"
          by (metis "*" calculation(2) calculation(3) nonzero_mult_divide_mult_cancel_left)
        ultimately show ?thesis
          by (simp add: mult.commute power2_eq_square)
      qed

      moreover have "\<gamma> (Rep_PoincareDisc u)^2 = 1/(1-cmod(Rep_PoincareDisc u)^2)"
        by (smt (verit, ccfv_SIG) Rep_PoincareDisc div_by_1 divide_divide_eq_right divide_eq_0_iff \<gamma>_def e_help1 mem_Collect_eq one_power2 power2_eq_square times_divide_eq_right)
      moreover have "(2*(\<gamma> (Rep_PoincareDisc u))^2)
/(2*(\<gamma> (Rep_PoincareDisc u))^2 -1) =  2/(1+ cmod(Rep_PoincareDisc u)^2)"
      proof-
        have "(2*(\<gamma> (Rep_PoincareDisc u))^2)
/(2*(\<gamma> (Rep_PoincareDisc u))^2 -1) = 2*(1/(1-cmod(Rep_PoincareDisc u)^2))/(2*(1/(1-cmod(Rep_PoincareDisc u)^2))-1)"
          using calculation(10) by presburger
        moreover have "2*(1/(1-cmod(Rep_PoincareDisc u)^2))/(2*(1/(1-cmod(Rep_PoincareDisc u)^2))-1) =
        (2/(1-cmod(Rep_PoincareDisc u)^2))/((2-(1-cmod(Rep_PoincareDisc u)^2))/(1-cmod(Rep_PoincareDisc u)^2))"
        proof-
          have "1-cmod(Rep_PoincareDisc u)^2 \<noteq>0"
            by (metis Rep_PoincareDisc cmod_def cmod_power2 eq_iff_diff_eq_0 less_numeral_extra(4) mem_Collect_eq real_norm_def real_sqrt_abs square_norm_one)
          then show ?thesis 
            by (smt (verit, ccfv_threshold) add_divide_distrib diff_divide_distrib divide_divide_eq_right divide_self_if eq_divide_eq mult_eq_0_iff times_divide_times_eq)
        qed
        moreover have "1-cmod(Rep_PoincareDisc u)^2 \<noteq>0"
            by (metis Rep_PoincareDisc cmod_def cmod_power2 eq_iff_diff_eq_0 less_numeral_extra(4) mem_Collect_eq real_norm_def real_sqrt_abs square_norm_one)
        ultimately show ?thesis 
          by (smt (verit, best) divide_divide_eq_right nonzero_eq_divide_eq)     
      qed
      ultimately show ?thesis 
        by (metis (no_types, lifting) of_real_1 of_real_add of_real_divide one_add_one times_divide_eq_left times_divide_eq_right)
    qed
  }
  ultimately show ?thesis by blast
qed


lemma helpic0:
  fixes a::real
  fixes b::real
  fixes c::complex
  fixes d::complex
  shows "inner (a*c) (b*d) = (a*b) * inner c d"
  by (simp add: inner_mult_left inner_mult_right)

lemma helpic1:
  fixes a::real
  fixes b::real
  fixes c::complex
  fixes d::complex
  assumes "norm c <1" "norm d < 1"
  "norm (a*c) < 1" "norm (b*d)<1"
shows "inner (a*c) (b*d) = (a*b) * inner c d"
  using helpic0 by blast


lemma einstein_gyroauto_help1:
  fixes a::real
  fixes b::real
  fixes u::complex
  fixes v::complex
  assumes "norm (a*u) < 1" "norm (b*v)<1"
    "norm u<1" "norm v <1"
  shows "(Abs_PoincareDisc (a*u)) \<cdot>\<^sub>E (Abs_PoincareDisc (b*v)) =
 (a*b) * ((Abs_PoincareDisc  u) \<cdot>\<^sub>E (Abs_PoincareDisc v))"
  by (simp add: Moebius_gyrodom'.to_dom assms(1) assms(2) assms(3) assms(4) e_inner'_def e_inner.rep_eq helpic0)



lemma einstain_gyroauto_help2:
  assumes "norm (Rep_PoincareDisc u) <1"
  shows "norm (cor ((2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2-1)) * (Rep_PoincareDisc u)) <1"
proof-
  have "norm (cor ((2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2-1)) * (Rep_PoincareDisc u))
  = abs((2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2-1))* (norm (Rep_PoincareDisc u))"
    by (metis norm_mult norm_of_real)
  moreover have "2*(\<gamma> (Rep_PoincareDisc u))^2-1 \<ge>1"
  proof-
    have "\<gamma> (Rep_PoincareDisc u)^2 = 1/(1-norm (Rep_PoincareDisc u)^2)"
      by (simp add: assms e_help1)
    moreover have "1-norm (Rep_PoincareDisc u)^2 \<le> 1"
      by auto
    moreover have "1/(1-norm (Rep_PoincareDisc u)^2)\<ge>1"
      by (smt (verit, ccfv_SIG) assms e_gamma_norm_connection le_divide_eq_1 zero_le_power2)
    ultimately show ?thesis 
      by linarith       
  qed
  moreover have "\<gamma> (Rep_PoincareDisc u) \<ge> 0"
    using assms \<gamma>_def gamma_factor_def gamma_factor_positive_always by auto
  moreover  have "norm (cor ((2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2-1)) * (Rep_PoincareDisc u))
  = ((2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2-1))* (norm (Rep_PoincareDisc u))"
    using calculation(1) calculation(2) by auto
  moreover have  "\<gamma> (Rep_PoincareDisc u)^2 = 1/(1-norm (Rep_PoincareDisc u)^2)"
       by (simp add: assms e_help1)
  moreover have "((2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2-1)) =
    (2 * (1/(1-norm (Rep_PoincareDisc u)^2)))/(2*(1/(1-norm (Rep_PoincareDisc u)^2)) -1)"
    using calculation(5) by presburger
  moreover have "  (2 * (1/(1-norm (Rep_PoincareDisc u)^2)))/(2*(1/(1-norm (Rep_PoincareDisc u)^2)) -1) =
    2 / (2-(1-norm(Rep_PoincareDisc u)^2))"
  proof-
    have "1-norm (Rep_PoincareDisc u)^2 \<noteq>0"
      using assms real_sqrt_unique by fastforce
    then show ?thesis
    proof -
      have "\<forall>r. (1::real) / (1 / r) = r"
        by simp
      then have "2 / ((2 * (1 / (1 - (cmod (Rep_PoincareDisc u))\<^sup>2)) - 1) / (1 / (1 - (cmod (Rep_PoincareDisc u))\<^sup>2))) = 2 / (2 - (1 - (cmod (Rep_PoincareDisc u))\<^sup>2))"
        by (metis (full_types) \<open>1 - (cmod (Rep_PoincareDisc u))\<^sup>2 \<noteq> 0\<close> diff_divide_eq_iff zero_eq_1_divide_iff)
      then show ?thesis
        by (metis (no_types) divide_divide_eq_right)
    qed
  qed

  moreover have "    2 / (2-(1-norm(Rep_PoincareDisc u)^2)) = 2/(1+norm (Rep_PoincareDisc u)^2)"
    by simp
  moreover have "   ((2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2-1))* (norm (Rep_PoincareDisc u)) =
   (2/ (1+ norm (Rep_PoincareDisc u)^2)) * norm (Rep_PoincareDisc u)"
    using calculation(6) calculation(7) by force

  moreover have "  (2/ (1+ norm (Rep_PoincareDisc u)^2)) * norm (Rep_PoincareDisc u) < 1"
  proof-
    have " (2/ (1+ norm (Rep_PoincareDisc u)^2)) * norm (Rep_PoincareDisc u) = (2*norm (Rep_PoincareDisc u))/
      (1+norm (Rep_PoincareDisc u)^2)"
      using times_divide_eq_left by blast
    moreover have "(1-norm(Rep_PoincareDisc u))^2>0"
      using assms by auto
    moreover have "(1-norm(Rep_PoincareDisc u))^2 = 1+norm(Rep_PoincareDisc u)^2 -  2*norm (Rep_PoincareDisc u)"
      by (simp add: power2_diff)
    moreover have "1+norm(Rep_PoincareDisc u)^2 > 2*norm (Rep_PoincareDisc u)"
      using calculation(2) calculation(3) by force
    ultimately show ?thesis
      by (smt (verit, best) divide_less_eq_1_pos power2_less_0)
  qed

  moreover have "norm (cor ((2*(\<gamma> (Rep_PoincareDisc u))^2)/(2*(\<gamma> (Rep_PoincareDisc u))^2-1)) * (Rep_PoincareDisc u)) =
     (2/ (1+ norm (Rep_PoincareDisc u)^2)) * norm (Rep_PoincareDisc u)"
    using calculation(4) calculation(9) by presburger
  ultimately show ?thesis 
    by presburger
qed

lemma einstein_gyroauto_help3:
  shows  "2*( 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))/(2*( 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1)
    = (1+\<gamma> (Rep_PoincareDisc a))/(\<gamma> (Rep_PoincareDisc a))"
      proof-
        have " (1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2) \<noteq>0"
          by (metis add.commute add_0 add_right_cancel diff_add_cancel eq_divide_eq_1 iso_ei_inner_mo_help3 iso_ei_mo_inner_help7_1 real_average_minus_second zero_neq_one)
        moreover have **:"1/((1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))\<noteq>0"
          using calculation by auto
        moreover have "2*1/((1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1 =
        1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2) *(2-((1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2)))"
          by (smt (verit, del_insts) calculation(1) diff_divide_distrib divide_self nonzero_mult_div_cancel_left one_add_one times_divide_eq_left)
        moreover have "(2-((1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))) =
          1+ ((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2"
          by fastforce

        moreover have " ((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2 =
      ((\<gamma> (Rep_PoincareDisc a))-1)/(1+(\<gamma> (Rep_PoincareDisc a)))"
          using iso_ei_inner_mo_help3 iso_ei_mo_inner_help7_1 by presburger

        moreover have "1+ ((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2=
      2*(\<gamma> (Rep_PoincareDisc a))/(1+(\<gamma> (Rep_PoincareDisc a))) "
          using Rep_PoincareDisc calculation(5) iso_ei_mo_help3 by auto

        
        moreover have "2*( 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))/(2*( 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1) =
              2*(1/((1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2)))/( 2*(\<gamma> (Rep_PoincareDisc a))/(1+(\<gamma> (Rep_PoincareDisc a))) *(1/((1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))))"
          using calculation(3) calculation(6) by auto
          
        
        ultimately show ?thesis 
          by (simp add: add_divide_distrib)
      qed

lemma einstein_gyroauto_help4:
  shows "(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2)/
(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 -1) = (1+\<gamma> (Rep_PoincareDisc a))/(\<gamma> (Rep_PoincareDisc a))"
    proof-
      have "norm(Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))) <1"
        using Rep_PoincareDisc by blast
      moreover have "(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 = 
1/(1-norm(Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a)))^2)"
        by (simp add: \<open>cmod (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))) < 1\<close> e_help1)
      moreover have "1/(1-norm(Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a)))^2) = 1/(1-(norm (Rep_PoincareDisc ((1/2) \<otimes>\<^sub>E a)))^2)"
        using Moebius_gyrodom'.gyronorm_def mobius_gyroauto_norm by presburger
      moreover have " 1/(1-(norm (Rep_PoincareDisc ((1/2) \<otimes>\<^sub>E a)))^2) = 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2)"
        by (metis Moebius_gyrodom'.of_dom half_times_gamma iso_ei_inner_help2 iso_ei_inner_mo_help3)
      moreover have "(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2)/
(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 -1) = 2*( 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))/(2*
( 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1)"
        using calculation(2) calculation(3) calculation(4) by presburger
      moreover have "2*( 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))/(2*( 1/(1-((\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1)
    = (1+\<gamma> (Rep_PoincareDisc a))/(\<gamma> (Rep_PoincareDisc a))"
        using einstein_gyroauto_help3 by blast
      ultimately show ?thesis 
        by presburger
    qed

lemma einstain_gyroauto:
  shows "e_gyr u v a \<cdot>\<^sub>E e_gyr u v b = a \<cdot>\<^sub>E b"
proof-
  have "e_gyr u v a =  2 \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a)"
    by (simp add: e_gyr_m_gyr2)
  moreover have "e_gyr u v b =  2 \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b)"
    using e_gyr_m_gyr2 by blast
  moreover have *:"\<llangle> m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a) \<rrangle>\<^sub>m = \<llangle> ((1/2) \<otimes>\<^sub>E a) \<rrangle>\<^sub>m"
    using mobius_gyroauto_norm by force
  moreover have " \<llangle> ((1/2) \<otimes>\<^sub>E a) \<rrangle>\<^sub>m = (\<gamma> (Rep_PoincareDisc a))/(1+\<gamma> (Rep_PoincareDisc a)) *  \<llangle>a\<rrangle>\<^sub>m"
    by (smt (verit, ccfv_SIG) Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.of_dom add_divide_distrib diff_divide_distrib divide_self half_times_gamma iso_ei_inner_help2 iso_ei_mo_inner_help7_1 norm_mult norm_of_real of_real_divide power2_eq_square real_minus_mult_self_le)
  moreover have "e_gyr u v a = Abs_PoincareDisc (cor (2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2)/
(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 -1) * (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))"
    using calculation(1) two_times_gamma_factor by presburger
  moreover have "e_gyr u v b = Abs_PoincareDisc (cor (2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))^2)/
(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))^2 -1) * (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))"
    using calculation(2) two_times_gamma_factor by presburger
  moreover have "e_gyr u v a \<cdot>\<^sub>E e_gyr u v b =   2 *
    (\<gamma>
      (Rep_PoincareDisc
        (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))))\<^sup>2 /
    (2 *
     (\<gamma>
       (Rep_PoincareDisc
         (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))))\<^sup>2 -
     1) *
    (2 *
     (\<gamma>
       (Rep_PoincareDisc
         (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))))\<^sup>2 /
     (2 *
      (\<gamma>
        (Rep_PoincareDisc
          (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))))\<^sup>2 -
      1)) *
    Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))) \<cdot>\<^sub>E
    Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))) "
    by (metis (no_types, lifting) Rep_PoincareDisc calculation(5) calculation(6) einstain_gyroauto_help2 einstein_gyroauto_help1 mem_Collect_eq of_real_divide)

  moreover have " Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))) =
    m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a)"
    using Moebius_gyrodom'.of_dom by auto
    moreover have " Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))) =
    m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b)"
      using Moebius_gyrodom'.of_dom by auto
    moreover have "  Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))) \<cdot>\<^sub>E
    Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))) = 
 m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a)  \<cdot>\<^sub>E
  m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b) "
      by (simp add: Moebius_gyrodom'.of_dom)

    moreover have "m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a)  \<cdot>\<^sub>E
  m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b) =  ((1 / 2) \<otimes>\<^sub>E a)  \<cdot>\<^sub>E  ((1 / 2) \<otimes>\<^sub>E b)"
    proof-
      let ?u = "((1 / 2) \<otimes>\<^sub>E u)"
      let ?v = "((1 / 2) \<otimes>\<^sub>E v)"
      let ?a = "((1 / 2) \<otimes>\<^sub>E a)"
      let ?b = "((1 / 2) \<otimes>\<^sub>E b)"
      show ?thesis using mobius_gyroauto[of ?u ?v ?a ?b]
        by (simp add: Moebius_gyrodom'.gyroinner_def e_inner'_def e_inner.rep_eq)
    qed

    moreover have "  ((1 / 2) \<otimes>\<^sub>E a)  \<cdot>\<^sub>E  ((1 / 2) \<otimes>\<^sub>E b) = ((\<gamma> (Rep_PoincareDisc a))
  /(1+\<gamma> (Rep_PoincareDisc a)))*((\<gamma> (Rep_PoincareDisc b))/
  (1+\<gamma> (Rep_PoincareDisc b)))* a  \<cdot>\<^sub>E b"
      by (metis Moebius_gyrodom'.of_dom e_inner'_def e_inner.rep_eq half_times_gamma iso_ei_inner_help2 iso_ei_mo_inner_help5)


    moreover have "\<llangle> m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b) \<rrangle>\<^sub>m = \<llangle> ((1/2) \<otimes>\<^sub>E b) \<rrangle>\<^sub>m"
    using mobius_gyroauto_norm by force
    moreover have "(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2)/
(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 -1) = (1+\<gamma> (Rep_PoincareDisc a))/(\<gamma> (Rep_PoincareDisc a))"
      using einstein_gyroauto_help4 by presburger
        moreover have "(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))^2)/
(2*(\<gamma> (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))^2 -1) = (1+\<gamma> (Rep_PoincareDisc b))/(\<gamma> (Rep_PoincareDisc b))"
      using einstein_gyroauto_help4 by presburger
    
    moreover have "   2 *
    (\<gamma>
      (Rep_PoincareDisc
        (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))))\<^sup>2 /
    (2 *
     (\<gamma>
       (Rep_PoincareDisc
         (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))))\<^sup>2 -
     1) *
    (2 *
     (\<gamma>
       (Rep_PoincareDisc
         (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))))\<^sup>2 /
     (2 *
      (\<gamma>
        (Rep_PoincareDisc
          (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))))\<^sup>2 -
      1)) *
    Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))) \<cdot>\<^sub>E
    Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))) =
(1+\<gamma> (Rep_PoincareDisc a))/(\<gamma> (Rep_PoincareDisc a))*
(1+\<gamma> (Rep_PoincareDisc b))/(\<gamma> (Rep_PoincareDisc b))
   *((\<gamma> (Rep_PoincareDisc a))
  /(1+\<gamma> (Rep_PoincareDisc a)))*((\<gamma> (Rep_PoincareDisc b))/
  (1+\<gamma> (Rep_PoincareDisc b)))* a  \<cdot>\<^sub>E b "
      by (simp add: calculation(11) calculation(12) calculation(14) calculation(15) calculation(8) calculation(9))
    moreover have "(1+\<gamma> (Rep_PoincareDisc a))/(\<gamma> (Rep_PoincareDisc a))*
(1+\<gamma> (Rep_PoincareDisc b))/(\<gamma> (Rep_PoincareDisc b))
   *((\<gamma> (Rep_PoincareDisc a))
  /(1+\<gamma> (Rep_PoincareDisc a)))*((\<gamma> (Rep_PoincareDisc b))/
  (1+\<gamma> (Rep_PoincareDisc b))) = 1"
    proof-
      have "\<gamma> (Rep_PoincareDisc a) \<noteq>0"
        by (metis Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.of_dom add.commute add.right_neutral calculation(4) diff_add_cancel div_by_1 half_times_gamma iso_ei_inner_help2 iso_ei_mo_inner_help7_1 mult_zero_left power_zero_numeral zero_neq_one)
      moreover have "\<gamma> (Rep_PoincareDisc b)\<noteq>0"
        by (metis diff_zero division_ring_divide_zero e_help1 e_inv e_ozero'_def e_ozero.rep_eq gamma_plus5 mult_zero_left mult_zero_right norm_zero power_zero_numeral zero_less_one zero_neq_one)
      moreover have "1+\<gamma> (Rep_PoincareDisc a)\<noteq>0"
        by (metis Rep_PoincareDisc add_0 add_diff_cancel_left' division_ring_divide_zero iso_ei_mo_help4 mem_Collect_eq zero_neq_one)
      moreover have "1+\<gamma> (Rep_PoincareDisc b)\<noteq>0"
        by (metis (no_types, opaque_lifting) ab_group_add_class.ab_diff_conv_add_uminus diff_add_cancel diff_zero div_by_1 divide_divide_eq_right division_ring_divide_zero einstein_gyroauto_help3 one_add_one power_zero_numeral zero_neq_numeral)
      ultimately show ?thesis
        by simp
    qed
    ultimately show ?thesis 
      by (metis mult_cancel_right1)
  qed

lemma e_otimes_assoc:
  shows "(r1 * r2) \<otimes>\<^sub>E a = r1 \<otimes>\<^sub>E (r2 \<otimes>\<^sub>E a)"
proof -
  have "e_otimes' = m_otimes'"
    using e_otimes'_def by blast
  then show ?thesis
    using e_otimes_def m_otimes_assoc m_otimes_def by force
qed
lemma e_otimes_distrib:
  shows "(r1 + r2) \<otimes>\<^sub>E a = r1 \<otimes>\<^sub>E a \<oplus>\<^sub>E r2 \<otimes>\<^sub>E a" 
proof-
  have "r1 \<otimes>\<^sub>E a \<oplus>\<^sub>E r2 \<otimes>\<^sub>E a = 2  \<otimes>\<^sub>E ((1/2) \<otimes>\<^sub>E (r1 \<otimes>\<^sub>E a) \<oplus>\<^sub>m(1/2) \<otimes>\<^sub>E (r2 \<otimes>\<^sub>E a))"
    by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq iso_ei_mo m_otimes.rep_eq)
  moreover have "(1/2) \<otimes>\<^sub>E (r1 \<otimes>\<^sub>E a) = (1/2 * r1) \<otimes>\<^sub>E a"
    using e_otimes_assoc by presburger
   moreover have "(1/2) \<otimes>\<^sub>E (r2 \<otimes>\<^sub>E a) = (1/2 * r2) \<otimes>\<^sub>E a"
     using e_otimes_assoc by presburger
   moreover have "(1/2 * r1) \<otimes>\<^sub>E a \<oplus>\<^sub>m (1/2 * r2) \<otimes>\<^sub>E a = (r1/2+r2/2)  \<otimes>\<^sub>E a"
   proof -
     have "(\<otimes>\<^sub>E) = (\<otimes>\<^sub>m)"
       using e_otimes'_def e_otimes_def m_otimes_def by presburger
     then show ?thesis
       by (simp add: m_otimes_distrib)
   qed
   moreover have " 2  \<otimes>\<^sub>E  ((r1/2+r2/2)  \<otimes>\<^sub>E a) = (r1+r2)  \<otimes>\<^sub>E a "
     by (metis add_divide_distrib e_otimes_assoc field_sum_of_halves mult.commute mult_2_right)
   ultimately show ?thesis 
     by presburger
 qed

lemma einstein_scale_prop:
  fixes r::real
  assumes "r\<noteq>0"
  (*assumes "r\<noteq>0" "(Rep_PoincareDisc a)\<noteq>0"*)
  shows " (Rep_PoincareDisc (\<bar>r\<bar> \<otimes>\<^sub>E a)) / (\<llangle>r \<otimes>\<^sub>E a\<rrangle>\<^sub>E)  = ((Rep_PoincareDisc a) / \<llangle>a\<rrangle>\<^sub>E)"
  using Moebius_gyrodom'.gyronorm_def assms e_norm.rep_eq e_otimes'_def e_otimes_def m_norm'_def m_otimes_def mobius_scale_prop by presburger


lemma tanh_monotone:
  fixes x::real
  fixes y::real
  assumes "x>y"
  shows "tanh x > tanh y"
  by (simp add: assms)

lemma ln_monotone:
  fixes x::real
  fixes y::real
  assumes "x\<ge>y" "x>0" "y>0"
  shows "ln x \<ge> ln y"
  by (simp add: assms(1) assms(2) assms(3))

lemma ln_monotone2:
  fixes x::real
  assumes "x>0" "x<1"
  shows "(1+x)/(1-x) >0"
  using assms(1) assms(2) by auto

lemma ln_monotone3:
  fixes x::real
  assumes "x\<ge>0" "x<1" "y\<ge>0" "y<1" "x\<le>y"
  shows "(1+x)/(1-x) \<le> (1+y)/(1-y)"
  by (smt (verit, best) assms(1) assms(4) assms(5) frac_less)


lemma ln_monotone4:
  fixes x::real
  assumes "x\<ge>0" "x<1" "y\<ge>0" "y<1" "x\<le>y"
  shows "ln ((1+x)/(1-x)) \<le> ln((1+y)/(1-y))"
  using assms(1) assms(4) assms(5) ln_monotone3 by force

lemma artanh_monotone:
  fixes x::real
  fixes y::real
  assumes "x\<le>y" " x\<ge>0" "x < 1" "0 \<le> y" "y < 1" 
  shows "artanh x \<le> artanh y"
proof-
  have "artanh x = 1/2 * ln((1+x)/(1-x))"
    by (simp add: artanh_def)
  moreover have "artanh y = 1/2 * ln((1+y)/(1-y))"
    by (simp add: artanh_def)
  ultimately show ?thesis 
    by (simp add: artanh_def assms(1) assms(2) assms(3) assms(4) assms(5) ln_monotone4)

qed

lemma einstein_triangle_help:
  fixes x::real
  fixes y::real
  assumes "x<y" "0\<le>x" "x < 1" "0 \<le> y" "y < 1" 
  shows "tanh(2*artanh(x)) < tanh(2*artanh(y))"
  by (smt (z3) artanh_def assms(1) assms(2) assms(5) divide_less_0_iff divide_less_cancel frac_less ln_less_cancel_iff tanh_monotone)
   
lemma einstein_triangle:
  shows "(\<llangle>  a  \<oplus>\<^sub>E b \<rrangle>\<^sub>E ) \<le> cmod (Rep_PoincareDisc ((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E)))  \<oplus>\<^sub>E (Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) ))"
proof-
  have "\<llangle>  a  \<oplus>\<^sub>E b \<rrangle>\<^sub>E = \<llangle> 2 \<otimes>\<^sub>E (((1/2)\<otimes>\<^sub>E a)  \<oplus>\<^sub>m  ((1/2) \<otimes>\<^sub>E b)) \<rrangle>\<^sub>m"
    by (simp add: Moebius_gyrodom'.gyronorm_def e_norm.rep_eq e_otimes'_def e_otimes.rep_eq iso_ei_mo m_norm'_def m_otimes.rep_eq m_plus_full_m_plus)
  
  moreover have "\<llangle> 2 \<otimes>\<^sub>E (((1/2)\<otimes>\<^sub>E a)  \<oplus>\<^sub>m  ((1/2) \<otimes>\<^sub>E b)) \<rrangle>\<^sub>m = tanh(2*artanh(\<llangle>  (((1/2)\<otimes>\<^sub>E a)  \<oplus>\<^sub>m  ((1/2) \<otimes>\<^sub>E b)) \<rrangle>\<^sub>m))"
  proof-
    let ?iz = "Rep_PoincareDisc (((1/2)\<otimes>\<^sub>E a)  \<oplus>\<^sub>m  ((1/2) \<otimes>\<^sub>E b))"
    let ?iz2 = "cmod (Rep_PoincareDisc (((1/2)\<otimes>\<^sub>E a)  \<oplus>\<^sub>m  ((1/2) \<otimes>\<^sub>E b)))"
    have "cmod (?iz) <1"
      using Rep_PoincareDisc by force

    then show ?thesis using m_otimes'_k_tanh[of ?iz 2]
      by (simp add: Moebius_gyrodom'.gyronorm_def artanh_help cmod_m_otimes' e_otimes'_def e_otimes.rep_eq)  
  qed

  
  
  moreover have "cmod (Rep_PoincareDisc ((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E)))  \<oplus>\<^sub>E (Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) )) =
    cmod (Rep_PoincareDisc (2 \<otimes>\<^sub>E  ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E))))  \<oplus>\<^sub>m   (1/2)\<otimes>\<^sub>E ((Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) )) ))"
    using e_otimes'_def e_otimes.rep_eq iso_ei_mo m_otimes.rep_eq m_plus_full_m_plus by auto

  moreover have "   cmod (Rep_PoincareDisc (2 \<otimes>\<^sub>E  ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E))))  \<oplus>\<^sub>m   (1/2)\<otimes>\<^sub>E ((Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) )) )) =
      tanh(2*artanh(cmod (Rep_PoincareDisc ( ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E))))  \<oplus>\<^sub>m   (1/2)\<otimes>\<^sub>E ((Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) )) ))))"
  proof-
    let ?iz = "Rep_PoincareDisc ( ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E))))  \<oplus>\<^sub>m   (1/2)\<otimes>\<^sub>E ((Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) )) )"
    have "cmod ?iz <1 "
      using Rep_PoincareDisc by auto
    then show ?thesis using m_otimes'_k_tanh[of ?iz 2] 
      by (simp add: artanh_help cmod_m_otimes' e_otimes'_def e_otimes.rep_eq)
  qed

  moreover have "\<llangle>  (((1/2)\<otimes>\<^sub>E a)  \<oplus>\<^sub>m  ((1/2) \<otimes>\<^sub>E b)) \<rrangle>\<^sub>m \<le> cmod (Rep_PoincareDisc ( ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E))))  \<oplus>\<^sub>m   (1/2)\<otimes>\<^sub>E ((Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) )) ))"
    using  moebius_triangle moebius_homogenity
  proof-
    let ?iz1 ="((1/2)\<otimes>\<^sub>E a)"
    let ?iz2 ="((1/2)\<otimes>\<^sub>E b)"
    have " \<llangle>(1 / 2) \<otimes>\<^sub>E a \<oplus>\<^sub>m (1 / 2) \<otimes>\<^sub>E b\<rrangle>\<^sub>m
  \<le> cmod (Rep_PoincareDisc
            (Abs_PoincareDisc (cor (\<llangle>(1 / 2) \<otimes>\<^sub>E a\<rrangle>\<^sub>m)) \<oplus>\<^sub>m
             Abs_PoincareDisc (cor (\<llangle>(1 / 2) \<otimes>\<^sub>E b\<rrangle>\<^sub>m))))"
      using moebius_triangle by blast

    moreover have " \<llangle>(1 / 2) \<otimes>\<^sub>m a\<rrangle>\<^sub>m = cmod (Rep_PoincareDisc (\<bar>1 / 2\<bar> \<otimes>\<^sub>m Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>m))))"
      using moebius_homogenity by blast
    moreover have "cmod (Rep_PoincareDisc (\<bar>1 / 2\<bar> \<otimes>\<^sub>m Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>m)))) = Rep_PoincareDisc ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E)))))"
    proof-
      have "\<bar>(1 / 2)::real\<bar> = 1/2"
        by simp
      moreover have "cmod (Rep_PoincareDisc a) <1"
        using Rep_PoincareDisc by blast
      ultimately show ?thesis
        by (smt (verit, ccfv_threshold) Moebius_gyrodom'.gyronorm_def divide_eq_1_iff e_norm.rep_eq e_otimes'_def e_otimes.rep_eq iso_ei_inner_help2 m_norm'_def m_otimes.rep_eq mobius_scale_prop mult_eq_0_iff norm_not_less_zero norm_of_real norm_zero of_real_0 of_real_eq_0_iff rep_abs_inv zero_less_divide_1_iff)
    qed

    
    moreover have " \<llangle>(1 / 2) \<otimes>\<^sub>m b\<rrangle>\<^sub>m = cmod (Rep_PoincareDisc (\<bar>1 / 2\<bar> \<otimes>\<^sub>m Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>m))))"
      using moebius_homogenity by blast
    moreover have "cmod (Rep_PoincareDisc (\<bar>1 / 2\<bar> \<otimes>\<^sub>m Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>m)))) = Rep_PoincareDisc ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E)))))"
    proof-
      have "\<bar>(1 / 2)::real\<bar> = 1/2"
        by simp
      moreover have "cmod (Rep_PoincareDisc b) <1"
        using Rep_PoincareDisc by blast
      ultimately show ?thesis
        by (smt (verit, ccfv_threshold) Moebius_gyrodom'.gyronorm_def divide_eq_1_iff e_norm.rep_eq e_otimes'_def e_otimes.rep_eq iso_ei_inner_help2 m_norm'_def m_otimes.rep_eq mobius_scale_prop mult_eq_0_iff norm_not_less_zero norm_of_real norm_zero of_real_0 of_real_eq_0_iff rep_abs_inv zero_less_divide_1_iff)
    qed

    ultimately show ?thesis 
      by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq)
    
  qed

  moreover have "\<llangle>  (((1/2)\<otimes>\<^sub>E a)  \<oplus>\<^sub>m  ((1/2) \<otimes>\<^sub>E b)) \<rrangle>\<^sub>m \<ge>0"
    by (simp add: Moebius_gyrodom'.gyronorm_def)
  moreover have "\<llangle>  (((1/2)\<otimes>\<^sub>E a)  \<oplus>\<^sub>m  ((1/2) \<otimes>\<^sub>E b)) \<rrangle>\<^sub>m <1"
    using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc by auto
  moreover have "cmod (Rep_PoincareDisc ( ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E))))  \<oplus>\<^sub>m   (1/2)\<otimes>\<^sub>E ((Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) )) )) \<ge>0"
    by auto
  moreover have "cmod (Rep_PoincareDisc ( ((1/2)\<otimes>\<^sub>E((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>E))))  \<oplus>\<^sub>m   (1/2)\<otimes>\<^sub>E ((Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>E))) )) )) <1"
    using Rep_PoincareDisc by blast
  
  ultimately show ?thesis 
    by (simp add: artanh_monotone)
qed

lemma einstein_homogenity:
  shows "\<llangle>(r  \<otimes>\<^sub>E a)\<rrangle>\<^sub>E =  (cmod (Rep_PoincareDisc ((abs r)  \<otimes>\<^sub>E ( Abs_PoincareDisc (cor(\<llangle>a\<rrangle>\<^sub>E))))))"
  using e_norm_def e_otimes'_def e_otimes_def m_norm_def m_otimes_def moebius_homogenity by presburger

lemma e_gyr_gyrospace2:
  shows "e_gyr u v ( r  \<otimes>\<^sub>E a) = r  \<otimes>\<^sub>E (e_gyr u v a)"
proof-
  have "e_gyr u v ( r  \<otimes>\<^sub>E a) = 2 \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2)  \<otimes>\<^sub>E ( r  \<otimes>\<^sub>E a) ) "
    using e_gyr_m_gyr2 by blast
  moreover have " m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2)  \<otimes>\<^sub>E ( r  \<otimes>\<^sub>E a) ) =  m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) (((1/2)* r)  \<otimes>\<^sub>E a) "
    using e_otimes_assoc by presburger
  moreover have "m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) (((1/2)* r)  \<otimes>\<^sub>E a) = m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) (r \<otimes>\<^sub>E ( (1/2)   \<otimes>\<^sub>E a) )"
    by (metis (mono_tags, opaque_lifting) e_otimes_assoc mult.commute)
  moreover have " m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) (r \<otimes>\<^sub>E ( (1/2)   \<otimes>\<^sub>E a) ) = r \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ( ( (1/2)   \<otimes>\<^sub>E a) )"
     using m_gyr_gyrospace2 
     by (metis Moebius_gyrodom'.of_dom e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq)
   moreover have "e_gyr u v ( r  \<otimes>\<^sub>E a) = 2 \<otimes>\<^sub>E ( r \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ( ( (1/2)   \<otimes>\<^sub>E a) ))"
     using calculation(1) calculation(2) calculation(3) calculation(4) by presburger
   moreover have "e_gyr u v  ( r  \<otimes>\<^sub>E a) = r  \<otimes>\<^sub>E(2 \<otimes>\<^sub>E m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ( ( (1/2)   \<otimes>\<^sub>E a) ))"
     by (metis calculation(5) e_otimes_assoc mult.commute)
   ultimately show ?thesis 
     using e_gyr_m_gyr2 by presburger
 qed


lemma e_gyr_gyrospace:
  shows "e_gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) = id"
proof-
  fix x
  show ?thesis
  proof-
  have "e_gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) x  = 2  \<otimes>\<^sub>E m_gyr ((1/2)  \<otimes>\<^sub>E (r1 \<otimes>\<^sub>E v)) ((1/2) \<otimes>\<^sub>E (r2 \<otimes>\<^sub>E v)) ((1/2) \<otimes>\<^sub>E x)"
    by (metis Moebius_gyrodom'.of_dom e_gyr_m_gyr2 e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq)
  moreover have "m_gyr ((1/2)  \<otimes>\<^sub>E (r1 \<otimes>\<^sub>E v)) ((1/2) \<otimes>\<^sub>E (r2 \<otimes>\<^sub>E v)) ((1/2) \<otimes>\<^sub>E x) = m_gyr (((1/2)*r1) \<otimes>\<^sub>E v) (((1/2)*r2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E x)"
    using e_otimes_assoc by presburger
  moreover have " m_gyr (((1/2)*r1) \<otimes>\<^sub>E v) (((1/2)*r2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E x) = ((1/2) \<otimes>\<^sub>E x)"
    using  m_gyr_gyrospace
    by (simp add: e_otimes'_def e_otimes_def m_otimes_def)
  moreover have "e_gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) x  = 2  \<otimes>\<^sub>E ((1/2) \<otimes>\<^sub>E x)"
    using calculation(1) calculation(2) calculation(3) by presburger
  moreover have "e_gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) x = x"
    by (metis calculation(4) e_gyr_inv e_gyr_m_gyr e_gyr_m_gyr2)
  moreover have "\<forall>x. (e_gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) x = x)"
    by (metis Moebius_gyrodom'.of_dom e_gyr_inv e_gyr_m_gyr e_gyr_m_gyr2 e_otimes'_def e_otimes.rep_eq id_apply m_gyr_gyrospace m_otimes.rep_eq m_otimes_assoc)
  ultimately show ?thesis
    using eq_id_iff by blast
  qed
qed


end
