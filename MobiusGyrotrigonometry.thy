theory MobiusGyrotrigonometry
  imports Main MobiusGyroGroup MobiusGyroVectorSpace  GyroVectorSpace GammaFactor HyperbolicFunctions
  MoreComplex
begin


lemma arccos_well_defined:
  shows "norm (inner  ((to_complex (⊖⇩m a ⊕⇩m b )) /⇩R ⟪((⊖⇩m a ⊕⇩m b))⟫)
 ((to_complex (⊖⇩m a ⊕⇩m c)) /⇩R ⟪((⊖⇩m a ⊕⇩m c))⟫)) ≤ 1"
proof-
  have "norm (((to_complex (⊖⇩m a ⊕⇩m b )) /⇩R ⟪((⊖⇩m a ⊕⇩m b))⟫)) ≤ 1"
    by (metis Mobius_gyrodom.norm_inner abs_inverse divide_eq_0_iff divide_eq_1_iff divide_inverse_commute less_eq_real_def norm_p.rep_eq norm_scaleR real_sqrt_abs square_norm_inner zero_less_one)   
  moreover have "norm (((to_complex (⊖⇩m a ⊕⇩m c )) /⇩R ⟪((⊖⇩m a ⊕⇩m c))⟫)) ≤ 1"
    by (metis Mobius_gyrodom'.gyronorm_def abs_inverse abs_norm_cancel divide_inverse_commute divide_self_if le_numeral_extra(4) linordered_nonzero_semiring_class.zero_le_one norm_scaleR)
  ultimately show ?thesis 
    using abs_inner_lt_1
    by (smt (verit, del_insts) Cauchy_Schwarz_ineq2 inner_real_def inverse_1 inverse_eq_divide left_inverse mult_eq_0_iff norm_geq_zero norm_p.rep_eq norm_scaleR real_norm_def)
    
qed

definition angle::"PoincareDisc ⇒ PoincareDisc ⇒ PoincareDisc ⇒ real" where 
  "angle a b c = arccos (inner  ((to_complex (⊖⇩m a ⊕⇩m b )) /⇩R ⟪((⊖⇩m a ⊕⇩m b))⟫)
    ((to_complex (⊖⇩m a ⊕⇩m c)) /⇩R ⟪((⊖⇩m a ⊕⇩m c))⟫))"



definition m_gyroray::"PoincareDisc ⇒ PoincareDisc ⇒ PoincareDisc set" where
  "m_gyroray x p = {s::PoincareDisc. ∃t::real. t≥0 ∧ s=(x ⊕⇩m t ⊗ (⊖⇩m x ⊕⇩m p))}"


lemma T8_5:
  assumes "b2 ∈ m_gyroray a1 b1" 
          "b2≠a1" "c2 ∈ m_gyroray a1 c1"
          "c2≠a1"
  shows "angle a1 b1 c1 = angle a1 b2 c2"
proof-
  obtain t1::real where "t1>0 ∧ b2 = a1 ⊕⇩m t1 ⊗ (⊖⇩m a1 ⊕⇩m b1)"
    using assms(1) assms(2) gyrozero_PoincareDisc_def less_eq_real_def m_gyroray_def by auto
  also obtain t2::real where "t2>0 ∧ c2 = a1 ⊕⇩m t2 ⊗ (⊖⇩m a1 ⊕⇩m c1)"
    using assms(3) assms(4) gyrozero_PoincareDisc_def less_eq_real_def m_gyroray_def by auto
  moreover have " ⊖⇩m a1 ⊕⇩m b2 =  t1 ⊗ (⊖⇩m a1 ⊕⇩m b1)"
    using Mobius_gyrogroup.gyro_left_cancel' calculation by blast
  moreover have " ⊖⇩m a1 ⊕⇩m c2 =  t2 ⊗ (⊖⇩m a1 ⊕⇩m c1)"
    by (simp add: Mobius_gyrogroup.gyro_left_cancel' ‹0 < t2 ∧ c2 = a1 ⊕⇩m t2 ⊗ (⊖⇩m a1 ⊕⇩m c1)›)
  moreover have "angle a1 b2 c2 = arccos (inner ((to_complex (⊖⇩m a1 ⊕⇩m b2)) /⇩R ⟪((⊖⇩m a1 ⊕⇩m b2))⟫)
   ((to_complex (⊖⇩m a1 ⊕⇩m c2)) /⇩R ⟪((⊖⇩m a1 ⊕⇩m c2))⟫))"
    using angle_def by presburger
  moreover have "inner ((to_complex (⊖⇩m a1 ⊕⇩m b2)) /⇩R ⟪((⊖⇩m a1 ⊕⇩m b2))⟫)
   ((to_complex (⊖⇩m a1 ⊕⇩m c2)) /⇩R ⟪((⊖⇩m a1 ⊕⇩m c2))⟫) =
 inner ((to_complex (t1 ⊗ (⊖⇩m a1 ⊕⇩m b1))) /⇩R ⟪((t1 ⊗ (⊖⇩m a1 ⊕⇩m b1)))⟫)
((to_complex (t2 ⊗ (⊖⇩m a1 ⊕⇩m c1))) /⇩R ⟪((t2 ⊗ (⊖⇩m a1 ⊕⇩m c1)))⟫)"
    using ‹⊖⇩m a1 ⊕⇩m b2 = t1 ⊗ (⊖⇩m a1 ⊕⇩m b1)› ‹⊖⇩m a1 ⊕⇩m c2 = t2 ⊗ (⊖⇩m a1 ⊕⇩m c1)› by auto
  moreover have "Abs_PoincareDisc ((to_complex (t2 ⊗ (⊖⇩m a1 ⊕⇩m c1))) /⇩R ⟪((t2 ⊗ (⊖⇩m a1 ⊕⇩m c1)))⟫) =
     Abs_PoincareDisc ((to_complex  (⊖⇩m a1 ⊕⇩m c1)) /⇩R ⟪(⊖⇩m a1 ⊕⇩m c1)⟫)"
    by (smt (verit, ccfv_SIG) Mobius_gyrovector_space.scale_prop1 ‹0 < t2 ∧ c2 = a1 ⊕⇩m t2 ⊗ (⊖⇩m a1 ⊕⇩m c1)›)
  moreover have "Abs_PoincareDisc ((to_complex (t2 ⊗ (⊖⇩m a1 ⊕⇩m b1))) /⇩R ⟪((t2 ⊗ (⊖⇩m a1 ⊕⇩m b1)))⟫) =
     Abs_PoincareDisc ((to_complex  (⊖⇩m a1 ⊕⇩m b1)) /⇩R ⟪(⊖⇩m a1 ⊕⇩m b1)⟫)"
    by (metis Mobius_gyrovector_space.scale_prop1 ‹0 < t2 ∧ c2 = a1 ⊕⇩m t2 ⊗ (⊖⇩m a1 ⊕⇩m c1)› abs_of_pos less_numeral_extra(3))
  ultimately show ?thesis 
    by (metis Mobius_gyrovector_space.scale_prop1 abs_of_pos angle_def nless_le)
qed




datatype m_gyrotriangle = M_gyrotriangle (A:PoincareDisc) (B:PoincareDisc) (C:PoincareDisc)
definition get_a::"m_gyrotriangle ⇒ PoincareDisc" where
  "get_a t = ⊖⇩m (C t) ⊕⇩m (B t)"
definition get_b::"m_gyrotriangle ⇒ PoincareDisc" where
  "get_b t = ⊖⇩m (C t) ⊕⇩m (A t)"
definition get_c::"m_gyrotriangle ⇒ PoincareDisc" where
  "get_c t = ⊖⇩m (B t) ⊕⇩m (A t)"

definition get_alpha::"m_gyrotriangle ⇒ real" where
  "get_alpha t = angle (A t) (B t) (C t)"

definition get_beta::"m_gyrotriangle ⇒ real" where
  "get_beta t = angle (B t) (C t) (A t)"

definition get_gamma::"m_gyrotriangle ⇒ real" where
  "get_gamma t = angle (C t) (A t) (B t)"


definition cong_gyrotriangles::"m_gyrotriangle ⇒ m_gyrotriangle ⇒ bool" where
  "cong_gyrotriangles t1 t2 ⟷ (⟪get_a t1⟫ = ⟪get_a t2⟫ ∧ ⟪get_b t1⟫ = ⟪get_b t2⟫
∧ ⟪get_c t1⟫ = ⟪get_c t2⟫ ∧ (get_alpha t1 = get_alpha t2) ∧  (get_beta t1 = get_beta t2) ∧  (get_gamma t1 = get_gamma t2) )"

lemma m_gamma_h1:
  shows "⊖⇩m a ⊕⇩m b = Abs_PoincareDisc (((Rep_PoincareDisc b)-(Rep_PoincareDisc a))/(1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b)))"
  by (metis Mobius_gyrodom'.of_dom add.commute add_uminus_conv_diff complex_cnj_minus m_ominus'_def m_ominus.rep_eq m_oplus'_def m_oplus.rep_eq mult_minus_left)

lemma m_gamma_h2:
  shows " ⟪⊖⇩m a ⊕⇩m b⟫* ⟪⊖⇩m a ⊕⇩m b⟫ = ( ⟪b⟫* ⟪b⟫+⟪a⟫* ⟪a⟫ -(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))/
(1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫)"

proof-
  have "((Rep_PoincareDisc b)-(Rep_PoincareDisc a))*cnj((Rep_PoincareDisc b)-(Rep_PoincareDisc a)) =
    ⟪b⟫* ⟪b⟫+⟪a⟫* ⟪a⟫ -(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) "
  proof-
    have "cnj((Rep_PoincareDisc b)-(Rep_PoincareDisc a)) = cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)"
      by simp
    then show ?thesis 
      by (metis (no_types, lifting) Mobius_gyrodom'.gyronorm_def complex_norm_square diff_add_eq diff_diff_eq2 mult.commute of_real_add power2_eq_square right_diff_distrib)
  qed
  moreover have "(1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))*cnj (1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b)) =
      (1-(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫)"
    by (smt (verit, ccfv_threshold) ab_semigroup_mult_class.mult_ac(1) complex_cnj_cnj complex_cnj_diff complex_cnj_mult complex_mod_cnj complex_norm_square diff_add_eq diff_diff_eq2 left_diff_distrib mult.right_neutral mult_1 norm_mult norm_p.rep_eq power2_eq_square power_mult_distrib right_diff_distrib)
  moreover have "(((Rep_PoincareDisc b)-(Rep_PoincareDisc a))*cnj((Rep_PoincareDisc b)-(Rep_PoincareDisc a)))/((1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))*cnj (1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))) =
    ⟪⊖⇩m a ⊕⇩m b⟫* ⟪⊖⇩m a ⊕⇩m b⟫ "
  proof-
    have "  (((Rep_PoincareDisc b)-(Rep_PoincareDisc a))/(1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))) *
        cnj((((Rep_PoincareDisc b)-(Rep_PoincareDisc a))/(1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b)))) = 
         (((Rep_PoincareDisc b)-(Rep_PoincareDisc a))* cnj(((Rep_PoincareDisc b)-(Rep_PoincareDisc a))))/
          ((1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))*cnj((1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))))"
      by simp
    then show ?thesis
      by (metis (no_types, lifting) add_uminus_conv_diff complex_cnj_minus complex_norm_square m_ominus'_def m_ominus.rep_eq m_oplus'_def m_oplus.rep_eq mult_minus_left norm_p.rep_eq power2_eq_square uminus_add_conv_diff)
  qed
  ultimately show ?thesis
    by presburger
qed

lemma m_gamma_h3:
  shows "1-⟪⊖⇩m a ⊕⇩m b⟫* ⟪⊖⇩m a ⊕⇩m b⟫ = (1- ⟪b⟫* ⟪b⟫-  ⟪a⟫* ⟪a⟫ +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫)/(1-(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b)+⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫)"
proof-
  have "⟪⊖⇩m a ⊕⇩m b⟫* ⟪⊖⇩m a ⊕⇩m b⟫ = ( ⟪b⟫* ⟪b⟫+⟪a⟫* ⟪a⟫ -(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))/
(1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫)
" 
    using m_gamma_h2 by blast
  moreover have "1-⟪⊖⇩m a ⊕⇩m b⟫* ⟪⊖⇩m a ⊕⇩m b⟫ = 1-(( ⟪b⟫* ⟪b⟫+⟪a⟫* ⟪a⟫ -(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))/
(1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫))"
    using m_gamma_h2 by fastforce
  moreover have "1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫ -( ⟪b⟫* ⟪b⟫+⟪a⟫* ⟪a⟫ -(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))
    = 1- ⟪b⟫* ⟪b⟫-  ⟪a⟫* ⟪a⟫ +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫ "
    by force
  moreover have "1-⟪⊖⇩m a ⊕⇩m b⟫* ⟪⊖⇩m a ⊕⇩m b⟫ = (1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫ -( ⟪b⟫* ⟪b⟫+⟪a⟫* ⟪a⟫ -(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b)))/
(1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫)"
  proof-
    have "1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) ≠0"
      by (smt (verit, del_insts) Mobius_gyrodom'.to_dom_zero add_uminus_conv_diff complex_cnj_minus complex_norm_square division_ring_divide_zero gamma_factor_eq1 gamma_factor_positive gyrozero_PoincareDisc_def m_gamma_h1 m_ominus'_def m_ominus.rep_eq m_ozero'_def m_ozero.abs_eq mult_eq_0_iff mult_minus_left norm_p.rep_eq norm_zero zero_power2)
    moreover have "cnj(1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))≠0"
      using calculation by force
    moreover have "1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫ ≠0"
    proof-
      have "cnj(1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b)) = 1 - (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)"
        by simp
      moreover have "1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b) +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫ =
       (1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))*cnj(1-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b))"
        by (smt (verit) ab_semigroup_mult_class.mult_ac(1) add_diff_cancel_left' add_diff_eq calculation complex_cnj_diff complex_cnj_one complex_mod_cnj complex_norm_square diff_add_cancel left_diff_distrib mult.right_neutral mult_1 norm_mult norm_p.rep_eq power2_eq_square power_mult_distrib right_diff_distrib)
      ultimately show ?thesis 
        using ‹1 - cnj (to_complex a) * to_complex b ≠ 0› ‹cnj (1 - cnj (to_complex a) * to_complex b) ≠ 0› by auto
    qed
    ultimately show ?thesis
      by (metis ‹cor (1 - ⟪⊖⇩m a ⊕⇩m b⟫ * ⟪⊖⇩m a ⊕⇩m b⟫) = 1 - (cor (⟪b⟫ * ⟪b⟫ + ⟪a⟫ * ⟪a⟫) - to_complex a * cnj (to_complex b) - cnj (to_complex a) * to_complex b) / (1 - to_complex a * cnj (to_complex b) - cnj (to_complex a) * to_complex b + cor (⟪a⟫ * ⟪a⟫ * ⟪b⟫ * ⟪b⟫))› diff_divide_distrib divide_eq_1_iff)
  qed
    ultimately show ?thesis 
      by presburger
  qed

lemma m_gamma_h4:
  shows "(γ⇩m (⊖⇩m a ⊕⇩m b))*(γ⇩m (⊖⇩m a ⊕⇩m b)) = (1-(Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b)-cnj(Rep_PoincareDisc a)*(Rep_PoincareDisc b)
  +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫
 )/(1- ⟪b⟫* ⟪b⟫-  ⟪a⟫* ⟪a⟫ +  ⟪a⟫* ⟪a⟫* ⟪b⟫* ⟪b⟫)"
proof-
  have "(γ⇩m (⊖⇩m a ⊕⇩m b))*(γ⇩m (⊖⇩m a ⊕⇩m b)) = 1/(1- ⟪⊖⇩m a ⊕⇩m b⟫* ⟪⊖⇩m a ⊕⇩m b⟫)"
  proof-
    have " ⟪⊖⇩m a ⊕⇩m b⟫<1" 
      using norm_lt_one by auto
    then show ?thesis using gamma_factor_def 
      by (metis gamma_factor_square_norm m_gammma_factor.rep_eq norm_p.rep_eq power2_eq_square)
  qed
  then show ?thesis
    using m_gamma_h3 by auto
qed

lemma m_gamma_equation:
  shows "(γ⇩m (⊖⇩m a ⊕⇩m b))*(γ⇩m (⊖⇩m a ⊕⇩m b)) = (γ⇩m a)*(γ⇩m a)*(γ⇩m b)*(γ⇩m b)*(1-2*(a⋅b)+⟪a⟫*⟪a⟫*⟪b⟫*⟪b⟫)"
proof-
  have "2*(a⋅b) = (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b) + (Rep_PoincareDisc b)*cnj(Rep_PoincareDisc a)"
    using Mobius_gyrodom'.gyroinner_def two_inner_cnj by auto
  moreover have "(γ⇩m a)*(γ⇩m a) = 1/(1-⟪a⟫*⟪a⟫)"
    by (metis gamma_factor_square_norm m_gammma_factor.rep_eq norm_lt_one norm_p.rep_eq power2_eq_square)
  moreover have "(γ⇩m b)*(γ⇩m b) = 1/(1-⟪b⟫*⟪b⟫)"
    by (metis gamma_factor_square_norm m_gammma_factor.rep_eq norm_lt_one norm_p.rep_eq power2_eq_square)
  moreover have " (1/(1-⟪a⟫*⟪a⟫)) *  (1/(1-⟪b⟫*⟪b⟫)) = 1/(1-⟪a⟫*⟪a⟫-⟪b⟫*⟪b⟫+⟪a⟫*⟪a⟫*⟪b⟫*⟪b⟫)"
  proof-
    have "(1-⟪a⟫*⟪a⟫) ≠0"
      by (metis diff_0 diff_gt_0_iff_gt eq_iff_diff_eq_0 mult_minus1_right norm_lt_one norm_not_less_zero norm_p.rep_eq order_less_irrefl square_eq_1_iff zero_less_one)
    moreover have "(1-⟪b⟫*⟪b⟫)≠0"
      by (metis diff_0 diff_gt_0_iff_gt eq_iff_diff_eq_0 mult_minus1_right norm_lt_one norm_not_less_zero norm_p.rep_eq order_less_irrefl square_eq_1_iff zero_less_one)
    moreover have "(1-⟪a⟫*⟪a⟫)*(1-⟪b⟫*⟪b⟫) = 1-⟪a⟫*⟪a⟫-⟪b⟫*⟪b⟫+⟪a⟫*⟪a⟫*⟪b⟫*⟪b⟫"
      by (simp add: mult.commute right_diff_distrib)
    ultimately show ?thesis 
      by force
  qed
  moreover have "(1-2*(a⋅b)+⟪a⟫*⟪a⟫*⟪b⟫*⟪b⟫) = (1- (Rep_PoincareDisc a)*cnj(Rep_PoincareDisc b) - (Rep_PoincareDisc b)*cnj(Rep_PoincareDisc a)+
       ⟪a⟫*⟪a⟫*⟪b⟫*⟪b⟫)" 
    using calculation(1) by auto
  ultimately show ?thesis
    using m_gamma_h4 
    by (smt (verit, del_insts) mult.commute mult_1 of_real_1 of_real_divide of_real_eq_iff of_real_mult times_divide_eq_left)
qed



lemma T8_25_help1:
   assumes   "(A t) ≠ (B t)" "(A t) ≠ (C t)" "(C t) ≠ (B t)"
           "a = ⟪get_a t⟫* ⟪get_a t⟫" "b=⟪get_b t⟫ *⟪get_b t⟫" "c = ⟪get_c t⟫* ⟪get_c t⟫"
         shows "to_complex ((of_complex (cor a)) ⊕⇩m (of_complex (cor b)) ⊕⇩m (⊖⇩m (of_complex (cor c)))) =
      (a+b-c-a*b*c)/(1+a*b - a*c - b*c)"
proof-
  have "norm a < 1" 
    using Mobius_gyrodom.norm_inner assms(4) norm_lt_one square_norm_inner by force
  moreover have "norm b < 1"
    by (metis abs_real_def assms(5) norm_lt_one norm_not_less_zero norm_of_real norm_p.rep_eq of_real_inner_1 real_inner_1_right real_sqrt_abs2 real_sqrt_lt_1_iff real_sqrt_mult_self)
  moreover have "norm c < 1"
    by (metis abs_real_def assms(6) norm_lt_one norm_not_less_zero norm_of_real norm_p.rep_eq of_real_inner_1 power2_eq_square real_inner_1_right real_sqrt_abs real_sqrt_lt_0_iff real_sqrt_lt_1_iff)
  moreover have "(of_complex (cor a)) ⊕⇩m (of_complex (cor b)) = of_complex (((cor a)+(cor b))/(1+cnj((cor a))*b))"
    using m_oplus_def m_oplus'_def
    by (metis Mobius_gyrodom'.of_dom Mobius_gyrodom'.to_dom calculation(1) calculation(2) m_oplus.rep_eq norm_of_real real_norm_def)
  moreover have" to_complex ((of_complex (cor a)) ⊕⇩m (of_complex (cor b)) ⊕⇩m (⊖⇩m (of_complex (cor c)))) = 
    ((((cor a)+(cor b))/(1+cnj((cor a))*b))-c)/(1-cnj(((cor a)+(cor b))/(1+cnj((cor a))*b))*c) "
     using m_oplus_def m_oplus'_def m_ominus_def m_ominus'_def
     using Mobius_gyrodom'.to_dom calculation(1) calculation(2) calculation(3) m_ominus.rep_eq m_oplus.rep_eq by auto
  moreover have" to_complex ((of_complex (cor a)) ⊕⇩m (of_complex (cor b)) ⊕⇩m (⊖⇩m (of_complex (cor c)))) = 
    ((((cor a)+(cor b))/(1+((cor a))*b))-c)/(1-(((cor a)+(cor b))/(1+((cor a))*b))*c) "
    by (simp add: calculation(5))
  moreover have "(((cor a)+(cor b))/(1+(cor a)*b))-c = (a+b-c-a*b*c)/(1+a*b)"
  proof-
    have "1+(cor a)*b ≠0"

      by (metis calculation(1) calculation(2) complex_cnj_complex_of_real den_not_zero norm_of_real real_norm_def)
    moreover have "1+(cor a)*b = 1+a*b" 
      by simp
    moreover have "c*(1+a*b) = c+ c*a*b"
      by (simp add: distrib_left)
    moreover have "a+b - c*(1+a*b) = a+b -c -c*a*b"
      using calculation(3) by force
    moreover have "(cor a) + (cor b) = a+b"
   
      by simp
    moreover have "(((cor a)+(cor b))/(1+(cor a)*b))-c = (a+b-c*(1+a*b))/(1+a*b)"

      by (metis calculation(1) calculation(2) calculation(5) diff_divide_distrib nonzero_mult_div_cancel_right of_real_diff of_real_divide of_real_eq_0_iff)
    ultimately show ?thesis 
      by (metis mult.commute mult.left_commute)
     
  qed
  moreover have "1-(((cor a)+(cor b))/(1+(cor a)*b))*c = (1+a*b-a*c-b*c)/(1+a*b)"
  proof-
    have "(cor a)+(cor b) = a+b" 
      by auto
    moreover have "1+(cor a)*b = 1+a*b" 
      by auto
    moreover have "1+a*b ≠0"
      by (metis add_less_same_cancel1 assms(4) assms(5) linorder_not_less zero_le_mult_iff zero_le_square zero_less_one)
    moreover have "c*(a+b) = c*a+c*b" 
      by (simp add: distrib_left)
    moreover have "1-(((cor a)+(cor b))/(1+(cor a)*b))*c = 1-((a+b)/(1+a*b))*c"
      by force
    moreover have "((a+b)/(1+a*b))*c = ((a+b)*c)/(1+a*b)"
      by auto
    moreover have "1-((a+b)/(1+a*b))*c = 1-((a+b)*c)/(1+a*b) "
      by auto
    moreover have "1-((a+b)*c)/(1+a*b) = (1+a*b-(a+b)*c)/(1+a*b)"
      by (metis calculation(3) diff_divide_distrib right_inverse_eq)
    ultimately show ?thesis 
      by (smt (verit, best) mult.commute)
  qed
  ultimately show ?thesis
    using assms(6) mult_eq_0_iff norm_mult norm_of_real norm_one of_real_divide real_minus_mult_self_le by force
qed

lemma help1:
  fixes x::real
  fixes y::real
  shows "(1+x)*(1+y) =(1+x+x*y+y)"
          by (smt (verit, ccfv_SIG) mult_cancel_left2 mult_cancel_right2 mult_diff_mult)

lemma T8_25_help2:
  assumes   "(A t) ≠ (B t)" "(A t) ≠ (C t)" "(C t) ≠ (B t)"
           "a = ⟪get_a t⟫" "b=⟪get_b t⟫" "c = ⟪get_c t⟫"
           "alpha = get_alpha t" "beta = get_beta t" "gamma = get_gamma t"
            "beta_a = 1/sqrt(1+a*a)" "beta_b = 1/sqrt(1+b*b)"
          shows "cos(gamma) = (a*a+b*b-c*c-a*a*b*b*c*c)/(2*a*b*(1-c*c))"
proof-
  have "⊖⇩m (get_a t) ⊕⇩m (get_b t) = m_gyr (⊖⇩m (C t)) (B t) (get_c t)"
    by (simp add: Mobius_gyrogroup.gyro_translation_1 get_a_def get_b_def get_c_def)
  moreover have "⟪⊖⇩m (get_a t) ⊕⇩m (get_b t)⟫=⟪get_c t⟫"
    by (simp add: calculation moebius_gyroauto_norm)
  moreover have *:"m_gammma_factor (⊖⇩m (get_a t) ⊕⇩m (get_b t)) = m_gammma_factor (get_c t)"
  proof-
    have "⟪⊖⇩m (get_a t) ⊕⇩m (get_b t)⟫ <1 "
      using norm_lt_one by blast
    then show ?thesis
      by (metis calculation(2) comp_def gamma_factor_def m_gammma_factor_def map_fun_def norm_p.rep_eq)
  qed
  let ?l = "m_gammma_factor (⊖⇩m (get_a t) ⊕⇩m (get_b t))"
  let ?r = "m_gammma_factor (get_c t)"
  have "?l*?l = ?r*?r" using * 
    by presburger
  let ?a = "get_a t"
  let ?b = "get_b t"
  have "?l*?l = (γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b)*(1-2*(inner (to_complex ?a) (to_complex ?b))+⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫)"
    using inner_p.rep_eq m_gamma_equation by presburger
  moreover have "(inner (to_complex ?a) (to_complex ?b)) = a*b*cos(gamma)"
  proof-
    have "gamma = angle (C t) (A t) (B t)"
      using assms(6) get_gamma_def 
      by (simp add: assms(9))
    moreover have "gamma = arccos (inner ((to_complex (⊖⇩m (C t) ⊕⇩m (A t))) /⇩R 
⟪((⊖⇩m (C t) ⊕⇩m (A t)))⟫)  ((to_complex (⊖⇩m (C t) ⊕⇩m (B t))) /⇩R ⟪(⊖⇩m (C t) ⊕⇩m (B t))⟫))"
      using angle_def calculation by blast
   
    moreover have *:"cos(gamma) = (inner ((to_complex ?a) /⇩R 
a) ((to_complex (?b)) /⇩R b))"
      by (smt (verit) Cauchy_Schwarz_ineq2 assms(4) assms(5) calculation(2) cos_arccos_abs get_a_def get_b_def inner_commute inner_real_def inner_zero_right inverse_nonnegative_iff_nonnegative left_inverse norm_geq_zero norm_p.rep_eq norm_scaleR real_inner_1_right)

    moreover have "b≠0" 
      by (metis Mobius_gyrodom.norm_zero_iff Mobius_gyrogroup.gyro_left_cancel' Mobius_gyrogroup.gyro_right_id assms(2) assms(5) get_b_def gyrozero_PoincareDisc_def)
    moreover have "a≠0"
      by (metis Mobius_gyrodom.norm_zero_iff Mobius_gyrogroup.gyro_left_cancel' Mobius_gyrogroup.gyro_right_id assms(3) assms(4) get_a_def gyrozero_PoincareDisc_def)
    moreover have "cos(gamma)*a*b = (inner  (to_complex ?a) (to_complex (?b)))"
      by (simp add: "*" calculation(4) calculation(5) mult.left_commute)
    ultimately show ?thesis
      by (simp add: mult.left_commute)
  qed
  moreover have "(γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b)*(1-2*(inner (to_complex ?a) (to_complex ?b))+⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫)
      = (γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b)*(1-2* a*b*cos(gamma)+⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫)"
    by (simp add: calculation(4))
  moreover have "?r*?r =(γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b)*(1-2* a*b*cos(gamma)+⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫) "
    using "*" calculation(3) calculation(5) by presburger
  moreover have **:"(?r*?r)/((γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b)) = (1-2* a*b*cos(gamma)+⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫)"
   proof-
    have "(γ⇩m ?a) ≠0"
      by (metis gamma_factor_positive linorder_not_le m_gammma_factor.rep_eq norm_lt_one norm_p.rep_eq order.refl)
    moreover have "(γ⇩m ?b) ≠0"
      by (metis gamma_factor_positive linorder_not_le m_gammma_factor.rep_eq norm_lt_one norm_p.rep_eq order.refl)
    ultimately show ?thesis 
      by (simp add: ‹γ⇩m (get_c t) * γ⇩m (get_c t) = γ⇩m (get_a t) * γ⇩m (get_a t) * γ⇩m (get_b t) * γ⇩m (get_b t) * (1 - 2 * a * b * cos gamma + ⟪get_a t⟫ * ⟪get_a t⟫ * ⟪get_b t⟫ * ⟪get_b t⟫)›)
  qed
  moreover have "(?r*?r)/((γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b)) = ((1-⟪?a⟫*⟪?a⟫)*(1-⟪?b⟫*⟪?b⟫))/(1-⟪get_c t⟫*⟪get_c t⟫)"
  proof-
    have "(γ⇩m ?a)*(γ⇩m ?a) = 1/(1-⟪?a⟫*⟪?a⟫)"
      by (metis gamma_factor_square_norm m_gammma_factor.rep_eq norm_lt_one norm_p.rep_eq power2_eq_square)
    moreover have "(γ⇩m ?b)*(γ⇩m ?b) = 1/(1-⟪?b⟫*⟪?b⟫)"
      by (metis gamma_factor_square_norm m_gammma_factor.rep_eq norm_lt_one norm_p.rep_eq power2_eq_square)
    moreover have "?r*?r = 1/(1-⟪get_c t⟫*⟪get_c t⟫)"
      by (metis gamma_factor_square_norm m_gammma_factor.rep_eq norm_lt_one norm_p.rep_eq power2_eq_square)
    ultimately show ?thesis
      by simp
  qed
  moreover have "(1+⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫ -(?r*?r)/((γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b)))/(2*a*b) = cos(gamma)"
  proof-
    have "a≠0"
      by (metis Mobius_gyrodom.norm_zero_iff Mobius_gyrogroup.gyro_left_cancel' Mobius_gyrogroup.gyro_right_id assms(3) assms(4) get_a_def gyrozero_PoincareDisc_def)
    moreover have "b≠0"
      by (metis Mobius_gyrodom.norm_zero_iff Mobius_gyrogroup.gyro_left_cancel' Mobius_gyrogroup.gyro_right_id assms(2) assms(5) get_b_def gyrozero_PoincareDisc_def)
    ultimately show ?thesis 
      using **
      by force
  qed
  moreover have "(1+⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫ -(?r*?r)/((γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b))) =  (a*a+b*b-c*c-a*a*b*b*c*c)/(1-c*c)"
  proof-
    have "(1+⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫ -(?r*?r)/((γ⇩m ?a)*(γ⇩m ?a)*(γ⇩m ?b)*(γ⇩m ?b))) =
    1 + ⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫ - ((1-⟪?a⟫*⟪?a⟫)*(1-⟪?b⟫*⟪?b⟫))/(1-⟪get_c t⟫*⟪get_c t⟫)"
      using calculation(8) by presburger
    moreover have "1 + ⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫ - ((1-⟪?a⟫*⟪?a⟫)*(1-⟪?b⟫*⟪?b⟫))/(1-⟪get_c t⟫*⟪get_c t⟫) =
      ( (1 + ⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫)* (1-⟪get_c t⟫*⟪get_c t⟫)-(1-⟪?a⟫*⟪?a⟫)*(1-⟪?b⟫*⟪?b⟫))/(1-⟪get_c t⟫*⟪get_c t⟫) "
      by (smt (verit, ccfv_SIG) Mobius_gyrodom.norm_inner diff_divide_distrib nonzero_mult_div_cancel_right norm_lt_one power2_eq_square real_sqrt_one square_norm_inner)
    moreover have " ( (1 + ⟪?a⟫*⟪?a⟫*⟪?b⟫*⟪?b⟫)* (1-⟪get_c t⟫*⟪get_c t⟫)-(1-⟪?a⟫*⟪?a⟫)*(1-⟪?b⟫*⟪?b⟫)) =
        ((1+a*a*b*b)*(1-c*c) - (1-a*a)*(1-b*b))"
      using assms(4) assms(5) assms(6) by fastforce
    moreover have "((1+a*a*b*b)*(1-c*c) - (1-a*a)*(1-b*b)) = (a*a+b*b-c*c-a*a*b*b*c*c)"
    proof-
      have "(1+a*a*b*b)*(1-c*c) = 1 - c*c +a*a*b*b -a*a*b*b*c*c"
      proof-
        let ?iz1 = "a*a*b*b"
        let ?iz2 = "-c*c"
        have "Re(a*a*b*b) = a*a*b*b"
          using Re_complex_of_real by blast
        moreover have "Re(-c*c) = -c*c"
          using Re_complex_of_real by blast
        ultimately show ?thesis using help1[of ?iz1 ?iz2] 
          by auto
      qed
      moreover have "(1-a*a)*(1-b*b) = 1-a*a+a*a*b*b - b*b"
       proof-
        let ?iz1 = "-a*a"
        let ?iz2 = "-b*b"
        have "Re(-a*a) = -a*a"
          using Re_complex_of_real by blast
        moreover have "Re(-b*b) = -b*b"
          using Re_complex_of_real by blast
        ultimately show ?thesis using help1[of ?iz1 ?iz2] 
          by auto
      qed
      ultimately show ?thesis 
        by fastforce
    qed
    ultimately show ?thesis 
      by (simp add: assms(6))
  qed
    ultimately show ?thesis
      by (metis (mono_tags, lifting) divide_divide_eq_left')
qed   

lemma T8_25_help3:
  assumes   "(A t) ≠ (B t)" "(A t) ≠ (C t)" "(C t) ≠ (B t)"
           "a = ⟪get_a t⟫" "b=⟪get_b t⟫" "c = ⟪get_c t⟫"
           "alpha = get_alpha t" "beta = get_beta t" "gamma = get_gamma t"
            "beta_a = 1/sqrt(1+a*a)" "beta_b = 1/sqrt(1+b*b)"
          shows "2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma) = (a*a+b*b-c*c-a*a*b*b*c*c)/((1+a*a)*(1+b*b)*(1-c*c))"
proof-
  have "cos(gamma) = (a*a+b*b-c*c-a*a*b*b*c*c)/(2*a*b*(1-c*c))"
    using T8_25_help2[OF assms] by auto
  moreover have "beta_a*beta_a = 1/(1+a*a)"
    by (simp add: assms(10))
   moreover have "beta_b*beta_b = 1/(1+b*b)"
     by (simp add: assms(11))
   moreover have "beta_a*beta_a*beta_b*beta_b = 1/((1+a*a)*(1+b*b))"
     by (simp add: calculation(2) calculation(3))
   moreover have "beta_a*beta_a*beta_b*beta_b*cos(gamma) = (a*a+b*b-c*c-a*a*b*b*c*c)/(2*a*b*(1-c*c)*(1+a*a)*(1+b*b))"
     using calculation(1) calculation(4) by auto
   moreover have "beta_a*beta_a*beta_b*beta_b*cos(gamma)*2*a*b = (a*a+b*b-c*c-a*a*b*b*c*c)/((1-c*c)*(1+a*a)*(1+b*b))"
   proof-
     have "a≠0" 
       by (metis Mobius_gyrodom.norm_zero_iff Mobius_gyrogroup.gyro_left_cancel' Mobius_gyrogroup.gyro_right_id assms(3) assms(4) get_a_def gyrozero_PoincareDisc_def)
     moreover have "b≠0"
       by (metis Mobius_gyrodom.norm_zero_iff Mobius_gyrogroup.gyro_left_cancel' Mobius_gyrogroup.gyro_right_id assms(2) assms(5) get_b_def gyrozero_PoincareDisc_def)
     moreover have "(a*a+b*b-c*c-a*a*b*b*c*c)/(2*a*b*(1-c*c)*(1+a*a)*(1+b*b)) = (1/(2*a*b))*  ((a*a+b*b-c*c-a*a*b*b*c*c)/((1-c*c)*(1+a*a)*(1+b*b)))"
       by auto
     moreover have "2*a*b * ((a*a+b*b-c*c-a*a*b*b*c*c)/(2*a*b*(1-c*c)*(1+a*a)*(1+b*b))) = (2*a*b)*(1/(2*a*b))*  ((a*a+b*b-c*c-a*a*b*b*c*c)/((1-c*c)*(1+a*a)*(1+b*b)))"
       by simp
     moreover have "(2*a*b)*(1/(2*a*b)) = 1"
       using calculation(1) calculation(2) by force
       ultimately show ?thesis 
         by (metis (mono_tags, opaque_lifting) ‹beta_a * beta_a * beta_b * beta_b * cos gamma = (a * a + b * b - c * c - a * a * b * b * c * c) / (2 * a * b * (1 - c * c) * (1 + a * a) * (1 + b * b))› comm_monoid_mult_class.mult_1 mult.commute mult.left_commute)
     qed

   ultimately show ?thesis 
     by (metis (mono_tags, opaque_lifting) mult.commute mult.left_commute)
 qed

lemma dist_real0:
  fixes a::real
  fixes b::real
  shows "(1+a)*(1+b) = 1+a*b + a+ b"
  by (smt (verit, best) mult_cancel_left1 mult_cancel_right2 mult_diff_mult)
lemma dist_real:
  fixes a::real
  fixes b::real
  shows "(1+a*a)*(1+b*b) = (1+b*b+a*a+a*a*b*b)"
  by (simp add: dist_real0)

lemma dist_real1:
  fixes a::real
  fixes b::real
  shows "(1+a)*(1-b) = 1-a*b + a- b"
  by (metis add_uminus_conv_diff dist_real0 mult_minus_right)

lemma T8_25_help4:
  assumes   "(A t) ≠ (B t)" "(A t) ≠ (C t)" "(C t) ≠ (B t)"
           "a = ⟪get_a t⟫" "b=⟪get_b t⟫" "c = ⟪get_c t⟫"
           "alpha = get_alpha t" "beta = get_beta t" "gamma = get_gamma t"
            "beta_a = 1/sqrt(1+a*a)" "beta_b = 1/sqrt(1+b*b)"
          shows "1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma) =   ( 1+a*a*b*b -a*a*c*c - b*b*c*c )/((1+a*a)*(1+b*b)*(1-c*c))"
proof-
  have "2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma) = (a*a+b*b-c*c-a*a*b*b*c*c)/((1+a*a)*(1+b*b)*(1-c*c))"
    using T8_25_help3 assms by blast
  moreover have "1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma) = 1- (a*a+b*b-c*c-a*a*b*b*c*c)/((1+a*a)*(1+b*b)*(1-c*c))"
    using calculation by presburger
  moreover have "1- (a*a+b*b-c*c-a*a*b*b*c*c)/((1+a*a)*(1+b*b)*(1-c*c)) =((1+a*a)*(1+b*b)*(1-c*c)- (a*a+b*b-c*c-a*a*b*b*c*c))/((1+a*a)*(1+b*b)*(1-c*c))"
  proof-
    have "1+a*a≠0" 
      by (smt (verit, ccfv_SIG) zero_le_square)
    moreover have "1+b*b ≠0" 
      by (smt (verit, ccfv_SIG) zero_le_square)
    moreover have "1-c*c≠0"
      by (metis abs_norm_cancel assms(6) eq_iff_diff_eq_0 norm_lt_one norm_p.rep_eq order_less_irrefl real_sqrt_abs2 real_sqrt_one)
    moreover have "(1+a*a)*(1+b*b)*(1-c*c)≠0"
      using calculation(1) calculation(2) calculation(3) by auto
    moreover have "1- (a*a+b*b-c*c-a*a*b*b*c*c)/((1+a*a)*(1+b*b)*(1-c*c)) =((1+a*a)*(1+b*b)*(1-c*c))/((1+a*a)*(1+b*b)*(1-c*c)) - (a*a+b*b-c*c-a*a*b*b*c*c)/((1+a*a)*(1+b*b)*(1-c*c))"
      using calculation(4) by force
    ultimately show ?thesis 
      by (simp add: diff_divide_distrib)
  qed
 
  moreover have "(1+a*a)*(1+b*b)*(1-c*c) = 1 +a*a+b*b+a*a*b*b -c*c -a*a*c*c -b*b*c*c -a*a*b*b*c*c"
  proof-
      have "(1+a*a)*(1+b*b) = (1+b*b+a*a+a*a*b*b)"
        
        using dist_real by blast
      moreover have "(1+b*b+a*a+a*a*b*b)*(1-c*c) =  1 +a*a+b*b+a*a*b*b -c*c -a*a*c*c -b*b*c*c -a*a*b*b*c*c"
      proof-
        have " (1+b*b+a*a+a*a*b*b)*(1-c*c) = 1 - c*c + b*b+a*a+a*a*b*b - c*c*(b*b+a*a+a*a*b*b)"
          by (smt (verit, del_insts) dist_real1 mult.commute)
        let ?c = "c*c"
        let ?b = "b*b"
        let ?a = "a*a+a*a*b*b"
      have " c*c*(b*b+a*a+a*a*b*b) = c*c*b*b + c*c*a*a + c*c*a*a*b*b"
          using distrib_left[of ?c ?b ?a]
          by (simp add: distrib_left)
          
        then  show ?thesis 
          using ‹(1 + b * b + a * a + a * a * b * b) * (1 - c * c) = 1 - c * c + b * b + a * a + a * a * b * b - c * c * (b * b + a * a + a * a * b * b)› ‹c * c * (b * b + a * a + a * a * b * b) = c * c * b * b + c * c * a * a + c * c * a * a * b * b› by auto
      qed
      ultimately show ?thesis 
        by presburger
    qed
  ultimately show ?thesis by auto
qed

lemma T25_help5:
    assumes   "(A t) ≠ (B t)" "(A t) ≠ (C t)" "(C t) ≠ (B t)"
           "a = ⟪get_a t⟫" "b=⟪get_b t⟫" "c = ⟪get_c t⟫"
           "alpha = get_alpha t" "beta = get_beta t" "gamma = get_gamma t"
            "beta_a = 1/sqrt(1+a*a)" "beta_b = 1/sqrt(1+b*b)"
          shows "(2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))/
( 1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma)) = to_complex ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)) ⊕⇩m (⊖⇩m (of_complex (cor c*c))))"
proof-
  have "to_complex ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)) ⊕⇩m (⊖⇩m (of_complex (cor c*c)))) =
            (a*a+b*b-c*c-a*a*b*b*c*c)/(1+a*a*b*b - a*a*c*c - b*b*c*c)"
    by (metis (mono_tags, opaque_lifting) T8_25_help1 ab_semigroup_mult_class.mult_ac(1) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) of_real_mult)
  moreover have "(1+a*a)≠0"
    by (metis le_add_same_cancel1 not_one_le_zero zero_le_square)
  moreover have "(1+b*b)≠0"
    by (metis add_le_same_cancel2 not_one_le_zero zero_le_square)
  moreover have "(1-c*c)≠0"
    by (metis Mobius_gyrodom.norm_inner assms(6) eq_iff_diff_eq_0 norm_lt_one order_less_irrefl power2_eq_square real_sqrt_one square_norm_inner)
  moreover have *:"(1+a*a)*(1+b*b)*(1-c*c) ≠0"
    using calculation(2) calculation(3) calculation(4) divisors_zero by blast
  let ?iz = "(1+a*a)*(1+b*b)*(1-c*c)"
  have "(2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))/
( 1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma)) = ((a * a + b * b - c * c - a * a * b * b * c * c)/?iz)/
((1 + a * a * b * b - a * a * c * c - b * b * c * c)/?iz)"
  proof-
    have "(2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma)) = ((a * a + b * b - c * c - a * a * b * b * c * c)/?iz)"
      using T8_25_help3 assms by blast
    moreover have "( 1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma)) =((1 + a * a * b * b - a * a * c * c - b * b * c * c)/?iz)"
      using T8_25_help4 assms by blast
    ultimately show ?thesis 
      by presburger
  qed
  moreover have "(2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))/
( 1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma)) = (a * a + b * b - c * c - a * a * b * b * c * c)/(1 + a * a * b * b - a * a * c * c - b * b * c * c)"
    using "*" calculation(5) by auto
  ultimately show ?thesis
  proof -
    have "cor (2 * beta_a * beta_a * a * beta_b * beta_b * b * cos gamma) / (1 - cor (2 * beta_a * beta_a * a * beta_b * beta_b * b * cos gamma)) = to_complex (of_complex (cor (a * a)) ⊕⇩m of_complex (cor (b * b)) ⊕⇩m ⊖⇩m (of_complex (cor (c * c))))"
      by (smt (z3) ‹2 * beta_a * beta_a * a * beta_b * beta_b * b * cos gamma / (1 - 2 * beta_a * beta_a * a * beta_b * beta_b * b * cos gamma) = (a * a + b * b - c * c - a * a * b * b * c * c) / (1 + a * a * b * b - a * a * c * c - b * b * c * c)› ‹to_complex (of_complex (cor a * cor a) ⊕⇩m of_complex (cor b * cor b) ⊕⇩m ⊖⇩m (of_complex (cor c * cor c))) = cor ((a * a + b * b - c * c - a * a * b * b * c * c) / (1 + a * a * b * b - a * a * c * c - b * b * c * c))› of_real_1 of_real_diff of_real_divide of_real_mult)
    then show ?thesis
      by (simp add: cos_of_real)
  qed
qed


lemma T25_MobiusCosineLaw:
  assumes "(A t) ≠ (B t)" "(A t) ≠ (C t)" "(C t) ≠ (B t)"
           "a = ⟪get_a t⟫" "b=⟪get_b t⟫" "c = ⟪get_c t⟫"
           "alpha = get_alpha t" "beta = get_beta t" "gamma = get_gamma t"
            "beta_a = 1/sqrt(1+a*a)" "beta_b = 1/sqrt(1+b*b)"
          shows "c*c =  to_complex ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)) ⊕⇩m (⊖⇩m (of_complex (cor (2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))/
( 1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))))))"
proof-
  have  "(2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))/
( 1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma)) = to_complex ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)) ⊕⇩m (⊖⇩m (of_complex (cor c*c))))"
     using T25_help5[OF assms]
     by (simp add: cos_of_real)
   moreover have "norm ((2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))/
( 1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))) < 1"
     by (metis calculation norm_lt_one norm_of_real norm_p.rep_eq real_norm_def)
   moreover have "norm (cor a*a) < 1"
     by (simp add: assms(4) mult_closed_for_unit_disc norm_geq_zero norm_lt_one)
   moreover have "norm (cor b*b) < 1"
     by (metis abs_norm_cancel assms(5) linorder_not_le norm_lt_one norm_mult norm_of_real norm_p.rep_eq real_sqrt_abs2 real_sqrt_ge_one)
   moreover have "norm (cor c*c)<1"
     by (simp add: assms(6) mult_closed_for_unit_disc norm_geq_zero norm_lt_one)
   moreover have "Re (cor a*a) = a*a"
     by force
   moreover have "Re (cor b*b) = b*b"
     by force
   moreover have "Re (cor c*c) = c*c"
     by force
   moreover have "c*c = to_complex ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)) ⊕⇩m (⊖⇩m ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)) ⊕⇩m (⊖⇩m (of_complex (cor c*c))))))"
     by (metis Mobius_gyrocommutative_gyrogroup.gyroautomorphic_inverse Mobius_gyrodom'.to_dom Mobius_gyrogroup.gyro_inv_idem Mobius_gyrogroup.gyrominus_def Mobius_gyrogroup.oplus_ominus_cancel calculation(5) of_real_mult)
   moreover have "c*c = to_complex ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)) ⊕⇩m ( (⊖⇩m(of_complex (cor a*a)))⊕⇩m  ⊖⇩m (of_complex (cor b*b)) ⊕⇩m (of_complex (cor c*c))))"
     using Mobius_gyrocommutative_gyrogroup.gyroautomorphic_inverse Mobius_gyrogroup.gyrominus_def calculation(9) by auto 
   ultimately show ?thesis
   proof -
     have f1: "cor (2 * beta_a * beta_a * a * beta_b * beta_b * b * cos gamma / (1 - 2 * beta_a * beta_a * a * beta_b * beta_b * b * cos gamma)) = to_complex (of_complex (cor (a * a)) ⊕⇩m of_complex (cor (b * b)) ⊕⇩m ⊖⇩m (of_complex (cor (c * c))))"
       using ‹cor (2 * beta_a * beta_a * a * beta_b * beta_b * b * cos gamma / (1 - 2 * beta_a * beta_a * a * beta_b * beta_b * b * cos gamma)) = to_complex (of_complex (cor a * cor a) ⊕⇩m of_complex (cor b * cor b) ⊕⇩m ⊖⇩m (of_complex (cor c * cor c)))› by auto
     have "to_complex (of_complex (cor (a * a)) ⊕⇩m of_complex (cor (b * b)) ⊕⇩m ⊖⇩m (of_complex (cor (a * a)) ⊕⇩m of_complex (cor (b * b)) ⊕⇩m ⊖⇩m (of_complex (cor (c * c))))) = cor (c * c)"
       using ‹cor (c * c) = to_complex (of_complex (cor a * cor a) ⊕⇩m of_complex (cor b * cor b) ⊕⇩m ⊖⇩m (of_complex (cor a * cor a) ⊕⇩m of_complex (cor b * cor b) ⊕⇩m ⊖⇩m (of_complex (cor c * cor c))))› by auto
     then show ?thesis
       using f1 by (simp add: Mobius_gyrodom'.of_dom cos_of_real)
   qed
 qed

lemma T_MobiusPythagorean:
  assumes "(A t) ≠ (B t)" "(A t) ≠ (C t)" "(C t) ≠ (B t)"
           "a = ⟪get_a t⟫" "b=⟪get_b t⟫" "c = ⟪get_c t⟫"
           "alpha = get_alpha t" "beta = get_beta t" "gamma = get_gamma t"
            "beta_a = 1/sqrt(1+a*a)" "beta_b = 1/sqrt(1+b*b)"
           "gamma = pi/2"
          shows "c*c =  to_complex ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)))"
proof-
  have "c*c =  to_complex ((of_complex (cor a*a)) ⊕⇩m (of_complex (cor b*b)) ⊕⇩m (⊖⇩m (of_complex (cor (2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))/
( 1-2*beta_a*beta_a*a*beta_b*beta_b*b*cos(gamma))))))"
    using T25_MobiusCosineLaw[OF assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) assms(10) assms(11)]
    by (simp add: cos_of_real)
  moreover have "cos(gamma) = 0"
    using assms(12) cos_pi_half by blast
  ultimately show ?thesis 
    using m_ozero'_def m_ozero_def by force 
qed

end
