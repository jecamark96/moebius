theory MobiusCollinear
  imports MobiusGyroVectorSpace 
begin

lemma collinear_0_proportional':
  assumes "v ≠ 0⇩m"
  shows "Mobius_pre_gyrovector_space.collinear x 0⇩m v ⟷ (∃ k::real. to_complex x = k * (to_complex v))"
  unfolding Mobius_pre_gyrovector_space.collinear_def gyroplus_PoincareDisc_def gyroinv_PoincareDisc_def
  using assms
proof transfer
  fix v x
  assume "cmod v < 1" "cmod x < 1" "v ≠ ozero_m'"
  then have "v ≠ 0"
    unfolding ozero_m'_def
    by simp
  have "(∃t. x = (otimes'_k t v) * v / cor (cmod v)) ⟷ (∃k :: real. x = k * v)" (is "?lhs ⟷ ?rhs")
  proof
    assume ?lhs
    then show ?rhs
      by (metis of_real_divide times_divide_eq_left)
  next
    assume ?rhs
    then obtain k::real where "x = k * v"
      by auto

    moreover

    have "abs (k * cmod v) < 1"
      by (metis ‹cmod x < 1› ‹x = cor k * v› abs_mult abs_norm_cancel norm_mult norm_of_real)

    have "artanh (cmod v) ≠ 0"
      using ‹v ≠ 0›
      by (simp add: ‹cmod v < 1› artanh_not_0)
    
    have "∃ t. (otimes'_k t v) / (cmod v) = k"
    proof-
      let ?t = "artanh(k * cmod v) / artanh (cmod v)"
      have "tanh (?t * artanh (cmod v)) = k * cmod v"
        using ‹artanh (cmod v) ≠ 0› tanh_artanh[of "k * cmod v"] ‹abs (k * cmod v) < 1›
        by (simp add: field_simps)
      then show ?thesis
        by (metis ‹cmod v < 1› ‹v ≠ 0› nonzero_mult_div_cancel_right norm_zero otimes'_k_tanh zero_less_norm_iff)
    qed
    ultimately
    show ?lhs
      by auto
  qed
  then show "(ozero_m' = v ∨ (∃t. x = oplus_m' ozero_m' (otimes' t (oplus_m' (ominus_m' ozero_m') v)))) ⟷
        (∃ k::real. x = k * v)"
    using ‹v ≠ 0›
    unfolding oplus_m'_def ozero_m'_def ominus_m'_def otimes'_def
    by simp
qed

lemma
  assumes "v ≠ 0⇩m"
  shows "Mobius_pre_gyrovector_space.collinear x 0⇩m v ⟷ to_complex x * cnj (to_complex v) = cnj (to_complex x) * to_complex v"
  using Mobius_gyrocarrier'.to_carrier_zero_iff assms cnj_mix_ex_real_k collinear_0_proportional' gyrozero_PoincareDisc_def
  by fastforce

lemma collinear_0_proportional:
  shows "Mobius_pre_gyrovector_space.collinear x 0⇩m v ⟷ v = 0⇩m ∨ (∃ k::real. to_complex x = k * (to_complex v))"
  by (metis Mobius_pre_gyrovector_space.collinear_def collinear_0_proportional')

lemma to_complex_0 [simp]:
  shows "to_complex 0⇩m = 0"
  by transfer (simp add: ozero_m'_def)

lemma to_complex_0_iff [iff]:
  shows "to_complex x = 0 ⟷ x = 0⇩m"
  by transfer (simp add: ozero_m'_def)

lemma mobius_between_0xy:
  shows "Mobius_pre_gyrovector_space.between 0⇩m x y ⟷ 
         (∃ k::real. 0 ≤ k ∧ k ≤ 1 ∧ to_complex x = k * to_complex y)"
proof (cases "y = 0⇩m")
  case True
  then show ?thesis
    using Mobius_pre_gyrovector_space.between_xyx[of "0⇩m" x]
    by auto
next
  case False
  then show ?thesis
    unfolding Mobius_pre_gyrovector_space.between_def gyroplus_PoincareDisc_def gyrozero_PoincareDisc_def gyroinv_PoincareDisc_def
  proof (transfer)
    fix x y
    assume "cmod y < 1" "y ≠ ozero_m'" "cmod x < 1"
    then have "y ≠ 0"
      by (simp add: ozero_m'_def)

    have "(∃t≥0. t ≤ 1 ∧ x = cor (otimes'_k t y) * y / cor (cmod y)) =
          (∃k≥0. k ≤ 1 ∧ x = cor k * y)" (is "?lhs = ?rhs")
    proof
      assume ?lhs
      then obtain t where "0 ≤ t" "t ≤ 1" "x = (otimes'_k t y / cmod y) * y"
        by auto
      moreover
      have "0 ≤ otimes'_k t y / cmod y" 
        unfolding otimes'_k_tanh[OF ‹cmod y < 1›]
        using ‹cmod y < 1› ‹t ≥ 0› tanh_artanh_nonneg 
        by auto
      moreover
      have "otimes'_k t y / cmod y ≤ 1"
        unfolding otimes'_k_tanh[OF ‹cmod y < 1›]
        using ‹cmod y < 1› ‹y ≠ 0› artanh_nonneg ‹t ≤ 1›
        by (smt (verit, best) divide_le_eq_1 mult_le_cancel_right2 norm_le_zero_iff strict_mono_less_eq tanh_artanh tanh_real_strict_mono)
      ultimately
      show ?rhs
        by auto
    next
      assume ?rhs
      then obtain k::real where "x = k * y"
        by auto

      moreover

      have "abs (k * cmod y) < 1"
        by (metis ‹cmod x < 1› ‹x = cor k * y› abs_mult abs_norm_cancel norm_mult norm_of_real)

      have "artanh (cmod y) ≠ 0"
        using ‹y ≠ 0›
        by (simp add: ‹cmod y < 1› artanh_not_0)
    
      have "∃ t. 0 ≤ t ∧ t ≤ 1 ∧ (otimes'_k t y) / (cmod y) = k"
      proof-
        let ?t = "artanh(k * cmod y) / artanh (cmod y)"
        have "tanh (?t * artanh (cmod y)) = k * cmod y"
          using ‹artanh (cmod y) ≠ 0› tanh_artanh[of "k * cmod y"] ‹abs (k * cmod y) < 1›
          by (simp add: field_simps)
        moreover
        have "?t ≥ 0"
          using ‹∃k≥0. k ≤ 1 ∧ x = cor k * y› ‹cmod y < 1› ‹x = cor k * y› ‹y ≠ 0›
          by (smt (verit, ccfv_SIG)  artanh_nonneg calculation divide_eq_0_iff mult_right_cancel norm_le_zero_iff of_real_eq_iff tanh_real_nonneg_iff zero_le_mult_iff)
        moreover
        have "?t ≤ 1"
          using ‹∃k≥0. k ≤ 1 ∧ x = cor k * y› ‹cmod y < 1› ‹x = cor k * y› ‹y ≠ 0›
          by (smt (verit, ccfv_SIG)  artanh_monotone artanh_nonneg calculation(1) less_divide_eq_1 nonzero_divide_eq_eq of_real_eq_iff tanh_artanh_nonneg zero_less_norm_iff)
        ultimately show ?thesis
          by (metis ‹cmod y < 1› ‹y ≠ 0› nonzero_mult_div_cancel_right norm_zero otimes'_k_tanh zero_less_norm_iff)
      qed
      ultimately
      show ?lhs
        by auto
    qed
    then show "(∃t≥0. t ≤ 1 ∧
                       x = oplus_m' ozero_m' (otimes' t (oplus_m' (ominus_m' ozero_m') y))) =
               (∃k≥0. k ≤ 1 ∧ x = cor k * y)"
      using ‹y ≠ 0›
      unfolding ozero_m'_def oplus_m'_def ominus_m'_def otimes'_def
      by simp
  qed
qed

end
