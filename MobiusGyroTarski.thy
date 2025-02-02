theory MobiusGyroTarski
imports MobiusGeometry TarskiIsomorphism Poincare_Disc.Poincare_Tarski
begin

text ‹This theory depends on the following AFP entries:

https://www.isa-afp.org/entries/Poincare_Disc.html
https://www.isa-afp.org/entries/Complex_Geometry.html

They must be downloaded in order to check this theory.
›

(* -------------------------------------------------------------- *)
text ‹The following lemmas can be moved to the cited AFP entries.›


lemma eqArgLessCmod:
  assumes "u ≠ 0" "v ≠ 0"
  shows "Arg u = Arg v ∧ cmod u ≤ cmod v ⟷ (∃k. k ≥ 0 ∧ k ≤ 1 ∧ u = cor k * v)"
proof 
  assume "Arg u = Arg v ∧ cmod u ≤ cmod v"
  then show "∃k. k ≥ 0 ∧ k ≤ 1 ∧ u = cor k * v"
    using cmod_cis[OF ‹u ≠ 0›] cmod_cis[OF ‹v ≠ 0›] assms
    by (rule_tac x="cmod u / cmod v" in exI)
       (smt (verit, ccfv_threshold) divide_le_eq_1_pos divide_nonneg_nonneg mult.assoc mult_cancel_right2 nonzero_eq_divide_eq norm_ge_zero of_real_divide of_real_eq_1_iff)
next
  assume "(∃k. k ≥ 0 ∧ k ≤ 1 ∧ u = cor k * v)"
  then show "Arg u = Arg v ∧ cmod u ≤ cmod v"
    by (metis abs_of_nonneg arg_mult_real_positive assms(1) mult.commute mult_eq_0_iff mult_left_le norm_ge_zero norm_mult norm_of_real zero_less_norm_iff)
qed

(* -------------------------------------------------------------- *)

lift_definition p_blaschke :: "p_point ⇒ p_isometry" is "λ a. (moebius_pt (blaschke (to_complex a)))"
  by (metis blaschke_unit_disc_fix inf_notin_unit_disc of_complex_to_complex unit_disc_fix_f_moebius_pt unit_disc_iff_cmod_lt_1)

lemma p_between_p_isometry_pt [simp]:
  shows "p_between (p_isometry_pt f a) (p_isometry_pt f b) (p_isometry_pt f c)  ⟷ p_between a b c"
  by transfer (auto simp add: unit_disc_fix_f_def)

lemma p_blaschke_id [simp]:
  shows "p_isometry_pt (p_blaschke x) x = p_zero"
  by transfer (metis blaschke_a_to_zero inversion_infty inversion_noteq_unit_disc less_irrefl of_complex_to_complex unit_disc_iff_cmod_lt_1 zero_in_unit_disc)

lemma p_between_0uv:
  shows "p_between p_zero u v ⟷ 
        (∃k≥0. k ≤ 1 ∧ to_complex (Rep_p_point u) = cor k * to_complex (Rep_p_point v))"
proof transfer
  fix u v
  assume uv: "u ∈ unit_disc" "v ∈ unit_disc"
  then show "poincare_between 0⇩h u v =
             (∃k≥0. k ≤ 1 ∧ to_complex u = cor k * to_complex v)"
  proof (cases "u = 0⇩h ∨ v = 0⇩h")
    case True
    then show ?thesis
      by (metis dual_order.refl inf_notin_unit_disc linordered_nonzero_semiring_class.zero_le_one mult_cancel_left1 mult_zero_class.mult_zero_right of_complex_to_complex of_complex_zero of_real_0 poincare_between_nonstrict(1) poincare_between_sandwich to_complex_zero_zero uv(1) zero_in_unit_disc)
  next
    case False
    then have z: "u ≠ 0⇩h" "v ≠ 0⇩h"
      by auto
    let ?u = "to_complex u" and ?v = "to_complex v"
    have "poincare_between 0⇩h u v ⟷ Arg ?u = Arg ?v ∧ cmod ?u ≤ cmod ?v"
      using poincare_between_0uv[OF uv z]
      by (auto simp add: Let_def)
    also have "… ⟷ (∃k≥0. k ≤ 1 ∧ ?u = cor k * ?v)"
      by (metis False eqArgLessCmod to_complex_zero_zero unit_disc_to_complex_inj uv(1) uv(2) zero_in_unit_disc)
    finally show ?thesis
      .
  qed
qed

(* -------------------------------------------------------------- *)
text ‹A bijection between AFP type representing the Poincare disc (based on complex homogenous coordinates) 
and our type for poincare disc (based on ordinary complex numbers) ›

lift_definition φ :: "p_point ⇒ PoincareDisc" is to_complex
  by (metis inf_notin_unit_disc of_complex_to_complex unit_disc_iff_cmod_lt_1)

lemma distance_m_p_dist:
  shows "distance_m (PoincareDisc.to_complex (φ x)) (PoincareDisc.to_complex (φ y)) = p_dist x y"
  unfolding φ.rep_eq
proof transfer
  fix x y
  assume "x ∈ unit_disc" "y ∈ unit_disc"
  then show "distance_m (Homogeneous_Coordinates.to_complex x) (Homogeneous_Coordinates.to_complex y) =
        poincare_distance x y"
    by (simp add: distance_m_def poincare_distance_formula)
qed

definition blaschke' :: "complex ⇒ complex ⇒ complex" where
  "blaschke' a z = (z - a) / (1 - cnj a * z)"

lemma blaschke'_translation:
  fixes a z :: complex
  shows "blaschke' a z = oplus_m' (ominus_m' a) z"
  unfolding blaschke'_def oplus_m'_def ominus_m'_def
  by (simp add: minus_divide_left)

lift_definition blaschke_g :: "PoincareDisc ⇒ PoincareDisc ⇒ PoincareDisc" is blaschke'
  using blaschke'_translation ominus_m'_in_disc oplus_m'_in_disc by presburger

lemma blaschke_translation: 
  "blaschke_g a z = (⊖⇩m a) ⊕⇩m z"
  by transfer (simp add: blaschke'_translation)

text ‹Isomorphism between hyperbolic geometry of Poincare disc defined in AFP entry, and hyperbolic 
geometry in Mobius gyrovector space. Since these two are isomorphic, the geometry of Mobius gyrovector  
space satisfies Tarski axioms. ›

interpretation MobiusGyroTarskiIso: ElementaryTarskiHyperbolicIso p_congruent p_between φ cong⇩m Mobius_pre_gyrovector_space.between
proof
  show "bij φ"
    unfolding bij_def inj_def surj_def
    by transfer (metis inf_notin_unit_disc mem_Collect_eq of_complex_to_complex to_complex_of_complex unit_disc_iff_cmod_lt_1)
next
  fix x y z w
  show "cong⇩m (φ x) (φ y) (φ z) (φ w) ⟷ p_congruent x y z w"
    unfolding cong⇩m_def distance⇩m_equiv p_congruent_def
    by (simp add: distance_m_p_dist)
next
  fix x y z
  show "Mobius_pre_gyrovector_space.between (φ x) (φ y) (φ z) ⟷ p_between x y z"
  proof-
    let ?f = "λ a. ⊖ (φ x) ⊕ a"
    let ?f' = "λ a. p_isometry_pt (p_blaschke x) a"

    have *: "∀ a. PoincareDisc.to_complex (?f (φ a)) = to_complex (Rep_p_point (?f' a))"
      unfolding gyroplus_PoincareDisc_def gyroinv_PoincareDisc_def blaschke_translation[symmetric]
    proof (transfer, safe)
      fix x a
      assume "x ∈ unit_disc" "a ∈ unit_disc"
      then have *: "to_complex (moebius_pt (blaschke (to_complex x)) a) = 
                ((to_complex a - to_complex x) / (1 - cnj (to_complex x) * to_complex a))"
        using moebius_pt_blaschke[of "to_complex x" "to_complex a"]
        by (smt (verit) blaschke_a_to_zero complex_cnj_zero_iff diff_zero div_by_0 div_by_1 inf_notin_unit_disc inversion_noteq_unit_disc inversion_of_complex mult_eq_0_iff of_complex_to_complex to_complex_of_complex to_complex_zero_zero unit_disc_iff_cmod_lt_1)

      show "blaschke' (to_complex x) (to_complex a) = to_complex (moebius_pt (blaschke (to_complex x)) a)"
        unfolding * blaschke'_def
        by simp
    qed

    have "Mobius_pre_gyrovector_space.between (φ x) (φ y) (φ z) ⟷ 
          Mobius_pre_gyrovector_space.between 0⇩m (?f (φ y)) (?f (φ z))"
      by (metis Mobius_pre_gyrovector_space.between_translate Mobius_pre_gyrovector_space.translate_def gyro_left_inv gyrozero_PoincareDisc_def)
    also have "… ⟷ (∃k≥0. k ≤ 1 ∧ PoincareDisc.to_complex (?f (φ y)) = More_Complex.cor k * PoincareDisc.to_complex (?f (φ z)))"
      using mobius_between_0uv
      by simp
    also have "… ⟷ (∃k≥0. k ≤ 1 ∧ to_complex (Rep_p_point (?f' y)) = More_Complex.cor k * to_complex (Rep_p_point (?f' z)))"
      using *
      by auto
    also have "… ⟷ p_between p_zero (?f' y) (?f' z)"
      using p_between_0uv
      by blast
    also have "… ⟷ p_between (?f' x) (?f' y) (?f' z)"
      by simp
    finally show ?thesis
      using p_between_p_isometry_pt by blast
  qed
qed

interpretation MobiusGyroTarski: ElementaryTarskiHyperbolic cong⇩m Mobius_pre_gyrovector_space.between
  by (simp add: MobiusGyroTarskiIso.ElementaryTarskiHyperbolic_axioms)


end
