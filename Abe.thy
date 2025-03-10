theory Abe
  imports GyroGroup "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces VectorSpace
begin



locale one_dim_vector_space_with_domain =
  vector_space_with_domain + 
  assumes "∀y. ∀x. (y∈ dom ∧
 x∈ dom ∧ x≠zero ⟶ (∃!r::real. y = smult r x))"
  
locale GGV = 
  fixes fi ::"'a::gyrocommutative_gyrogroup ⇒ 'b::real_inner"
  fixes scale ::"real ⇒ 'a ⇒ 'a"
  fixes plus'::"real ⇒ real ⇒ real"
  fixes smult'::"real ⇒ real ⇒ real"
  (*fixes zero'::"real"*)
  assumes "inj fi"
  assumes "norm (fi (gyr u v a)) = norm (fi a)"
  assumes "scale 1 a = a"
  assumes "scale (r1+r2) a = (scale r1 a) ⊕ (scale r2 a)"
  assumes "scale (r1*r2) a = scale r1 (scale r2 a)"
  assumes "(a≠gyrozero ∧ r≠0)⟶ (fi (scale ¦r¦ a)) /⇩R (norm (fi (scale r a))) = (fi a) /⇩R (norm (fi a))"
  assumes "gyr u v (scale r a) = scale r (gyr u v a)"
  assumes "gyr (scale r1 v) (scale r2 v) = id"
  assumes "vector_space_with_domain {x.∃a. x = norm (fi a) ∨ x = - norm (fi a)} plus' 0 smult'"
  assumes "norm (fi (scale r a)) = smult' ¦r¦ (norm (fi a))"
  assumes "norm (fi (a ⊕ b)) = plus' (norm (fi a)) (norm (fi b))"
begin
  
end

class gyrolinear_space = 
  gyrocommutative_gyrogroup +
  fixes scale :: "real ⇒ 'a::gyrocommutative_gyrogroup  ⇒ 'a" (infixl "⊗" 105) 
  assumes scale_1: "⋀ a :: 'a. 1 ⊗ a = a"
  assumes scale_distrib: "⋀ (r1 :: real) (r2 :: real) (a :: 'a). (r1 + r2) ⊗ a = r1 ⊗ a ⊕ r2 ⊗ a"
  assumes scale_assoc: "⋀ (r1 :: real) (r2 :: real) (a :: 'a). (r1 * r2) ⊗ a = r1 ⊗ (r2 ⊗ a)"
  assumes gyroauto_property: "⋀ (u :: 'a) (v :: 'a) (r :: real) (a :: 'a). gyr u v (r ⊗ a) = r ⊗ (gyr u v a)"
  assumes gyroauto_id: "⋀ (r1 :: real) (r2 :: real) (v :: 'a). gyr (r1 ⊗ v) (r2 ⊗ v) = id"
  
begin

end

locale normed_gyrolinear_space = 
  fixes norm'::"'a::gyrolinear_space ⇒ real"
  fixes f::"real ⇒ real"
  assumes "∀a::'a. (norm' a ≥ 0)"
  assumes "∀y::real. (y∈ (norm' ` UNIV) ⟶ (f y) ≥ 0)"
  assumes "bij_betw f (norm' ` UNIV) {x::real. x≥0}"
  assumes "∀y::real. ∀z::real. (( y∈ norm' ` UNIV ∧
z∈ norm' ` UNIV ∧ y>z)⟶ (f y) > (f z))"

  assumes "∀x::'a. ∀y::'a. f(norm' (gyroplus x y)) ≤ (f (norm' x)) + (f (norm' y))"
  assumes "f (norm' (scale r x)) = ¦r¦ * (f (norm' x))"
  assumes "norm' (gyr u v x) = norm' x"
  assumes "∀x::'a. ((norm' x) = 0 ⟷ x = gyrozero)"
begin
  
definition norms::"real set" where 
  "norms = norm' ` UNIV"

definition norms_neg::"real set" where 
  "norms_neg = (λx. -1 * norm' x) ` UNIV"

definition norms_all::"real set" where 
  "norms_all = norms ∪ norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg ≠ {}"
  using add.inverse_inverse norms_neg_def by fastforce


lemma zero_only_norms_norms_neg:
  assumes "x∈norms" "x∈norms_neg"
  shows "x=0"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) f_inv_into_f normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def norms_neg_def)


lemma a1_a2:
  shows "∃f':: real ⇒ real. ((∀x::real. ∀y::real. ( x∈norms_all ∧ y ∈norms_all ∧ x>y)⟶ (f' x) > (f' y))
 ∧ (f' 0) = 0 ∧ bij_betw f' norms_all UNIV)"  
proof-
  let ?f' = "λx. if x=0 then 0 else if (x ∈ norms) then (f x) else if (x∈ norms_neg) then - (f (-x)) else undefined" 
  have fact3: "?f' 0 = 0"
    by auto
  moreover have fact1: "(∀x::real. ∀y::real. ( x∈norms_all ∧ y ∈norms_all ∧ x>y)⟶ (?f' x) > (?f' y))"
  proof-
    {fix x y 
    assume "x∈norms_all ∧ y ∈norms_all ∧ x>y"
    have "(?f' x) > (?f' y)"
    proof-
      have "x=0 ∨ x≠0" by blast
      moreover {
        assume "x=0"
        then have ?thesis 
          by (smt (verit, del_insts) Un_def ‹x ∈ norms_all ∧ y ∈ norms_all ∧ y < x› f_inv_into_f mem_Collect_eq normed_gyrolinear_space.norms_neg_def normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_all_def norms_def rangeI)
          
      }
      moreover {
        assume "x≠0"
        have "x∈norms ∨ x∈norms_neg"
          using ‹x ∈ norms_all ∧ y ∈ norms_all ∧ y < x› norms_all_def by force
        moreover {
          assume "x∈norms"
          then have "y=0∨ y≠0"
            by blast
          moreover {
            assume "y=0"
            then have ?thesis 
              by (smt (z3) ‹x ∈ norms› ‹x ∈ norms_all ∧ y ∈ norms_all ∧ y < x› normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def rangeI)
          } moreover {
            assume "y≠0"
            have "y∈norms ∨ y∈norms_neg"
              using ‹x ∈ norms_all ∧ y ∈ norms_all ∧ y < x› norms_all_def by auto
            moreover {
              assume "y∈norms"
              then have ?thesis 
                by (smt (z3) ‹x ∈ norms› ‹x ∈ norms_all ∧ y ∈ norms_all ∧ y < x› ‹x ≠ 0› normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def)
                
            } moreover {
              assume "y∈norms_neg"
              then have "?f' y = - (f (-y))"
                using ‹y ≠ 0› zero_only_norms_norms_neg by fastforce
              moreover have "-y ∈ norms"
                using ‹y ∈ norms_neg› norms_def norms_neg_def by force
              moreover have "?f' y ≤ 0"
     
                by (smt (verit, ccfv_threshold) calculation(1) calculation(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def)
                
              moreover have "?f' y ≠0"
              proof(rule ccontr)
                assume "¬(?f' y ≠ 0)"
                then show False 
                  by (smt (verit, del_insts) ‹y ≠ 0› calculation(1) calculation(2) f_inv_into_f normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def rangeI)
              qed
              ultimately have ?thesis 
                by (smt (z3) ‹x ∈ norms› normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def) 
            }
            ultimately have ?thesis by blast
            }
            ultimately have ?thesis by blast
          } moreover {
            assume "x∈norms_neg"
            then have ?thesis 
              by (smt (verit, del_insts) Un_def ‹x ∈ norms_all ∧ y ∈ norms_all ∧ y < x› f_inv_into_f mem_Collect_eq normed_gyrolinear_space.norms_neg_def normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_all_def norms_def rangeI)

        }
        ultimately have ?thesis by blast
      } ultimately show ?thesis by blast
    qed
  }
  then show ?thesis by blast
qed
  moreover have fact2: " bij_betw ?f' norms_all UNIV"
  proof-
    have *:"∀x. ∀y. (x∈norms_all ∧ y∈norms_all ∧ (?f' x) = (?f' y)) ⟶ x = y"
      by (smt (verit, ccfv_threshold) calculation(2))
    moreover have **:"∀x::real. ∃y. (y∈ norms_all ∧ ?f' y = x)"
    proof-
      have "∀x::real. (x≥0 ⟶ (∃y. (y ∈ norms ∧ f y = x )))"
        by (metis (no_types, opaque_lifting) bij_betw_iff_bijections mem_Collect_eq normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def)
      moreover have "∀x::real. (x<0 ⟶ (∃y. (y ∈ norms ∧ (f y) =  -x)))"
        by (simp add: calculation)
      moreover have  "∀x::real. (x≥0 ⟶ (∃y. (y ∈ norms ∧ ?f' y = x )))"
        by (smt (z3) calculation(1) f_inv_into_f normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def)
      moreover have  "∀x::real. (x<0 ⟶ (∃y. (y ∈ norms_neg ∧ (f (-y)) =  -x)))"
        using calculation(2) norms_def norms_neg_def by auto
      moreover have    "∀x::real. (x<0 ⟶ (∃y. (y ∈ norms_neg ∧ (?f' (-y)) =  -x)))"
        by (smt (z3) calculation(1) calculation(4) f_inv_into_f normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def norms_neg_def rangeI)
      moreover have "∀x::real. (x≥ 0 ∨ x<0)"
        by (simp add: linorder_le_less_linear)
      ultimately show ?thesis
      proof -
        { fix rr :: real
          have ff1: "∀r. (r::real) < 0 ∨ 0 ≤ r"
            by (smt (z3))
          have ff2: "∀r ra. sup (ra::real) r = sup r ra"
            by (smt (z3) inf_sup_aci(5))
          have ff3: "∀R Ra. (Ra::real set) ∪ R = R ∪ Ra"
            by (smt (z3) Un_commute)
          have ff4: "∀r ra. (r::real) ≤ sup r ra"
            by simp
          have ff5: "∀R Ra. (R::real set) ⊆ Ra ∪ R"
            by (smt (z3) inf_sup_ord(4))
          have ff6: "∀r. (r::real) ≤ r"
            by (smt (z3))
          have ff7: "∀r R Ra. (r::real) ∉ R ∨ r ∈ Ra ∨ ¬ R ⊆ Ra"
            by blast
          have ff8: "∀r. - (- (r::real)) = r"
            using verit_minus_simplify(4) by blast
          have ff9: "- (0::real) = 0"
            by (smt (z3))
          have "∀r ra. r ∉ norms_all ∨ (if r = 0 then 0 else if r ∈ norms then f r else if r ∈ norms_neg then - f (- r) else undefined) ≠ (if ra = 0 then 0 else if ra ∈ norms then f ra else if ra ∈ norms_neg then - f (- ra) else undefined) ∨ ra ∉ norms_all ∨ r = ra"
            using ‹∀x y. x ∈ norms_all ∧ y ∈ norms_all ∧ (if x = 0 then 0 else if x ∈ norms then f x else if x ∈ norms_neg then - f (- x) else undefined) = (if y = 0 then 0 else if y ∈ norms then f y else if y ∈ norms_neg then - f (- y) else undefined) ⟶ x = y› by blast
          then have "∀r. (if r = 0 then 0 else if r ∈ norms then f r else if r ∈ norms_neg then - f (- r) else undefined) ≠ (if True then 0 else if 0 ∈ norms then f 0 else if 0 ∈ norms_neg then - f 0 else undefined) ∨ r = 0 ∨ 0 ∉ norms_all ∨ r ∉ norms_all"
            using ff9 by (smt (z3))
          then have "(∃r. (if r = 0 then 0 else if r ∈ norms then f r else if r ∈ norms_neg then - f (- r) else undefined) = rr ∧ r ∈ norms_all) ∨ (∃r. (if r = 0 then 0 else if r ∈ norms then f r else if r ∈ norms_neg then - f (- r) else undefined) = rr ∧ r ∈ norms_all)"
            using ff9 ff8 ff7 ff6 ff5 ff4 ff3 ff2 ff1 ‹∀x<0. ∃y. y ∈ norms_neg ∧ f (- y) = - x› ‹∀x≥0. ∃y. y ∈ norms ∧ (if y = 0 then 0 else if y ∈ norms then f y else if y ∈ norms_neg then - f (- y) else undefined) = x› ‹∀x≥0. ∃y. y ∈ norms ∧ f y = x› if_True norms_all_def zero_only_norms_norms_neg by moura }
        then show ?thesis
          by blast
      qed
      
    qed
    moreover have "inj_on ?f' norms_all"
      using "*" inj_on_def by blast
    moreover have ***:"∀x::real. ∃y∈norms_all. (?f' y = x)"
      using "**" by blast
    moreover have "?f' ` norms_all = UNIV"
    proof-
      have "?f' ` norms_all ⊆ UNIV"
        by blast
      moreover have "UNIV ⊆ ?f' ` norms_all"
      proof-
        fix x::real
        have "∃y∈norms_all. (?f' y = x)"
          using "**" by blast
        then have "x ∈ (?f' ` norms_all)"
          by blast
        then have "∀x::real. (x ∈ (?f' ` norms_all))"
          by (smt (verit, del_insts) "**" image_iff)
        then show ?thesis 
          by blast
      qed
      ultimately show ?thesis
        by force
    qed
    ultimately show " bij_betw ?f' norms_all UNIV" 
      using bij_betw_def by blast
  qed
 
  moreover have fact_fin: " ((∀x::real. ∀y::real. ( x∈norms_all ∧ y ∈norms_all ∧ x>y)⟶ (?f' x) > (?f' y))
 ∧ (?f' 0) = 0 ∧ bij_betw ?f' norms_all UNIV)"
    using fact1 fact2 by argo
  
  ultimately show ?thesis
    using fact_fin
    by (smt (verit, del_insts))
qed

end

locale normed_gyrolinear_space' = 
  fixes norm'::"'a::gyrolinear_space ⇒ real"
  fixes f'::"real ⇒ real"
  assumes "∀a::'a. (norm' a ≥ 0)"
  assumes "bij_betw f' ((norm' ` UNIV) ∪ ((λx. -1 * norm' x) ` UNIV)) UNIV"
  assumes "∀y::real. ∀z::real. (( y∈  ((norm' ` UNIV) ∪ ((λx. -1 * norm' x) ` UNIV)) ∧
z∈  ((norm' ` UNIV) ∪ ((λx. -1 * norm' x) ` UNIV)) ∧ y>z)⟶ (f' y) > (f' z))"
  assumes "f' 0 = 0"
  assumes "∀x::'a. ∀y::'a. f'(norm' (gyroplus x y)) ≤ (f' (norm' x)) + (f' (norm' y))"
  assumes "f' (norm' (scale r x)) = ¦r¦ * (f' (norm' x))"
  assumes "norm' (gyr u v x) = norm' x"
  assumes "∀x::'a. ((norm' x) = 0 ⟷ x = gyrozero)"
begin

definition norms::"real set" where 
  "norms = norm' ` UNIV"

definition norms_neg::"real set" where 
  "norms_neg = (λx. -1 * norm' x) ` UNIV"

definition norms_all::"real set" where 
  "norms_all = norms ∪ norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg ≠ {}"
  using add.inverse_inverse norms_neg_def by fastforce


lemma zero_only_norms_norms_neg:
  assumes "x∈norms" "x∈norms_neg"
  shows "x=0"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) f_inv_into_f normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_def norms_neg_def)
 

definition norm_oplus_f::"real ⇒ real ⇒ real" (infixl " ⊕⇩f" 105)
  where "a ⊕⇩f b = (if (a∈norms_all ∧ b∈norms_all) then (inv_into norms_all f') ((f' a) + (f' b))
else undefined)"


definition norm_otimes_f::"real ⇒ real ⇒ real" (infixl "⊗⇩f" 105)
  where "r ⊗⇩f a = (if (a∈norms_all) then (inv_into norms_all f') (r * (f' a))
else undefined)"

lemma vector_space_of_norms:
  shows "vector_space_with_domain norms_all norm_oplus_f 0 norm_otimes_f"
proof
  fix x y
  show "x ∈ norms_all ⟹ y ∈ norms_all ⟹ x  ⊕⇩f y ∈ norms_all"
  proof-
    assume "x∈norms_all"
    show "y ∈ norms_all ⟹ x  ⊕⇩f y ∈ norms_all"
    proof-
      assume "y∈norms_all"
      show "x  ⊕⇩f y ∈ norms_all"
        by (smt (verit, del_insts) UNIV_I ‹x ∈ norms_all› ‹y ∈ norms_all› bij_betw_def inv_into_into norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    qed
  qed
next
  show "0 ∈ norms_all"
    by (metis Un_iff normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
next 
  fix x y z
  show " x ∈ norms_all ⟹
       y ∈ norms_all ⟹ z ∈ norms_all ⟹ x  ⊕⇩f y  ⊕⇩f z = x  ⊕⇩f (y  ⊕⇩f z)"
  proof-
    assume "x∈norms_all"
    show " y ∈ norms_all ⟹ z ∈ norms_all ⟹ x  ⊕⇩f y  ⊕⇩f z = x  ⊕⇩f (y  ⊕⇩f z)"
    proof-
      assume "y ∈ norms_all"
      show "z ∈ norms_all ⟹ x  ⊕⇩f y  ⊕⇩f z = x  ⊕⇩f (y  ⊕⇩f z)"
      proof-
        assume "z ∈ norms_all"
        show " x  ⊕⇩f y  ⊕⇩f z = x  ⊕⇩f (y  ⊕⇩f z)"
        proof-
          have " x  ⊕⇩f y = (inv_into norms_all f') ((f' x) + (f' y))"
            by (simp add: ‹x ∈ norms_all› ‹y ∈ norms_all› norm_oplus_f_def)
          moreover have "x  ⊕⇩f y  ⊕⇩f z = (inv_into norms_all f') ((
        f' ( (inv_into norms_all f') ((f' x) + (f' y)))) + (f' z))"
            by (metis (no_types, lifting) UNIV_I ‹z ∈ norms_all› bij_betw_imp_surj_on calculation inv_into_into norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
          moreover have "x  ⊕⇩f y  ⊕⇩f z = (inv_into norms_all f') (((f' x)+ (f' y))+(f' z))"
            by (metis (mono_tags, lifting) UNIV_I bij_betw_imp_surj_on calculation(2) f_inv_into_f normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
          moreover have " (y  ⊕⇩f z) =  (inv_into norms_all f') ((f' y) + (f' z))"
            by (simp add: ‹y ∈ norms_all› ‹z ∈ norms_all› norm_oplus_f_def)
          moreover have " x  ⊕⇩f (y  ⊕⇩f z) = (inv_into norms_all f') ((f' x) + 
        (f' ((inv_into norms_all f') ((f' y) + (f' z)))))"
            by (metis (mono_tags, lifting) UNIV_I ‹x ∈ norms_all› bij_betw_def calculation(4) inv_into_into norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
          moreover have " x  ⊕⇩f (y  ⊕⇩f z) = (inv_into norms_all f') ((f' x) + 
          ((f' y) + (f' z)))"
            by (metis (mono_tags, lifting) UNIV_I bij_betw_imp_surj_on calculation(5) f_inv_into_f normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
          ultimately show ?thesis 
            by argo
        qed
      qed
    qed
  qed
next
  fix x y
  show "x ∈ norms_all ⟹ y ∈ norms_all ⟹ x  ⊕⇩f y = y  ⊕⇩f x"
  proof-
    assume "x∈ norms_all"
    show "y ∈ norms_all ⟹ x  ⊕⇩f y = y  ⊕⇩f x"
    proof-
      assume "y ∈ norms_all"
      show " x ⊕⇩f y = y ⊕⇩f x"
        by (simp add: add.commute norm_oplus_f_def)
    qed
  qed
next 
  fix x
  show " x ∈ norms_all ⟹ x  ⊕⇩f 0 = x"
  proof-
    assume "x∈norms_all"
    show "x  ⊕⇩f 0 = x"
    proof-
      have "x  ⊕⇩f 0  = (inv_into norms_all f')  ((f' x) + (f' 0))"
        by (metis (mono_tags, lifting) Un_iff ‹x ∈ norms_all› norm_oplus_f_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
      then show ?thesis
        by (smt (verit, del_insts) ‹x ∈ norms_all› bij_betw_def inv_into_f_eq normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    qed
  qed
next 
  fix x
  show "x ∈ norms_all ⟹ ∃y∈norms_all. x  ⊕⇩f y = 0"
  proof-
    assume "x∈norms_all"
    show " ∃y∈norms_all. x  ⊕⇩f y = 0"
    proof-
      let ?y = "(inv_into norms_all f') (-(f' x))"
      have " x  ⊕⇩f ?y = (inv_into norms_all f') ((f' x) + (f' ?y))"
        by (smt (verit, ccfv_SIG) ‹x ∈ norms_all› bij_betwE bij_betw_inv_into f_inv_into_f inv_into_into norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI) 
      moreover have " x  ⊕⇩f ?y = (inv_into norms_all f') ((f' x) + (-(f' x)))"
        by (smt (verit, ccfv_SIG) bij_betw_inv_into_right calculation iso_tuple_UNIV_I normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
      moreover have "x  ⊕⇩f ?y =(inv_into norms_all f') 0"
        using calculation(2) by force
      moreover have "x  ⊕⇩f ?y = 0"
        by (metis (no_types, lifting) Un_iff bij_betw_def calculation(3) inv_into_f_eq normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
      moreover have "?y ∈ norms_all"
        by (metis (no_types, lifting) UNIV_I bij_betw_imp_surj_on inv_into_into normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
      ultimately show ?thesis
        by blast
    qed
  qed
next
  fix x a
  show "x ∈ norms_all ⟹ a ⊗⇩f x ∈ norms_all"
  proof-
    assume "x∈norms_all"
    show " a ⊗⇩f x ∈ norms_all"
      by (smt (verit, best) ‹x ∈ norms_all› bij_betw_imp_surj_on bij_betw_inv_into norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
  qed
next 
  fix x a b
  show "x ∈ norms_all ⟹ (a + b) ⊗⇩f x = a ⊗⇩f x  ⊕⇩f (b ⊗⇩f x)"
  proof-
    assume "x∈norms_all"
    show "(a + b) ⊗⇩f x = a ⊗⇩f x  ⊕⇩f (b ⊗⇩f x)"
    proof-
      have "(a + b) ⊗⇩f x = (inv_into norms_all f') ((a+b) * (f' x))"
        using ‹x ∈ norms_all› norm_otimes_f_def by presburger
      moreover have "(a + b) ⊗⇩f x = (inv_into norms_all f') (a*(f' x) + b*(f' x))"
        using calculation by argo
      moreover have *:" a ⊗⇩f x  ⊕⇩f (b ⊗⇩f x) = (inv_into norms_all f')
      ((f' (a ⊗⇩f x)) + (f' (b ⊗⇩f x)))"
      proof -
        have "⋀f. ¬ normed_gyrolinear_space' norm' f ∨ bij_betw f norms_all UNIV"
          by (metis (no_types) normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_def norms_all_def norms_def)
        then show ?thesis
          by (metis (full_types) UNIV_I ‹x ∈ norms_all› bij_betw_imp_surj_on inv_into_into norm_oplus_f_def norm_otimes_f_def normed_gyrolinear_space'_axioms)
      qed
      moreover have **:" (inv_into norms_all f')
      ((f' (a ⊗⇩f x)) + (f' (b ⊗⇩f x))) = (inv_into norms_all f')
    ((f' ((inv_into norms_all f') (a*(f' x)))) +
    (f' ((inv_into norms_all f') (b*(f' x)))))"
        using ‹x ∈ norms_all› norm_otimes_f_def by presburger
      moreover have "a ⊗⇩f x  ⊕⇩f (b ⊗⇩f x) = (inv_into norms_all f') ((a*(f' x)) + (b*(f' x)))"
        using * **
        by (smt (verit, ccfv_threshold) UNIV_I bij_betw_imp_surj_on f_inv_into_f normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
      ultimately show ?thesis 
        by presburger
    qed
  qed
next
  fix x a b
  show " x ∈ norms_all ⟹ a ⊗⇩f (b ⊗⇩f x) = (a * b) ⊗⇩f x"
  proof-
    assume "x∈norms_all"
   show "a ⊗⇩f (b ⊗⇩f x) = (a * b) ⊗⇩f x"
      by (smt (verit, best) UNIV_I ‹x ∈ norms_all› ab_semigroup_mult_class.mult_ac(1) bij_betw_imp_surj_on f_inv_into_f inv_into_into norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
  qed
next 
  fix x
  show "x ∈ norms_all ⟹ 1 ⊗⇩f x = x"
  proof-
    assume "x∈norms_all"
    show " 1 ⊗⇩f x = x"
    proof-
      have " 1 ⊗⇩f x = (inv_into norms_all f') (1*(f' x))"
        using ‹x ∈ norms_all› norm_otimes_f_def by presburger
      then show ?thesis 
        by (metis (no_types, lifting) ‹x ∈ norms_all› bij_betw_inv_into_left lambda_one normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    qed
  qed
next
  show "⋀x y a.
       x ∈ norms_all ⟹
       y ∈ norms_all ⟹ a ⊗⇩f (x  ⊕⇩f y) = a ⊗⇩f x  ⊕⇩f (a ⊗⇩f y)"
  proof-
    {
    fix x y a
    assume "x∈ norms_all \<and> y\<in> norms_all"
    have "a ⊗⇩f (x  ⊕⇩f y) = (inv_into norms_all f') (a * f' ((inv_into norms_all f') ((f' x) + (f' y))))"
      by (smt (verit, best) UNIV_I ‹x ∈ norms_all ∧ y ∈ norms_all› bij_betw_imp_surj_on inv_into_into norm_oplus_f_def norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    moreover have "a ⊗⇩f x  ⊕⇩f (a ⊗⇩f y) = (inv_into norms_all f') ((f' (inv_into norms_all f' (a * (f' x))))+(f' (inv_into norms_all f' (a * (f' y)))))"
      by (smt (verit) ‹x ∈ norms_all ∧ y ∈ norms_all› bij_betw_def inv_into_into iso_tuple_UNIV_I normed_gyrolinear_space'.norm_oplus_f_def normed_gyrolinear_space'.norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    ultimately have "a ⊗⇩f (x  ⊕⇩f y) = a ⊗⇩f x  ⊕⇩f (a ⊗⇩f y)"
      using UNIV_I bij_betw_imp_surj_on f_inv_into_f normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def norms_neg_def ring_class.ring_distribs(1)
      by (smt (verit, best) normed_gyrolinear_space'.norms_neg_def)
  }
   show "⋀x y a.
       x ∈ norms_all ⟹
       y ∈ norms_all ⟹ a ⊗⇩f (x  ⊕⇩f y) = a ⊗⇩f x  ⊕⇩f (a ⊗⇩f y)"
     using ‹⋀y x a. x ∈ norms_all ∧ y ∈ norms_all ⟹ a ⊗⇩f (x ⊕⇩f y) = a ⊗⇩f x ⊕⇩f (a ⊗⇩f y)› by blast
   qed
qed


lemma r2:
  shows "norm' (x ⊕ y) ≤ (norm' x)  ⊕⇩f (norm' y)"
proof-
    have " (f' (norm' (x ⊕ y))) ≤ (f' (norm' x)) + (f' (norm' y))"
      using normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def by blast
    moreover have "(inv_into norms_all f' (f' (norm' (x ⊕ y)))) ≤ 
(inv_into norms_all f' ((f' (norm' x)) + (f' (norm' y))))"
      by (smt (verit, ccfv_SIG) UNIV_I bij_betw_def f_inv_into_f inv_into_into normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
  ultimately show ?thesis
    by (metis (no_types, lifting) UnI1 bij_betw_def inv_into_f_eq normed_gyrolinear_space'.norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
qed

lemma r3:
  shows "norm' (r  ⊗  x) =  ¦r¦ ⊗⇩f (norm' x)"
  by (smt (verit, best) bij_betw_inv_into_left in_mono inf_sup_ord(3) norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)

lemma one_dim_vs:
  shows "one_dim_vector_space_with_domain norms_all norm_oplus_f 0 norm_otimes_f"
proof-
  have step1: "vector_space_with_domain  norms_all norm_oplus_f 0 norm_otimes_f"
    using vector_space_of_norms by auto
  moreover have step2: "∀y. ∀x. (y∈ norms_all ∧
 x∈ norms_all ∧ x≠0 ⟶ (∃!r::real. y = r ⊗⇩f x))"
  proof
    fix y
    show " ∀x. (y∈ norms_all ∧
 x∈ norms_all ∧ x≠0 ⟶ (∃!r::real. y = r ⊗⇩f x))"
    proof
      fix x
      show "y∈ norms_all ∧
 x∈ norms_all ∧ x≠0 ⟶ (∃!r::real. y = r ⊗⇩f x)"
      proof
        assume "y∈ norms_all ∧
 x∈ norms_all ∧ x≠0"
        show "(∃!r::real. y = r ⊗⇩f x)"
        proof-
          have "(∃r::real. y = r ⊗⇩f x)"
          proof-
            let ?r = "f'(y)/f'(x)"
            have "?r ⊗⇩f x = (inv_into norms_all f') (?r * (f' x))"
              by (simp add: ‹y ∈ norms_all ∧ x ∈ norms_all ∧ x ≠ 0› norm_otimes_f_def)
            then show ?thesis 
              by (smt (verit, ccfv_SIG) ‹y ∈ norms_all ∧ x ∈ norms_all ∧ x ≠ 0› bij_betw_inv_into_left nonzero_eq_divide_eq normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def vector_space_of_norms vector_space_with_domain.zero_in_dom)
          qed
          
          moreover have "∀r1.∀r2. (y = r1 ⊗⇩f x ∧ y = r2 ⊗⇩f x ⟶ r1=r2)"
          proof
            fix r1 
            show "∀r2. y = r1 ⊗⇩f x ∧ y = r2 ⊗⇩f x ⟶ r1=r2"
            proof
              fix r2 
              show "y = r1 ⊗⇩f x ∧ y = r2 ⊗⇩f x ⟶ r1=r2"
              proof
                assume "y = r1 ⊗⇩f x ∧ y = r2 ⊗⇩f x "
                show "r1=r2"
                proof-
                        have "r1 ⊗⇩f x = (inv_into norms_all f') (r1 * (f' x))"
            by (simp add: ‹y ∈ norms_all ∧ x ∈ norms_all ∧ x ≠ 0› norm_otimes_f_def)
          moreover have "r2 ⊗⇩f x = (inv_into norms_all f') (r2 * (f' x))"
            using ‹y ∈ norms_all ∧ x ∈ norms_all ∧ x ≠ 0› norm_otimes_f_def by presburger
          moreover 
            have "(inv_into norms_all f') (r1 * (f' x)) = (inv_into norms_all f') (r2 * (f' x))"
              using ‹y = r1 ⊗⇩f x ∧ y = r2 ⊗⇩f x› calculation(1) calculation(2) by fastforce
            moreover have" f' ( (inv_into norms_all f') (r1 * (f' x))) =
        f'( (inv_into norms_all f') (r2 * (f' x)))"
              using calculation by presburger
            moreover have "r1* (f' x) = r2* (f' x)"
              by (metis (mono_tags, lifting) UNIV_I bij_betw_imp_surj_on calculation(3) inv_into_injective normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
            ultimately show ?thesis
              by (metis (no_types, opaque_lifting) ‹y ∈ norms_all ∧ x ∈ norms_all ∧ x ≠ 0› mult_right_cancel norm_oplus_f_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def vector_space_of_norms vector_space_with_domain.add_zero vector_space_with_domain.zero_in_dom)
          qed
          
        qed
      qed
    qed
    ultimately show ?thesis
      by blast
  qed
qed
qed
qed
  ultimately show ?thesis
    by (simp add: one_dim_vector_space_with_domain.intro one_dim_vector_space_with_domain_axioms.intro)
qed

end

locale normed_gyrolinear_space'' = 
  fixes norm'::"'a::gyrolinear_space ⇒ real"
  fixes oplus'::"real ⇒ real ⇒ real"
  fixes otimes'::"real⇒real ⇒ real"
  assumes "∀a::'a. (norm' a ≥ 0)"
  assumes ax_space: "one_dim_vector_space_with_domain ((norm' ` UNIV) ∪ ((λx. -1 * norm' x) ` UNIV))
      oplus' 0 otimes'"
  assumes ax3: "∀x::'a. ∀y::'a. (norm' (gyroplus x y)) ≤ oplus' (norm' x) (norm' y)"
  assumes "(norm' (scale r x)) = otimes' ¦r¦ (norm' x)"
  assumes "norm' (gyr u v x) = norm' x"
  assumes "∀x::'a. ((norm' x) = 0 ⟷ x = gyrozero)"
begin

definition norms::"real set" where 
  "norms = norm' ` UNIV"

definition norms_neg::"real set" where 
  "norms_neg = (λx. -1 * norm' x) ` UNIV"

definition norms_all::"real set" where 
  "norms_all = norms ∪ norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg ≠ {}"
  using add.inverse_inverse norms_neg_def by fastforce


lemma zero_only_norms_norms_neg:
  assumes "x∈norms" "x∈norms_neg"
  shows "x=0"
 by (smt (verit, ccfv_threshold) assms(1) assms(2) f_inv_into_f normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def norms_def norms_neg_def)

lemma not_trivial_domen_has_pos:
  assumes "∃x. (x∈norms_all ∧ x≠0)"
  shows "∃x. (x∈norms ∧ x≠0)"
  using assms norms_all_def norms_def norms_neg_def by auto

lemma iso_with_real:
  assumes "∃x. (x∈norms_all ∧ x≠0)" (* not trivial domain *)
  shows "∃g. (bij_betw g norms_all UNIV ∧ (g 0) = 0 ∧
  (∀u.∀v. (u∈norms_all ∧ v∈norms_all ⟶ g (oplus' u v) = (g u) + (g v)))
 ∧ (∀u.∀r::real. (u∈norms_all ⟶ g (otimes' r u) = r*(g u)))
)" (*∧ (∀u. (u∈norms ⟶ (g u)≥0))*)
proof-
  obtain "x" where "x∈norms ∧ x≠0"
    using assms not_trivial_domen_has_pos by presburger
  moreover have "x∈ norms_all"
    by (simp add: calculation norms_all_def)
  have "∀y. (y∈norms_all ⟶ (∃!r.(y = otimes' r x)))"
    using ax_space  one_dim_vector_space_with_domain_axioms_def
    by (metis ‹x ∈ norms_all› calculation norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(2))
  let ?g = "λy. (THE r. y = otimes' r x)"
  have "bij_betw ?g norms_all UNIV"
  proof-
    have "inj_on ?g norms_all"
      by (smt (verit, best) ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› inj_on_def the_equality)
    moreover have "∀r::real. ∃y. (y∈ norms_all ∧ y = otimes' r x)"
      by (metis ‹x ∈ norms_all› ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
    moreover have "∀r::real.∃y∈norms_all. ?g y = r"
      using ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› calculation(2) by blast
    ultimately show ?thesis 
      by (smt (verit, ccfv_threshold) UNIV_eq_I bij_betw_apply inj_on_imp_bij_betw)
  qed
  moreover have "?g 0 = 0"
  proof-
    obtain "r" where "0 = otimes' r x"
      by (metis ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain_def vector_space_with_domain.zero_in_dom)
    
    moreover obtain "xx" where "x=norm' xx "
      using norms_all_def 
      using norms_def norms_neg_def
      using ‹x ∈ norms ∧ x ≠ 0› by auto
   
    moreover  have "otimes' 0 x = norm' (0 ⊗ xx)"
      by (metis (no_types, lifting) calculation(2) norm_zero normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def real_norm_def)
    moreover have "otimes' 0 x = 0"
      by (smt (verit, ccfv_threshold) ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› ‹x ∈ norms_all› ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain_def)
    ultimately show ?thesis 
      by (smt (verit) ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) the1_equality vector_space_with_domain.zero_in_dom)
  qed
  moreover have "∀u.∀v. (u∈norms_all ∧ v∈norms_all ⟶ ?g (oplus' u v) = (?g u) + (?g v))"
  proof
    fix u
    show "∀v. (u∈norms_all ∧ v∈norms_all ⟶ ?g (oplus' u v) = (?g u) + (?g v))"
    proof
      fix v
      show "u∈norms_all ∧ v∈norms_all ⟶ ?g (oplus' u v) = (?g u) + (?g v)"
      proof
        assume "u∈norms_all ∧ v∈norms_all"
        show " ?g (oplus' u v) = (?g u) + (?g v)"
        proof-
          obtain "a" where "u = otimes' a x"
            using ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› ‹u ∈ norms_all ∧ v ∈ norms_all› by blast
          moreover obtain "b" where "v = otimes' b x"
            using ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› ‹u ∈ norms_all ∧ v ∈ norms_all› by blast
          moreover have *:"oplus' u v = otimes' (a+b) x"
            by (metis ‹x ∈ norms_all› ax_space calculation(1) calculation(2) norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain_def vector_space_with_domain.smult_distr_sadd)
          moreover have "oplus' u v ∈ norms_all"
            by (metis "*" ‹x ∈ norms_all› ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
          moreover have "?g (oplus' u v) = (a+b)"
            using * 
            using ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› calculation(4) by auto
          ultimately show ?thesis 
            by (smt (verit, del_insts) ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› ‹u ∈ norms_all ∧ v ∈ norms_all› the1_equality)
        qed
      qed
    qed
  qed
  moreover have "(∀u.∀r::real. (u∈norms_all ⟶ ?g (otimes' r u) = r*(?g u)))"
  proof
    fix u
    show "∀r::real. (u∈norms_all ⟶ ?g (otimes' r u) = r*(?g u))"
    proof
      fix r
      show "u∈norms_all ⟶ ?g (otimes' r u) = r*(?g u)"
      proof
        assume "u∈norms_all"
        show "?g (otimes' r u) = r*(?g u)"
        proof-
          obtain "a" where "u = otimes' a x"
            using ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› ‹u ∈ norms_all› by blast
          moreover have "otimes' r u = otimes' (r*a) x"
            by (metis ‹x ∈ norms_all› ax_space calculation norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_assoc)
          moreover have "otimes' r u ∈ norms_all"
            by (metis ‹u ∈ norms_all› ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
          moreover have "?g (otimes' r u) = (r*a)"
            using ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› calculation(2) calculation(3) by auto
          ultimately show ?thesis 
            by (smt (verit, ccfv_threshold) ‹∀y. y ∈ norms_all ⟶ (∃!r. y = otimes' r x)› ‹u ∈ norms_all› theI')
        qed
      qed
    qed
  qed
 
  ultimately show ?thesis 
    by blast
qed

definition g_iso::"(real⇒real)⇒bool" where
  "g_iso g ⟷ (bij_betw g norms_all UNIV ∧ (g 0) = 0 ∧
  (∀u.∀v. (u∈norms_all ∧ v∈norms_all ⟶ g (oplus' u v) = (g u) + (g v)))
 ∧ (∀u.∀r::real. (u∈norms_all ⟶ g (otimes' r u) = r*(g u))))"

lemma iso_neg_with_real:
  assumes "∃x. (x∈norms_all ∧ x≠0)" (* not trivial domain *)
  shows "g_iso g ⟶ g_iso (λx. -1 * (g x))" 
proof
  assume "g_iso g"
  show " g_iso (λx. -1 * (g x))"
  proof-
    have "bij_betw (λx. -1 * (g x)) norms_all UNIV"
    proof-
      have "inj_on (λx. -1 * (g x)) norms_all"
        by (smt (verit, ccfv_threshold) ‹g_iso g› bij_betw_imp_inj_on g_iso_def inj_on_def)
      moreover have "∀r::real.∃y∈norms_all. ((λx. -1 * (g x)) y = r)"
        by (metis UNIV_I ‹g_iso g› bij_betw_iff_bijections g_iso_def minus_equation_iff mult_cancel_right2 mult_minus_left)
      ultimately show ?thesis 
        by (metis (mono_tags, lifting) UNIV_eq_I bij_betwE bij_betw_imageI)
    qed
    moreover have " (λx. -1 * (g x)) 0 = 0"
      using ‹g_iso g› g_iso_def by force
    moreover have "(∀u.∀v. (u∈norms_all ∧ v∈norms_all ⟶  (λx. -1 * (g x)) (oplus' u v)
 = ( (λx. -1 * (g x)) u) + ( (λx. -1 * (g x)) v)))"
      using ‹g_iso g› g_iso_def by auto
    moreover have "(∀u.∀r::real. (u∈norms_all ⟶  (λx. -1 * (g x)) (otimes' r u) = r*( (λx. -1 * (g x)) u)))"
      using ‹g_iso g› g_iso_def by auto
    ultimately show ?thesis 
      using g_iso_def by presburger
  qed
qed

lemma iso_with_real_positive_on_norms:
  assumes "∃x. (x∈norms_all ∧ x≠0)" (* not trivial domain *)
  shows "∃g. (g_iso g ∧ (∀x.(x∈norms ⟶ (g x)≥0))
∧ bij_betw (λx. if x ∈ norms then (g x) else undefined) norms {r::real. r≥0})"
proof-
  obtain "xx" where "xx∈norms ∧ xx≠0"
    using assms not_trivial_domen_has_pos by blast
  moreover obtain "x" where "norm' x = xx"
    using calculation norms_def by auto
  moreover obtain "g" where "g_iso g"
    using iso_with_real
    using assms g_iso_def by blast
  let ?g = "if (g xx) < 0 then  (λx. -1 * (g x)) else g"
  have *:"?g xx ≥ 0"
    by force
  moreover have "?g xx ≠0"
  proof (rule ccontr)
    assume "¬(?g xx ≠0)"
    have "?g xx = 0"
      using ‹¬ (if g xx < 0 then λx. - 1 * g x else g) xx ≠ 0› by blast
    then have "?g xx = g xx"
      by (smt (verit, ccfv_threshold))
    then have "g xx = 0"
      by (simp add: ‹(if g xx < 0 then λx. - 1 * g x else g) xx = 0›)
    then have "xx=0"
      by (metis ‹g_iso g› ax_space bij_betw_iff_bijections calculation(1) g_iso_def in_mono inf_sup_ord(3) norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.zero_in_dom)
    then show False 
      using calculation(1) by blast
  qed
  moreover have "g_iso ?g"
    using ‹g_iso g› assms iso_neg_with_real by presburger
  moreover have "∀x.(x∈norms ⟶ (?g x)≥0)"
  proof(rule ccontr)
    assume "¬(∀x.(x∈norms ⟶ (?g x)≥0))"
    have "∃x. (x∈norms ∧ (?g x) < 0)"
      using ‹¬ (∀x. x ∈ norms ⟶ 0 ≤ (if g xx < 0 then λx. - 1 * g x else g) x)› by fastforce
    moreover obtain "yy" where "yy ∈ norms ∧ (?g yy) <0"
      using calculation by blast
    moreover obtain "y" where "norm' y = yy"
      using calculation(2) norms_def by auto
    let ?A = "{norm' (r ⊗ x) | r::real. True}"
    let ?B = "{norm' (r ⊗ y) | r::real. True}"
    have "?A ∪ ?B ⊆ norms"
      using norms_def by auto
    let ?gA = "{(?g a)|a. a∈?A}"
    have "?gA = {r::real. r≥0}"
    proof-
      have "∀a. (a∈?A ⟶ ?g a ≥0)"
      proof
        fix a
        show "(a∈?A ⟶ ?g a ≥0)"
        proof
            assume "a∈?A"
            show "?g a ≥0"
            proof-
              obtain "r" where "a = norm'  (r ⊗ x) "
                using ‹a ∈ {norm' (r ⊗ x) |r. True}› by blast
              moreover have "?g a = ?g (norm'  (r ⊗ x) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' ¦r¦ (norm' x))"
                by (metis calculation(1) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              moreover have "?g a =  ¦r¦ * ?g (norm' x)"
                using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› ‹norm' x = xx› ‹xx ∈ norms ∧ xx ≠ 0› calculation(3) g_iso_def norms_all_def by auto
              ultimately show ?thesis 
                by (simp add: ‹norm' x = xx›)
            qed
        qed
      qed
      moreover have "?gA ⊆ {r::real. r≥0}"
        using calculation by fastforce
      moreover have "{r::real. r≥0} ⊆ ?gA"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› g_iso_def by blast
        moreover have "∀r::real. (r≥0 ⟶ r∈?gA)"
        proof
          fix r
          show "r≥0 ⟶ r∈?gA"
          proof
            assume "r≥0"
            show "r∈?gA"
            proof-
              obtain "r'" where "¦r'¦ = r / (?g xx)"
                using  *
                by (meson ‹0 ≤ r› abs_of_nonneg divide_nonneg_nonneg)
              moreover have "r =  ¦r'¦ * (?g xx)"
                by (simp add: ‹(if g xx < 0 then λx. - 1 * g x else g) xx ≠ 0› calculation)
              moreover have "r =  ¦r'¦ * (?g (norm' x))"
                using ‹norm' x = xx› calculation(2) by blast
              moreover have "r = ?g (otimes' ¦r'¦  (norm' x))"
                using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› ‹norm' x = xx› ‹xx ∈ norms ∧ xx ≠ 0› calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (¦r'¦  ⊗ x))"
                by (smt (verit, del_insts) calculation(4) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed
    let ?gB = "{(?g b)|b. b∈?B}"
    have "?gB = {r::real. r≤0}"


 proof-
      have "∀a. (a∈?B ⟶ ?g a ≤0)"
      proof
        fix a
        show "(a∈?B ⟶ ?g a ≤0)"
        proof
            assume "a∈?B"
            show "?g a≤0"
            proof-
              obtain "r" where "a = norm'  (r ⊗ y) "
                     using ‹a ∈ {norm' (r ⊗ y) |r. True}› by blast
              moreover have "?g a = ?g (norm'  (r ⊗ y) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' ¦r¦ (norm' y))"
                by (metis calculation(1) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              moreover have "?g a =  ¦r¦ * ?g (norm' y)"
                using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› ‹norm' y = yy› ‹yy ∈ norms ∧ (if g xx < 0 then λx. - 1 * g x else g) yy < 0› calculation(3) g_iso_def norms_all_def by auto
               
              ultimately show ?thesis 
                by (simp add: ‹norm' y = yy› ‹yy ∈ norms ∧ (if g xx < 0 then λx. - 1 * g x else g) yy < 0› mult_le_0_iff order_less_imp_le)
            qed
        qed
      qed
      moreover have "?gB ⊆ {r::real. r≤0}"
        using calculation by fastforce
      moreover have "{r::real. r≤0} ⊆ ?gB"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› g_iso_def by blast
        moreover have "∀r::real. (r≤0 ⟶ r∈?gB)"
        proof
          fix r
          show "r≤0 ⟶ r∈?gB"
          proof
            assume "r≤0"
            show "r∈?gB"
            proof-
              obtain "r'" where "¦r'¦ = r / (?g yy)"
                using  *
                by (metis ‹r ≤ 0› ‹yy ∈ norms ∧ (if g xx < 0 then λx. - 1 * g x else g) yy < 0› abs_if divide_less_0_iff less_eq_real_def not_less_iff_gr_or_eq)
              moreover have "r =  ¦r'¦ * (?g yy)"
                using ‹yy ∈ norms ∧ (if g xx < 0 then λx. - 1 * g x else g) yy < 0› calculation by auto
              moreover have "r =  ¦r'¦ * (?g (norm' y))"
                using ‹norm' y = yy› calculation(2) by blast
              moreover have "r = ?g (otimes' ¦r'¦  (norm' y))"
                using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› ‹norm' y = yy› ‹yy ∈ norms ∧ (if g xx < 0 then λx. - 1 * g x else g) yy < 0› calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (¦r'¦  ⊗ y))"
                by (smt (verit, del_insts) calculation(4) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed

    let ?gX_norms = "{(?g x)|x. x∈norms}"
    let ?gX_norms_all = "{(?g x)|x. x∈norms_all}"
    let ?gA_union_B = "{(?g x)|x. x∈ ?A∪?B}"
    have "?gA_union_B ⊆ ?gX_norms"
      using ‹{norm' (r ⊗ x) |r. True} ∪ {norm' (r ⊗ y) |r. True} ⊆ norms› by force
    moreover have "?gA_union_B = ?gA ∪ ?gB"
    proof-
      have "?gA_union_B ⊆ ?gA ∪ ?gB"
        by blast
      moreover have "?gA ∪ ?gB ⊆ ?gA_union_B"
        by blast
      ultimately show ?thesis
        by force
    qed
    moreover have "?gA_union_B = UNIV"
      using ‹{(if g xx < 0 then λx. - 1 * g x else g) a |a. a ∈ {norm' (r ⊗ x) |r. True}} = {r. 0 ≤ r}› ‹{(if g xx < 0 then λx. - 1 * g x else g) b |b. b ∈ {norm' (r ⊗ y) |r. True}} = {r. r ≤ 0}› calculation(4) by force
    moreover have "UNIV ⊆ ?gX_norms"
      using calculation(3) calculation(5) by argo
   (* moreover have "?gX_norms ⊂ ?gX_norms_all"
    proof-
      have "∀a. (a∈ ?gX_norms ⟶ a∈ ?gX_norms_all)"
        using norms_all_def by fastforce*)
      (*moreover have "∃a. (a∈?gX_norms_all ∧ ¬a∈?gX_norms)"
      proof-*)
        obtain "a" where "a∈norms_all ∧ ¬a∈norms"
          by (metis (mono_tags, lifting) Un_iff add.inverse_inverse assms mult_minus1 norms_all_def norms_def norms_neg_def rangeE rangeI zero_only_norms_norms_neg)
        let ?a = "?g a"
        have "?a ∈ ?gX_norms_all "

          using ‹a ∈ norms_all ∧ a ∉ norms› by blast

        moreover have "¬?a∈ ?gX_norms"
        proof(rule ccontr)
          assume "¬(¬?a∈ ?gX_norms)"
          have "?a∈?gX_norms"
            using ‹¬ (if g xx < 0 then λx. - 1 * g x else g) a ∉ {(if g xx < 0 then λx. - 1 * g x else g) x |x. x ∈ norms}› by blast
          then obtain "b" where "b∈norms ∧ ?g b = ?a"
            by force
         
            then show False using  ‹a ∈ norms_all ∧ a ∉ norms› ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subsetD
              by (smt (verit, ccfv_threshold) ‹g_iso g›)
          qed
          moreover have "False" 

            using ‹UNIV ⊆ {(if g xx < 0 then λx. - 1 * g x else g) x |x. x ∈ norms}› calculation(7) by blast
            
    ultimately show False 
      by auto
  qed
  

  moreover have " bij_betw (λx. if x ∈ norms then (?g x) else undefined) norms {r::real. r≥0}"
  proof-
    let ?f = "(λx. if x ∈ norms then (?g x) else undefined)"
     let ?A = "{norm' (r ⊗ x) | r::real. True}"
     let ?gA = "{(?g a)|a. a∈?A}"
     have s1:"?gA = {r::real. r≥0}"
        proof-
      have "∀a. (a∈?A ⟶ ?g a ≥0)"
      proof
        fix a
        show "(a∈?A ⟶ ?g a ≥0)"
        proof
            assume "a∈?A"
            show "?g a ≥0"
            proof-
              obtain "r" where "a = norm'  (r ⊗ x) "
                using ‹a ∈ {norm' (r ⊗ x) |r. True}› by blast
              moreover have "?g a = ?g (norm'  (r ⊗ x) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' ¦r¦ (norm' x))"
                by (metis calculation(1) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              moreover have "?g a =  ¦r¦ * ?g (norm' x)"
                using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› ‹norm' x = xx› ‹xx ∈ norms ∧ xx ≠ 0› calculation(3) g_iso_def norms_all_def by auto
              ultimately show ?thesis 
                by (simp add: ‹norm' x = xx›)
            qed
        qed
      qed
      moreover have "?gA ⊆ {r::real. r≥0}"
        using calculation by fastforce
      moreover have "{r::real. r≥0} ⊆ ?gA"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› g_iso_def by blast
        moreover have "∀r::real. (r≥0 ⟶ r∈?gA)"
        proof
          fix r
          show "r≥0 ⟶ r∈?gA"
          proof
            assume "r≥0"
            show "r∈?gA"
            proof-
              obtain "r'" where "¦r'¦ = r / (?g xx)"
                using  *
                by (meson ‹0 ≤ r› abs_of_nonneg divide_nonneg_nonneg)
              moreover have "r =  ¦r'¦ * (?g xx)"
                by (simp add: ‹(if g xx < 0 then λx. - 1 * g x else g) xx ≠ 0› calculation)
              moreover have "r =  ¦r'¦ * (?g (norm' x))"
                using ‹norm' x = xx› calculation(2) by blast
              moreover have "r = ?g (otimes' ¦r'¦  (norm' x))"
                using ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› ‹norm' x = xx› ‹xx ∈ norms ∧ xx ≠ 0› calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (¦r'¦  ⊗ x))"
                by (smt (verit, del_insts) calculation(4) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed
     moreover have s2:"∀y. (?g (norm' y) ≥0)"
       using ‹∀x. x ∈ norms ⟶ 0 ≤ (if g xx < 0 then λx. - 1 * g x else g) x› norms_def by blast
     moreover have "norms = ?A"
     proof-
       have "∀y. (?g (norm' y) ∈ ?gA)"
         using s1 s2 by blast
       moreover have "norms ⊆ ?A"
       proof-
         have "∀y. (y∈norms ⟶ y∈?A)"
         proof
           fix y
           show "y∈norms ⟶ y∈?A"
           proof
             assume "y∈norms"
             show "y∈?A"
             proof-
               obtain "yy" where "y=norm' yy"
                 using ‹y ∈ norms› norms_def by auto
               moreover have "?g (norm' yy) ∈?gA"
                 using ‹∀y. (if g xx < 0 then λx. - 1 * g x else g) (norm' y) ∈ {(if g xx < 0 then λx. - 1 * g x else g) a |a. a ∈ {norm' (r ⊗ x) |r. True}}› by blast
               moreover have "norm' yy ∈ ?A"
               proof-
                 obtain "h" where "h ∈ ?A ∧ ?g h = ?g (norm' yy)"
                   using calculation(2) by fastforce
                 moreover have "?g h ≥0"
                   using calculation s2 by blast
                
                 moreover {
                   assume "?g = g"
                   have " g h = g (norm' yy)"
                     by (smt (verit, ccfv_SIG) calculation(1))
                   
                   moreover have "h=norm' yy"
                   proof-
                     have "h∈norms"
                       using ‹h ∈ {norm' (r ⊗ x) |r. True} ∧ (if g xx < 0 then λx. - 1 * g x else g) h = (if g xx < 0 then λx. - 1 * g x else g) (norm' yy)› norms_def by force
                     moreover have "norm' yy ∈ norms"
                       using ‹y = norm' yy› ‹y ∈ norms› by blast
                     ultimately show ?thesis 
                       by (metis ‹g h = g (norm' yy)› ‹g_iso g› bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subset_iff)
                   qed
                   ultimately have ?thesis
                     using ‹h ∈ {norm' (r ⊗ x) |r. True} ∧ (if g xx < 0 then λx. - 1 * g x else g) h = (if g xx < 0 then λx. - 1 * g x else g) (norm' yy)› by blast
                 }
                   moreover {
                   assume "?g = (λx. -1 * (g x))"
                   have " g h = g (norm' yy)"
                     by (smt (verit, ccfv_SIG) calculation(1))
                   
                   moreover have "h=norm' yy"
                   proof-
                     have "h∈norms"
                       using ‹h ∈ {norm' (r ⊗ x) |r. True} ∧ (if g xx < 0 then λx. - 1 * g x else g) h = (if g xx < 0 then λx. - 1 * g x else g) (norm' yy)› norms_def by force
                     moreover have "norm' yy ∈ norms"
                       using ‹y = norm' yy› ‹y ∈ norms› by blast
                     ultimately show ?thesis 
                       by (metis ‹g h = g (norm' yy)› ‹g_iso g› bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subset_iff)
                   qed
                   ultimately have ?thesis
                     using ‹h ∈ {norm' (r ⊗ x) |r. True} ∧ (if g xx < 0 then λx. - 1 * g x else g) h = (if g xx < 0 then λx. - 1 * g x else g) (norm' yy)› by blast
                 }
                 ultimately show ?thesis 
                   by argo
               qed
               ultimately show ?thesis 
                 by fastforce
             qed
         qed
       qed
        show ?thesis 
          using ‹∀y. y ∈ norms ⟶ y ∈ {norm' (r ⊗ x) |r. True}› by blast
      qed
      ultimately show ?thesis 
        using norms_def by fastforce
    qed
     moreover have step1:"inj_on ?f  norms"
     proof-
       have "∀x.∀y. (x∈ norms ∧ y∈ norms ∧ (?f x) = (?f y) ⟶ x=y)"
       proof
         fix x 
         show "∀y. (x∈ norms ∧ y∈ norms ∧ (?f x) = (?f y) ⟶ x=y)"
         proof
           fix y 
           show " (x∈ norms ∧ y∈ norms ∧ (?f x) = (?f y) ⟶ x=y)"
             by (metis ‹g_iso (if g xx < 0 then λx. - 1 * g x else g)› bij_betw_imp_inj_on g_iso_def inf_sup_ord(3) inj_on_def norms_all_def subsetD)
         qed
       qed
       then show ?thesis
         using inj_on_def by blast
     qed
     moreover have "∀r::real. (r≥0 ⟶ (∃x. (x∈ norms ∧ ?f x = r)))"
       by (smt (verit) calculation(3) mem_Collect_eq s1)
       
     moreover have step2:"∀r::real. (r≥0 ⟶ (∃x∈ norms.( ?f x = r)))"
 
       using calculation(5) by blast
     moreover have "∀r∈{x::real. x≥0}. (∃x∈norms. (?f x = r))"
       using step2
       by blast
     moreover have **:"?f=(λx. if x ∈ norms then (?g x) else undefined)"
       by meson
     moreover have "?f ` norms = {r::real. r≥0}"
       by (smt (verit) Collect_cong Setcompr_eq_image calculation(3) s1)
     ultimately show ?thesis 
       by (simp add: bij_betw_def)
    
   qed
 
  ultimately show ?thesis
    by blast
qed




lemma comparing_norms_help:
  assumes "x∈norms" "y∈norms_all"
  "x≤y"
shows "y∈ norms"
proof-
  have "x < y ∨ x=y"
    using assms(3) by argo
  moreover {
    assume "x<y"
    have ?thesis 
      by (smt (verit) Un_iff ‹x < y› add_0 add_uminus_conv_diff assms(1) assms(2) full_SetCompr_eq linorder_not_less mem_Collect_eq mult_minus1 normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def norms_all_def norms_def norms_neg_def order_le_less_trans)
  }
  moreover {
    assume "x=y"
    have ?thesis 
      using ‹x = y› assms(1) by blast
  }
  ultimately show ?thesis by blast
qed

lemma existence_of_f:
 assumes "∃x. (x∈norms_all ∧ x≠0)" (* not trivial domain *)
  shows "∃f. (bij_betw f norms {x::real. x≥0}
∧  (∀y::real. ∀z::real. (( y∈ norms ∧
z∈  norms ∧ y>z)⟶ (f y) > (f z)))
  ∧ (∀x. ∀y. f(norm' (x ⊕ y)) ≤ (f (norm' x)) + (f (norm' y)))
∧ (∀r::real. (∀x. (f (norm' (r ⊗ x)) = ¦r¦ * (f (norm' x))))))"
proof-
  obtain "g" where "(g_iso g ∧ (∀x.(x∈norms ⟶ (g x)≥0))
∧ bij_betw (λx. if x ∈ norms then (g x) else undefined) norms {r::real. r≥0})"
    using  iso_with_real_positive_on_norms
    assms by blast
  let ?f = "λx. if x ∈ norms then (g x) else undefined"
  have "∀α::real. ∀β::real. ∀x. ((0 ≤ α ∧ α ≤ β) ⟶ ((otimes' α  (norm' x)) ≤ (otimes' β  (norm' x))))"
  proof
    fix α 
    show " ∀β::real. ∀x.((0 ≤ α ∧ α ≤ β) ⟶ ((otimes' α  (norm' x)) ≤ (otimes' β  (norm' x))))"
    proof
      fix β
      show " ∀x.((0 ≤ α ∧ α ≤ β) ⟶ ((otimes' α  (norm' x)) ≤ (otimes' β  (norm' x))))"
      proof
        fix x 
        show "((0 ≤ α ∧ α ≤ β) ⟶ ((otimes' α  (norm' x)) ≤ (otimes' β  (norm' x))))"
        proof
          assume "0 ≤ α ∧ α ≤ β"
          show "((otimes' α  (norm' x)) ≤ (otimes' β  (norm' x)))"
          proof-
            have "otimes' α  (norm' x) = norm' (α ⊗ x)"
              by (metis ‹0 ≤ α ∧ α ≤ β› abs_of_nonneg normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
            moreover have " norm' (α ⊗ x) = norm' (((β+α)/2 - (β-α)/2)⊗ x)"
              by (simp add: add_divide_distrib diff_divide_distrib)
            moreover have "norm' (((β+α)/2 - (β-α)/2)⊗ x) = 
            norm' (((β+α)/2) ⊗ x ⊕  (- (β-α)/2) ⊗ x )"
              by (metis add.commute divide_minus_left scale_distrib uminus_add_conv_diff)
            moreover have " norm' (((β+α)/2) ⊗ x ⊕  (- (β-α)/2) ⊗ x )
        ≤  oplus' (norm' (((β+α)/2)⊗ x)) (norm' ((-(β-α)/2)  ⊗ x))"
              using  ax3
              by blast
            moreover have "-(β-α)/2 ≤0"
              by (simp add: ‹0 ≤ α ∧ α ≤ β›)
            moreover have "(β+α)/2 ≥0"
              using ‹0 ≤ α ∧ α ≤ β› by auto
            moreover have *:"(norm' (((β+α)/2)⊗ x)) =(otimes' ((β+α)/2) (norm' x))"
              by (smt (verit, ccfv_threshold) calculation(6) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
            moreover have " ¦-(β-α)/2¦ = (β-α)/2 "
              using calculation(5) by force
            moreover have **:"(norm' ((-(β-α)/2)⊗ x)) =(otimes' ((β-α)/2) (norm' x))"
              by (metis calculation(8) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
            moreover have "  oplus' (norm' (((β+α)/2)⊗ x)) (norm' ((-(β-α)/2)  ⊗ x)) =
       oplus' (otimes' ((β+α)/2) (norm' x)) (otimes' ( (β-α)/2) (norm' x)) "
              using * **
              by presburger
            moreover have "oplus' (otimes' ((β+α)/2) (norm' x)) (otimes' ( (β-α)/2) (norm' x))
      = otimes' ((β+α)/2 + ((β-α)/2)) (norm' x)"
              by (metis Un_iff ax_space one_dim_vector_space_with_domain_def rangeI vector_space_with_domain.smult_distr_sadd)
            moreover have " otimes' ((β+α)/2 + ((β-α)/2)) (norm' x) = otimes' β (norm' x)"
              by argo
            ultimately show ?thesis 
              by linarith
          qed
        qed
      qed
    qed
  qed
  moreover have "∀α::real. ∀β::real. ∀x. ((0 < α ∧ α < β ∧ x≠gyrozero) ⟶ ((otimes' α  (norm' x)) < (otimes' β  (norm' x))))"
  proof -
    have f1: "∀f fa fb. normed_gyrolinear_space'' f fa fb = (((∀a. 0 ≤ f (a::'a)) ∧ one_dim_vector_space_with_domain (range f ∪ range (λa. - 1 * f a)) fa 0 fb ∧ (∀a aa. f (a ⊕ aa) ≤ fa (f a) (f aa))) ∧ (∀r a. f (r ⊗ a) = fb (if r < 0 then - r else r) (f a)) ∧ (∀a aa ab. f (gyr a aa ab) = f ab) ∧ (∀a. (f a = 0) = (a = 0⇩g)))"
      by (simp add: abs_if_raw normed_gyrolinear_space''_def)
    obtain rr :: "real ⇒ real" where
      f2: "bij_betw rr norms_all UNIV ∧ 0 = rr 0 ∧ (∀r ra. r ∈ norms_all ∧ ra ∈ norms_all ⟶ rr (oplus' r ra) = rr r + rr ra) ∧ (∀r ra. r ∈ norms_all ⟶ rr (otimes' ra r) = ra * rr r)"
      using assms iso_with_real by auto
    have "∀a. (0 = norm' a) = (0⇩g = a)"
      using f1 by (smt (z3) normed_gyrolinear_space''_axioms)
    then show ?thesis
      using f2 by (smt (z3) UnI2 bij_betw_inv_into_left calculation mult_right_cancel norms_all_def norms_def rangeI sup_commute)
  qed
  moreover obtain "xx0" where "xx0∈norms ∧ xx0≠0"
    using assms not_trivial_domen_has_pos by blast
  moreover obtain "x0" where "xx0 = norm' x0"
    using calculation(3) norms_def by auto
  moreover have mon:"(∀y z. y ∈ norms ∧ z ∈ norms ∧ z < y ⟶ ?f z < ?f y)"
  proof
    fix y 
    show "∀z. (y ∈ norms ∧ z ∈ norms ∧ z < y ⟶ ?f z < ?f y)"
    proof
      fix z 
      show "y ∈ norms ∧ z ∈ norms ∧ z < y ⟶ ?f z < ?f y"
      proof
        assume "y ∈norms ∧ z ∈ norms ∧ z < y"
        show "?f z < ?f y"
        proof-
          let ?alpha = "(?f y)/(?f (norm' x0))"
          let ?beta = "(?f z)/(?f (norm' x0))"
          have "otimes' ?alpha (norm' x0) = y"
            by (smt (verit, del_insts) ‹g_iso g ∧ (∀x. x ∈ norms ⟶ 0 ≤ g x) ∧ bij_betw (λx. if x ∈ norms then g x else undefined) norms {r. 0 ≤ r}› ‹y ∈ norms ∧ z ∈ norms ∧ z < y› ax_space bij_betw_imp_inj_on calculation(3) calculation(4) g_iso_def in_mono inf_sup_ord(3) inj_on_def nonzero_eq_divide_eq norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed vector_space_with_domain.zero_in_dom)
          moreover have "otimes' ?beta (norm' x0) = z"
            by (smt (verit, del_insts) ‹g_iso g ∧ (∀x. x ∈ norms ⟶ 0 ≤ g x) ∧ bij_betw (λx. if x ∈ norms then g x else undefined) norms {r. 0 ≤ r}› ‹xx0 = norm' x0› ‹xx0 ∈ norms ∧ xx0 ≠ 0› ‹y ∈ norms ∧ z ∈ norms ∧ z < y› ax_space bij_betw_imp_inj_on g_iso_def inf_sup_ord(3) inj_on_def nonzero_eq_divide_eq norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) subset_iff vector_space_with_domain.smult_closed vector_space_with_domain.zero_in_dom)
          moreover have "?alpha ≥ 0 ∧ ?beta ≥0"
             using ‹g_iso g ∧ (∀x. x ∈ norms ⟶ 0 ≤ g x) ∧ bij_betw (λx. if x ∈ norms then g x else undefined) norms {r. 0 ≤ r}› ‹xx0 = norm' x0› ‹xx0 ∈ norms ∧ xx0 ≠ 0› ‹y ∈ norms ∧ z ∈ norms ∧ z < y› by auto
           moreover have "0 < ?alpha ∧ ?alpha < ?beta ⟷ 0<y ∧ y<z"
             by (smt (verit, ccfv_threshold) ‹∀α β x. 0 ≤ α ∧ α ≤ β ⟶ otimes' α (norm' x) ≤ otimes' β (norm' x)› ‹y ∈ norms ∧ z ∈ norms ∧ z < y› calculation(1) calculation(2))
           moreover have "0<?alpha ∧ ?alpha < ?beta ⟷ 0 ≤ (?f y) ∧ (?f y) < (?f z)"
             by (smt (verit, best) ‹∀α β x. 0 ≤ α ∧ α ≤ β ⟶ otimes' α (norm' x) ≤ otimes' β (norm' x)› ‹y ∈ norms ∧ z ∈ norms ∧ z < y› calculation(1) calculation(2) calculation(3) div_by_0 frac_less zero_le_divide_iff)
           ultimately show ?thesis
             using ‹g_iso g ∧ (∀x. x ∈ norms ⟶ 0 ≤ g x) ∧ bij_betw (λx. if x ∈ norms then g x else undefined) norms {r. 0 ≤ r}› ‹y ∈ norms ∧ z ∈ norms ∧ z < y› by auto
         qed
      qed
    qed
  qed
  moreover have " (∀x y. ?f (norm' (x ⊕ y)) ≤ ?f (norm' x) + ?f (norm' y))"
  proof
    fix x 
    show "∀y. (?f (norm' (x ⊕ y)) ≤ ?f (norm' x) + ?f (norm' y))"
    proof
      fix y
      show " (?f (norm' (x ⊕ y)) ≤ ?f (norm' x) + ?f (norm' y))"
      proof-
        have "norm' x∈norms"
          using norms_def by blast
        moreover have "norm' y ∈ norms"
          using norms_def by blast
        moreover have "norm' (x ⊕ y)∈ norms"
          using norms_def by blast
        moreover have "norm' (x ⊕ y) ≤ oplus' (norm' x) (norm' y)"
          using ax3 by blast
        moreover have "(?f (norm' (x ⊕ y))) ≤ (?f (oplus' (norm' x) (norm' y)))"
        proof-
          have "norm' (x ⊕ y) ≤ oplus' (norm' x) (norm' y) ∨ norm' (x ⊕ y) = oplus' (norm' x) (norm' y)"
            using calculation(4) by blast
          moreover {
            assume st1:"norm' (x ⊕ y) < oplus' (norm' x) (norm' y)"
            have "norm' x ∈ norms"
              using norms_def by blast
            moreover have "norm' y ∈ norms"
              using norms_def by blast
            moreover have "vector_space_with_domain norms_all oplus' 0 otimes'"
              using ax_space norms_def 
              one_dim_vector_space_with_domain_def
              by (metis norms_all_def norms_neg_def)
            moreover have "oplus' (norm' x) (norm' y) ∈ norms_all"
              by (metis Un_iff calculation(1) calculation(2) calculation(3) norms_all_def vector_space_with_domain.add_closed)
            moreover have st2:"norm' (x ⊕ y)∈ norms"
              by (simp add: ‹norm' (x ⊕ y) ∈ norms›)
            moreover have st3:"oplus' (norm' x) (norm' y) ∈ norms"  
              using ax3 calculation(4) comparing_norms_help st2 by blast
            
moreover have "(?f (norm' (x ⊕ y))) < (?f (oplus' (norm' x) (norm' y)))"
              using mon st1 st2 st3
              by blast
            ultimately have ?thesis 
              by linarith
          }
          moreover {
              assume "norm' (x ⊕ y) = oplus' (norm' x) (norm' y)"
              then have ?thesis 
                by auto
            }
            ultimately show ?thesis
              by fastforce
        qed 
        moreover have " (?f (oplus' (norm' x) (norm' y))) = (?f (norm' x)) + (?f (norm' y))"
        proof-
          have f1:"norm' (x ⊕ y) ≤ oplus' (norm' x) (norm' y)"
            using ax3 by blast
          moreover have f2:"norm' (x ⊕ y) ∈ norms"
            by (simp add: ‹norm' (x ⊕ y) ∈ norms›)
          moreover have f3:"vector_space_with_domain norms_all oplus' 0 otimes'"
              using ax_space norms_def 
              one_dim_vector_space_with_domain_def
              by (metis norms_all_def norms_neg_def)
          moreover have "oplus' (norm' x) (norm' y)∈ norms"
              by (metis UnI1 ‹norm' x ∈ norms› ‹norm' y ∈ norms› f1 f2 f3 normed_gyrolinear_space''.comparing_norms_help normed_gyrolinear_space''_axioms norms_all_def vector_space_with_domain.add_closed)
            ultimately show ?thesis 
              using ‹g_iso g ∧ (∀x. x ∈ norms ⟶ 0 ≤ g x) ∧ bij_betw (λx. if x ∈ norms then g x else undefined) norms {r. 0 ≤ r}› ‹norm' x ∈ norms› ‹norm' y ∈ norms› g_iso_def norms_all_def by force
          qed
          ultimately show ?thesis 
            by force
      qed
    qed
  qed

  moreover have "(∀r::real. (∀x. (?f (norm' (r ⊗ x)) = ¦r¦ * (?f (norm' x)))))"
    by (smt (verit, ccfv_SIG) Un_iff ‹g_iso g ∧ (∀x. x ∈ norms ⟶ 0 ≤ g x) ∧ bij_betw (λx. if x ∈ norms then g x else undefined) norms {r. 0 ≤ r}› g_iso_def normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def norms_all_def norms_def rangeI)

  ultimately show ?thesis
    using ‹g_iso g ∧ (∀x. x ∈ norms ⟶ 0 ≤ g x) ∧ bij_betw (λx. if x ∈ norms then g x else undefined) norms {r. 0 ≤ r}› by blast
qed



end



end

