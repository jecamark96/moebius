theory Einstein
  imports Complex_Main GyroGroup GyroVectorSpace HOL.Real_Vector_Spaces
  MobiusGyroGroup HOL.Transcendental
begin

definition e_inner' :: "complex \<Rightarrow> complex \<Rightarrow> real" where
  "e_inner' z1 z2 = inner z1 z2"

lift_definition e_inner :: "PoincareDisc \<Rightarrow> PoincareDisc\<Rightarrow>real" (infixl "\<cdot>\<^sub>E" 100) is e_inner'
  done

lemma e_inner'_m_inner':
  shows "m_inner' z1 z2 = e_inner' z1 z2"
  by (simp add: e_inner'_def inner_complex_def m_inner'_def)

definition e_ozero' :: "complex" where
  "e_ozero' = 0"

lemma norm_0:
  fixes x::complex
  assumes "x=0"
  shows "inner x x = 0"
  using assms by force


lift_definition e_ozero :: PoincareDisc  ("0\<^sub>E") is e_ozero'
  unfolding e_ozero'_def
  using norm_0 by auto

definition e_gamma_factor::"complex \<Rightarrow> real" where
  "e_gamma_factor u = (if ((norm u)^2)<1 then (1/sqrt(1-(norm u)*(norm u)))
      else 0)"

lemma e_gamma_ok:
  assumes "(norm u)^2 < 1"
  shows "1/sqrt(1-(norm u)*(norm u)) \<noteq>0"
  by (metis assms eq_iff_diff_eq_0 order_less_irrefl power2_eq_square real_sqrt_eq_zero_cancel_iff zero_eq_1_divide_iff)

definition e_oplus' :: "complex\<Rightarrow>complex \<Rightarrow>complex"  where
  "e_oplus' u v = (1/(1+ e_inner' u v)) *\<^sub>R (u + ((1/(e_gamma_factor u)) *\<^sub>R v)
      + (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u)"


(*
lemma e_gamma_real2:
  assumes "norm u\<noteq>0" "e_gamma_factor' u = e_gamma_factor u"
  shows "norm u <1"
  sorry
*)
lemma help1_e:
  fixes x::real
  fixes y::real
  shows "x * y \<le> (x * y + x * y) /2" 
proof-
    have "(x - y)*(x - y) \<ge> 0"
      by simp
    moreover have " x * x - 2*x * y + y * y \<ge> 0"
      by (smt (verit, ccfv_SIG) power2_eq_square sum_squares_bound)
    moreover have "(x * x + y * y) \<ge> 2*x * y"
      using calculation(2) by linarith
    ultimately show ?thesis 
      by auto
qed
lemma smaller_than_1:
  assumes "norm u <1" "norm v<1"
  shows "(e_inner' u v) < 1"
  using e_inner'_def
  by (metis assms(1) assms(2) linorder_not_less mult_closed norm_cauchy_schwarz norm_mult order_less_le_trans)


lemma cauchy_swartz_here:
  shows "abs(inner u v) \<le> norm(u)*norm(v)"
    using Cauchy_Schwarz_ineq2 by blast

lemma help2_e:
  assumes "norm(u)<1" "norm(v)<1"
  shows "abs(inner u v) < 1"
  using cauchy_swartz_here[of u v]
  by (smt (verit) assms(1) assms(2) mult_le_cancel_left2 norm_not_less_zero)

(*
lemma help3_e:
  assumes "(norm u)\<noteq>0"
  shows "(Re (gamma_factor_e u) = (gamma_factor_e u)) \<longleftrightarrow> (norm u)<1"
proof-
  {
    assume "(norm u)<1"
    have "1-(norm u)^2 > 0"
      using \<open>norm u < 1\<close> real_sqrt_lt_1_iff by fastforce
    moreover have "Re(sqrt(1-(norm u)^2)) = sqrt(1-(norm u)^2)"
      using Re_complex_of_real by blast
    ultimately have "Re(gamma_factor_e u) = (gamma_factor_e u)"
      using gamma_factor_e_def 
      using Re_complex_of_real by blast
  } 
  moreover have "(norm u) < 1 \<longrightarrow> Re (gamma_factor_e u) = (gamma_factor_e u)"
    using calculation by blast

  moreover {
    assume "\<not>((norm u)\<le>1)"
    have "(norm u >1)"
      using \<open>\<not> norm u \<le> 1\<close> by force
    moreover have "1-(norm u)^2 < 0"
      by (simp add: calculation)
    moreover have "Im(sqrt(1-(norm u)^2)) \<noteq> 0"
      sorry
    ultimately have "Re (gamma_factor_e u) = (gamma_factor_e u)"
      sorry
  }
  ultimately show ?thesis sorry
qed
*)

lemma e_help1:
  assumes "norm u <1"
  shows "(norm u)^2 = 1 - 1/((e_gamma_factor u)^2)"
proof-
  have "e_gamma_factor u = 1/sqrt(1-(norm u)^2)"
    by (metis assms e_gamma_factor_def mult_closed norm_mult power2_eq_square)
  have "(e_gamma_factor u)^2 = 1/(1-(norm u)^2)"
    by (metis \<open>e_gamma_factor u = 1 / sqrt (1 - (cmod u)\<^sup>2)\<close> diff_ge_0_iff_ge e_gamma_factor_def less_eq_real_def power_one_over real_sqrt_eq_zero_cancel_iff real_sqrt_pow2 zero_eq_1_divide_iff)
  moreover have "1/((e_gamma_factor u)^2) = 1-(norm u)^2"
    by (simp add: calculation)
  ultimately show ?thesis 
    by linarith
qed

lemma e_help2:
  assumes "norm u <1" 
  shows "(1/(e_gamma_factor u)) + ((e_gamma_factor u) * ((norm u)^2))/(1+(e_gamma_factor u)) =1"
proof-
   have "e_gamma_factor u = 1/sqrt(1-(norm u)^2)"
    by (metis assms e_gamma_factor_def mult_closed norm_mult power2_eq_square)
  let ?g = "(e_gamma_factor u)"
  have "(1/(e_gamma_factor u)) + ((e_gamma_factor u) * ((norm u)^2))/(1+(e_gamma_factor u)) = 
    (1+?g + (?g)^2 * ((norm u)^2))/(?g* (1+?g))"
  proof-
    have "?g\<noteq>0"
      by (metis assms diff_zero divide_eq_0_iff e_help1 less_numeral_extra(4) norm_eq_sqrt_inner power2_eq_square power2_norm_eq_inner real_scaleR_def real_sqrt_lt_1_iff scaleR_eq_0_iff)
    moreover have "1+?g \<noteq>0"
      by (metis \<open>e_gamma_factor u = 1 / sqrt (1 - (cmod u)\<^sup>2)\<close> add.commute assms gamma_factor_def gamma_factor_positive_always less_add_one not_less_iff_gr_or_eq power2_eq_square)
    ultimately show ?thesis 
      by (metis (no_types, lifting) add_divide_distrib nonzero_divide_mult_cancel_right nonzero_mult_divide_mult_cancel_left numeral_One power_add_numeral2 power_one_right semiring_norm(2))
  qed
  moreover have " (1+?g + (?g)^2 * ((norm u)^2))/(?g* (1+?g)) = (1+?g + ?g^2 * (1-1/(?g^2)))/(?g*(1+?g))"
    by (simp add: assms e_help1)
  moreover have "(1+?g + ?g^2 * (1-1/(?g^2)))/(?g*(1+?g)) = (1+?g+?g^2-1)/(?g*(1+?g))"
    by (simp add: Rings.ring_distribs(4))
  moreover have "(1+?g+?g^2-1)/(?g*(1+?g)) = (?g*(1+?g))/(?g*(1+?g))"
    by (simp add: power2_eq_square ring_class.ring_distribs(1))
  moreover have "?g\<noteq>0"
    by (metis assms diff_zero divide_eq_0_iff e_help1 less_numeral_extra(4) norm_eq_sqrt_inner power2_eq_square power2_norm_eq_inner real_scaleR_def real_sqrt_lt_1_iff scaleR_eq_0_iff)
  moreover have "(norm u)^2 <1"
    by (simp add: abs_square_less_1 assms)
  moreover have "?g+1\<noteq>0"

    by (metis \<open>e_gamma_factor u = 1 / sqrt (1 - (cmod u)\<^sup>2)\<close> add.commute diff_gt_0_iff_gt divide_pos_pos e_gamma_factor_def le_add_same_cancel2 less_numeral_extra(1) linordered_nonzero_semiring_class.zero_le_one real_sqrt_gt_0_iff verit_comp_simplify1(3))

  ultimately show ?thesis 
    by (metis add.commute div_by_1 divide_divide_eq_right eq_divide_eq_1)
qed

lemma help3_e:
  assumes "norm u <1"
  shows "((e_gamma_factor u)^2 * (norm u)^2)/((1+e_gamma_factor u)^2) + (2*e_gamma_factor u)/
      ((e_gamma_factor u)*(1+e_gamma_factor u)) = 1"
proof-
  let ?g = "(e_gamma_factor u)"
  have "((e_gamma_factor u)^2 * (norm u)^2)/((1+e_gamma_factor u)^2) + (2*e_gamma_factor u)/
      ((e_gamma_factor u)*(1+e_gamma_factor u)) = (?g^2*(1-1/(?g^2)))/((1+?g)^2) + (2*?g)/(?g*(1+?g))"
    using assms e_help1 by presburger
  moreover have "?g\<noteq>0"
    using assms e_help2 by fastforce
  moreover have "1+?g\<noteq>0"
    by (metis add.right_neutral add_less_same_cancel1 assms division_ring_divide_zero e_help2 eq_divide_eq_1 not_one_less_zero zero_less_one) 
   have "(?g^2*(1-1/(?g^2)))/((1+?g)^2) + (2*?g)/(?g*(1+?g)) = (?g^2-1)/((1+?g)^2)+ (2*?g)/(?g*(1+?g))"
      by (simp add: calculation(2) right_diff_distrib)
    moreover have "(?g^2-1)/((1+?g)^2)+ (2*?g)/(?g*(1+?g)) = (?g*(?g^2-1))/(?g*(1+?g)^2) + (2*?g*(1+?g))/(?g*(1+?g)^2)"
      by (simp add: \<open>e_gamma_factor u \<noteq> 0\<close> mult.commute power2_eq_square)
    moreover have "(?g*(?g^2-1))/(?g*(1+?g)^2) + (2*?g*(1+?g))/(?g*(1+?g)^2) = (?g^3-?g+2*?g+2*?g^2)/(?g*(1+?g)^2)"
      by (smt (verit, best) add_divide_distrib inner_commute inner_real_def power2_diff power3_eq_cube real_inner_1_right right_diff_distrib')
    moreover have "(?g^3-?g+2*?g+2*?g^2)/(?g*(1+?g)^2) = (?g^3+?g+2*?g^2)/(?g*(1+?g)^2)"
      by fastforce
    moreover have "(?g^3+?g+2*?g^2)/(?g*(1+?g)^2) = (?g*(?g^2+1+2*?g))/(?g*(1+?g)^2)"
      by (simp add: distrib_left power2_eq_square power3_eq_cube)
    moreover have "(?g*(?g^2+1+2*?g))/(?g*(1+?g)^2)  = ((?g*(1+?g)^2)/(?g*(1+?g)^2))"
      by (simp add: power2_sum)
    ultimately show ?thesis 
      by (metis \<open>1 + e_gamma_factor u \<noteq> 0\<close> eq_divide_eq_1 mult_eq_0_iff power_eq_0_iff)
  qed

lemma help5_e:
  assumes "norm u<1" "norm v<1"
  shows "(norm u)^2 + (1/(e_gamma_factor u)^2)*((norm v)^2) = (norm u)^2 + (1-(norm u)^2)*((norm v)^2)"
  by (simp add: assms(1) e_help1)


lemma norm_plus_e:
  assumes "norm u < 1" "norm v <1"
  shows "norm(e_oplus' u v)^2 = (1/(1+e_inner' u v)^2) * (norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2))"
proof-
  have "norm(e_oplus' u v)^2 = norm((1/(1+ e_inner' u v)))^2 * norm( (u + ((1/(e_gamma_factor u)) *\<^sub>R v)
      + (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u))^2"  
    by (metis e_oplus'_def norm_scaleR power_mult_distrib real_norm_def)
  moreover have "norm((1/(1+ e_inner' u v)))^2=  (1/(1+e_inner' u v)^2)"
    by (simp add: power_one_over)
  moreover have "inner ( (u + ((1/(e_gamma_factor u)) *\<^sub>R v)
      + (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u)) ( (u + ((1/(e_gamma_factor u)) *\<^sub>R v)
      + (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u)) = 
      (norm u)^2 + (norm  ((1/(e_gamma_factor u)) *\<^sub>R v))^2 + (norm ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u) )^2 +
    2 * (inner u  ((1/(e_gamma_factor u)) *\<^sub>R v)) + 2* (inner u ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u)) +
      2* (inner ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u) ((1/(e_gamma_factor u)) *\<^sub>R v)) "
    by (smt (verit) inner_commute inner_right_distrib power2_norm_eq_inner)
  moreover have "(inner u  ((1/(e_gamma_factor u)) *\<^sub>R v)) = (1/(e_gamma_factor u)) * (inner u v)"
    using inner_scaleR_right by blast
  moreover have "(inner ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u) ((1/(e_gamma_factor u)) *\<^sub>R v)) =
     (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) * (1/(e_gamma_factor u)) * (inner u v) "
    by force
  moreover have "(inner u ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u)) =
      (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) * (inner u u)"
    using inner_scaleR_right by blast
  let ?g = "(e_gamma_factor u)"
  have A1:"2/?g * (inner u v) + 2*(?g*(norm u)^2/(1+?g))*(inner u v) = 2*(inner u v)"
  proof-
    have *:"1/?g + ?g*(norm u)^2/(1+?g) = 1"
      using assms(1) e_help2 by blast
    moreover have "2/?g * (inner u v) + 2*(?g*(norm u)^2/(1+?g))*(inner u v) = 2*(inner u v)* (1/?g + ?g*(norm u)^2/(1+?g))"
    proof-
      have "2/?g = 2*(1/?g)"
        by auto
      moreover have "2/?g*(inner u v) = 2*(inner u v)*1/?g"
        by simp
      moreover have "2*(?g*(norm u)^2/(1+?g))*(inner u v) = 2*(inner u v)*(?g*(norm u)^2/(1+?g))"
        by fastforce
      moreover have "2/?g * (inner u v) + 2*(?g*(norm u)^2/(1+?g))*(inner u v) = 2*(inner u v)*1/?g+   2*(inner u v)*(?g*(norm u)^2/(1+?g))"
        by force
      moreover have "2*(inner u v)*(1/?g)+   2*(inner u v)*(?g*(norm u)^2/(1+?g)) = 2*(inner u v)*(1/?g + ?g*(norm u)^2/(1+?g))"
        by (simp add: distrib_left)
        ultimately show ?thesis using * 
          by (metis times_divide_eq_right)
      qed
      ultimately show ?thesis
        by simp
    qed

  
    moreover have A2:"(?g/(1+?g))^2*(norm u)^2 * (inner u v)^2 + 2*(1/?g)*(?g/(1+?g))*(inner u v)^2 = (inner u v)^2"
    proof-
      have "(?g/(1+?g))^2*(norm u)^2 + 2*(1/?g)*(?g/(1+?g)) = 1"
      proof -
        have "\<forall>r n ra. ((r::real) / ra) ^ n = r ^ n / ra ^ n"
          by (simp add: power_divide)
        then show ?thesis
          using assms(1) help3_e by fastforce
      qed
      moreover have "(?g/(1+?g))^2*(norm u)^2 * (inner u v)^2 + 2*(1/?g)*(?g/(1+?g))*(inner u v)^2 = 
        ((?g/(1+?g))^2*(norm u)^2 + 2*(1/?g)*(?g/(1+?g))) * (inner u v)^2"
        by (simp add: ring_class.ring_distribs(2))
      ultimately show ?thesis
        by simp
    qed
    moreover have A3:"(norm u)^2 + (1/?g^2)*(norm v)^2 = (norm u)^2 + (1-(norm u)^2)*(norm v)^2"
      using assms(1) assms(2) help5_e by blast
    
    moreover have " (norm  ((1/(e_gamma_factor u)) *\<^sub>R v))^2 = (1/(e_gamma_factor u)^2) * norm(v)^2"
      by (simp add: power_divide)
    
    moreover have "(norm ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u) )^2 =
      (?g/(1+?g))^2*(inner u v)^2 * (norm u)^2"
      by (simp add: e_inner'_def power2_eq_square)
    moreover have "  (norm u)^2 + (norm  ((1/(e_gamma_factor u)) *\<^sub>R v))^2 + (norm ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u) )^2 +
    2 * (inner u  ((1/(e_gamma_factor u)) *\<^sub>R v)) + 2* (inner u ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u)) +
      2* (inner ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u) ((1/(e_gamma_factor u)) *\<^sub>R v)) =
    2*(inner u v) + (inner u v)^2 +  (norm u)^2 + (1-(norm u)^2)*(norm v)^2 "
    proof-
      have " (norm u)^2 + (norm  ((1/(e_gamma_factor u)) *\<^sub>R v))^2 + (norm ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u) )^2 +
    2 * (inner u  ((1/(e_gamma_factor u)) *\<^sub>R v)) + 2* (inner u ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u)) +
      2* (inner ((((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) *\<^sub>R u) ((1/(e_gamma_factor u)) *\<^sub>R v)) =
          (norm u)^2 + (1/(e_gamma_factor u)^2) * norm(v)^2 +  (?g/(1+?g))^2*(inner u v)^2 * (norm u)^2+
   2*(1/(e_gamma_factor u)) * (inner u v) + 2*  (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) * (1/(e_gamma_factor u)) * (inner u v)+
    2*  (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) * (inner u u)"
        using calculation(10) calculation(9) by force
      let ?g = "(e_gamma_factor u)"
      have "(norm u)^2 + (1/(e_gamma_factor u)^2) * norm(v)^2 +  (?g/(1+?g))^2*(inner u v)^2 * (norm u)^2+
   2*(1/(e_gamma_factor u)) * (inner u v) + 2*  (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) * (1/(e_gamma_factor u)) * (inner u v)+
    2*  (((e_gamma_factor u)/(1+(e_gamma_factor u)))*(e_inner' u v)) * (inner u u) =
  (norm u)^2 + (1/?g^2)*(norm v)^2 +  (?g/(1+?g))^2*(norm u)^2 * (inner u v)^2 + 2*(1/?g)*(?g/(1+?g))*(inner u v)^2+
     2/?g * (inner u v) + 2*(?g*(norm u)^2/(1+?g))*(inner u v)
"

        by (simp add: dot_square_norm e_inner'_def mult.commute mult.left_commute power2_eq_square)
        

        moreover have "(norm u)^2 + (1/?g^2)*(norm v)^2 +  (?g/(1+?g))^2*(norm u)^2 * (inner u v)^2 + 2*(1/?g)*(?g/(1+?g))*(inner u v)^2+
     2/?g * (inner u v) + 2*(?g*(norm u)^2/(1+?g))*(inner u v) =
   2*(inner u v) +  (inner u v)^2 + (norm u)^2 + (1-(norm u)^2)*(norm v)^2"
        using A1 A2 A3 

        by fastforce
      ultimately show ?thesis
        using \<open>(cmod u)\<^sup>2 + (cmod ((1 / e_gamma_factor u) *\<^sub>R v))\<^sup>2 + (cmod ((e_gamma_factor u / (1 + e_gamma_factor u) * e_inner' u v) *\<^sub>R u))\<^sup>2 + 2 * inner u ((1 / e_gamma_factor u) *\<^sub>R v) + 2 * inner u ((e_gamma_factor u / (1 + e_gamma_factor u) * e_inner' u v) *\<^sub>R u) + 2 * inner ((e_gamma_factor u / (1 + e_gamma_factor u) * e_inner' u v) *\<^sub>R u) ((1 / e_gamma_factor u) *\<^sub>R v) = (cmod u)\<^sup>2 + 1 / (e_gamma_factor u)\<^sup>2 * (cmod v)\<^sup>2 + (e_gamma_factor u / (1 + e_gamma_factor u))\<^sup>2 * (inner u v)\<^sup>2 * (cmod u)\<^sup>2 + 2 * (1 / e_gamma_factor u) * inner u v + 2 * (e_gamma_factor u / (1 + e_gamma_factor u) * e_inner' u v) * (1 / e_gamma_factor u) * inner u v + 2 * (e_gamma_factor u / (1 + e_gamma_factor u) * e_inner' u v) * inner u u\<close> by presburger
       
    qed
    moreover have "(norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2)) =    2*(inner u v) +  (inner u v)^2 + (norm u)^2 + (1-(norm u)^2)*(norm v)^2 "
    proof-
      have "(norm (u+v))^2 = (norm u)^2 + 2*(inner u v) + (norm v)^2"
        by (smt (verit, best) dot_square_norm inner_commute inner_left_distrib)
      moreover have "(norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2)) = 
    (norm u)^2 + 2*(inner u v) + (norm v)^2 - (norm u)^2*(norm v)^2 + (inner u v)^2 "
        by (simp add: calculation e_inner'_def)
      moreover have "(norm v)^2-(norm u)^2*(norm v)^2 = (1-(norm u)^2)*(norm v)^2"
  
        by (simp add: mult.commute right_diff_distrib')
      
      ultimately show ?thesis 
        by linarith
    qed
    ultimately show ?thesis
      by (metis dot_square_norm)
  qed
(*
definition my_sqrt::"real \<Rightarrow> complex" where
  "my_sqrt z = (if (z\<ge>0) then (SOME w. (w\<ge>0 \<and> (w * w = z))) else 
          (SOME w. w*w=z))"

lemma ms1:
  fixes z::real
  shows "z\<ge>0 \<longrightarrow> (\<exists>!x. (x=my_sqrt(z)))"
  by blast

lemma ms2:
  fixes z::real
  shows "z<0 \<longrightarrow> Im(my_sqrt(z))\<noteq>0"
  sorry *)


(*
lemma hh:
  assumes "x=sqrt(y)"
  shows "x*x = y"
  using sqrt_def root_def[of 2 x] 
  sorry
*)
(*
lemma hq:
  shows "\<forall>z.(z=sqrt(-1) \<longrightarrow>Im(z)\<noteq>0)"
proof(rule ccontr)
  assume "\<not>(\<forall>z.(z=sqrt(-1) \<longrightarrow>Im(z)\<noteq>0))"
  have "\<exists>z.(z=sqrt(-1) \<and> Im(z) = 0)"
    by simp
  moreover obtain "z" where "z=sqrt(-1) \<and> Im(z) = 0"
    using calculation by blast
  moreover have "z=sqrt(-1)"
    by (simp add: calculation(2))
  moreover have "z=0 \<or> z\<noteq>0"
    by blast
 
qed
*)
lemma help6_e:
  fixes a::real
  fixes b::real
  shows "(1+a)*(1+b) = 1+a*b+a+b"
  by (simp add: distrib_left ring_class.ring_distribs(2))


lemma gamma_plus:
  assumes "norm u < 1" "norm v < 1"
  shows "1/sqrt(1-norm(e_oplus' u v)^2) = (e_gamma_factor u)*(e_gamma_factor v)*
      abs(1+e_inner' u v)"
proof-
   have "e_gamma_factor u = 1/sqrt(1-(norm u)^2)"
     by (metis assms(1) e_gamma_factor_def mult_closed norm_power power2_eq_square)
  moreover have "e_gamma_factor v = 1/sqrt(1-(norm v)^2)"
    by (metis add_0 assms(2) div_0 division_ring_divide_zero e_gamma_factor_def e_help2 mult.commute mult_zero_right power2_eq_square)
  moreover have "1-norm(e_oplus' u v)^2 = 1-( (1/(1+e_inner' u v)^2) * (norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2)))"
    using assms(1) assms(2) norm_plus_e by presburger
  moreover have "1-( (1/(1+e_inner' u v)^2) * (norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2))) = ((1+e_inner' u v)^2 - (norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2)))/
    ((1+e_inner' u v)^2)"
  proof-
    have "e_inner' u v\<noteq>-1"
      by (metis assms(1) assms(2) e_inner'_def inner_scaleR_left mult.right_neutral norm_minus_cancel power2_abs power2_eq_square real_norm_def scaleR_minus1_left smaller_than_1 verit_comp_simplify1(1))
    moreover have "(1+e_inner' u v)^2 \<noteq>0"
      using calculation by fastforce
    moreover have " (1/(1+e_inner' u v)^2) * (norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2)) = (norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2))/((1+e_inner' u v)^2)"
      by simp
    ultimately show ?thesis
      by (smt (verit, ccfv_SIG) add_divide_distrib eq_divide_eq_1)    
  qed
  moreover have "((1+e_inner' u v)^2 - (norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2))) = 1 - (norm u)^2 - (norm v)^2
       + (norm u)^2*(norm v)^2"
  proof-
    have "(1+e_inner' u v)^2  = 1+2*inner u v + (inner u v)^2"
      by (simp add: e_inner'_def power2_sum)
    moreover have "norm(u+v)^2 - 
        ((norm u)^2 *(norm v)^2 - (e_inner' u v)^2) = (norm u)^2 + 2*(inner u v) + (norm v)^2
    - (norm u)^2*(norm v)^2 + (inner u v)^2"
      by (smt (z3) dot_norm e_inner'_def field_sum_of_halves)
    ultimately show ?thesis
      by linarith
  qed
  moreover have "1/sqrt(1-norm(e_oplus' u v)^2) = 1/sqrt(( 1 - (norm u)^2 - (norm v)^2
       + (norm u)^2*(norm v)^2)/(1+e_inner' u v)^2)"
    using calculation(3) calculation(4) calculation(5) by presburger
  moreover have "1/sqrt(1-norm(e_oplus' u v)^2) = abs(1+e_inner' u v)/sqrt(( 1 - (norm u)^2 - (norm v)^2
       + (norm u)^2*(norm v)^2))"
    by (simp add: calculation(6) real_sqrt_divide)
  moreover have " (e_gamma_factor u)*(e_gamma_factor v) = (1/sqrt(1-(norm u)^2))* (1/sqrt(1-(norm v)^2))"
    using calculation(1) calculation(2) by auto
    moreover have " (e_gamma_factor u)*(e_gamma_factor v) = 1/sqrt(( 1 - (norm u)^2 - (norm v)^2
       + (norm u)^2*(norm v)^2))"
    proof-
      let ?iz1 = "-1*(norm u)^2"
      let ?iz2 = "-1*(norm v)^2"
      have "(1-(norm u)^2)*(1-(norm v)^2) = 1 - (norm u)^2 - (norm v)^2
       + (norm u)^2*(norm v)^2 "
        using help6_e[of ?iz1 ?iz2] 
        by simp
      then show ?thesis 
        by (metis calculation(8) divide_divide_eq_left' mult_1 real_sqrt_mult times_divide_eq_left)
    qed
    ultimately show ?thesis 
      by (metis (no_types, lifting) mult_cancel_right1 times_divide_eq_left)
  qed

lemma gamma_plus1:
  assumes "norm u < 1" "norm v < 1"
  shows "1/sqrt(1-norm(e_oplus' u v)^2) \<noteq> 0"
  using assms(1) assms(2) divide_eq_0_iff e_help2 gamma_plus mult_eq_0_iff norm_plus_e real_sqrt_eq_zero_cancel_iff zero_power2 by force



lemma e_oplus'_in_ball:
  assumes "norm c1 < 1" "norm c2 < 1"
  shows "norm (e_oplus' c1 c2) < 1"
  by (smt (verit, ccfv_SIG) assms(1) assms(2) dot_square_norm e_gamma_factor_def gamma_factor_def gamma_factor_positive_always gamma_plus gamma_plus1 mult_nonneg_nonneg norm_eq_sqrt_inner real_sqrt_gt_0_iff real_sqrt_lt_1_iff zero_less_divide_1_iff)

lemma gamma_plus3:
  assumes "norm u < 1" "norm v < 1"
  shows "1/sqrt(1-norm(e_oplus' u v)^2) = (e_gamma_factor u)*(e_gamma_factor v)*
      (1+e_inner' u v)"
proof-
  have "abs(e_inner' u v) < 1"
    by (simp add: assms(1) assms(2) e_inner'_def help2_e)
  moreover have "1+e_inner' u v >0"
    using calculation by fastforce
  ultimately show ?thesis 
    by (simp add: assms(1) assms(2) gamma_plus)
qed

lemma gamma_plus4:
   assumes "norm u < 1" "norm v < 1"
  shows "e_gamma_factor (e_oplus' u v) = (e_gamma_factor u)*(e_gamma_factor v)*
      (1+e_inner' u v)"
proof-
  have "e_gamma_factor (e_oplus' u v) = 1/sqrt(1-norm(e_oplus' u v)^2) "
    by (metis (no_types, lifting) assms(1) assms(2) e_gamma_factor_def e_oplus'_in_ball mult_closed norm_mult numeral_One power_add_numeral power_one_right semiring_norm(2))
  then show ?thesis
    by (simp add: assms(1) assms(2) gamma_plus3)
qed


lift_definition e_oplus :: "PoincareDisc\<Rightarrow>PoincareDisc\<Rightarrow>PoincareDisc" (infixl "\<oplus>\<^sub>E" 100) is e_oplus'
  using e_oplus'_in_ball by presburger


lemma gamma_plus5:
  shows "e_gamma_factor (Rep_PoincareDisc(u \<oplus>\<^sub>E v)) =
 (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))*
      (1+inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))"
proof-
  have "norm (Rep_PoincareDisc u) < 1"
    using Rep_PoincareDisc by auto
  moreover have "norm (Rep_PoincareDisc v) < 1"
    using Rep_PoincareDisc by auto
  ultimately show ?thesis
    by (simp add: e_inner'_def e_oplus.rep_eq gamma_plus4)
qed


lemma inner_0:
  fixes a::complex
  shows "inner 0 a = 0"
  by simp

lemma m_left_id:
  shows "0\<^sub>E \<oplus>\<^sub>E a = a"
  using e_oplus_def e_oplus'_def inner_0
  by (metis Moebius_gyrodom'.of_dom add.right_neutral add_0 diff_zero div_by_1 e_gamma_factor_def e_inner'_def e_oplus.rep_eq e_ozero'_def e_ozero.rep_eq mult_zero_right norm_zero power2_eq_square real_sqrt_one scaleR_one scaleR_zero_left zero_less_one)
  
definition e_ominus' :: "complex \<Rightarrow> complex" where
  "e_ominus' v = - v"                                      

lemma e_ominus'_in_ball:
  assumes "norm z < 1"
  shows "norm (e_ominus' z) < 1"
  using assms
  unfolding e_ominus'_def
  by simp

lift_definition e_ominus :: "PoincareDisc \<Rightarrow> PoincareDisc" ("\<ominus>\<^sub>E") is e_ominus'
  using e_ominus'_in_ball by blast

definition e_otimes' :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "e_otimes' r z = m_otimes' r z"

lift_definition e_otimes :: "real \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<otimes>\<^sub>E" 105) is e_otimes'
  using cmod_m_otimes' cmod_m_otimes'_k e_otimes'_def by auto


lemma powr_sqrt_equal:
  fixes x::real
  assumes "x\<ge>0"
  shows "x powr (1/2) = sqrt(x)" 
  by (simp add: assms powr_half_sqrt)


lemma h1:
  assumes "cmod z <1" "cmod z \<noteq>0"
  shows "((1 + cmod z) powr (1/2) - (1 - cmod z) powr (1/2)) /
                     ((1 + cmod z) powr (1/2) + (1 - cmod z) powr (1/2)) = 
     (1- sqrt(1-(cmod z)^2))/(cmod z)"
proof-
  have "((1 + cmod z) powr (1/2) - (1 - cmod z) powr (1/2)) /
                     ((1 + cmod z) powr (1/2) + (1 - cmod z) powr (1/2)) =
    (sqrt(1 + cmod z)  - sqrt(1 - cmod z)) /
                     (sqrt(1 + cmod z)  + sqrt(1 - cmod z))"
    using assms powr_half_sqrt by auto
  moreover have "(sqrt(1 + cmod z)  - sqrt(1 - cmod z)) /
                     (sqrt(1 + cmod z)  + sqrt(1 - cmod z)) =
  (sqrt(1 + cmod z)  - sqrt(1 - cmod z)) /
                     (sqrt(1 + cmod z)  + sqrt(1 - cmod z)) * (sqrt(1 + cmod z)  - sqrt(1 - cmod z))/(sqrt(1 + cmod z)  - sqrt(1 - cmod z))"
    by simp
  moreover have "(sqrt(1 + cmod z)  - sqrt(1 - cmod z)) /
                     (sqrt(1 + cmod z)  + sqrt(1 - cmod z))  = (sqrt(1 + cmod z)  - sqrt(1 - cmod z))^2 /
                     (sqrt(1 + cmod z)^2  - sqrt(1 - cmod z)^2) "
    by (smt (verit, del_insts) calculation(2) divide_divide_eq_left' mult.commute power2_eq_square real_sqrt_mult sqrt_def square_diff_square_factored times_divide_eq_right)
  moreover have "(sqrt(1 + cmod z)  - sqrt(1 - cmod z)) /
                     (sqrt(1 + cmod z)  + sqrt(1 - cmod z)) = 
      (1+(cmod z) - 2*sqrt(1+cmod z)*sqrt(1-cmod z) + 1 - (cmod z))/(1+(cmod z)-1+(cmod z))"
    by (smt (verit, ccfv_SIG) assms calculation(3) norm_not_less_zero power2_diff real_less_lsqrt real_sqrt_ge_zero sqrt_le_D)
  moreover have " (1+(cmod z) - 2*sqrt(1+cmod z)*sqrt(1-cmod z) + 1 - (cmod z)) =
            (2-  2*sqrt(1+cmod z)*sqrt(1-cmod z))"
    by fastforce
  moreover have "sqrt(1+cmod z) * sqrt (1-cmod z) = sqrt((1+cmod z)*(1-cmod z))"
    using real_sqrt_mult by auto
  moreover have "sqrt((1+cmod z)*(1-cmod z)) = sqrt(1-(cmod z)^2)"
    by (metis mult_1 power2_eq_square square_diff_square_factored)
  ultimately show ?thesis
  proof -
    have f1: "\<forall>r ra. ((1::real) + 1) * (r / (ra + ra)) = r / ra"
      by simp
    have f2: "\<forall>r ra. (r::real) + r - (1 + 1) * ra = (1 + 1) * (r - ra)"
      by auto
    have "\<forall>r ra. (r::real) + ra - r = ra"
      by simp
    then have "(sqrt (1 + cmod z) - sqrt (1 - cmod z)) / (sqrt (1 - cmod z) + sqrt (1 + cmod z)) = (1 - sqrt ((1 + cmod z) * (1 - cmod z))) / cmod z"
      using f2 f1 by (metis (no_types) \<open>(sqrt (1 + cmod z) - sqrt (1 - cmod z)) / (sqrt (1 + cmod z) + sqrt (1 - cmod z)) = (1 + cmod z - 2 * sqrt (1 + cmod z) * sqrt (1 - cmod z) + 1 - cmod z) / (1 + cmod z - 1 + cmod z)\<close> \<open>1 + cmod z - 2 * sqrt (1 + cmod z) * sqrt (1 - cmod z) + 1 - cmod z = 2 - 2 * sqrt (1 + cmod z) * sqrt (1 - cmod z)\<close> \<open>sqrt (1 + cmod z) * sqrt (1 - cmod z) = sqrt ((1 + cmod z) * (1 - cmod z))\<close> add.commute mult.assoc one_add_one times_divide_eq_right)
    then show ?thesis
      by (metis \<open>((1 + cmod z) powr (1 / 2) - (1 - cmod z) powr (1 / 2)) / ((1 + cmod z) powr (1 / 2) + (1 - cmod z) powr (1 / 2)) = (sqrt (1 + cmod z) - sqrt (1 - cmod z)) / (sqrt (1 + cmod z) + sqrt (1 - cmod z))\<close> \<open>sqrt ((1 + cmod z) * (1 - cmod z)) = sqrt (1 - (cmod z)\<^sup>2)\<close> add.commute)
  qed
qed


lemma half_times_gamma:
  shows "((1/2)\<otimes>\<^sub>E a) = Abs_PoincareDisc (cor (e_gamma_factor (Rep_PoincareDisc a)) /
        (1+(e_gamma_factor (Rep_PoincareDisc a))) * (Rep_PoincareDisc a)) "
proof-
  have "norm (Rep_PoincareDisc a) = 0 \<or> norm (Rep_PoincareDisc a)\<noteq>0"
    by simp
  moreover {
    assume "norm (Rep_PoincareDisc a) = 0"
    have "(e_gamma_factor (Rep_PoincareDisc a)) = 1"
      by (simp add: \<open>cmod (Rep_PoincareDisc a) = 0\<close> e_gamma_factor_def)
    moreover have " (cor (e_gamma_factor (Rep_PoincareDisc a)) /
        (1+(e_gamma_factor (Rep_PoincareDisc a))) * (Rep_PoincareDisc a)) = 0"
      using \<open>cmod (Rep_PoincareDisc a) = 0\<close> by auto
    ultimately have ?thesis 
      by (simp add: e_otimes'_def e_otimes_def m_otimes'_def)
  }
  moreover {
    assume "norm (Rep_PoincareDisc a) \<noteq>0"
    have "(Rep_PoincareDisc a)\<noteq>0"
      using \<open>cmod (Rep_PoincareDisc a) \<noteq> 0\<close> by auto
    moreover have "(1/2)\<otimes>\<^sub>m a = Abs_PoincareDisc(((1 + (cmod (Rep_PoincareDisc a))) powr (1/2) 
- (1 - cmod (Rep_PoincareDisc a)) powr (1/2)) /
                   ((1 + cmod (Rep_PoincareDisc a)) powr (1/2) + (1 - cmod (Rep_PoincareDisc a)) powr (1/2))
          * ((Rep_PoincareDisc a)/(cmod (Rep_PoincareDisc a))))"
      by (metis Moebius_gyrodom'.of_dom calculation m_otimes'_def m_otimes'_k_def m_otimes.rep_eq)
    moreover have "(1/2)\<otimes>\<^sub>m a = Abs_PoincareDisc ((  (1- sqrt(1-(cmod (Rep_PoincareDisc a))^2))/(cmod (Rep_PoincareDisc a)))
      * ((Rep_PoincareDisc a)/(cmod (Rep_PoincareDisc a))))"
      using Rep_PoincareDisc \<open>cmod (Rep_PoincareDisc a) \<noteq> 0\<close> calculation(2) h1 by force
    moreover have "(1/2)\<otimes>\<^sub>m a=Abs_PoincareDisc ((  (1- sqrt(1-(cmod (Rep_PoincareDisc a))^2))/((cmod (Rep_PoincareDisc a))^2))
      * ((Rep_PoincareDisc a)))"
      by (simp add: calculation(3) power2_eq_square)
    ultimately have ?thesis 
    proof-
      have "cmod (Rep_PoincareDisc a) < 1"
        using Rep_PoincareDisc by blast
      moreover have "1/(sqrt(1-(cmod (Rep_PoincareDisc a))^2)) = e_gamma_factor (Rep_PoincareDisc a)"
        using calculation e_gamma_factor_def e_help2 power2_eq_square by fastforce
      moreover have " (1- sqrt(1-(cmod (Rep_PoincareDisc a))^2)) = 1-1/(e_gamma_factor (Rep_PoincareDisc a))"
        by (metis \<open>1 / sqrt (1 - (cmod (Rep_PoincareDisc a))\<^sup>2) = e_gamma_factor (Rep_PoincareDisc a)\<close> div_by_1 divide_divide_eq_right mult_1)
      moreover have "(cmod (Rep_PoincareDisc a))^2 = 1-1/(e_gamma_factor (Rep_PoincareDisc a))^2"
        using calculation(1) e_help1 by blast
      moreover have "(1-1/(e_gamma_factor (Rep_PoincareDisc a))) =
          ((e_gamma_factor (Rep_PoincareDisc a)) - 1)/(e_gamma_factor (Rep_PoincareDisc a))"
        by (metis calculation(1) calculation(2) diff_divide_distrib divide_self_if gamma_factor_def gamma_factor_positive_always order_less_irrefl power2_eq_square)
      moreover have "1-1/(e_gamma_factor (Rep_PoincareDisc a))^2 = ((e_gamma_factor (Rep_PoincareDisc a))^2-1)/((e_gamma_factor (Rep_PoincareDisc a))^2) "
        by (metis calculation(5) diff_divide_distrib divide_self_if power_not_zero)
      moreover have " ((e_gamma_factor (Rep_PoincareDisc a))^2-1)/((e_gamma_factor (Rep_PoincareDisc a))^2) =
         ((  ((e_gamma_factor (Rep_PoincareDisc a)) - 1))*(  ((e_gamma_factor (Rep_PoincareDisc a)) + 1)))/((e_gamma_factor (Rep_PoincareDisc a))^2) "
        by (simp add: power2_eq_square square_diff_one_factored)
      moreover have "(1-1/(e_gamma_factor (Rep_PoincareDisc a)))/(1-1/(e_gamma_factor (Rep_PoincareDisc a))^2) = 
        (  ((e_gamma_factor (Rep_PoincareDisc a)) - 1)/(e_gamma_factor (Rep_PoincareDisc a)))/( ((  ((e_gamma_factor (Rep_PoincareDisc a)) - 1))*(  ((e_gamma_factor (Rep_PoincareDisc a)) + 1)))/((e_gamma_factor (Rep_PoincareDisc a))^2))"
        using calculation(5) calculation(6) calculation(7) by presburger
      moreover have "(1-1/(e_gamma_factor (Rep_PoincareDisc a)))/(1-1/(e_gamma_factor (Rep_PoincareDisc a))^2) =
       (e_gamma_factor (Rep_PoincareDisc a)) /
        (1+(e_gamma_factor (Rep_PoincareDisc a))) "
        by (smt (verit) \<open>cmod (Rep_PoincareDisc a) \<noteq> 0\<close> add_divide_distrib calculation(2) calculation(4) calculation(8) diff_divide_distrib distrib_left div_self divide_cancel_right divide_divide_eq_left' divide_divide_eq_right divide_divide_times_eq divide_eq_0_iff left_diff_distrib mult.commute mult.left_commute mult_cancel_left2 mult_eq_0_iff nonzero_mult_div_cancel_left norm_one numerals(1) one_power2 power2_eq_square power_divide power_eq_0_iff power_one_over power_one_right real_sqrt_eq_zero_cancel_iff real_sqrt_zero right_diff_distrib' square_diff_one_factored times_divide_eq_left times_divide_eq_right)
      ultimately show ?thesis 
        by (metis Moebius_gyrodom'.of_dom \<open>(1 / 2) \<otimes>\<^sub>m a = Abs_PoincareDisc (cor ((1 - sqrt (1 - (cmod (Rep_PoincareDisc a))\<^sup>2)) / (cmod (Rep_PoincareDisc a))\<^sup>2) * Rep_PoincareDisc a)\<close> e_otimes'_def e_otimes.rep_eq m_otimes.rep_eq of_real_divide)
    qed
  }
  ultimately show ?thesis by blast
qed

lemma iso_ei_mo_help1:
  shows "(1/2)\<otimes>\<^sub>m u \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>m v = Abs_PoincareDisc (m_plus_full (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m u))  
          (Rep_PoincareDisc ((1/2) \<otimes>\<^sub>m v)))"
  using m_plus_full_m_plus by blast

lemma e_gamma_norm_connection:
  assumes "norm v <1"
  shows "(norm v)^2 = ((e_gamma_factor v)^2 - 1)/(e_gamma_factor v)^2"
  by (smt (verit, ccfv_SIG) add_divide_distrib assms divide_self division_ring_divide_zero e_help1 norm_le_square norm_one one_power2)
lemma iso_ei_mo_help2:
  assumes "norm v <1"
  shows "norm (((e_gamma_factor v)/(1+e_gamma_factor v)) *\<^sub>R  v)^2 = ((e_gamma_factor v)-1)/((e_gamma_factor v)+1)"
proof-
  have "norm (((e_gamma_factor v)/(1+e_gamma_factor v)) *\<^sub>R  v)^2 =((e_gamma_factor v)/(1+e_gamma_factor v))^2 *(norm v)^2"
    by (simp add: power2_eq_square)
  moreover have "((e_gamma_factor v)/(1+e_gamma_factor v))^2 *(norm v)^2 = 
      ((e_gamma_factor v)/(1+e_gamma_factor v))^2 *((e_gamma_factor v)^2 - 1)/(e_gamma_factor v)^2"
    by (simp add: assms e_gamma_norm_connection)
  moreover have " ((e_gamma_factor v)/(1+e_gamma_factor v))^2 =  ((e_gamma_factor v)^2/(1+e_gamma_factor v)^2)"
    by (simp add: power_divide)
  moreover have "(e_gamma_factor v)^2 - 1 = ((e_gamma_factor v) - 1)* ((e_gamma_factor v) + 1)"
    by (simp add: power2_eq_square square_diff_one_factored)
  moreover have " ((e_gamma_factor v)^2/(1+e_gamma_factor v)^2) * ((e_gamma_factor v) - 1)* ((e_gamma_factor v) + 1)/(e_gamma_factor v)^2 =
            ((e_gamma_factor v)-1)/(1+e_gamma_factor v)"
  proof-
    have "e_gamma_factor v \<noteq>0"
      using assms e_help2 by fastforce
    moreover have "1+e_gamma_factor v \<noteq>0"
      using assms help3_e by force
    ultimately show ?thesis
      by (simp add: add.commute power2_eq_square)
  qed
  ultimately show ?thesis 
    by auto
qed

lemma iso_ei_mo_help2_1:
  assumes "norm v <1"
  shows "norm (((e_gamma_factor v)/(1+e_gamma_factor v)) *\<^sub>R  v)^2 = 
  ((e_gamma_factor v)/(1+e_gamma_factor v))^2 * (norm v)^2 "
  by (simp add: power2_eq_square)

lemma  iso_ei_mo_help3:
  assumes "norm v < 1"
  shows "1 + ((e_gamma_factor v)-1)/(1+e_gamma_factor v) = (2*e_gamma_factor v)/(1+e_gamma_factor v)"
proof-
  have "1+e_gamma_factor v\<noteq>0"
    using assms e_help2 by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_ei_mo_help4:
  assumes "norm v < 1"
  shows "1 - ((e_gamma_factor v)-1)/(1+e_gamma_factor v) = 2/(1+e_gamma_factor v)"
proof-
  have "1+e_gamma_factor v\<noteq>0"
    using assms e_help2 by fastforce
  then show ?thesis 
    by (smt (verit, del_insts) diff_divide_distrib divide_self)
qed

lemma  iso_ei_mo_help5:
  assumes "norm v < 1" "norm u <1"
  shows "1+ (((e_gamma_factor v)-1)/(1+e_gamma_factor v))*  (((e_gamma_factor u)-1)/(1+e_gamma_factor u)) =
      (2*(1+(e_gamma_factor u)*(e_gamma_factor v)))/((1+e_gamma_factor v)*(1+e_gamma_factor u))"
proof-
  have "1+e_gamma_factor v\<noteq>0"
    using assms e_help2 by fastforce
  moreover have "1+e_gamma_factor u\<noteq>0"
    using assms(2) iso_ei_mo_help3 by fastforce
  moreover have "(1+e_gamma_factor v)*(1+e_gamma_factor u) = 1+ (e_gamma_factor v) +
    (e_gamma_factor u) + (e_gamma_factor u)*(e_gamma_factor v)"
    by (simp add: help1)
  moreover have "((e_gamma_factor v)-1)*((e_gamma_factor u)-1) =
        (e_gamma_factor u)*(e_gamma_factor v) - (e_gamma_factor u)
    - (e_gamma_factor v) +1"
    by (smt (verit) help1 mult.commute)
  moreover have "1+ (((e_gamma_factor v)-1)/(1+e_gamma_factor v))*  (((e_gamma_factor u)-1)/(1+e_gamma_factor u)) = 
    ((1+e_gamma_factor v)*(1+e_gamma_factor u)+((e_gamma_factor u)-1)*((e_gamma_factor v)-1))/((1+e_gamma_factor v)*(1+e_gamma_factor u))"
    by (simp add: add_divide_distrib calculation(1) calculation(2))
    ultimately show ?thesis 
      by (simp add: mult.commute)
qed

lemma  iso_ei_mo_help6:
  assumes "norm u <1" "norm v <1"
  shows "1 + (2*((e_gamma_factor u)/(1+e_gamma_factor u)) *
 ((e_gamma_factor v)/(1+e_gamma_factor v)))*inner u v + (norm ( ((e_gamma_factor v)/(1+e_gamma_factor v)) *\<^sub>R v))^2=
    (2*(e_gamma_factor v)/(1+e_gamma_factor v) + (2*(e_gamma_factor v)*(e_gamma_factor u)/((1+e_gamma_factor v)*(1+e_gamma_factor u))) * inner u v)"
proof-
  have "(norm ( ((e_gamma_factor v)/(1+e_gamma_factor v)) *\<^sub>R v))^2 =  ((e_gamma_factor v)-1)/((e_gamma_factor v)+1)"
    using assms(2) iso_ei_mo_help2 by presburger
  moreover have "1+ ((e_gamma_factor v)-1)/((e_gamma_factor v)+1) = (2*(e_gamma_factor v)/(1+e_gamma_factor v))"
    by (smt (verit, del_insts) assms(2) iso_ei_mo_help3)
  ultimately show ?thesis 
    by (simp add: mult.commute mult.left_commute)
qed

lemma  iso_ei_mo_help7:
  assumes "norm u <1" 
  shows "(1-(norm (((e_gamma_factor u)/(1+e_gamma_factor u)) *\<^sub>R u))^2) = 
      2/(1+e_gamma_factor u)"
  by (metis add.commute assms iso_ei_mo_help2 iso_ei_mo_help4)

lemma  iso_ei_mo_help8:
  assumes "norm u <1" "norm v <1"
  shows " 1+ (norm (((e_gamma_factor u)/(1+e_gamma_factor u)) *\<^sub>R u))^2 *
      (norm (((e_gamma_factor v)/(1+e_gamma_factor v)) *\<^sub>R v))^2 =
     (2*(1+(e_gamma_factor u)*(e_gamma_factor v)))/((1+e_gamma_factor v)*(1+e_gamma_factor u)) "
  by (smt (verit) assms(1) assms(2) iso_ei_mo_help2 iso_ei_mo_help5 mult.commute)

lemma  iso_ei_mo_help8_1:
  assumes "norm u <1" "norm v <1"
  shows " 1+ (((e_gamma_factor u)-1)/(1+e_gamma_factor u))  *
       (((e_gamma_factor v)-1)/(1+e_gamma_factor v)) =
     (2*(1+(e_gamma_factor u)*(e_gamma_factor v)))/((1+e_gamma_factor v)*(1+e_gamma_factor u)) "
  by (metis assms(1) assms(2) iso_ei_mo_help5 mult.commute)
lemma iso_ei_inner_help:
  fixes a::real
  fixes b::real
  shows "inner (a*x) (b*y) = (a*b)* inner x y"
  by fastforce

lemma iso_ei_inner_help2:
  shows "(Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) = (cor (e_gamma_factor (Rep_PoincareDisc u)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc u)) *
      Rep_PoincareDisc u)"
proof-
  have "Rep_PoincareDisc (Abs_PoincareDisc ((cor (e_gamma_factor (Rep_PoincareDisc u)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc u)) *
      Rep_PoincareDisc u))) = (cor (e_gamma_factor (Rep_PoincareDisc u)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc u)) *
      Rep_PoincareDisc u)"
    by (smt (verit, del_insts) Moebius_gyrodom'.to_dom divide_eq_0_iff divide_eq_1_iff e_gamma_factor_def less_1_mult less_divide_eq_1_pos mult_closed mult_eq_0_iff mult_pos_pos norm_divide norm_ge_zero norm_of_real of_real_0 one_power2 power2_eq_square real_sqrt_gt_0_iff real_sqrt_lt_1_iff)
   show ?thesis 
     using \<open>Rep_PoincareDisc (Abs_PoincareDisc (cor (e_gamma_factor (Rep_PoincareDisc u)) / cor (1 + e_gamma_factor (Rep_PoincareDisc u)) * Rep_PoincareDisc u)) = cor (e_gamma_factor (Rep_PoincareDisc u)) / cor (1 + e_gamma_factor (Rep_PoincareDisc u)) * Rep_PoincareDisc u\<close> e_otimes'_def e_otimes_def half_times_gamma m_otimes_def by presburger
qed

lemma iso_ei_inner_mo_help3:
  shows " (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2 =
  ((e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v)))^2 * (norm (Rep_PoincareDisc v))^2 "
  proof-
    have "(cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2 = (norm ( (cor (e_gamma_factor (Rep_PoincareDisc v)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc v)) *
      Rep_PoincareDisc v)))^2 "
      using iso_ei_inner_help2 by auto
    moreover have "(norm ( (cor (e_gamma_factor (Rep_PoincareDisc v)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc v)) *
      Rep_PoincareDisc v)))^2 =  (norm(cor (e_gamma_factor (Rep_PoincareDisc v)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc v))))^2 * (norm (Rep_PoincareDisc v))^2"
      by (metis norm_mult power_mult_distrib)
    moreover have "(norm(cor (e_gamma_factor (Rep_PoincareDisc v)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc v))))^2 =  ((e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v)))^2 "
      by (metis norm_of_real of_real_divide power2_abs)
    ultimately show ?thesis 
      by presburger
  qed

lemma iso_ei_inner_mo_help4:
  shows "  inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) =
   (cor (e_gamma_factor (Rep_PoincareDisc u)) /
      (1 + e_gamma_factor (Rep_PoincareDisc u))) * 
     (cor (e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v))) *
    inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)"
  proof-
    have "(1 / 2) \<otimes>\<^sub>E v =
    Abs_PoincareDisc
     (cor (e_gamma_factor (Rep_PoincareDisc v)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc v)) *
      Rep_PoincareDisc v)"
      using half_times_gamma by auto
      
    moreover have "(1 / 2) \<otimes>\<^sub>E u =
    Abs_PoincareDisc
     (cor (e_gamma_factor (Rep_PoincareDisc u)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc u)) *
      Rep_PoincareDisc u)"
      using half_times_gamma by blast
    moreover have " inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) =
    inner ((cor (e_gamma_factor (Rep_PoincareDisc v)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc v)) *
      Rep_PoincareDisc v)) (  (cor (e_gamma_factor (Rep_PoincareDisc u)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc u)) *
      Rep_PoincareDisc u))"
      by (simp add: inner_commute iso_ei_inner_help2)
    moreover have " inner ((cor (e_gamma_factor (Rep_PoincareDisc v)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc v)) *
      Rep_PoincareDisc v)) (  (cor (e_gamma_factor (Rep_PoincareDisc u)) /
      cor (1 + e_gamma_factor (Rep_PoincareDisc u)) *
      Rep_PoincareDisc u)) =    (cor (e_gamma_factor (Rep_PoincareDisc u)) /
      (1 + e_gamma_factor (Rep_PoincareDisc u))) * 
     (cor (e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v))) *
    inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)"
      by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1) inner_commute inner_mult_left of_real_divide of_real_mult)
    ultimately show ?thesis 
      by presburger
qed

lemma iso_ei_mo_inner_help5:
  shows "inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) =
   ((e_gamma_factor (Rep_PoincareDisc u)) /
      (1 + e_gamma_factor (Rep_PoincareDisc u))) * 
     ( (e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v))) *
    inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)"
  by (metis iso_ei_inner_mo_help4 of_real_divide of_real_eq_iff of_real_mult)


lemma iso_ei_mo_inner_help6:
  shows "(1 +
      2 *
      inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) +
      (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2) *\<^sub>R
     Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u) = (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v))) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) *
    ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u)"
proof-
  have "inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) =
   ((e_gamma_factor (Rep_PoincareDisc u)) /
      (1 + e_gamma_factor (Rep_PoincareDisc u))) * 
     ( (e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v))) *
    inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)"
    using iso_ei_mo_inner_help5 by blast
  moreover have " (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2 =
  ((e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v)))^2 * (norm (Rep_PoincareDisc v))^2 "
    using iso_ei_inner_mo_help3 by blast
  moreover have " ((e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v)))^2 * (norm (Rep_PoincareDisc v))^2 = ((e_gamma_factor (Rep_PoincareDisc v))-1)/(1+e_gamma_factor  (Rep_PoincareDisc v))
    "

  proof-
    have "norm (Rep_PoincareDisc v) <1"
      using Rep_PoincareDisc by auto
    then show ?thesis using iso_ei_mo_help2_1 iso_ei_mo_help2
      by force
  qed
      
  moreover have "Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u) =  ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u) "
    by (simp add: iso_ei_inner_help2)
  moreover have "1 + ((e_gamma_factor (Rep_PoincareDisc v))-1)/(1+e_gamma_factor  (Rep_PoincareDisc v)) = (2*e_gamma_factor  (Rep_PoincareDisc v))/(1+e_gamma_factor  (Rep_PoincareDisc v))"
    by (metis (no_types, opaque_lifting) ab_group_add_class.ab_diff_conv_add_uminus add.right_neutral cancel_comm_monoid_add_class.diff_cancel div_by_1 dot_square_norm e_gamma_factor_def iso_ei_mo_help3 mult_2 norm_eq_sqrt_inner real_sqrt_lt_1_iff uminus_add_conv_diff)
  
  moreover have "(1 +
      2 *
      inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) +
      (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2) *\<^sub>R
     Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u) = (
1+ 2* ((e_gamma_factor (Rep_PoincareDisc u)) /
      (1 + e_gamma_factor (Rep_PoincareDisc u))) * 
     ( (e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v))) *
    inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) + ((e_gamma_factor (Rep_PoincareDisc v))-1)/(1+e_gamma_factor  (Rep_PoincareDisc v)) )
  *(((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u))"
    by (metis (mono_tags, opaque_lifting) calculation(2) calculation(3) calculation(4) iso_ei_mo_inner_help5 mult.assoc scaleR_conv_of_real)
  ultimately show ?thesis
    by (smt (verit, best) diff_divide_distrib distrib_left inner_commute inner_real_def mult.assoc of_real_mult)
qed

lemma iso_ei_mo_inner_help7_1:
  shows "(cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2 =
((e_gamma_factor (Rep_PoincareDisc u))-1)/(1+e_gamma_factor  (Rep_PoincareDisc u))
    "
proof-
    have  " ((e_gamma_factor (Rep_PoincareDisc u)) /
       (1 + e_gamma_factor (Rep_PoincareDisc u)))^2 * (norm (Rep_PoincareDisc u))^2 = ((e_gamma_factor (Rep_PoincareDisc u))-1)/(1+e_gamma_factor  (Rep_PoincareDisc u))
    "
    proof-
   have "norm (Rep_PoincareDisc u) <1"
      using Rep_PoincareDisc by auto
    then show ?thesis using iso_ei_mo_help2_1 iso_ei_mo_help2
      by force
  qed
  moreover have "(cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2 =  ((e_gamma_factor (Rep_PoincareDisc u)) /
       (1 + e_gamma_factor (Rep_PoincareDisc u)))^2 * (norm (Rep_PoincareDisc u))^2"
    using iso_ei_inner_mo_help3 by blast
  moreover have "(cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2 =
((e_gamma_factor (Rep_PoincareDisc u))-1)/(1+e_gamma_factor  (Rep_PoincareDisc u))
    "
    using calculation(1) calculation(2) by presburger
  ultimately show ?thesis by blast
qed


lemma iso_ei_mo_inner_help7:
  shows "(1 - (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2) *\<^sub>R
     Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v) = 2*(e_gamma_factor (Rep_PoincareDisc v))/
    ((1+e_gamma_factor (Rep_PoincareDisc v)) *(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc v)"
proof-
 have "(cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2 =
((e_gamma_factor (Rep_PoincareDisc u))-1)/(1+e_gamma_factor  (Rep_PoincareDisc u))
    "
   using iso_ei_mo_inner_help7_1 by blast
  moreover have "1 - ((e_gamma_factor (Rep_PoincareDisc u))-1)/
(1+e_gamma_factor (Rep_PoincareDisc u)) = 2/(1+e_gamma_factor (Rep_PoincareDisc u))"
  proof-
    have "norm (Rep_PoincareDisc u)<1"
      using Rep_PoincareDisc by blast
    then show ?thesis 
      using iso_ei_mo_help4 by auto
  qed
  moreover have "  Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v) =(e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v))
      *(Rep_PoincareDisc v)"
    using iso_ei_inner_help2 by force
  moreover have "(1 - (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2) *\<^sub>R
     Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v) =(1 - ((e_gamma_factor (Rep_PoincareDisc u))-1)/
(1+e_gamma_factor (Rep_PoincareDisc u)))*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v))
      *(Rep_PoincareDisc v)) "
    by (simp add: calculation(3) iso_ei_mo_inner_help7_1 scaleR_conv_of_real)
  ultimately  show ?thesis 
    by (simp add: of_real_def)
qed 

lemma iso_ei_mo_inner_help8:
  shows  "   1 +
         2 *
         inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u))
          (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) +
         (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2 *
         (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2 =
    2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u)))
  + 2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u)))"
proof-
  have "inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) =
   ((e_gamma_factor (Rep_PoincareDisc u)) /
      (1 + e_gamma_factor (Rep_PoincareDisc u))) * 
     ( (e_gamma_factor (Rep_PoincareDisc v)) /
       (1 + e_gamma_factor (Rep_PoincareDisc v))) *
    inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)"
    using iso_ei_mo_inner_help5 by presburger
  moreover have "    (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2 = ((e_gamma_factor (Rep_PoincareDisc u))-1)/(1+e_gamma_factor  (Rep_PoincareDisc u))"
    using iso_ei_mo_inner_help7_1 by blast
  moreover have " (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2 = ((e_gamma_factor (Rep_PoincareDisc v))-1)/(1+e_gamma_factor  (Rep_PoincareDisc v))"
    using iso_ei_mo_inner_help7_1 by blast
  moreover have "1 +  (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2 *
         (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2 = 1 +( ((e_gamma_factor (Rep_PoincareDisc u))-1)/(1+e_gamma_factor  (Rep_PoincareDisc u)))*( ((e_gamma_factor (Rep_PoincareDisc v))-1)/(1+e_gamma_factor  (Rep_PoincareDisc v))) "
    using calculation(2) calculation(3) by presburger

  moreover have " 1+ (((e_gamma_factor (Rep_PoincareDisc u))-1)/(1+e_gamma_factor  (Rep_PoincareDisc u)))  *
       (((e_gamma_factor  (Rep_PoincareDisc v))-1)/(1+e_gamma_factor  (Rep_PoincareDisc v))) =
     (2*(1+(e_gamma_factor  (Rep_PoincareDisc u))*(e_gamma_factor  (Rep_PoincareDisc v))))/((1+e_gamma_factor  (Rep_PoincareDisc v))*(1+e_gamma_factor  (Rep_PoincareDisc u)))"
  proof-
    have "norm (Rep_PoincareDisc u) < 1"
      using Rep_PoincareDisc by blast
    moreover have "norm (Rep_PoincareDisc v) <1"
      using Rep_PoincareDisc by auto
    ultimately show ?thesis 
      using iso_ei_mo_help8_1 by blast
  qed
  ultimately show ?thesis 
    by (smt (verit, ccfv_threshold) distrib_left divide_divide_eq_left' mult.commute times_divide_eq_right)
qed

lemma iso_ei_mo_help9:
  shows "m_plus_full (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m v))
 = ((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v))) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) *
    ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u) +  2*(e_gamma_factor (Rep_PoincareDisc v))/
    ((1+e_gamma_factor (Rep_PoincareDisc v)) *(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc v))/( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u)))
  + 2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))"
proof-
  have " m_plus_full (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u))
     (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) =
    ((1 +
      2 *
      inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) +
      (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2) *\<^sub>R
     Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u) +
     (1 - (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2) *\<^sub>R
     Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) /
    cor (1 +
         2 *
         inner (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u))
          (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)) +
         (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m u)))\<^sup>2 *
         (cmod (Rep_PoincareDisc ((1 / 2) \<otimes>\<^sub>m v)))\<^sup>2)"
    by (meson m_plus_full_def)
  then show ?thesis
    using iso_ei_mo_inner_help8[of u v]
          iso_ei_mo_inner_help7[of u v]
          iso_ei_mo_inner_help6[of u v]
    by presburger
qed

lemma iso_ei_mo_help10:
  shows "(1/2) \<otimes>\<^sub>E ( u \<oplus>\<^sub>E v) =  Abs_PoincareDisc(
    (((( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
       )/( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
      * (1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)) +1))*((
     ((Rep_PoincareDisc u) + cor(1/(e_gamma_factor (Rep_PoincareDisc u)))*(Rep_PoincareDisc v) +
    (cor(e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (Rep_PoincareDisc u)))))))"
proof-
  have " (1/2) \<otimes>\<^sub>E ( u \<oplus>\<^sub>E v)  = Abs_PoincareDisc (cor (e_gamma_factor (Rep_PoincareDisc  ( u \<oplus>\<^sub>E v) )) /
        (1+(e_gamma_factor (Rep_PoincareDisc  ( u \<oplus>\<^sub>E v) ))) * (Rep_PoincareDisc  ( u \<oplus>\<^sub>E v) )) "
    using half_times_gamma by force
  moreover have "e_gamma_factor (Rep_PoincareDisc  ( u \<oplus>\<^sub>E v) ) =
      (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
      * (1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)) "
  proof-
    have "norm (Rep_PoincareDisc u) <1"
      using Rep_PoincareDisc by auto
    moreover have "norm (Rep_PoincareDisc v) <1"
       using Rep_PoincareDisc by auto
     ultimately show ?thesis 
       using gamma_plus5 by auto
   qed
   moreover have " u \<oplus>\<^sub>E v = Abs_PoincareDisc ((1/(1+ inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)))
    * ((Rep_PoincareDisc u) + cor(1/(e_gamma_factor (Rep_PoincareDisc u)))*(Rep_PoincareDisc v) +
    (cor(e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (Rep_PoincareDisc u)))"
     using e_oplus_def e_oplus'_def
     by (metis (no_types, opaque_lifting) Moebius_gyrodom'.of_dom e_inner'_def e_oplus.rep_eq of_real_divide of_real_mult scaleR_conv_of_real)
   moreover have "(1/2) \<otimes>\<^sub>E ( u \<oplus>\<^sub>E v)  = Abs_PoincareDisc ((( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
      * (1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)) )/( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
      * (1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)) +1))*(((1/(1+ inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)))
    * ((Rep_PoincareDisc u) + cor(1/(e_gamma_factor (Rep_PoincareDisc u)))*(Rep_PoincareDisc v) +
    (cor(e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (Rep_PoincareDisc u)))))"
     by (smt (verit, del_insts) calculation(2) e_inner'_def e_oplus'_def e_oplus.rep_eq half_times_gamma of_real_divide of_real_mult scaleR_conv_of_real)
   moreover have "(1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v))\<noteq>0"
     
     by (metis Moebius_gyrodom'.to_dom add_cancel_left_right calculation(2) calculation(3) divide_eq_0_iff help3_e less_numeral_extra(1) mult_eq_0_iff norm_eq_zero of_real_eq_0_iff power_zero_numeral zero_neq_one)

   moreover have "(1/2) \<otimes>\<^sub>E ( u \<oplus>\<^sub>E v)  = Abs_PoincareDisc ((1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)) * ((( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
       )/( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
      * (1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)) +1))*(((1/(1+ inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)))
    * ((Rep_PoincareDisc u) + cor(1/(e_gamma_factor (Rep_PoincareDisc u)))*(Rep_PoincareDisc v) +
    (cor(e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (Rep_PoincareDisc u))))))"
     by (simp add: ab_semigroup_mult_class.mult_ac(1) calculation(4))
   moreover have "(1/2) \<otimes>\<^sub>E ( u \<oplus>\<^sub>E v)  = Abs_PoincareDisc(((1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)))*((1/(1+ inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))))*
    (((( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
       )/( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
      * (1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)) +1))*((
     ((Rep_PoincareDisc u) + cor(1/(e_gamma_factor (Rep_PoincareDisc u)))*(Rep_PoincareDisc v) +
    (cor(e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (Rep_PoincareDisc u)))))))"
     by (smt (verit, del_insts) calculation(6) mult.right_neutral mult_scaleR_right of_real_mult scaleR_conv_of_real)
   moreover have "(1/2) \<otimes>\<^sub>E ( u \<oplus>\<^sub>E v)  = Abs_PoincareDisc(
    (((( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
       )/( (e_gamma_factor (Rep_PoincareDisc u)) * (e_gamma_factor (Rep_PoincareDisc v))
      * (1+inner(Rep_PoincareDisc u) (Rep_PoincareDisc v)) +1))*((
     ((Rep_PoincareDisc u) + cor(1/(e_gamma_factor (Rep_PoincareDisc u)))*(Rep_PoincareDisc v) +
    (cor(e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (Rep_PoincareDisc u)))))))"
     by (simp add: calculation(5) calculation(7))
   ultimately show ?thesis 
     by force
 qed

lemma iso_ei_mo_help11:
  shows "((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v))) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) *
    ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u) +  2*(e_gamma_factor (Rep_PoincareDisc v))/
    ((1+e_gamma_factor (Rep_PoincareDisc v)) *(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc v)) = 1/(((1+e_gamma_factor (Rep_PoincareDisc v)) *(1+e_gamma_factor (Rep_PoincareDisc u))))
      * ( (2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u)) * (Rep_PoincareDisc u))
+2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) * (e_gamma_factor (Rep_PoincareDisc u))/(1+(e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc u) + 2*(e_gamma_factor (Rep_PoincareDisc v)) * (Rep_PoincareDisc v))"
proof-
  have "((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v))) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) *
    ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u)) = 
((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))))
*( ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u)) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*
((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) 
*
 (((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u))*
    (Rep_PoincareDisc u)))"
    by (simp add: mult.commute mult.left_commute ring_class.ring_distribs(1))
  moreover have "((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))))
*( ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u)) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*
((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) 
*
 (((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u))*
    (Rep_PoincareDisc u))) = (1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))
  *((2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
      *(Rep_PoincareDisc u)) + 
  (2*(e_gamma_factor (Rep_PoincareDisc v)) *(e_gamma_factor (Rep_PoincareDisc u))
  *
  (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) *
(((e_gamma_factor (Rep_PoincareDisc u)) )/(1+(e_gamma_factor (Rep_PoincareDisc u)) ))
  *(Rep_PoincareDisc u))
)
"
  proof-
    have "((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))))
*( ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u)) =(1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))
  *(2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
      *(Rep_PoincareDisc u))"
      by simp
    moreover have "(2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*
((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) 
*
 (((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u))*
    (Rep_PoincareDisc u))) =(1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))
  *(2*(e_gamma_factor (Rep_PoincareDisc v)) *(e_gamma_factor (Rep_PoincareDisc u))
  *
  (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) *
(((e_gamma_factor (Rep_PoincareDisc u)) )/(1+(e_gamma_factor (Rep_PoincareDisc u)) ))
  *(Rep_PoincareDisc u)
) "
      by simp

    moreover have "((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))))
*( ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u)) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*
((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) 
*
 (((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u))*
    (Rep_PoincareDisc u))) = (1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))
  *(2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
      *(Rep_PoincareDisc u)) + (1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))
  *(2*(e_gamma_factor (Rep_PoincareDisc v)) *(e_gamma_factor (Rep_PoincareDisc u))
  *
  (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) *
(((e_gamma_factor (Rep_PoincareDisc u)) )/(1+(e_gamma_factor (Rep_PoincareDisc u)) ))
  *(Rep_PoincareDisc u)
)" 
      using calculation(1) calculation(2) by presburger
    ultimately show ?thesis 
      by (simp add: distrib_left)
  qed
  ultimately show ?thesis 
    by (simp add: distrib_left)
qed


lemma iso_ei_mo_help12:
  shows "2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u)))
  + 2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))) =
 ((1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))) *(( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) + ((2+ (2*e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))))"
proof-
  have " 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))) =
  (1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))*( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)))"
    by force
  moreover have "2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))) =
   (1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))*
2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))) "
    by simp
  moreover have " (1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))*
2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))) =
   (1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))*
(2+ (2*e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))"
    by simp
  moreover have "2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u)))
  + 2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))) =
 ((1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))) *(( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) + ((2+ (2*e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))))"
    by (metis calculation(1) calculation(2) calculation(3) inner_real_def inner_right_distrib)
    ultimately show ?thesis 
      by linarith
qed

lemma iso_ei_mo_help13:
  shows "m_plus_full (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m v)) = ( (2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u)) * (Rep_PoincareDisc u))
+2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) * (e_gamma_factor (Rep_PoincareDisc u))/(1+(e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc u) + 2*(e_gamma_factor (Rep_PoincareDisc v)) * (Rep_PoincareDisc v))
/((( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) + ((2+ (2*e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))))))"
proof-
  have "m_plus_full (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m v))
 = ((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v))) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) *
    ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u) +  2*(e_gamma_factor (Rep_PoincareDisc v))/
    ((1+e_gamma_factor (Rep_PoincareDisc v)) *(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc v))/( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u)))
  + 2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))"
    using iso_ei_mo_help9 by blast
  moreover have "((2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v))) +
 (2*((e_gamma_factor (Rep_PoincareDisc v))/(1+e_gamma_factor (Rep_PoincareDisc v)))*((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) *
    ((e_gamma_factor (Rep_PoincareDisc u))/(1+e_gamma_factor (Rep_PoincareDisc u)))*
    (Rep_PoincareDisc u) +  2*(e_gamma_factor (Rep_PoincareDisc v))/
    ((1+e_gamma_factor (Rep_PoincareDisc v)) *(1+e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc v)) = 1/(((1+e_gamma_factor (Rep_PoincareDisc v)) *(1+e_gamma_factor (Rep_PoincareDisc u))))
      * ( (2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u)) * (Rep_PoincareDisc u))
+2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) * (e_gamma_factor (Rep_PoincareDisc u))/(1+(e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc u) + 2*(e_gamma_factor (Rep_PoincareDisc v)) * (Rep_PoincareDisc v))"
    using iso_ei_mo_help11 by blast
  moreover have "2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u)))
  + 2*(1+ (e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))) =
 ((1/((1+e_gamma_factor (Rep_PoincareDisc v))*(1+e_gamma_factor (Rep_PoincareDisc u))))) *(( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) + ((2+ (2*e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))))"
    using iso_ei_mo_help12 by presburger
  moreover have "(1+e_gamma_factor (Rep_PoincareDisc u)) \<noteq>0"
    by (metis Rep_PoincareDisc ab_group_add_class.ab_diff_conv_add_uminus add.right_neutral division_ring_divide_zero iso_ei_mo_help4 mem_Collect_eq neg_equal_zero zero_neq_one)
  moreover have "(1+e_gamma_factor (Rep_PoincareDisc v))\<noteq>0"
    by (metis (no_types, opaque_lifting) add_0_iff eq_divide_eq iso_ei_mo_inner_help5 iso_ei_mo_inner_help7_1 iso_ei_mo_inner_help8 mult_cancel_left1 mult_cancel_right1 zero_neq_one)
  
  moreover have "1/((1+e_gamma_factor (Rep_PoincareDisc u))*(1+e_gamma_factor (Rep_PoincareDisc v)))\<noteq>0"
    by (simp add: calculation(4) calculation(5))
  ultimately show ?thesis
    by (smt (verit, ccfv_threshold) divide_divide_eq_left' division_ring_divide_zero eq_divide_eq inner_commute inner_real_def mult_eq_0_iff mult_eq_0_iff nonzero_mult_divide_mult_cancel_left nonzero_mult_divide_mult_cancel_left numeral_One of_real_1 of_real_1 of_real_divide of_real_inner_1 of_real_mult one_divide_eq_0_iff real_inner_1_right times_divide_times_eq)
qed

lemma iso_ei_mo_help14:
  shows "m_plus_full (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m v)) =
    (((e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/
((e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
 * (1+inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))+1))*((Rep_PoincareDisc u)
  + (1/((e_gamma_factor (Rep_PoincareDisc u)))) *(Rep_PoincareDisc v)
  + (((e_gamma_factor (Rep_PoincareDisc u)))/(1+(e_gamma_factor (Rep_PoincareDisc u))))*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))*
(Rep_PoincareDisc u))"
proof-
  have "(e_gamma_factor (Rep_PoincareDisc u))\<noteq>0"
    by (metis Rep_PoincareDisc add_0 div_0 divide_divide_eq_right division_ring_divide_zero e_help2 mem_Collect_eq zero_neq_one)
  moreover have "(e_gamma_factor (Rep_PoincareDisc v))\<noteq>0"
    by (metis Rep_PoincareDisc add_0 div_0 divide_divide_eq_right division_ring_divide_zero e_help2 mem_Collect_eq zero_neq_one)
  moreover have "m_plus_full (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m u)) (Rep_PoincareDisc ((1/2)\<otimes>\<^sub>m v)) = ( (2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u)) * (Rep_PoincareDisc u))
+2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) * (e_gamma_factor (Rep_PoincareDisc u))/(1+(e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc u) + 2*(e_gamma_factor (Rep_PoincareDisc v)) * (Rep_PoincareDisc v))
/((( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) + ((2+ (2*e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))))))"
    using iso_ei_mo_help13 by blast
  moreover have " ( (2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u)) * (Rep_PoincareDisc u))
+2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) * (e_gamma_factor (Rep_PoincareDisc u))/(1+(e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc u) + 2*(e_gamma_factor (Rep_PoincareDisc v)) * (Rep_PoincareDisc v)) =
  2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u)) * 
  ((Rep_PoincareDisc u)
  + (1/((e_gamma_factor (Rep_PoincareDisc u)))) *(Rep_PoincareDisc v)
  + (((e_gamma_factor (Rep_PoincareDisc u)))/(1+(e_gamma_factor (Rep_PoincareDisc u))))*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))*
(Rep_PoincareDisc u))"
  proof-
    have "2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
    * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) * (e_gamma_factor (Rep_PoincareDisc u))/(1+(e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc u) = 2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u)) *
    (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) * (e_gamma_factor (Rep_PoincareDisc u))/(1+(e_gamma_factor (Rep_PoincareDisc u)))
    * (Rep_PoincareDisc u))"
      by simp
    moreover have "2* (e_gamma_factor (Rep_PoincareDisc v)) * (Rep_PoincareDisc v) =
    2*(e_gamma_factor (Rep_PoincareDisc v)) * (Rep_PoincareDisc v)
      * ((e_gamma_factor (Rep_PoincareDisc u)))/((e_gamma_factor (Rep_PoincareDisc u)))"
      by (simp add: \<open>e_gamma_factor (Rep_PoincareDisc u) \<noteq> 0\<close>)
    moreover have "2* (e_gamma_factor (Rep_PoincareDisc v)) * (Rep_PoincareDisc v) = 2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u))
    *(1/((e_gamma_factor (Rep_PoincareDisc u))))*(Rep_PoincareDisc v)"
      using \<open>e_gamma_factor (Rep_PoincareDisc u) \<noteq> 0\<close> by auto
    ultimately show ?thesis 
      by (simp add: distrib_left is_num_normalize(1) mult.commute)      
  qed
  moreover have "((( 2*(e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))) + ((2+ (2*e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))))) =
    2*((e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))*
  (1+inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))+1)"
    by (simp add: ring_class.ring_distribs(1))
  moreover have "( 2*(e_gamma_factor (Rep_PoincareDisc v))*(e_gamma_factor (Rep_PoincareDisc u)) * 
  ((Rep_PoincareDisc u)
  + (1/((e_gamma_factor (Rep_PoincareDisc u)))) *(Rep_PoincareDisc v)
  + (((e_gamma_factor (Rep_PoincareDisc u)))/(1+(e_gamma_factor (Rep_PoincareDisc u))))*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))*
(Rep_PoincareDisc u)))/( 2*((e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))*
  (1+inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))+1)) =  (((e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v)))/
((e_gamma_factor (Rep_PoincareDisc u))*(e_gamma_factor (Rep_PoincareDisc v))
 * (1+inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))+1))*((Rep_PoincareDisc u)
  + (1/((e_gamma_factor (Rep_PoincareDisc u)))) *(Rep_PoincareDisc v)
  + (((e_gamma_factor (Rep_PoincareDisc u)))/(1+(e_gamma_factor (Rep_PoincareDisc u))))*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v))*
(Rep_PoincareDisc u))"
  proof -
    have "\<forall>r ra rb. (ra::real) / r = ra * (rb / (rb * r)) \<or> 0 = rb"
      by simp
    then have "cor (e_gamma_factor (Rep_PoincareDisc u) * (e_gamma_factor (Rep_PoincareDisc v) / ((1 + inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (e_gamma_factor (Rep_PoincareDisc u) * e_gamma_factor (Rep_PoincareDisc v)) + 1))) * (Rep_PoincareDisc u + Rep_PoincareDisc v * cor (1 / e_gamma_factor (Rep_PoincareDisc u)) + Rep_PoincareDisc u * cor (e_gamma_factor (Rep_PoincareDisc u) * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) / (1 + e_gamma_factor (Rep_PoincareDisc u))))) = cor (e_gamma_factor (Rep_PoincareDisc u) * (e_gamma_factor (Rep_PoincareDisc v) * (2 / (2 * ((1 + inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (e_gamma_factor (Rep_PoincareDisc u) * e_gamma_factor (Rep_PoincareDisc v)) + 1))))) * (Rep_PoincareDisc u + Rep_PoincareDisc v * cor (1 / e_gamma_factor (Rep_PoincareDisc u)) + Rep_PoincareDisc u * cor (e_gamma_factor (Rep_PoincareDisc u) * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) / (1 + e_gamma_factor (Rep_PoincareDisc u)))))"
      by (metis (no_types) zero_neq_numeral)
    then have "cor (e_gamma_factor (Rep_PoincareDisc u) * (e_gamma_factor (Rep_PoincareDisc v) / ((1 + inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (e_gamma_factor (Rep_PoincareDisc u) * e_gamma_factor (Rep_PoincareDisc v)) + 1))) * (Rep_PoincareDisc u + Rep_PoincareDisc v * cor (1 / e_gamma_factor (Rep_PoincareDisc u)) + Rep_PoincareDisc u * cor (e_gamma_factor (Rep_PoincareDisc u) * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) / (1 + e_gamma_factor (Rep_PoincareDisc u))))) = cor (e_gamma_factor (Rep_PoincareDisc u) * (e_gamma_factor (Rep_PoincareDisc v) * 2 / (2 * ((1 + inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) * (e_gamma_factor (Rep_PoincareDisc u) * e_gamma_factor (Rep_PoincareDisc v)) + 1)))) * (Rep_PoincareDisc u + Rep_PoincareDisc v * cor (1 / e_gamma_factor (Rep_PoincareDisc u)) + Rep_PoincareDisc u * cor (e_gamma_factor (Rep_PoincareDisc u) * (inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) / (1 + e_gamma_factor (Rep_PoincareDisc u)))))"
      by auto
    then show ?thesis
      by (simp add: mult.commute)
  qed
  ultimately show ?thesis
    by presburger
qed


lemma iso_ei_mo_half:
  shows "(1/2) \<otimes>\<^sub>E ( u \<oplus>\<^sub>E v) =  ((1/2)\<otimes>\<^sub>m u \<oplus>\<^sub>m (1/2) \<otimes>\<^sub>m v)"
  by (simp add: iso_ei_mo_help10 iso_ei_mo_help14 m_plus_full_m_plus)

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
  shows "e_gamma_factor (Rep_PoincareDisc (\<ominus>\<^sub>E a)) = e_gamma_factor (Rep_PoincareDisc a)"
proof-
  have "norm (Rep_PoincareDisc (\<ominus>\<^sub>E a)) = norm (Rep_PoincareDisc a)"
    by (simp add: e_ominus'_def e_ominus.rep_eq)
  then show ?thesis 
    using \<open>cmod (Rep_PoincareDisc (\<ominus>\<^sub>E a)) = cmod (Rep_PoincareDisc a)\<close> e_gamma_factor_def by presburger
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
  have "((1/2)\<otimes>\<^sub>E (\<ominus>\<^sub>E a)) = Abs_PoincareDisc (cor (e_gamma_factor (Rep_PoincareDisc (\<ominus>\<^sub>E a))) /
        (1+(e_gamma_factor (Rep_PoincareDisc (\<ominus>\<^sub>E a)))) * (Rep_PoincareDisc (\<ominus>\<^sub>E a)))"
    using half_times_gamma by blast
  moreover have "\<ominus>\<^sub>E ((1/2) \<otimes>\<^sub>E a) = \<ominus>\<^sub>E( Abs_PoincareDisc (cor (e_gamma_factor (Rep_PoincareDisc a)) /
        (1+(e_gamma_factor (Rep_PoincareDisc a))) * (Rep_PoincareDisc  a)))"
    using half_times_gamma by presburger
  moreover have "((1/2)\<otimes>\<^sub>E (\<ominus>\<^sub>E a)) = Abs_PoincareDisc (cor (e_gamma_factor (Rep_PoincareDisc (a))) /
        (1+(e_gamma_factor (Rep_PoincareDisc ( a)))) * -1 * (Rep_PoincareDisc (a)))"
    using e_gamma_minus_plus e_ominus'_def e_ominus.rep_eq half_times_gamma by force
  let ?iz = " (Rep_PoincareDisc
       (Abs_PoincareDisc((cor (e_gamma_factor (Rep_PoincareDisc a)) /
        (1+(e_gamma_factor (Rep_PoincareDisc a))) * (Rep_PoincareDisc  a)))))"
  let ?iz1 = "Abs_PoincareDisc ((cor (e_gamma_factor (Rep_PoincareDisc a)) /
        (1+(e_gamma_factor (Rep_PoincareDisc a))) * (Rep_PoincareDisc  a)))"
  have "\<ominus>\<^sub>E ((1/2) \<otimes>\<^sub>E a) =Abs_PoincareDisc (-1* Rep_PoincareDisc
       (Abs_PoincareDisc
         (cor (e_gamma_factor (Rep_PoincareDisc a)) /
          cor (1 + e_gamma_factor (Rep_PoincareDisc a)) *
          Rep_PoincareDisc a)))"
    using  e_ominus'_def[of ?iz] e_ominus.rep_eq[of ?iz1]
    by (metis Moebius_gyrodom'.of_dom calculation(2) mult_minus1)
  moreover have "(-1* Rep_PoincareDisc
       (Abs_PoincareDisc
         (cor (e_gamma_factor (Rep_PoincareDisc a)) /
          cor (1 + e_gamma_factor (Rep_PoincareDisc a)) *
          Rep_PoincareDisc a))) = (-1 * (cor (e_gamma_factor (Rep_PoincareDisc a)) /
          cor (1 + e_gamma_factor (Rep_PoincareDisc a)) *
          Rep_PoincareDisc a))"
  proof-
    have "norm (Rep_PoincareDisc a) <1"
      using Rep_PoincareDisc by blast
    moreover have "e_gamma_factor (Rep_PoincareDisc a) = 1/sqrt(1-(norm (Rep_PoincareDisc a))^2)"
      by (metis calculation e_gamma_factor_def mult_closed norm_power power2_eq_square)
    moreover have "norm ((cor (e_gamma_factor (Rep_PoincareDisc a)) /
          cor (1 + e_gamma_factor (Rep_PoincareDisc a)) *
          Rep_PoincareDisc a)) <1"
      by (smt (verit, best) calculation(1) calculation(2) divide_eq_1_iff e_gamma_factor_def less_divide_eq_1_pos mult_closed norm_divide norm_of_real real_sqrt_gt_zero zero_less_divide_1_iff)    
    ultimately show ?thesis 
      using rep_abs_inv by presburger
  qed
  ultimately show ?thesis
    by (simp add: \<open>(1 / 2) \<otimes>\<^sub>E \<ominus>\<^sub>E a = Abs_PoincareDisc (cor (e_gamma_factor (Rep_PoincareDisc a)) / cor (1 + e_gamma_factor (Rep_PoincareDisc a)) * - 1 * Rep_PoincareDisc a)\<close>)
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
  shows "2 \<otimes>\<^sub>E u = Abs_PoincareDisc (cor(2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2 -1) * (Rep_PoincareDisc u))"
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

      moreover have "e_gamma_factor (Rep_PoincareDisc u)^2 = 1/(1-cmod(Rep_PoincareDisc u)^2)"
        by (smt (verit, ccfv_SIG) Rep_PoincareDisc div_by_1 divide_divide_eq_right divide_eq_0_iff e_gamma_factor_def e_help1 mem_Collect_eq one_power2 power2_eq_square times_divide_eq_right)
      moreover have "(2*(e_gamma_factor (Rep_PoincareDisc u))^2)
/(2*(e_gamma_factor (Rep_PoincareDisc u))^2 -1) =  2/(1+ cmod(Rep_PoincareDisc u)^2)"
      proof-
        have "(2*(e_gamma_factor (Rep_PoincareDisc u))^2)
/(2*(e_gamma_factor (Rep_PoincareDisc u))^2 -1) = 2*(1/(1-cmod(Rep_PoincareDisc u)^2))/(2*(1/(1-cmod(Rep_PoincareDisc u)^2))-1)"
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
  shows "norm (cor ((2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2-1)) * (Rep_PoincareDisc u)) <1"
proof-
  have "norm (cor ((2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2-1)) * (Rep_PoincareDisc u))
  = abs((2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2-1))* (norm (Rep_PoincareDisc u))"
    by (metis norm_mult norm_of_real)
  moreover have "2*(e_gamma_factor (Rep_PoincareDisc u))^2-1 \<ge>1"
  proof-
    have "e_gamma_factor (Rep_PoincareDisc u)^2 = 1/(1-norm (Rep_PoincareDisc u)^2)"
      by (simp add: assms e_help1)
    moreover have "1-norm (Rep_PoincareDisc u)^2 \<le> 1"
      by auto
    moreover have "1/(1-norm (Rep_PoincareDisc u)^2)\<ge>1"
      by (smt (verit, ccfv_SIG) assms e_gamma_norm_connection le_divide_eq_1 zero_le_power2)
    ultimately show ?thesis 
      by linarith       
  qed
  moreover have "e_gamma_factor (Rep_PoincareDisc u) \<ge> 0"
    using assms e_gamma_factor_def gamma_factor_def gamma_factor_positive_always by auto
  moreover  have "norm (cor ((2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2-1)) * (Rep_PoincareDisc u))
  = ((2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2-1))* (norm (Rep_PoincareDisc u))"
    using calculation(1) calculation(2) by auto
  moreover have  "e_gamma_factor (Rep_PoincareDisc u)^2 = 1/(1-norm (Rep_PoincareDisc u)^2)"
       by (simp add: assms e_help1)
  moreover have "((2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2-1)) =
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
  moreover have "   ((2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2-1))* (norm (Rep_PoincareDisc u)) =
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

  moreover have "norm (cor ((2*(e_gamma_factor (Rep_PoincareDisc u))^2)/(2*(e_gamma_factor (Rep_PoincareDisc u))^2-1)) * (Rep_PoincareDisc u)) =
     (2/ (1+ norm (Rep_PoincareDisc u)^2)) * norm (Rep_PoincareDisc u)"
    using calculation(4) calculation(9) by presburger
  ultimately show ?thesis 
    by presburger
qed

lemma einstein_gyroauto_help3:
  shows  "2*( 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))/(2*( 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1)
    = (1+e_gamma_factor (Rep_PoincareDisc a))/(e_gamma_factor (Rep_PoincareDisc a))"
      proof-
        have " (1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2) \<noteq>0"
          by (metis add.commute add_0 add_right_cancel diff_add_cancel eq_divide_eq_1 iso_ei_inner_mo_help3 iso_ei_mo_inner_help7_1 real_average_minus_second zero_neq_one)
        moreover have **:"1/((1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))\<noteq>0"
          using calculation by auto
        moreover have "2*1/((1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1 =
        1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2) *(2-((1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2)))"
          by (smt (verit, del_insts) calculation(1) diff_divide_distrib divide_self nonzero_mult_div_cancel_left one_add_one times_divide_eq_left)
        moreover have "(2-((1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))) =
          1+ ((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2"
          by fastforce

        moreover have " ((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2 =
      ((e_gamma_factor (Rep_PoincareDisc a))-1)/(1+(e_gamma_factor (Rep_PoincareDisc a)))"
          using iso_ei_inner_mo_help3 iso_ei_mo_inner_help7_1 by presburger

        moreover have "1+ ((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2=
      2*(e_gamma_factor (Rep_PoincareDisc a))/(1+(e_gamma_factor (Rep_PoincareDisc a))) "
          using Rep_PoincareDisc calculation(5) iso_ei_mo_help3 by auto

        
        moreover have "2*( 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))/(2*( 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1) =
              2*(1/((1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2)))/( 2*(e_gamma_factor (Rep_PoincareDisc a))/(1+(e_gamma_factor (Rep_PoincareDisc a))) *(1/((1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))))"
          using calculation(3) calculation(6) by auto
          
        
        ultimately show ?thesis 
          by (simp add: add_divide_distrib)
      qed

lemma einstein_gyroauto_help4:
  shows "(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2)/
(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 -1) = (1+e_gamma_factor (Rep_PoincareDisc a))/(e_gamma_factor (Rep_PoincareDisc a))"
    proof-
      have "norm(Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))) <1"
        using Rep_PoincareDisc by blast
      moreover have "(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 = 
1/(1-norm(Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a)))^2)"
        by (simp add: \<open>cmod (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))) < 1\<close> e_help1)
      moreover have "1/(1-norm(Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a)))^2) = 1/(1-(norm (Rep_PoincareDisc ((1/2) \<otimes>\<^sub>E a)))^2)"
        using Moebius_gyrodom'.gyronorm_def mobius_gyroauto_norm by presburger
      moreover have " 1/(1-(norm (Rep_PoincareDisc ((1/2) \<otimes>\<^sub>E a)))^2) = 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2)"
        by (metis Moebius_gyrodom'.of_dom half_times_gamma iso_ei_inner_help2 iso_ei_inner_mo_help3)
      moreover have "(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2)/
(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 -1) = 2*( 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))/(2*
( 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1)"
        using calculation(2) calculation(3) calculation(4) by presburger
      moreover have "2*( 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))/(2*( 1/(1-((e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)))^2 *(norm (Rep_PoincareDisc a))^2))-1)
    = (1+e_gamma_factor (Rep_PoincareDisc a))/(e_gamma_factor (Rep_PoincareDisc a))"
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
  moreover have " \<llangle> ((1/2) \<otimes>\<^sub>E a) \<rrangle>\<^sub>m = (e_gamma_factor (Rep_PoincareDisc a))/(1+e_gamma_factor (Rep_PoincareDisc a)) *  \<llangle>a\<rrangle>\<^sub>m"
    by (smt (verit, ccfv_SIG) Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.of_dom add_divide_distrib diff_divide_distrib divide_self half_times_gamma iso_ei_inner_help2 iso_ei_mo_inner_help7_1 norm_mult norm_of_real of_real_divide power2_eq_square real_minus_mult_self_le)
  moreover have "e_gyr u v a = Abs_PoincareDisc (cor (2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2)/
(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 -1) * (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))"
    using calculation(1) two_times_gamma_factor by presburger
  moreover have "e_gyr u v b = Abs_PoincareDisc (cor (2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))^2)/
(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))^2 -1) * (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))"
    using calculation(2) two_times_gamma_factor by presburger
  moreover have "e_gyr u v a \<cdot>\<^sub>E e_gyr u v b =   2 *
    (e_gamma_factor
      (Rep_PoincareDisc
        (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))))\<^sup>2 /
    (2 *
     (e_gamma_factor
       (Rep_PoincareDisc
         (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))))\<^sup>2 -
     1) *
    (2 *
     (e_gamma_factor
       (Rep_PoincareDisc
         (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))))\<^sup>2 /
     (2 *
      (e_gamma_factor
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

    moreover have "  ((1 / 2) \<otimes>\<^sub>E a)  \<cdot>\<^sub>E  ((1 / 2) \<otimes>\<^sub>E b) = ((e_gamma_factor (Rep_PoincareDisc a))
  /(1+e_gamma_factor (Rep_PoincareDisc a)))*((e_gamma_factor (Rep_PoincareDisc b))/
  (1+e_gamma_factor (Rep_PoincareDisc b)))* a  \<cdot>\<^sub>E b"
      by (metis Moebius_gyrodom'.of_dom e_inner'_def e_inner.rep_eq half_times_gamma iso_ei_inner_help2 iso_ei_mo_inner_help5)


    moreover have "\<llangle> m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b) \<rrangle>\<^sub>m = \<llangle> ((1/2) \<otimes>\<^sub>E b) \<rrangle>\<^sub>m"
    using mobius_gyroauto_norm by force
    moreover have "(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2)/
(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E a))))^2 -1) = (1+e_gamma_factor (Rep_PoincareDisc a))/(e_gamma_factor (Rep_PoincareDisc a))"
      using einstein_gyroauto_help4 by presburger
        moreover have "(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))^2)/
(2*(e_gamma_factor (Rep_PoincareDisc (m_gyr ((1/2) \<otimes>\<^sub>E u) ((1/2) \<otimes>\<^sub>E v) ((1/2) \<otimes>\<^sub>E b))))^2 -1) = (1+e_gamma_factor (Rep_PoincareDisc b))/(e_gamma_factor (Rep_PoincareDisc b))"
      using einstein_gyroauto_help4 by presburger
    
    moreover have "   2 *
    (e_gamma_factor
      (Rep_PoincareDisc
        (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))))\<^sup>2 /
    (2 *
     (e_gamma_factor
       (Rep_PoincareDisc
         (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))))\<^sup>2 -
     1) *
    (2 *
     (e_gamma_factor
       (Rep_PoincareDisc
         (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))))\<^sup>2 /
     (2 *
      (e_gamma_factor
        (Rep_PoincareDisc
          (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))))\<^sup>2 -
      1)) *
    Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E a))) \<cdot>\<^sub>E
    Abs_PoincareDisc
     (Rep_PoincareDisc (m_gyr ((1 / 2) \<otimes>\<^sub>E u) ((1 / 2) \<otimes>\<^sub>E v) ((1 / 2) \<otimes>\<^sub>E b))) =
(1+e_gamma_factor (Rep_PoincareDisc a))/(e_gamma_factor (Rep_PoincareDisc a))*
(1+e_gamma_factor (Rep_PoincareDisc b))/(e_gamma_factor (Rep_PoincareDisc b))
   *((e_gamma_factor (Rep_PoincareDisc a))
  /(1+e_gamma_factor (Rep_PoincareDisc a)))*((e_gamma_factor (Rep_PoincareDisc b))/
  (1+e_gamma_factor (Rep_PoincareDisc b)))* a  \<cdot>\<^sub>E b "
      by (simp add: calculation(11) calculation(12) calculation(14) calculation(15) calculation(8) calculation(9))
    moreover have "(1+e_gamma_factor (Rep_PoincareDisc a))/(e_gamma_factor (Rep_PoincareDisc a))*
(1+e_gamma_factor (Rep_PoincareDisc b))/(e_gamma_factor (Rep_PoincareDisc b))
   *((e_gamma_factor (Rep_PoincareDisc a))
  /(1+e_gamma_factor (Rep_PoincareDisc a)))*((e_gamma_factor (Rep_PoincareDisc b))/
  (1+e_gamma_factor (Rep_PoincareDisc b))) = 1"
    proof-
      have "e_gamma_factor (Rep_PoincareDisc a) \<noteq>0"
        by (metis Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.of_dom add.commute add.right_neutral calculation(4) diff_add_cancel div_by_1 half_times_gamma iso_ei_inner_help2 iso_ei_mo_inner_help7_1 mult_zero_left power_zero_numeral zero_neq_one)
      moreover have "e_gamma_factor (Rep_PoincareDisc b)\<noteq>0"
        by (metis diff_zero division_ring_divide_zero e_help1 e_inv e_ozero'_def e_ozero.rep_eq gamma_plus5 mult_zero_left mult_zero_right norm_zero power_zero_numeral zero_less_one zero_neq_one)
      moreover have "1+e_gamma_factor (Rep_PoincareDisc a)\<noteq>0"
        by (metis Rep_PoincareDisc add_0 add_diff_cancel_left' division_ring_divide_zero iso_ei_mo_help4 mem_Collect_eq zero_neq_one)
      moreover have "1+e_gamma_factor (Rep_PoincareDisc b)\<noteq>0"
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
