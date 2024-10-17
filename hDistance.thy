theory hDistance
  imports Complex_Main GyroGroup GyroVectorSpace HOL.Real_Vector_Spaces
        MobiusGyroGroup Einstein
begin


definition hexplicit1::"complex \<Rightarrow> complex \<Rightarrow> real" where 
  "hexplicit1 u v = arcosh(1+ 2*norm(u-v)^2/((1-norm(u)^2)*(1-norm(v)^2)))"

lemma arcosh_ln:
  fixes x::real
  assumes "x\<ge>1"
  shows "arcosh x = ln(x+sqrt(x^2-1))"
  using arcosh_real_def assms by blast

lemma h1:
  shows "(norm (1-(cnj u)*v))^2 = 1-(cnj u)*v - u*(cnj v) + (norm u)^2 * (norm v)^2"
proof-
  have "(norm (1-(cnj u)*v))^2 = (1-(cnj u)*v)*(cnj (1-(cnj u)*v))"
    using complex_norm_square by blast
  moreover have "(1-(cnj u)*v)*(cnj (1-(cnj u)*v)) = (1-(cnj u)*v)* (1-u*(cnj v))"
    by simp
  moreover have "(1-(cnj u)*v)* (1-u*(cnj v)) = 1-u*(cnj v)-(cnj u)*v + (cnj u)*v*u*(cnj v)"
    by (simp add: left_diff_distrib' right_diff_distrib')
  ultimately show ?thesis 
    using complex_norm_square by auto
qed
lemma h2:
  shows "(norm (u-v))^2 = (norm u)^2 - u*(cnj v) - v*(cnj u) + (norm v)^2"
  by (metis complex_cnj_diff complex_norm_square diff_add_eq diff_diff_eq2 left_diff_distrib right_diff_distrib')

lemma h3:
  shows "(norm (1-(cnj u)*v))^2 - (norm (u-v))^2 = (1-(norm u)^2)*(1-(norm v)^2)"
proof-
  have "(norm (1-(cnj u)*v))^2 = 1-(cnj u)*v - u*(cnj v) + (norm u)^2 * (norm v)^2"
    using h1 by blast
  moreover have "(norm (u-v))^2 = (norm u)^2 - u*(cnj v) - v*(cnj u) + (norm v)^2"
    using h2 by blast
  moreover have "(norm (1-(cnj u)*v))^2 - (norm (u-v))^2 = 1+(norm u)^2 * (norm v)^2 - (norm u)^2 - (norm v)^2"
        by (smt (verit, del_insts) Re_complex_of_real calculation(1) calculation(2) minus_complex.simps(1) mult.commute one_complex.simps(1) plus_complex.simps(1))
  ultimately show ?thesis 
    by (simp add: Rings.ring_distribs(4) mult.commute)
qed

lemma h4:
  assumes "norm u < 1" "norm v < 1"
  shows "1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)) \<ge> 1"
proof-
  have "(norm (u-v))^2 \<ge>0"
    using zero_le_power2 by blast
  moreover have "(1-(norm u)^2) > 0"
    using assms(1) real_sqrt_lt_1_iff by fastforce
  moreover have "(1-(norm v)^2)>0"
    using assms(2) real_sqrt_lt_1_iff by fastforce
  moreover have "2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)) \<ge>0"
    using calculation(2) calculation(3) by auto
  ultimately show ?thesis
    by linarith
qed

lemma h5:
  assumes "norm u < 1" "norm v <1"
  shows "arcosh(1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2))) =
    ln(1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)) + sqrt((1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)))^2-1))"
proof-
  let ?iz = "1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2))"
  have "?iz \<ge>1"
    using assms(1) assms(2) h4 by blast
  then show ?thesis
    using   arcosh_ln[OF  `?iz\<ge>1`]
    by fastforce
qed 

lemma h6:
  assumes "norm u < 1" "norm v <1"
  shows "sqrt((1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)))^2-1) = 
    sqrt(4*(norm (u-v)^2/((1-(norm u)^2)*(1-(norm v)^2))) + 4*((norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)))^2)"
  by (smt (verit, best) add_divide_distrib four_x_squared inner_real_def one_power2 power2_diff real_inner_1_right)

lemma h7:
  assumes "norm u < 1" "norm v < 1"
  shows " sqrt(4*(norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)) + 4*((norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)))^2) =
    2*(norm (u-v))/((1-(norm u)^2)*(1-(norm v)^2))*sqrt((1-(norm u)^2)*(1-(norm v)^2) + (norm(u-v))^2)"
proof-
  have "4*(norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)) + 4*((norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)))^2=
  4*(norm (u-v)^2) * (1/((1-(norm u)^2)*(1-(norm v)^2)) + ((norm (u-v))/((1-(norm u)^2)*(1-(norm v)^2)))^2)"
  proof-
    have "4*((norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)))^2 = 4*(norm (u-v))^2 * ((norm (u-v))/((1-(norm u)^2)*(1-(norm v)^2)))^2"
      by (simp add: power2_eq_square)
    moreover have "4*(norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)) = 4*(norm (u-v))^2 * 1/((1-(norm u)^2)*(1-(norm v)^2))"
      by fastforce
    ultimately show ?thesis 
      by (smt (verit) inner_real_def inner_right_distrib real_inner_1_right times_divide_eq_right)
  qed
  moreover have "1/((1-(norm u)^2)*(1-(norm v)^2)) + ((norm (u-v))/((1-(norm u)^2)*(1-(norm v)^2)))^2 =
        ((1-(norm u)^2)*(1-(norm v)^2) + (norm (u-v))^2)/((1-(norm u)^2)*(1-(norm v)^2))^2"
  proof-
    have "((norm (u-v))/((1-(norm u)^2)*(1-(norm v)^2)))^2 = ((norm (u-v))^2 /((1-(norm u)^2)*(1-(norm v)^2))^2)"
      using power_divide by blast
    moreover have "1/((1-(norm u)^2)*(1-(norm v)^2)) + ((norm (u-v))^2 /((1-(norm u)^2)*(1-(norm v)^2))^2) =
        ((1-(norm u)^2)*(1-(norm v)^2) + (norm (u-v))^2)/((1-(norm u)^2)*(1-(norm v)^2))^2"
    proof-
      have "((1-(norm u)^2)*(1-(norm v)^2))^2 = ((1-(norm u)^2)*(1-(norm v)^2)) *((1-(norm u)^2)*(1-(norm v)^2)) "
        by (simp add: power2_eq_square)
      then show ?thesis 
        by (simp add: add_divide_distrib)
    qed
    ultimately show ?thesis 
      by presburger
  qed
  moreover have "sqrt(4*(norm (u-v))^2*((1-(norm u)^2)*(1-(norm v)^2) + (norm (u-v))^2)/((1-(norm u)^2)*(1-(norm v)^2))^2) =
        2*(norm (u-v))*sqrt((1-(norm u)^2)*(1-(norm v)^2) + (norm (u-v))^2)/((1-(norm u)^2)*(1-(norm v)^2))"
    by (smt (verit, ccfv_SIG) assms(1) assms(2) four_x_squared mult_nonneg_nonneg norm_not_less_zero one_power2 power_mono real_root_divide real_root_mult real_sqrt_unique sqrt_def)
      
  ultimately show ?thesis 
    by force
qed

lemma h8:
  assumes "norm u < 1" "norm v <1"
  shows " 2*(norm (u-v))/((1-(norm u)^2)*(1-(norm v)^2))*sqrt((1-(norm u)^2)*(1-(norm v)^2) + (norm(u-v))^2) =
    2*(norm (u-v))/((1-(norm u)^2)*(1-(norm v)^2)) * (norm (1-(cnj u)*v))"
  by (smt (verit, ccfv_SIG) cmod_def cmod_power2 h3)

lemma h9:
  assumes "norm u <1" "norm v <1"
  shows "1 + 2*(norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)) = ((1-(norm u)^2)*(1-(norm v)^2)+2*(norm (u-v))^2)/
    ((1-(norm u)^2)*(1-(norm v)^2))"
proof-
  have "(1-(norm u)^2)\<noteq>0"
    by (metis abs_norm_cancel assms(1) order_less_irrefl real_sqrt_abs real_sqrt_one right_minus_eq)
  moreover have "(1-(norm v)^2)\<noteq>0"
    by (metis abs_norm_cancel assms(2) order_less_irrefl real_sqrt_abs real_sqrt_one right_minus_eq)
  ultimately show ?thesis 
    by (simp add: add_divide_distrib)
qed

lemma h10:
  assumes "norm u < 1" "norm v<1"
  shows "((1-(norm u)^2)*(1-(norm v)^2)+2*(norm (u-v))^2)/
    ((1-(norm u)^2)*(1-(norm v)^2)) = ((norm (1-(cnj u)*v))^2 + (norm (u-v)^2))/((1-(norm u)^2)*(1-(norm v)^2))"
  by (smt (verit, ccfv_SIG) h3)


lemma h11:
  assumes "norm u <1" "norm v<1"
  shows "sqrt((1-(norm u)^2)*(1-(norm v)^2) + (norm(u-v))^2) = (norm (1-(cnj u)*v))"
  by (smt (verit, ccfv_threshold) cmod_def cmod_power2 h3)

lemma h12:
  assumes "norm u <1" "norm v < 1"
  shows "arcosh(1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2))) = 
        ln(((norm (1-(cnj u)*v))^2 + 2*(norm (1-(cnj u)*v))*(norm (u-v))+ (norm (u-v))^2)/((1-(norm u)^2)*(1-(norm v)^2)))"
proof-
  have "arcosh(1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2))) =
    ln(1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)) + sqrt((1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)))^2-1))"
    using assms(1) assms(2) h5 by blast
  moreover have "1 + 2*(norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)) = ((1-(norm u)^2)*(1-(norm v)^2)+2*(norm (u-v))^2)/
    ((1-(norm u)^2)*(1-(norm v)^2))"
    using assms(1) assms(2) h9 by blast
  moreover have "((1-(norm u)^2)*(1-(norm v)^2)+2*(norm (u-v))^2)/
    ((1-(norm u)^2)*(1-(norm v)^2)) = ((norm (1-(cnj u)*v))^2 + (norm (u-v)^2))/((1-(norm u)^2)*(1-(norm v)^2))"
    using assms(1) assms(2) h10 by blast
  moreover have **:"sqrt(4*(norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)) + 4*((norm (u-v))^2/((1-(norm u)^2)*(1-(norm v)^2)))^2) =
    2*(norm (u-v))/((1-(norm u)^2)*(1-(norm v)^2))*sqrt((1-(norm u)^2)*(1-(norm v)^2) + (norm(u-v))^2)"
    using assms(1) assms(2) h7 by blast
  moreover have "1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)) + sqrt((1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)))^2-1) =
    ((norm (1-(cnj u)*v))^2 + 2*(norm (1-(cnj u)*v))*(norm (u-v))+ (norm (u-v))^2)/((1-(norm u)^2)*(1-(norm v)^2))"
  proof-
    have "1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)) = ((norm (1-(cnj u)*v))^2
      + (norm (u-v))^2)/((1-(norm u)^2)*(1-(norm v)^2))"
      using calculation(2) calculation(3) by presburger
    moreover have " sqrt((1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)))^2-1) =
      (2*(norm (u-v)) * (norm (1-(cnj u)*v)))/((1-(norm u)^2)*(1-(norm v)^2))"
      using ** h11
      by (simp add: assms(1) assms(2) h6)
    ultimately show ?thesis 
      by (simp add: add_divide_distrib)
  qed
  moreover have "ln(1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)) + sqrt((1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2)))^2-1)) = ln(
    ((norm (1-(cnj u)*v))^2 + 2*(norm (1-(cnj u)*v))*(norm (u-v))+ (norm (u-v))^2)/((1-(norm u)^2)*(1-(norm v)^2)))"
    using calculation(5) by presburger
  ultimately show ?thesis
    by linarith
qed

lemma h13:
  assumes "norm u <1" "norm v <1"
  shows "1 + (norm (u-v))/(norm (1-(cnj u)*v)) = ((norm (u-v)) + (norm (1-(cnj u)*v)))
      /(norm(1 - (cnj u)*v))"
  by (metis (no_types, opaque_lifting) add_diff_cancel_left' add_divide_distrib assms(1) assms(2) complex_mod_cnj diff_diff_eq2 diff_zero divide_self_if mult_closed norm_eq_zero norm_one order_less_irrefl)

lemma h14:
  assumes "norm u < 1" "norm v <1"
  shows "1- (norm (u-v))/(norm (1-(cnj u)*v)) = ((norm (1-(cnj u)*v))-(norm (u-v)))/
    (norm (1-(cnj u)*v))"
  by (smt (verit, ccfv_SIG) add_divide_distrib assms(1) assms(2) h13)

lemma h15:
  assumes "norm u<1" "norm v <1"
  shows "(1 + (norm (u-v))/(norm (1-(cnj u)*v)))/(1- (norm (u-v))/(norm (1-(cnj u)*v))) =
    ((norm (u-v)) + (norm (1-(cnj u)*v)))/ ((norm (1-(cnj u)*v))-(norm (u-v)))"
proof-
  have "(norm (1-(cnj u)*v))\<noteq>0"
        by (metis assms(1) assms(2) complex_mod_cnj eq_iff_diff_eq_0 mult_closed norm_eq_zero norm_one order_less_irrefl)
      moreover have "1 + (norm (u-v))/(norm (1-(cnj u)*v)) = ((norm (u-v)) + (norm (1-(cnj u)*v)))
      /(norm(1 - (cnj u)*v))"
        using assms(1) assms(2) h13 by blast
      moreover have "1- (norm (u-v))/(norm (1-(cnj u)*v)) = ((norm (1-(cnj u)*v))-(norm (u-v)))/
    (norm (1-(cnj u)*v))"
        using assms(1) assms(2) h14 by auto
      moreover have "(1 + (norm (u-v))/(norm (1-(cnj u)*v)))/(1- (norm (u-v))/(norm (1-(cnj u)*v))) =
     (((norm (u-v)) + (norm (1-(cnj u)*v)))
      /(norm(1 - (cnj u)*v)))/(((norm (1-(cnj u)*v))-(norm (u-v)))/
    (norm (1-(cnj u)*v)))"
        using calculation(2) calculation(3) by presburger
      ultimately show ?thesis
        by simp
    qed

lemma h16:
  assumes "norm u < 1" "norm v <1"
  shows " ((norm (u-v)) + (norm (1-(cnj u)*v)))/ ((norm (1-(cnj u)*v))-(norm (u-v))) =
    ((norm (1-(cnj u)*v)) + (norm (u-v)))^2/((1-(norm u)^2)*(1-(norm v)^2))"
proof-
  let ?iz = "((norm (1-(cnj u)*v)) + (norm (u-v)))"
  have " ((norm (u-v)) + (norm (1-(cnj u)*v)))/ ((norm (1-(cnj u)*v))-(norm (u-v))) =  ((norm (u-v)) + (norm (1-(cnj u)*v)))/ ((norm (1-(cnj u)*v))-(norm (u-v)))
    * ?iz/?iz"
    by fastforce
  moreover have "((norm (u-v)) + (norm (1-(cnj u)*v))) *?iz = ((norm (1-(cnj u)*v)) + (norm (u-v)))^2"
    by (simp add: power2_eq_square)
  moreover have "((norm (1-(cnj u)*v))-(norm (u-v))) * ?iz = (1-(norm u)^2)*(1-(norm v)^2)"
  proof-
    have "((norm (1-(cnj u)*v))-(norm (u-v))) * ?iz = ((norm (1-(cnj u)*v))^2 - (norm (u-v))^2)"
      by (simp add: power2_eq_square square_diff_square_factored)
    moreover have "((norm (1-(cnj u)*v))^2 - (norm (u-v))^2) =  (1-(norm u)^2)*(1-(norm v)^2)"
      using h3 by blast
    ultimately show ?thesis 
      by presburger
  qed
  ultimately show ?thesis 
    by simp
qed

lemma h17:
  assumes "norm u < 1" "norm v <1"
  shows "((norm (1-(cnj u)*v)) + (norm (u-v)))^2 = ((norm (1-(cnj u)*v))^2 +
    2*(norm (1-(cnj u)*v))*(norm (u-v)) + (norm (u-v))^2)"
  by (simp add: power2_sum)

lemma h18:    
  assumes "norm u < 1" "norm v <1"
  shows "arcosh(1 + 2*(norm (u-v))^2 / ((1-(norm u)^2)*(1-(norm v)^2))) = 
ln((1 + (norm (u-v))/(norm (1-(cnj u)*v)))/(1- (norm (u-v))/(norm (1-(cnj u)*v))))"
  by (simp add: assms(1) assms(2) h12 h15 h16 h17)

end
