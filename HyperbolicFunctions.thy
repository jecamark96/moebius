theory HyperbolicFunctions
imports HOL.Transcendental
begin

lemma artanh_abs_tanh:
  fixes x::real
  shows "artanh (abs (tanh x)) = abs x"
proof (cases "x \<ge> 0")
  case True
  then show ?thesis 
    by (simp add: artanh_tanh_real)
next
  case False
  then show ?thesis
    by (metis artanh_tanh_real tanh_real_abs)
qed

lemma artanh_nonneg:
  fixes x :: real
  assumes "0 \<le> x" "x < 1"
  shows "artanh x \<ge> 0"
proof-
  have "(1+x)/(1-x) \<ge> 1/(1-x)"
    by (metis assms add_0 add_increasing2 divide_right_mono le_diff_eq less_eq_real_def)
  moreover have "1/(1-x) \<ge> 1"
    using assms 
    by simp
  moreover have "artanh x = 1/2*ln((1+x)/(1-x))"
    by (simp add: artanh_def)
  moreover have "ln((1+x)/(1-x))\<ge>0"
    using calculation(1) calculation(2) by fastforce
  moreover have "((artanh x)\<ge>0)"
    using calculation(3) calculation(4) by linarith
  moreover have "(0\<le>x \<and> x<1)\<longrightarrow> ((artanh x)\<ge>0)"
    using calculation by blast
  ultimately 
  show ?thesis 
    by blast
qed

lemma artanh_not_0:
  fixes x :: real
  assumes "x > 0" "x < 1"
  shows "artanh x \<noteq> 0"
  using assms
  by (simp add: artanh_def)

lemma tanh_not_0:
  fixes x :: real
  assumes "x > 0" "x < 1"
  shows "tanh x \<noteq> 0"
  using assms
  by simp

end