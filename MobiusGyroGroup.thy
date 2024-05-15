theory MobiusGyroGroup
  imports Complex_Main GyroGroup GyroVectorSpace HOL.Real_Vector_Spaces
      HOL.Transcendental
begin

abbreviation "cor \<equiv> complex_of_real"

typedef PoincareDisc = "{z::complex. cmod z < 1}"
  by (rule_tac x=0 in exI, auto)

setup_lifting type_definition_PoincareDisc                    



definition m_inner' :: "complex \<Rightarrow> complex \<Rightarrow> real" where
  "m_inner' z1 z2 = Re z1 * Re z2 + Im z1 * Im z2"

lemma m_inner'_def': 
  shows "m_inner' z1 z2 = (z1 * cnj z2 + z2 * cnj z1) / 2"
proof-
  obtain "a" "b" where "Re z1=a \<and> Im z1=b"
    by blast
  obtain "c" "d" where "Re z2=c \<and> Im z2=d"
    by blast
  moreover have "Re (z1 * cnj z2) = a*c + b*d"
    by (simp add: \<open>Re z1 = a \<and> Im z1 = b\<close> calculation)
  moreover have "Re (z2 * cnj z1) = a*c + b*d"
    by (simp add: \<open>Re z1 = a \<and> Im z1 = b\<close> calculation)
  moreover have "Im (z1 * cnj z2) = b*c - a*d"
    by (simp add: \<open>Re z1 = a \<and> Im z1 = b\<close> calculation(1))
  moreover have "Im (z2 * cnj z1) = -b*c + a*d"
    by (simp add: \<open>Re z1 = a \<and> Im z1 = b\<close> calculation(1))
  moreover have " (z1 * cnj z2 + z2 * cnj z1) / 2 =  a*c + b*d"
    by (metis (no_types, opaque_lifting) calculation(2) cnj_add_mult_eq_Re divide_eq_eq_numeral1(1) mult.commute of_real_mult of_real_numeral zero_neq_numeral)
  ultimately show ?thesis
    using \<open>Re z1 = a \<and> Im z1 = b\<close> m_inner'_def by presburger
qed

lemma m_inner_more:
  shows "m_inner' z1 z2 = Re (cnj z1 * z2)"
  by (simp add: m_inner'_def)
  (*unfolding m_inner'_def apply auto
  by simp*)

lift_definition m_inner :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> real" (infixl "\<cdot>\<^sub>m" 100) is m_inner'
  done

definition m_oplus' :: "complex \<Rightarrow> complex \<Rightarrow> complex"  where
  "m_oplus' a z = (a + z) / (1 + (cnj a) *z)"

lemma m_oplus'_in_disc:
  assumes "cmod c1 < 1" "cmod c2 < 1"
  shows "cmod (m_oplus' c1 c2) < 1"
proof-
  have "Im ((c1 + c2) * (cnj c1 + cnj c2)) = 0"
    by (metis complex_In_mult_cnj_zero complex_cnj_add)
  moreover
  have "Im ((1 + cnj c1 * c2) * (1 + c1 * cnj c2)) = 0"
    by (cases c1, cases c2, simp add: field_simps)
  ultimately
  have 1: "Re (m_oplus' c1 c2 * cnj (m_oplus' c1 c2)) = 
        Re (((c1 + c2) * (cnj c1 + cnj c2))) /
        Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2)))"
    unfolding m_oplus'_def
    by (simp add: complex_is_Real_iff)

  have "Re (((c1 + c2) * (cnj c1 + cnj c2))) = 
       (cmod c1)\<^sup>2 + (cmod c2)\<^sup>2 + Re (cnj c1 * c2 + c1 * cnj c2)"
    by (smt Re_complex_of_real complex_norm_square plus_complex.simps(1) semiring_normalization_rules(34) semiring_normalization_rules(7))
  moreover
  have "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) =
        Re (1 + cnj c1 * c2 + cnj c2 * c1 + c1 * cnj c1 * c2 * cnj c2)"
    by (simp add: field_simps)
  hence *: "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) =
        1 + Re (cnj c1 * c2 + c1 * cnj c2) + (cmod c1)\<^sup>2 * (cmod c2)\<^sup>2"
    by (smt Re_complex_of_real ab_semigroup_mult_class.mult_ac(1) complex_In_mult_cnj_zero complex_cnj_one complex_norm_square one_complex.simps(1) one_power2 plus_complex.simps(1) power2_eq_square semiring_normalization_rules(7) times_complex.simps(1))
  moreover
  have "(cmod c1)\<^sup>2 + (cmod c2)\<^sup>2 < 1 + (cmod c1)\<^sup>2 * (cmod c2)\<^sup>2"
  proof-
    have "(cmod c1)\<^sup>2 < 1" "(cmod c2)\<^sup>2 < 1"
      using assms
      by (simp_all add: cmod_def)
    hence "(1 - (cmod c1)\<^sup>2) * (1 - (cmod c2)\<^sup>2) > 0"
      by simp
    thus ?thesis
      by (simp add: field_simps)
  qed
  ultimately
  have "Re (((c1 + c2) * (cnj c1 + cnj c2))) < Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2)))"
    by simp
  moreover
  have "Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) > 0"
    by (smt "*" Re_complex_div_lt_0 calculation complex_cnj_add divide_self mult_zero_left one_complex.simps(1) zero_complex.simps(1))
  ultimately
  have 2: "Re (((c1 + c2) * (cnj c1 + cnj c2))) / Re (((1 + cnj c1 * c2) * (1 + c1 * cnj c2))) < 1"
    by (simp add: divide_less_eq)
  
  have "Re (m_oplus' c1 c2 * cnj (m_oplus' c1 c2)) < 1"
    using 1 2
    by simp
    
  thus ?thesis
    by (simp add: complex_mod_sqrt_Re_mult_cnj)
qed

lift_definition m_oplus :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<oplus>\<^sub>m" 100) is m_oplus'
proof-
  fix c1 c2
  assume "cmod c1 < 1" "cmod c2 < 1"
  thus "cmod (m_oplus' c1 c2) < 1"
    by (simp add: m_oplus'_in_disc)
qed

definition m_ominus' :: "complex \<Rightarrow> complex" where
  "m_ominus' z = - z"                                      

lemma m_ominus'_in_disc:
  assumes "cmod z < 1"
  shows "cmod (m_ominus' z) < 1"
  using assms
  unfolding m_ominus'_def
  by simp

lift_definition m_ominus :: "PoincareDisc \<Rightarrow> PoincareDisc" ("\<ominus>\<^sub>m") is m_ominus'
proof-
  fix c
  assume "cmod c < 1"
  thus "cmod (m_ominus' c) < 1" 
    by (simp add: m_ominus'_def)
qed

definition m_ozero' :: "complex" where
  "m_ozero' = 0"                                     

lift_definition m_ozero :: PoincareDisc  ("0\<^sub>m") is m_ozero'
  unfolding m_ozero'_def
  by simp

lemma m_left_id:
  shows "0\<^sub>m \<oplus>\<^sub>m a = a"
  by (transfer, simp add: m_oplus'_def m_ozero'_def)

lemma m_left_inv:
  shows "\<ominus>\<^sub>m a \<oplus>\<^sub>m a = 0\<^sub>m"
  by (transfer, simp add: m_oplus'_def m_ominus'_def m_ozero'_def)

lemma den_not_zero:
  assumes "cmod a < 1" "cmod b < 1"
  shows "1 + cnj a * b \<noteq> 0"
  using assms
  by (smt add.inverse_unique complex_mod_cnj i_squared norm_ii norm_mult norm_mult_less)

definition m_gyr' :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex" where
  "m_gyr' a b z = ((1 + a * cnj b) / (1 + cnj a * b)) * z"

lift_definition m_gyr :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" is m_gyr'
proof-
  fix a b z
  assume "cmod a < 1" "cmod b < 1" "cmod z < 1"
  have "cmod (1 + a * cnj b) = cmod (1 + cnj a * b)"
    by (metis complex_cnj_add complex_cnj_cnj complex_cnj_mult complex_cnj_one complex_mod_cnj)
  hence "cmod ((1 + a * cnj b) / (1 + cnj a * b)) = 1"
    by (simp add: \<open>cmod a < 1\<close> \<open>cmod b < 1\<close> den_not_zero norm_divide)
  thus "cmod (m_gyr' a b z) < 1"
    using \<open>cmod z < 1\<close>
    unfolding m_gyr'_def
    by (metis mult_cancel_right1 norm_mult)
qed


lemma m_gyro_commute:
  "a \<oplus>\<^sub>m b = m_gyr a b (b \<oplus>\<^sub>m a)"
  by transfer (metis (no_types, opaque_lifting) m_oplus'_def m_gyr'_def add.commute den_not_zero mult.commute nonzero_mult_divide_mult_cancel_right2 times_divide_times_eq)

lemma m_gyro_left_assoc:
  "a \<oplus>\<^sub>m (b \<oplus>\<^sub>m z) = (a \<oplus>\<^sub>m b) \<oplus>\<^sub>m m_gyr a b z"
proof transfer
  fix a b z
  assume *: "cmod a < 1" "cmod b < 1" "cmod z < 1"
  have 1: "m_oplus' a (m_oplus' b z) =
          (a + b + (1 + a * cnj b) * z) / 
          ((cnj a + cnj b) * z + (1 + cnj a * b))"
      unfolding m_gyr'_def m_oplus'_def
      by (smt "*"(2) "*"(3) ab_semigroup_mult_class.mult_ac(1) add.left_commute add_divide_eq_iff combine_common_factor den_not_zero divide_divide_eq_right mult.commute mult_cancel_right2 nonzero_mult_div_cancel_left semiring_normalization_rules(1) semiring_normalization_rules(23) semiring_normalization_rules(34) times_divide_eq_right)
  have 2: "m_oplus' (m_oplus' a b) (m_gyr' a b z) = 
          ((a + b) + (1 + a * cnj b) * z) / 
          ((cnj a + cnj b) * z + (1 + cnj a * b))"
  proof-
    have x: "((a + b) / (1 + cnj a * b) +
           (1 + a * cnj b) / (1 + cnj a * b) * z) = 
          ((a + b) + (1 + a * cnj b) * z) / (1 + cnj a * b)"
      by (metis add_divide_distrib times_divide_eq_left)
    moreover
    have "1 + cnj ((a + b) / (1 + cnj a * b)) *
               ((1 + a * cnj b) / (1 + cnj a * b) * z) = 
          1 + (cnj a + cnj b) / (1 + cnj a * b) * z"
      using divide_divide_times_eq divide_eq_0_iff mult_eq_0_iff nonzero_mult_div_cancel_left
      by force
    hence y: "1 + cnj ((a + b) / (1 + cnj a * b)) *
               ((1 + a * cnj b) / (1 + cnj a * b) * z) =
          ((cnj a + cnj b) * z + (1 + cnj a * b)) / (1 + cnj a * b)"
      by (metis "*"(1) "*"(2) add.commute add_divide_distrib den_not_zero divide_self times_divide_eq_left)
    ultimately
    show ?thesis
      unfolding m_gyr'_def m_oplus'_def  
      by (subst x, subst y, simp add: "*"(1) "*"(2) den_not_zero)
  qed
  show "m_oplus' a (m_oplus' b z) =
        m_oplus' (m_oplus' a b) (m_gyr' a b z)"
      by (subst 1, subst 2, simp)
qed

lemma m_gyr_inv:
  "m_gyr a b (m_gyr b a z) = z"
  by transfer (simp add: m_gyr'_def, metis den_not_zero nonzero_mult_div_cancel_left nonzero_mult_divide_mult_cancel_right semiring_normalization_rules(7))

lemma m_gyr_bij:
  shows "bij (m_gyr a b)"
  by (metis bij_betw_def inj_def m_gyr_inv surj_def)

lemma poincare_disc_two_elems:
  shows "\<exists> z1 z2::PoincareDisc. z1 \<noteq> z2"
proof-
  have "cmod 0 < 1"
    by simp
  moreover
  have "cmod (1/2) < 1"
    by simp
  moreover
  have "(0::complex) \<noteq> 1/2"
    by simp
  ultimately
  show ?thesis
    by transfer blast
qed

lemma m_gyr_not_degenerate:
  shows "\<exists> z1 z2. m_gyr a b z1 \<noteq> m_gyr a b z2"
proof-
  obtain z1 z2 :: PoincareDisc where "z1 \<noteq> z2"
    using poincare_disc_two_elems
    by blast
  hence "m_gyr a b z1 \<noteq> m_gyr a b z2"
    by (metis m_gyr_inv)
  thus ?thesis
    by blast
qed

lemma m_gyr_left_loop:
  shows "m_gyr a b = m_gyr (a \<oplus>\<^sub>m b) b"
proof-
  have "\<exists> z. m_gyr (a \<oplus>\<^sub>m b) b z \<noteq> 0\<^sub>m"
    using m_gyr_not_degenerate
    by metis
  hence "\<And> z. m_gyr a b z = m_gyr (a \<oplus>\<^sub>m b) b z"
  proof transfer
    fix a b z
    assume "\<exists>z\<in>{z. cmod z < 1}. m_gyr' (m_oplus' a b) b z \<noteq> m_ozero'"
    then obtain z' where
      "cmod z' < 1" "m_gyr' (m_oplus' a b) b z' \<noteq> m_ozero'"
      by auto
    hence *: "1 + (a + b) / (1 + cnj a * b) * cnj b \<noteq> 0"
      by (simp add: m_gyr'_def m_oplus'_def m_ozero'_def)
    assume "cmod a < 1" "cmod b < 1" "cmod z < 1"    
    have 1: "1 + (a + b) / (1 + cnj a * b) * cnj b = 
          (1 + cnj a * b + a * cnj b + b * cnj b) / (1 + cnj a * b)"
      using \<open>cmod a < 1\<close> \<open>cmod b < 1\<close> add_divide_distrib den_not_zero divide_self times_divide_eq_left
      by (metis (no_types, lifting) ab_semigroup_add_class.add_ac(1) distrib_right)
    have 2: "1 + cnj ((a + b) / (1 + cnj a * b)) * b = 
             (1 + cnj a * b + a * cnj b + b * cnj b) / (1 + a * cnj b)"
      by (smt "1" complex_cnj_add complex_cnj_cnj complex_cnj_divide complex_cnj_mult complex_cnj_one semiring_normalization_rules(23) semiring_normalization_rules(7))
    have "1 + cnj a * b + a * cnj b + b * cnj b \<noteq> 0"
      using * 1
      by auto
    then show "m_gyr' a b z = m_gyr' (m_oplus' a b) b z"
      unfolding m_gyr'_def m_oplus'_def
      by (subst 1, subst 2, simp)
  qed
  thus ?thesis
    by auto
qed

lemma m_gyr_distrib:
  shows "m_gyr a b (a' \<oplus>\<^sub>m b') = m_gyr a b a' \<oplus>\<^sub>m m_gyr a b b'"
  apply transfer
  apply (auto simp add: m_gyr'_def m_oplus'_def)
  apply (simp add: add_divide_distrib distrib_left)
  done

interpretation Moebius_gyrogroup: gyrogroup m_ozero m_oplus m_ominus m_gyr
proof
  fix a
  show "0\<^sub>m \<oplus>\<^sub>m a = a"
    by (simp add: m_left_id)
next
  fix a
  show "\<ominus>\<^sub>m a \<oplus>\<^sub>m a = 0\<^sub>m"
    by (simp add: m_left_inv)
next
  fix a b z
  show "a \<oplus>\<^sub>m (b \<oplus>\<^sub>m z) = a \<oplus>\<^sub>m b \<oplus>\<^sub>m m_gyr a b z"
    by (simp add: m_gyro_left_assoc)
next
  fix a b
  show "m_gyr a b = m_gyr (a \<oplus>\<^sub>m b) b"
    using m_gyr_left_loop by auto
next
  fix a b
  show "gyrogroup'.gyroaut (\<oplus>\<^sub>m) (m_gyr a b)"
    unfolding gyrogroup'.gyroaut_def
  proof safe
    fix a' b'
    show "m_gyr a b (a' \<oplus>\<^sub>m b') = m_gyr a b a' \<oplus>\<^sub>m m_gyr a b b'"
      by (simp add: m_gyr_distrib)
  next
    show "bij (m_gyr a b)"
      by (simp add: m_gyr_bij)
  qed
qed

interpretation Moebius_gyrocommutative_gyrogroup: gyrocommutative_gyrogroup m_ozero m_oplus m_ominus m_gyr
proof
  fix a b
  show "a \<oplus>\<^sub>m b = m_gyr a b (b \<oplus>\<^sub>m a)"
    using m_gyro_commute by blast
qed


instantiation PoincareDisc :: gyrogroup'
begin
definition gyrozero_PoincareDisc where
 "gyrozero_PoincareDisc = m_ozero"
definition gyroplus_PoincareDisc where
 "gyroplus_PoincareDisc = m_oplus"
definition gyroinv_PoincareDisc where
 "gyroinv_PoincareDisc = m_ominus"
definition gyr_PoincareDisc where
 "gyr_PoincareDisc = m_gyr"
instance ..
end

instantiation PoincareDisc :: gyrogroup
begin
instance proof
  fix a :: PoincareDisc
  show "0\<^sub>g \<oplus> a = a"
    by (simp add: gyroplus_PoincareDisc_def gyrozero_PoincareDisc_def)
next
  fix a :: PoincareDisc
  show "\<ominus> a \<oplus> a = 0\<^sub>g"
    by (simp add: gyroinv_PoincareDisc_def gyroplus_PoincareDisc_def gyrozero_PoincareDisc_def)
next
  fix a b :: PoincareDisc
  show "gyroaut (gyr a b)"
    by (simp add: gyr_PoincareDisc_def gyroaut_def gyroplus_PoincareDisc_def m_gyr_bij)
next
  fix a b z :: PoincareDisc
  show "a \<oplus> (b \<oplus> z) = a \<oplus> b \<oplus> gyr a b z"
    by (simp add: gyr_PoincareDisc_def gyroplus_PoincareDisc_def m_gyro_left_assoc)
next
  fix a b :: PoincareDisc
  show  "gyr a b = gyr (a \<oplus> b) b"
    using gyr_PoincareDisc_def gyroplus_PoincareDisc_def m_gyr_left_loop by auto
qed
end

instantiation PoincareDisc :: gyrocommutative_gyrogroup
begin
instance proof
  fix a b :: PoincareDisc
  show "a \<oplus> b = gyr a b (b \<oplus> a)"
    using gyr_PoincareDisc_def gyroplus_PoincareDisc_def m_gyro_commute by auto
qed
end

(* --------------------------------------------------------- *)



definition m_norm' :: "complex \<Rightarrow> real" where
  "m_norm' z = norm z"

lift_definition m_norm :: "PoincareDisc \<Rightarrow> real"  ("\<llangle>_\<rrangle>\<^sub>m" [100] 100) is m_norm'
  done


definition gamma_factor::"complex \<Rightarrow> real" where
  "gamma_factor u = (if ((norm u)^2)<1 then (1/sqrt(1-(norm u)*(norm u)))
      else 0)"
(*definition gamma_factor::"complex\<Rightarrow>real" where
  "gamma_factor u = 1/(sqrt(1 - ((cmod u)*(cmod u))))"
*)

lemma gamma_ok:
  assumes "(norm u)^2 < 1"
  shows "1/sqrt(1-(norm u)*(norm u)) \<noteq>0"
  by (metis assms eq_iff_diff_eq_0 order_less_irrefl power2_eq_square real_sqrt_eq_zero_cancel_iff zero_eq_1_divide_iff)

lemma abs_increasing_function:
  fixes x y :: real
  assumes "x < y" "x\<ge>0"
  shows "abs(x) < abs(y)"
  using assms(1) assms(2) by force

lemma gamma_factor_increase:
  fixes t1::real
  fixes t2::real
  assumes "t1<1" "t1>t2" "t2\<ge>0"
  shows "gamma_factor t1 > gamma_factor t2" 
proof-
  have d1:"(cmod t1) = abs t1"
    using norm_of_real by blast
  moreover have d2:"(cmod t2) = abs t2"
    using norm_of_real by blast
  moreover have "(abs t1) > (abs t2)"
    using assms 
    using abs_increasing_function by blast
  moreover have "(abs t1)*(abs t1) > (abs t2)*(abs t2)"
    by (simp add: assms(2) assms(3) mult_strict_mono')
  moreover have "1 - ((abs t1)*(abs t1)) < 1- ((abs t2)*(abs t2))"
    using calculation(4) by auto
  moreover have **:"sqrt(1 - ((abs t1)*(abs t1)))  < sqrt(1- ((abs t2)*(abs t2)))"
    using calculation(5) real_sqrt_less_iff by blast
  moreover have *:"1/(sqrt(1 - ((abs t1)*(abs t1)))) > 1/(sqrt(1- ((abs t2)*(abs t2))))"
    using ** frac_less2
    by (metis (no_types, opaque_lifting) abs_ge_zero abs_le_self_iff assms(1) assms(2) assms(3) diff_gt_0_iff_gt leI less_le_not_le order_le_less_trans real_sqrt_abs2 real_sqrt_gt_zero real_sqrt_lt_1_iff)
  moreover have "cmod t1 < 1"
    using assms(1) assms(2) assms(3) by force
  moreover have "cmod t2<1"
    using calculation(3) calculation(8) by force
  moreover have "(cmod t1)^2 < 1"
    by (smt (verit) calculation(8) norm_not_less_zero power2_nonneg_ge_1_iff)
  moreover have "gamma_factor t1 = 1/(sqrt(1 - (abs t1)^2))"
    by (metis calculation(10) d1 gamma_factor_def power2_eq_square)
  moreover have "(cmod t2)^2 < 1"
    using abs_square_less_1 calculation(9) by auto
  moreover have "gamma_factor t2 = 1/(sqrt(1 - (abs t2)^2))"
    by (metis calculation(12) d2 gamma_factor_def power2_eq_square)
    ultimately show ?thesis
    using * d1 d2 
    by (metis power2_eq_square)
qed

lemma gamma_factor_u_equal_normu:
  fixes u::real
  assumes "u\<ge>0" "u\<le>1"
  shows "gamma_factor u = gamma_factor (cmod u)"
  using gamma_factor_def by auto



lemma cnj_closed_for_PoincareDisc:
  assumes "cmod z1 < 1"
  shows "cmod (cnj z1) <1"
  by (simp add: assms)

lift_definition cnjP :: "PoincareDisc \<Rightarrow> PoincareDisc" is cnj
  by simp

lemma  mobius_gyroauto_help1:
  shows "z1 * cnj z1 = (cmod z1)^2"
  using complex_norm_square by fastforce
lemma  mobius_gyroauto_help2:
  assumes "cmod z1 = 1"
  shows "z1 * cnj z1 = 1"
  by (metis assms complex_cnj_one complex_norm_square mult.right_neutral norm_one)
lemma  mobius_gyroauto_help3:
  assumes "cmod u < 1" "cmod v <1"
  shows "cmod ((1+u*cnj v)/(1+ v *cnj u)) =1"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) complex_cnj_add complex_cnj_cnj complex_cnj_mult complex_cnj_one complex_mod_cnj den_not_zero divide_self_if mult.commute norm_divide norm_one)
lemma mult_closed:
  assumes "cmod z1 < 1" "cmod z2 < 1"
  shows "cmod (z1*z2)<1"
  using assms(1) assms(2) norm_mult_less by fastforce

interpretation Moebius_gyrodom': gyrodom' where
  to_dom = Rep_PoincareDisc and
  of_dom = Abs_PoincareDisc and
  in_dom = "\<lambda> z. cmod z < 1" 
rewrites
  "Moebius_gyrodom'.gyroinner = m_inner" and
  "Moebius_gyrodom'.gyronorm = m_norm"
proof-
  show *: "gyrodom' Rep_PoincareDisc Abs_PoincareDisc (\<lambda>z. cmod z < 1)"
  proof
    fix b
    assume "cmod b < 1"
    then show "Rep_PoincareDisc (Abs_PoincareDisc b) = b"
      by (simp add: Abs_PoincareDisc_inverse)
  next
    fix a
    show "Abs_PoincareDisc (Rep_PoincareDisc a) = a"
      by (simp add: Rep_PoincareDisc_inverse)
  next
    show "Rep_PoincareDisc 0\<^sub>g = 0"
      by (simp add: gyrozero_PoincareDisc_def m_ozero'_def m_ozero.rep_eq)
  qed

  show "gyrodom'.gyroinner Rep_PoincareDisc = (\<cdot>\<^sub>m)"
    apply rule
    apply rule
    unfolding gyrodom'.gyroinner_def[OF *]
    apply transfer
    by (simp add: inner_complex_def m_inner'_def)

  show "gyrodom'.gyronorm Rep_PoincareDisc = m_norm"
    apply rule
    unfolding gyrodom'.gyronorm_def[OF *]
    apply transfer
    by (simp add: m_norm'_def)
qed

lemma mobius_gyroauto:
  shows "m_gyr u v a \<cdot>\<^sub>m m_gyr u v b = a \<cdot>\<^sub>m b"
proof-
  have "m_gyr u v a \<cdot>\<^sub>m m_gyr u v b = Re((cnj (Rep_PoincareDisc (m_gyr u v a))) * (Rep_PoincareDisc (m_gyr u v b)))"
    using m_inner.rep_eq m_inner_more by presburger
  moreover have "m_gyr u v a = Abs_PoincareDisc(((1 + (Rep_PoincareDisc u) * cnj (Rep_PoincareDisc v)) / (1 + (cnj (Rep_PoincareDisc u)) * Rep_PoincareDisc v)) *
    (Rep_PoincareDisc a))"
    by (metis Moebius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
  moreover have "m_gyr u v b = Abs_PoincareDisc(((1 + (Rep_PoincareDisc u) * cnj (Rep_PoincareDisc v)) / (1 + (cnj (Rep_PoincareDisc u)) * Rep_PoincareDisc v)) *
    (Rep_PoincareDisc b))"
    by (metis Moebius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
  moreover have "(cnj (Rep_PoincareDisc (m_gyr u v a))) = cnj ((1 + (Rep_PoincareDisc u) * cnj (Rep_PoincareDisc v)) / (1 + (cnj (Rep_PoincareDisc u)) * Rep_PoincareDisc v)) *
    cnj (Rep_PoincareDisc a)"
    by (simp add: m_gyr'_def m_gyr.rep_eq)
  moreover have " (cnj ((1 + (Rep_PoincareDisc u) * cnj (Rep_PoincareDisc v)) / (1 + (Rep_PoincareDisc v)*(cnj (Rep_PoincareDisc u))) ))*  ((1 + (Rep_PoincareDisc u) * cnj (Rep_PoincareDisc v)) / (1 + (Rep_PoincareDisc v)*(cnj (Rep_PoincareDisc u)))) = 1"
  proof-
    have *:"cmod (Rep_PoincareDisc u) < 1"
      using Rep_PoincareDisc by blast
    moreover have **:"cmod (Rep_PoincareDisc v) < 1"
      using Rep_PoincareDisc by blast
    moreover have "cmod (((1 + (Rep_PoincareDisc u) * cnj (Rep_PoincareDisc v)) / (1 +  (Rep_PoincareDisc v)*(cnj (Rep_PoincareDisc u))))) =1"
      using   mobius_gyroauto_help3[OF * **] 
      by force
    ultimately show ?thesis using mobius_gyroauto_help2
      by (metis mult.commute)
  qed
  moreover have "m_gyr u v a \<cdot>\<^sub>m m_gyr u v b = Re((cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))"
    using calculation(1) calculation(5) m_gyr'_def m_gyr.rep_eq by force
  moreover have "a \<cdot>\<^sub>m b = Re((cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))"
    by (simp add: m_inner.rep_eq m_inner_more)
  ultimately show ?thesis
    by presburger
qed

(* --------------------------------------------------------- *)
interpretation Moebius_gyrodom: gyrodom Rep_PoincareDisc Abs_PoincareDisc "\<lambda> z. cmod z < 1"
proof
  fix u v a b
  have "gyr u v a \<cdot>\<^sub>m gyr u v b = a \<cdot>\<^sub>m b"
    by (simp add: gyr_PoincareDisc_def mobius_gyroauto)
  then show "gyrodom'.gyroinner Rep_PoincareDisc (gyr u v a) (gyr u v b) =
             gyrodom'.gyroinner Rep_PoincareDisc a b"  
    using Moebius_gyrodom'.gyrodom'_axioms Moebius_gyrodom'.gyroinner_def gyrodom'.gyroinner_def by fastforce
qed

(* --------------------------------------------------------- *)

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
  
definition m_otimes'_k :: "real \<Rightarrow> complex \<Rightarrow> real" where
  "m_otimes'_k r z = ((1 + cmod z) powr r - (1 - cmod z) powr r) /
                     ((1 + cmod z) powr r + (1 - cmod z) powr r)" 

lemma m_otimes'_k_tanh: 
  assumes "cmod z < 1"
  shows "m_otimes'_k r z = tanh (r * artanh (cmod z))"
proof-
  have "0 < 1 + cmod z"
    by (smt norm_not_less_zero)
  hence "(1 + cmod z) powr r \<noteq> 0"
    by auto

  have "1 - (1 - cmod z) powr r / (1 + cmod z) powr r = 
        ((1 + cmod z) powr r - (1 - cmod z) powr r) / (1 + cmod z) powr r"
    by (smt \<open>(1 + cmod z) powr r \<noteq> 0\<close> add_divide_distrib divide_self)
  moreover
  have "1 + (1 - cmod z) powr r / (1 + cmod z) powr r =
       ((1 + cmod z) powr r + (1 - cmod z) powr r) / (1 + cmod z) powr r"
    by (smt add_divide_distrib calculation)
  moreover
  have "exp (- (r * ln ((1 + cmod z) / (1 - cmod z)))) =
         ((1 + cmod z) / (1 - cmod z)) powr (-r)" 
    using `0 < 1 + cmod z` ln_powr[symmetric, of "(1 + cmod z) / (1 - cmod z)" "-r"]
    using assms
    by auto
  ultimately
  show ?thesis
    using assms powr_divide[of "1 + cmod z" "1 - cmod z" r]
    using `0 < 1 + cmod z` `(1 + cmod z) powr r \<noteq> 0`
    unfolding m_otimes'_k_def tanh_real_altdef artanh_def
    by (simp add: powr_minus_divide)
qed

lemma cmod_m_otimes'_k: 
  assumes "cmod z < 1"
  shows "cmod (m_otimes'_k r z) < 1"
  by (smt assms divide_less_eq_1_pos divide_minus_left m_otimes'_k_def norm_of_real powr_gt_zero zero_less_norm_iff)

definition m_otimes' :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "m_otimes' r z = 
     (if z = 0 then 0 else cor (m_otimes'_k r z) * (z / cmod z))"

lemma cmod_m_otimes':
  assumes "cmod z < 1"
  shows "cmod (m_otimes' r z) = abs (m_otimes'_k r z)"
proof (cases "z = 0")
  case True
  thus ?thesis
    by (simp add: m_otimes'_def m_otimes'_k_def)
next
  case False
  hence "cmod (cor (m_otimes'_k r z)) = abs (m_otimes'_k r z)"
    by simp
  then show ?thesis
    using False
    unfolding m_otimes'_def
    by (simp add: norm_divide norm_mult)
qed

lift_definition m_otimes :: "real \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<otimes>\<^sub>m" 105) is m_otimes'
  using cmod_m_otimes' cmod_m_otimes'_k by auto

lemma m_otimes_distrib_lemma':
  fixes "ax" "bx" "ay" "by" :: real
  assumes "ax + bx \<noteq> 0" "ay + by \<noteq> 0"
  shows "(ax * ay - bx * by) / (ax * ay + bx * by) = 
         ((ax - bx)/(ax + bx) + (ay - by)/(ay + by)) / 
          (1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)))" (is "?lhs = ?rhs")
proof-
  have "(ax - bx)/(ax + bx) + (ay - by)/(ay + by) = ((ax - bx)*(ay + by) + (ay - by)*(ax + bx)) / ((ax + bx)*(ay + by))"
    by (simp add: \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> add_frac_eq)
  hence 1: "(ax - bx)/(ax + bx) + (ay - by)/(ay + by) = 2 * (ax * ay - bx * by) / ((ax + bx)*(ay + by))"
    by (simp add: field_simps)

  have "1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)) = 
        (((ax + bx)*(ay + by)) + (ax - bx)*(ay - by))/((ax + bx)*(ay + by))"
    by (simp add: \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> add_divide_distrib)
  hence 2: "1 + ((ax - bx)/(ax + bx))*((ay - by)/(ay + by)) = 2 * (ax * ay + bx * by) / ((ax + bx)*(ay + by))"
    by (simp add: field_simps)

  have "?rhs = 2 * (ax * ay - bx * by) / ((ax + bx) * (ay + by)) /
              (2 * (ax * ay + bx * by) / ((ax + bx) * (ay + by)))"
    by (subst 1, subst 2, simp)
  also have "\<dots> = (2 * (ax * ay - bx * by) * ((ax + bx) * (ay + by))) /
                  (2 * ((ax + bx) * (ay + by)) * (ax * ay + bx * by))"
    by auto
  also have "\<dots> = ((2 * ((ax + bx) * (ay + by))) * (ax * ay - bx * by)) / 
                  ((2 * ((ax + bx) * (ay + by))) * (ax * ay + bx * by))"
    by (simp add: field_simps)
  also have "\<dots> = (ax * ay - bx * by) / (ax * ay + bx * by)"
    using \<open>ax + bx \<noteq> 0\<close> \<open>ay + by \<noteq> 0\<close> by auto
  finally
  show ?thesis
    by simp                                                                                 
qed

lemma m_otimes_distrib_lemma:
  assumes "cmod a < 1"
  shows "m_otimes'_k (r1 + r2) a = m_oplus' (m_otimes'_k r1 a) (m_otimes'_k r2 a)"
  unfolding m_otimes'_k_def m_oplus'_def
  unfolding powr_add
  apply (subst m_otimes_distrib_lemma')
  apply (smt powr_gt_zero powr_non_neg)
  apply (smt powr_gt_zero powr_non_neg)
  apply simp
  done


lemma m_otimes_distrib:
  shows "(r1 + r2) \<otimes>\<^sub>m a = r1 \<otimes>\<^sub>m a \<oplus>\<^sub>m r2 \<otimes>\<^sub>m a" 
proof transfer
  fix r1 r2 a
  assume "cmod a < 1"
  show "m_otimes' (r1 + r2) a = m_oplus' (m_otimes' r1 a) (m_otimes' r2 a)"
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: m_otimes'_def m_oplus'_def)
  next
    case False
    let ?p = "1 + cmod a" and ?m = "1 - cmod a"
    have "cor (m_otimes'_k (r1 + r2) a) * a / cor (cmod a) = 
          m_oplus' (m_otimes'_k r1 a) (m_otimes'_k r2 a) * a / cor (cmod a)"
      by (simp add: \<open>cmod a < 1\<close> m_otimes_distrib_lemma)
    moreover
    have "cor (m_otimes'_k r1 a) * cnj a * (cor (m_otimes'_k r2 a) * a) / (cor (cmod a) * cor (cmod a)) = 
          cor (m_otimes'_k r1 a) * cor (m_otimes'_k r2 a)"
      by (smt False complex_mod_cnj complex_mod_mult_cnj complex_norm_square mult.commute nonzero_mult_div_cancel_left norm_mult of_real_mult times_divide_times_eq zero_less_norm_iff)
    ultimately
     show ?thesis
      using False
      unfolding m_otimes'_def m_oplus'_def
      by (smt complex_cnj_complex_of_real complex_cnj_divide complex_cnj_mult distrib_right times_divide_eq_left times_divide_eq_right times_divide_times_eq)
  qed      
qed

(*
lemma h: 
  assumes "cmod z < 1"
  shows "tanh (r * artanh (cmod z)) = \<bar>r\<bar> * (cmod z)"
  sorry
*)
lemma m_otimes_assoc:
  shows "(r1 * r2) \<otimes>\<^sub>m a = r1 \<otimes>\<^sub>m (r2 \<otimes>\<^sub>m a)"
proof transfer
  fix r1 r2 a
  assume "cmod a < 1"
  show "m_otimes' (r1 * r2) a = m_otimes' r1 (m_otimes' r2 a)"
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: m_otimes'_def)
  next
    case False
    show ?thesis
    proof (cases "r2 = 0")
      case True
      thus ?thesis
        by (simp add: \<open>cmod a < 1\<close> m_otimes'_def m_otimes'_k_tanh)
    next
      case False
      let ?a2 = "m_otimes' r2 a"
      let ?k2 = "m_otimes'_k r2 a"
      have "cmod ?a2 = abs ?k2"
        using \<open>cmod a < 1\<close> cmod_m_otimes'
        by blast
      hence "cmod ?a2 < 1"
        using \<open>cmod a < 1\<close> cmod_m_otimes'_k
        by auto
      have "(1 + cmod a) / (1 - cmod a) > 1"
        using `a \<noteq> 0`
        by (simp add: \<open>cmod a < 1\<close>)
      hence "artanh (cmod a) > 0"
        by (simp add: artanh_def)
      hence "?k2 \<noteq> 0"
        using `cmod a < 1` `a \<noteq> 0` m_otimes'_k_tanh[of a r2] `r2 \<noteq> 0`
        by auto
      hence "?a2 \<noteq> 0"
        using `a \<noteq> 0`
        unfolding m_otimes'_def
        by simp
      have "sgn ?k2 = sgn r2"
        using m_otimes'_k_tanh[OF `cmod a < 1`, of r2]
        by (smt \<open>0 < artanh (cmod a)\<close> \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> \<open>?a2 \<noteq> 0\<close> mult_nonneg_nonneg mult_nonpos_nonneg sgn_neg sgn_pos tanh_0 tanh_real_neg_iff zero_less_norm_iff)
      have "m_otimes' r1 (m_otimes' r2 a) = 
             cor (m_otimes'_k r1 (cor ?k2 * a / cor (cmod a))) *
             (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using False `?a2 \<noteq> 0`
        using \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> 
        unfolding m_otimes'_def
        by auto
      also have "... = cor (tanh (r1 * \<bar>r2 * artanh (cmod a)\<bar>)) *  
                 (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using cmod_m_otimes'[of a r2] `cmod a < 1` `a \<noteq> 0`
        unfolding m_otimes'_def
        using \<open>cmod ?a2 < 1\<close> \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> m_otimes'_k_tanh 
        using \<open>cmod a < 1\<close> m_otimes'_k_tanh[of a r2]
        by (simp add: artanh_abs_tanh)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) *  
                 (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using `artanh (cmod a) > 0`
        by (smt ab_semigroup_mult_class.mult_ac(1) mult_minus_left mult_nonneg_nonneg)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) * sgn ?k2 * (a / cor (cmod a))"
        by (simp add: mult.commute real_sgn_eq)
      also have "... = cor (tanh (r1 * \<bar>r2\<bar> * artanh (cmod a))) * sgn r2 * (a / cor (cmod a))"
        using `sgn ?k2 = sgn r2`
        by simp
      also have "... = cor (tanh (r1 * r2 * artanh (cmod a))) * (a / cor (cmod a))"
        by (cases "r2 \<ge> 0") auto
      finally show ?thesis
        by (simp add: \<open>cmod a < 1\<close> m_otimes'_def m_otimes'_k_tanh)
    qed
  qed
qed

lemma real_compex_cmod:
  fixes r::real 
  shows "cmod(r*z) = abs(r) * cmod(z)"
  by (metis abs_mult norm_of_real)

lemma tanh_help:
  fixes x::real
  shows "tanh (abs x) = abs (tanh x)"
  using tanh_real_abs by blast

lemma artanh_help:
  fixes x::real
  shows "(0\<le>x \<and> x<1)\<longrightarrow> ((artanh x)\<ge>0)"
proof-
  {assume "0\<le>x \<and> x<1"
  have "(1+x)/(1-x) \<ge> 1/(1-x)"
    by (metis \<open>0 \<le> x \<and> x < 1\<close> add_0 add_increasing2 divide_right_mono le_diff_eq less_eq_real_def)
  moreover have "1/(1-x) \<ge> 1"
    using `0\<le>x \<and> x<1` 
    by simp
  moreover have "artanh x = 1/2*ln((1+x)/(1-x))"
    by (simp add: artanh_def)
  moreover have "ln((1+x)/(1-x))\<ge>0"
    using calculation(1) calculation(2) by fastforce
  moreover have "((artanh x)\<ge>0)"
    using calculation(3) calculation(4) by linarith
}
  moreover have "(0\<le>x \<and> x<1)\<longrightarrow> ((artanh x)\<ge>0)"
    using calculation by blast
  ultimately show ?thesis by blast
qed

  (*find_theorems artanh*)

lemma div_help:
  fixes x::real
  shows "(x\<noteq>0)\<longrightarrow>x/(x*y) = 1/y"
  by auto

lemma artanh_0:
  shows "artanh 0 = 0"
  by simp

lemma tanh_0:
  shows "tanh 0 = 0"
  by simp

lemma artanh_not_0:
  fixes x::real
  shows "(x>0 \<and> x<1) \<longrightarrow> (artanh x \<noteq> 0)"
  by (simp add: artanh_def)


lemma tanh_not_0:
  fixes x::real
  shows "(x>0 \<and> x<1) \<longrightarrow> (tanh x \<noteq> 0)"
  by simp

lemma mobius_scale_prop:
  fixes r::real
  assumes "r\<noteq>0"
  (*assumes "r\<noteq>0" "(Rep_PoincareDisc a)\<noteq>0"*)
  shows " (Rep_PoincareDisc (\<bar>r\<bar> \<otimes>\<^sub>m a)) / (\<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m)  = ((Rep_PoincareDisc a) / \<llangle>a\<rrangle>\<^sub>m)"
proof-
 
  have "(Rep_PoincareDisc (\<bar>r\<bar> \<otimes>\<^sub>m a)) = tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))* ((Rep_PoincareDisc a) / \<llangle>a\<rrangle>\<^sub>m)"
    using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc m_otimes'_def m_otimes'_k_tanh m_otimes.rep_eq by force
  moreover have "\<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m = cmod (tanh(r* artanh (cmod (Rep_PoincareDisc a)))* ((Rep_PoincareDisc a) / \<llangle>a\<rrangle>\<^sub>m))"
    by (metis (no_types, lifting) Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc calculation cmod_m_otimes' m_otimes'_def m_otimes'_k_tanh m_otimes.rep_eq mem_Collect_eq norm_mult norm_of_real)
  moreover have "\<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m = abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m) * (cmod (Rep_PoincareDisc a))"
    by (metis (no_types, opaque_lifting) calculation(2) norm_mult norm_of_real of_real_divide times_divide_eq_left times_divide_eq_right)
  moreover have " abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m) =  (tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m )"
    by (metis Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_divide abs_le_self_iff abs_mult_pos abs_norm_cancel artanh_help dual_order.refl mem_Collect_eq  tanh_real_abs)
  moreover have "tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a))) = tanh(\<bar>r\<bar>* abs (artanh (cmod (Rep_PoincareDisc a))))"
    by (smt (verit) Rep_PoincareDisc artanh_help mem_Collect_eq norm_ge_zero)
  moreover have "tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a))) = abs(tanh(r* artanh (cmod (Rep_PoincareDisc a))))"
    by (metis abs_mult calculation(5) tanh_real_abs)
  moreover have "(Rep_PoincareDisc (\<bar>r\<bar> \<otimes>\<^sub>m a)) =(tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))  / \<llangle>a\<rrangle>\<^sub>m)* (Rep_PoincareDisc a) "
     by (simp add: calculation(1))
   moreover have *:"(tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))  / \<llangle>a\<rrangle>\<^sub>m) =  abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m)"
     using calculation(4) by presburger
   moreover have "(Rep_PoincareDisc (\<bar>r\<bar> \<otimes>\<^sub>m a)) / (\<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m) = ((tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))  / \<llangle>a\<rrangle>\<^sub>m)* (Rep_PoincareDisc a)) / ( abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m) * (cmod (Rep_PoincareDisc a)))" 
     using calculation(3) calculation(7) by presburger

   moreover have "((tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))  / \<llangle>a\<rrangle>\<^sub>m)* (Rep_PoincareDisc a)) / ( abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m) * (cmod (Rep_PoincareDisc a))) =
        ((Rep_PoincareDisc a) * (tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))  / \<llangle>a\<rrangle>\<^sub>m)/(abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m) * (cmod (Rep_PoincareDisc a))) )"
     by simp
   have "(r=0 \<or> (Rep_PoincareDisc a)=0) \<or> (r\<noteq>0 \<and> (Rep_PoincareDisc a)\<noteq>0)"
    by blast
  moreover {
    assume "r=0 \<or> (Rep_PoincareDisc a)=0"
    moreover {
      assume "(Rep_PoincareDisc a)=0"
      then have ?thesis
        by (simp add: \<open>Rep_PoincareDisc (\<bar>r\<bar> \<otimes>\<^sub>m a) = cor (tanh (\<bar>r\<bar> * artanh (cmod (Rep_PoincareDisc a))) / \<llangle>a\<rrangle>\<^sub>m) * Rep_PoincareDisc a\<close>)
    } moreover {
      assume "r=0" (* ovo ne moze jer imamo nula vektor kroz normu nula vektora *)
      then have ?thesis 
       (* using assms(1) by auto*) 
        using assms by blast
    }
    then have ?thesis
      using calculation(1) calculation(2) by blast
  }
  moreover {
    assume "(r\<noteq>0 \<and> (Rep_PoincareDisc a)\<noteq>0)"
    have "abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m) \<noteq>0"
      by (metis MobiusGyroGroup.artanh_0 Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc \<open>r \<noteq> 0 \<and> Rep_PoincareDisc a \<noteq> 0\<close> abs_norm_cancel artanh_not_0 artanh_tanh_real divide_eq_0_iff linorder_not_less mem_Collect_eq mult_eq_0_iff norm_eq_zero not_less_iff_gr_or_eq zero_less_abs_iff)
    then have ?thesis 
      using Moebius_gyrodom'.gyronorm_def calculation(1) calculation(3) calculation(4) by fastforce
  }
  (* moreover have " ((tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))  / \<llangle>a\<rrangle>\<^sub>m) / 
      (abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m) * (cmod (Rep_PoincareDisc a)))) =
        (1/(cmod (Rep_PoincareDisc a)))"
     using *  sorry*)
   
  ultimately show ?thesis by blast
   
qed


lemma bin_square:
  fixes a::real
  fixes b::real
  shows "(a+b)*(a+b) = (a*a) + 2*a*b + (b*b)"
  by (smt (verit) power2_eq_square power2_sum)


lemma help1:
  fixes a::real
  fixes b::real
  shows "(1+a)*(1+b) = 1+a*b+a+b"
  by (simp add: distrib_left ring_class.ring_distribs(2))
lemma help2:
  fixes x::real
  fixes y::real
  assumes "x\<ge>0" "y\<ge>0" "x<1" "y<1"
  shows "(1-((x+y)*(x+y))/((1+x*y)*(1+x*y))) = ((1-x*x)*(1-y*y))/((1+x*y)*(1+x*y))"
proof-
  have *:"(1-((x+y)*(x+y))/((1+x*y)*(1+x*y))) = ((1+x*y)*(1+x*y) - (x+y)*(x+y))/((1+x*y)*(1+x*y))"
    by (smt (verit, ccfv_threshold) add_divide_distrib assms(1) assms(2) div_self mult_eq_0_iff mult_nonneg_nonneg)
  moreover have "((1+x*y)*(1+x*y)) = (1+x*y+x*y+x*y*x*y)"
  proof-
    obtain "a" "b" where "a=x*y \<and> b=x*y"
      by blast
    then show ?thesis using help1[of a b]
      by auto
  qed
  moreover have "(x+y)*(x+y) = x*x+x*y+y*x+y*y"
    by (simp add: distrib_right ring_class.ring_distribs(1))
  moreover have **:"((1+x*y)*(1+x*y) - (x+y)*(x+y)) = 1 +x*y*x*y - x*x - y*y"
    by (simp add: calculation(2) calculation(3))
  moreover have ***:" 1 +x*y*x*y - x*x - y*y = (1-x*x)*(1-y*y)"
    by (smt (verit, del_insts) help1 mult.assoc mult.commute mult_minus_right)
  ultimately show ?thesis
    using * ** ***
    by presburger
qed

lemma help3:
  fixes x::real
  fixes y::real
  assumes "x\<ge>0" "y\<ge>0" "x<1" "y<1"
  shows "sqrt((1-((x+y)*(x+y))/((1+x*y)*(1+x*y)))) = 
          (sqrt(1-x*x) *sqrt(1-y*y))/(sqrt((1+x*y)*(1+x*y)))"
  using assms(1) assms(2) assms(3) assms(4) help2 real_sqrt_divide real_sqrt_mult by presburger

lemma help4:
  fixes x::real
  fixes y::real
  assumes "x\<ge>0" "y\<ge>0" "x<1" "y<1"
  shows "1/(sqrt((1-((x+y)*(x+y))/((1+x*y)*(1+x*y))))) = 
         ((1+x*y)/ (sqrt(1-x*x) *sqrt(1-y*y)))"
  by (simp add: assms(1) assms(2) assms(3) assms(4) help3)

lemma help5:
  fixes x::real
  fixes y::real
  fixes t1::real
  fixes t2::real
  assumes "t1>t2" "x>0" "y>0"
  shows "x*y*t1 > x*y*t2"
  by (simp add: assms(1) assms(2) assms(3))

lemma gamma_factor_positive_always:
  shows "\<forall>x. ((cmod x <1)\<longrightarrow>(gamma_factor x >0))"
  unfolding gamma_factor_def
  by (smt (verit, del_insts) divide_pos_pos norm_ge_zero power2_eq_square power2_nonneg_ge_1_iff real_sqrt_gt_0_iff)
  

lemma help6:
  shows "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b)=
      (1-cmod(a)*cmod(a))*(1-cmod(b)*cmod(b))"
proof-
  have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b) * cnj(1+(cnj a)*b)"
    by (metis complex_norm_square power2_eq_square)
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b) * (cnj(1) + cnj((cnj a)*b))"
    using calculation complex_cnj_add by presburger
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b)*(1+(cnj(cnj a))* (cnj b))"
    using calculation(2) complex_cnj_mult complex_cnj_one by presburger
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b)*(1+a*(cnj b))"
    using calculation(3) by auto
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b)= 1+a*(cnj b)+(cnj a)*b + (cnj a)*b*a*(cnj b)"
    by (smt (verit, ccfv_threshold) add.assoc calculation(4) distrib_left mult.assoc mult.right_neutral mult_1 ring_class.ring_distribs(2))
  moreover have "cmod(a+b)*cmod(a+b) = (a+b)*cnj(a+b)"
    by (metis complex_norm_square power2_eq_square)
  moreover have "cmod(a+b)*cmod(a+b) = (a+b)*((cnj a)+(cnj b))"
    using calculation(6) by auto
  moreover have "cmod(a+b)*cmod(a+b) = a*(cnj a) + a*(cnj b) + b*(cnj a) + b*(cnj b)"
    by (metis calculation(7) comm_semiring_class.distrib group_cancel.add1 ring_class.ring_distribs(1))
  moreover have " cmod(a+b)*cmod(a+b) = cmod(a)*cmod(a) + a*(cnj b) + b*(cnj a) + cmod(b)*cmod(b)"
    by (metis calculation(8) complex_norm_square power2_eq_square)
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = 
    (1+a*(cnj b)+(cnj a)*b + (cnj a)*b*a*(cnj b))-( cmod(a)*cmod(a) + a*(cnj b) + b*(cnj a) + cmod(b)*cmod(b))"
    using calculation(5) calculation(9) by auto
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) =
      (1+a*(cnj b)+(cnj a)*b +(cnj a)*b*a*(cnj b) - cmod(a)*cmod(a)-a*(cnj b) - b*(cnj a)-cmod(b)*cmod(b))"
    using calculation(10) by fastforce
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cnj a)*b*a*(cnj b)- cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    using calculation(11) by fastforce
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cnj a)*a*(b*(cnj b)) - cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    using calculation(12) by fastforce
  moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cmod(a)*cmod(a))*(b*(cnj b))-cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by (metis (mono_tags, opaque_lifting) calculation(13) complex_norm_square mult.assoc mult.left_commute power2_eq_square)
    moreover have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cmod(a)*cmod(a))*(cmod(b)*cmod(b))-cmod(a)*cmod(a) - cmod(b)*cmod(b))"
      by (smt (verit) Re_complex_of_real calculation(14) cmod_power2 complex_In_mult_cnj_zero complex_mod_cnj complex_mod_mult_cnj diff_add_cancel mobius_gyroauto_help1 norm_mult norm_zero of_real_1 plus_complex.sel(1) times_complex.sel(1))
    moreover have " (1-cmod(a)*cmod(a))*(1-cmod(b)*cmod(b)) = 1+(cmod(a)*cmod(a))*(cmod(b)*cmod(b))-cmod(a)*cmod(a)-cmod(b)*cmod(b)"
    proof-
      let ?iz1 = "-cmod(a)*cmod(a)"
      let ?iz2 = "-cmod(b)*cmod(b)"
      show ?thesis using help1[of ?iz1 ?iz2] 
        by simp
    qed
    ultimately show ?thesis 
      by presburger
  qed

lemma help7:
  fixes x::real
  fixes y::real
  assumes "x\<ge>0" "y>0"  
  shows "1/(sqrt (1-((x*x)/(y*y)))) = abs(y)/(sqrt(y*y-x*x))"
proof-
  have "1-((x*x)/(y*y)) = (y*y-x*x)/(y*y)"
    by (metis assms(2) diff_divide_distrib div_0 divide_less_cancel divide_self no_zero_divisors)
  moreover have "sqrt(1-((x*x)/(y*y))) = sqrt((y*y-x*x)/(y*y))"
    using calculation by force
  moreover have "sqrt(1-((x*x)/(y*y))) = sqrt(y*y-x*x)/sqrt(y*y)"
    using calculation(1) real_sqrt_divide by presburger
  moreover have "sqrt(1-((x*x)/(y*y))) = sqrt(y*y-x*x)/abs(y)"
    using calculation(3) real_sqrt_abs2 by presburger
  moreover have "1/sqrt(1-((x*x)/(y*y))) = abs(y)/sqrt(y*y-x*x)"
    by (simp add: calculation(4))
  ultimately show ?thesis by auto
qed
lemma gamma_factor_eq1:
  shows "gamma_factor (\<llangle>  a  \<oplus>\<^sub>m b \<rrangle>\<^sub>m) = (gamma_factor (Rep_PoincareDisc a))* (gamma_factor (Rep_PoincareDisc b))*(cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b)))"
proof-

  have "norm (\<llangle>  a  \<oplus>\<^sub>m b \<rrangle>\<^sub>m) ^2 < 1"
    using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_square_less_1 by fastforce
  moreover have *:"gamma_factor (\<llangle>  a  \<oplus>\<^sub>m b \<rrangle>\<^sub>m) = 
1/sqrt(1-((cmod(((Rep_PoincareDisc a)+(Rep_PoincareDisc b))))/
(cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))))*((cmod(((Rep_PoincareDisc a)+(Rep_PoincareDisc b))))/
(cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b)))))"
    
    by (smt (verit, best) Moebius_gyrodom'.gyronorm_def calculation gamma_factor_def m_oplus'_def m_oplus.rep_eq norm_divide norm_eq_zero norm_le_zero_iff norm_of_real real_norm_def)
 
  moreover have **:"gamma_factor (\<llangle>  a  \<oplus>\<^sub>m b \<rrangle>\<^sub>m) = cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))/
    sqrt((cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))*cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b)) -
    (cmod((Rep_PoincareDisc a)+(Rep_PoincareDisc b)))*(cmod((Rep_PoincareDisc a)+(Rep_PoincareDisc b)))))"
  proof-
    let ?iz1 = "(cmod((Rep_PoincareDisc a)+(Rep_PoincareDisc b)))*(cmod((Rep_PoincareDisc a)+(Rep_PoincareDisc b)))"
    let ?iz2 = "(cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b)))*(cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b)))"
    have "?iz1\<ge>0" 
      by force
    moreover have "?iz2>0"
      using  den_not_zero
      using Rep_PoincareDisc by auto
    ultimately show ?thesis using help7[of ?iz1 ?iz2]
      by (simp add: * help7 zero_less_mult_iff)
  qed
  moreover have "sqrt((cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))*cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b)) -
    (cmod((Rep_PoincareDisc a)+(Rep_PoincareDisc b)))*(cmod((Rep_PoincareDisc a)+(Rep_PoincareDisc b))))) =
    sqrt((1-cmod((Rep_PoincareDisc a))*cmod((Rep_PoincareDisc a))) *(1-cmod((Rep_PoincareDisc b))*cmod((Rep_PoincareDisc b)))) "    
    using help6 by presburger
  ultimately show ?thesis    
    by (smt (verit, del_insts) Rep_PoincareDisc divide_divide_eq_left gamma_factor_def gamma_factor_positive_always mem_Collect_eq power2_eq_square power_one real_sqrt_mult times_divide_eq_left times_divide_eq_right)
qed

lemma gamma_factor_ineq1:
  shows "(gamma_factor (\<llangle>  a  \<oplus>\<^sub>m b \<rrangle>\<^sub>m )) \<le> (gamma_factor (Rep_PoincareDisc ((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>m)))  \<oplus>\<^sub>m (Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>m))) )))"
proof-
  have "(gamma_factor (Rep_PoincareDisc ((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>m)))  \<oplus>\<^sub>m (Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>m))) ))) = (gamma_factor ((cor (\<llangle>a\<rrangle>\<^sub>m))))*(gamma_factor ((cor (\<llangle>b\<rrangle>\<^sub>m))))*(1+ \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m)"
  proof-
    let ?izraz1 =  "((cor (\<llangle>a\<rrangle>\<^sub>m)+(cor (\<llangle>b\<rrangle>\<^sub>m)))/(1+(cor (\<llangle>a\<rrangle>\<^sub>m))* (cor (\<llangle>b\<rrangle>\<^sub>m))))"
    let ?izraz2 = "(Rep_PoincareDisc ((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>m)))  \<oplus>\<^sub>m (Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>m))) )) "
    have "?izraz1 = ?izraz2"
      using Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.to_dom Rep_PoincareDisc m_oplus'_def m_oplus.rep_eq by auto
    moreover have "norm ((\<llangle>a\<rrangle>\<^sub>m))^2 < 1"
      using Rep_PoincareDisc abs_square_less_1 m_norm'_def m_norm.rep_eq by fastforce
        moreover have "norm ((\<llangle>b\<rrangle>\<^sub>m))^2 < 1"
      using Rep_PoincareDisc abs_square_less_1 m_norm'_def m_norm.rep_eq by fastforce
    moreover have " (gamma_factor ((cor (\<llangle>a\<rrangle>\<^sub>m)))) = (1/(sqrt(1-((\<llangle>a\<rrangle>\<^sub>m)*(\<llangle>a\<rrangle>\<^sub>m)))))"
      using calculation(2) gamma_factor_def by auto
    
     moreover have " (gamma_factor ((cor (\<llangle>b\<rrangle>\<^sub>m)))) = (1/(sqrt(1-((\<llangle>b\<rrangle>\<^sub>m)*(\<llangle>b\<rrangle>\<^sub>m)))))"
       using calculation(3) gamma_factor_def by force
     
     moreover have "gamma_factor (?izraz1) = (1/(sqrt(1-((cmod (?izraz1)) * cmod(?izraz1))))) "
       by (smt (verit, best) Rep_PoincareDisc calculation(1) gamma_factor_def gamma_factor_positive_always mem_Collect_eq)
 
     moreover have *:"cmod(?izraz1) = (?izraz1)"
       by (smt (verit, ccfv_threshold) Moebius_gyrodom'.gyronorm_def mult_less_0_iff norm_divide norm_not_less_zero norm_of_real of_real_1 of_real_add of_real_divide of_real_mult)
     moreover have "gamma_factor (?izraz1) = (1/(sqrt(1-(Re(?izraz1)*Re(?izraz1))))) "
       by (metis "*" Re_complex_of_real calculation(6))

     moreover have "Re(?izraz1) = ?izraz1"
       by fastforce

     let ?a = " (\<llangle>a\<rrangle>\<^sub>m)"
     let ?b = " (\<llangle>b\<rrangle>\<^sub>m)"

     have "Re(?izraz1) = (?a+?b)/(1+?a*?b)"
       by force
     have "gamma_factor (((cor (\<llangle>a\<rrangle>\<^sub>m)+(cor (\<llangle>b\<rrangle>\<^sub>m)))/(1+(cor (\<llangle>a\<rrangle>\<^sub>m))* (cor (\<llangle>b\<rrangle>\<^sub>m))))) =
           ((1+\<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m)/ (sqrt(1-\<llangle>a\<rrangle>\<^sub>m*\<llangle>a\<rrangle>\<^sub>m) *sqrt(1-\<llangle>b\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m)))"
       using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc calculation(6) help4[of ?a ?b] 
       using calculation(8) by auto
       
     ultimately show ?thesis 
       by simp
   qed
   moreover have "(gamma_factor ((cor (\<llangle>a\<rrangle>\<^sub>m))))*(gamma_factor ((cor (\<llangle>b\<rrangle>\<^sub>m))))*(1+ \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m)
        \<ge> (gamma_factor (Rep_PoincareDisc a))*(gamma_factor (Rep_PoincareDisc b)) * (cmod (1  + (cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b)))"
   proof-
     have "gamma_factor((cor (\<llangle>a\<rrangle>\<^sub>m))) = gamma_factor (Rep_PoincareDisc a)"
       by (simp add: Moebius_gyrodom'.gyronorm_def gamma_factor_def)
     moreover have "gamma_factor((cor (\<llangle>b\<rrangle>\<^sub>m))) = gamma_factor (Rep_PoincareDisc b)"
       by (simp add: Moebius_gyrodom'.gyronorm_def gamma_factor_def)
     moreover have "cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))
                \<le> cmod(1) + cmod((cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))"
       using norm_triangle_ineq by blast
     moreover have "cmod(1) + cmod((cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))
          = cmod(1) +  cmod((cnj (Rep_PoincareDisc a))) * cmod(Rep_PoincareDisc b)"
       by (simp add: norm_mult)
     moreover have "cmod(1) +  cmod((cnj (Rep_PoincareDisc a))) * cmod(Rep_PoincareDisc b) =
        1+ cmod(Rep_PoincareDisc a)*cmod(Rep_PoincareDisc b)"
       by simp
     moreover have "(1+ cmod(Rep_PoincareDisc a)*cmod(Rep_PoincareDisc b))\<ge> cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b))"
       using calculation(3) calculation(4) by auto
     moreover have "(1+ cmod(Rep_PoincareDisc a)*cmod(Rep_PoincareDisc b)) = (1+ \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m)"
       using Moebius_gyrodom'.gyronorm_def by force
     moreover have "(gamma_factor ((cor (\<llangle>a\<rrangle>\<^sub>m))))*(gamma_factor ((cor (\<llangle>b\<rrangle>\<^sub>m))))*(1+ \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m)
    =  gamma_factor (Rep_PoincareDisc a)* gamma_factor (Rep_PoincareDisc b) *(1+ \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m) "
       by (simp add: calculation(1) calculation(2))
     moreover have "gamma_factor (Rep_PoincareDisc a)* gamma_factor (Rep_PoincareDisc b) *(1+ \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m) \<ge>
       gamma_factor (Rep_PoincareDisc a)* gamma_factor (Rep_PoincareDisc b) *cmod(1+(cnj (Rep_PoincareDisc a))*(Rep_PoincareDisc b)) "
      
       using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc calculation(6) gamma_factor_positive_always by auto
     
     ultimately show ?thesis 
       by presburger
   qed
   ultimately show ?thesis 
     using gamma_factor_eq1 by presburger
 qed

lemma gamma_factor_increase_revert:
  fixes t1::real
  fixes t2::real
  assumes "t1<1" "t2\<ge>0" "t2<1" "t1\<ge>0" "gamma_factor t1 > gamma_factor t2"
  shows "t1>t2"
  by (smt (verit, best) assms(3) assms(4) assms(5) gamma_factor_increase)


lemma moebius_triangle:
  shows "(\<llangle>  a  \<oplus>\<^sub>m b \<rrangle>\<^sub>m ) \<le> cmod (Rep_PoincareDisc ((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>m)))  \<oplus>\<^sub>m (Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>m))) ))"
proof-
  have "(Rep_PoincareDisc a)=-(Rep_PoincareDisc b) \<or>
    (Rep_PoincareDisc a)\<noteq> -(Rep_PoincareDisc b) " 
    by blast
  moreover {
    assume "(Rep_PoincareDisc a)=-(Rep_PoincareDisc b) "
    have ?thesis 
      by (simp add: Moebius_gyrodom'.gyronorm_def \<open>Rep_PoincareDisc a = - Rep_PoincareDisc b\<close> m_oplus'_def m_oplus.rep_eq)
  }
  moreover {
    assume " (Rep_PoincareDisc a)\<noteq> -(Rep_PoincareDisc b) "
    let ?iz1 = "(\<llangle>  a  \<oplus>\<^sub>m b \<rrangle>\<^sub>m) "
    let ?iz2 = "cmod (Rep_PoincareDisc ((Abs_PoincareDisc (cor (\<llangle>a\<rrangle>\<^sub>m)))  \<oplus>\<^sub>m (Abs_PoincareDisc (cor (\<llangle>b\<rrangle>\<^sub>m))) ))"
    have "?iz1 >0"
      by (smt (verit, best) Moebius_gyrodom'.gyronorm_def \<open>Rep_PoincareDisc a \<noteq> - Rep_PoincareDisc b\<close> ab_left_minus add_right_cancel divide_eq_0_iff gamma_factor_eq1 gamma_factor_positive_always m_oplus'_def m_oplus.rep_eq norm_eq_zero norm_le_zero_iff of_real_0 zero_less_mult_iff)
    moreover have "?iz2>0"
      by (smt (z3) Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.to_dom Moebius_gyrodom.norm_zero Re_complex_of_real Rep_PoincareDisc add_diff_cancel_left' calculation diff_0 divide_eq_0_iff gamma_factor_eq1 gamma_factor_positive_always m_oplus'_def m_oplus.rep_eq mem_Collect_eq norm_of_real of_real_minus zero_less_mult_iff zero_less_norm_iff)
    moreover have "?iz1<1"
      using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc by auto
    moreover have "?iz2<1"
      using Rep_PoincareDisc by auto
    ultimately have ?thesis 
      using gamma_factor_increase_revert[of ?iz1 ?iz2]
      by (smt (verit, best) gamma_factor_def gamma_factor_increase gamma_factor_ineq1 norm_of_real)
  } ultimately show ?thesis by blast  
qed

lemma mobius_gyroauto_norm:
  shows "\<llangle> m_gyr a b v\<rrangle>\<^sub>m = \<llangle>v\<rrangle>\<^sub>m"
  using Moebius_gyrodom.norm_gyr gyr_PoincareDisc_def by auto

lemma moebius_homogenity:
  shows "\<llangle>(r  \<otimes>\<^sub>m a)\<rrangle>\<^sub>m =  (cmod (Rep_PoincareDisc ((abs r)  \<otimes>\<^sub>m ( Abs_PoincareDisc (cor(\<llangle>a\<rrangle>\<^sub>m))))))"
proof-
  have "\<llangle>(r  \<otimes>\<^sub>m a)\<rrangle>\<^sub>m = abs(tanh(r*artanh(\<llangle>a\<rrangle>\<^sub>m)))"
    using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc cmod_m_otimes' m_otimes'_k_tanh m_otimes.rep_eq by force
  moreover have "a=0\<^sub>m \<or> a\<noteq>0\<^sub>m" by blast
  moreover {
    assume "a=0\<^sub>m"
    have ?thesis 
      using Moebius_gyrodom'.gyronorm_def \<open>a = 0\<^sub>m\<close> m_otimes'_def m_otimes.rep_eq m_ozero'_def m_ozero.rep_eq m_ozero_def by force
  }
  moreover {
    assume "a\<noteq>0\<^sub>m"
    have "( Rep_PoincareDisc ((abs r)  \<otimes>\<^sub>m ( Abs_PoincareDisc (cor(\<llangle>a\<rrangle>\<^sub>m))))) =
          (tanh(abs(r) * artanh(\<llangle>a\<rrangle>\<^sub>m)))"
    proof-
      have "cmod(cmod(Rep_PoincareDisc a)) = cmod(Rep_PoincareDisc a)"
        by simp
      let ?iz1 = "abs(r)"
      let ?iz2 = "\<llangle>a\<rrangle>\<^sub>m"
      have "Rep_PoincareDisc ((abs r)  \<otimes>\<^sub>m ( Abs_PoincareDisc (cor(\<llangle>a\<rrangle>\<^sub>m)))) = cor (m_otimes'_k \<bar>r\<bar> (cor (\<llangle>a\<rrangle>\<^sub>m))) * (cor (\<llangle>a\<rrangle>\<^sub>m) / cor (cmod (cor (\<llangle>a\<rrangle>\<^sub>m))))
" using m_otimes_def m_otimes'_def[of ?iz1 ?iz2]
        using Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.to_dom Rep_PoincareDisc m_otimes.rep_eq by force
      moreover have "(cor (\<llangle>a\<rrangle>\<^sub>m) / cor (cmod (cor (\<llangle>a\<rrangle>\<^sub>m)))) = 1"
        by (metis Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.of_dom \<open>a \<noteq> 0\<^sub>m\<close> \<open>cmod (cor (cmod (Rep_PoincareDisc a))) = cmod (Rep_PoincareDisc a)\<close> divide_self_if m_ozero'_def m_ozero_def norm_eq_zero)
      moreover have "Rep_PoincareDisc ((abs r)  \<otimes>\<^sub>m ( Abs_PoincareDisc (cor(\<llangle>a\<rrangle>\<^sub>m)))) = cor (m_otimes'_k \<bar>r\<bar> (cor (\<llangle>a\<rrangle>\<^sub>m)))"
        using calculation(1) calculation(2) by auto
      ultimately show ?thesis
        using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc m_otimes'_k_tanh by auto
    qed
    moreover have "abs(tanh(r* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m) =  (tanh(\<bar>r\<bar>* artanh (cmod (Rep_PoincareDisc a)))/ \<llangle>a\<rrangle>\<^sub>m )"
    by (metis Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_divide abs_le_self_iff abs_mult_pos abs_norm_cancel artanh_help dual_order.refl mem_Collect_eq  tanh_real_abs)
    ultimately have ?thesis 
      by (smt (verit, best) \<open>\<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m = \<bar>tanh (r * artanh (\<llangle>a\<rrangle>\<^sub>m))\<bar>\<close> norm_of_real real_compex_cmod tanh_real_abs)
  }
  ultimately show ?thesis by blast
qed

lemma m_gyr_gyrospace:
  shows "m_gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) = id"
  using m_gyr_def m_gyr'_def
proof-
  have "m_gyr' (Rep_PoincareDisc (r1 \<otimes>\<^sub>m v)) (Rep_PoincareDisc (r2 \<otimes>\<^sub>m v)) = id"
  proof-
    have "Rep_PoincareDisc (r1 \<otimes>\<^sub>m v) =  cor (tanh(r1*artanh(cmod(Rep_PoincareDisc v))))*(Rep_PoincareDisc v)/cmod(Rep_PoincareDisc v)"
      using Rep_PoincareDisc m_otimes'_def m_otimes'_k_tanh m_otimes.rep_eq by auto
    moreover have "Rep_PoincareDisc (r2 \<otimes>\<^sub>m v) =  cor (tanh(r2*artanh(cmod(Rep_PoincareDisc v))))*(Rep_PoincareDisc v)/cmod(Rep_PoincareDisc v)"  
      using Rep_PoincareDisc m_otimes'_def m_otimes'_k_tanh m_otimes.rep_eq by auto
    
    moreover have "cor (tanh(r1*artanh(cmod(Rep_PoincareDisc v))))*(Rep_PoincareDisc v)/cmod(Rep_PoincareDisc v) =(Rep_PoincareDisc v)*cor (tanh(r1*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v)"
      by simp

    moreover have "cor (tanh(r2*artanh(cmod(Rep_PoincareDisc v))))*(Rep_PoincareDisc v)/cmod(Rep_PoincareDisc v) =(Rep_PoincareDisc v)*cor (tanh(r2*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v)"
      by simp
    moreover have " cnj((Rep_PoincareDisc v)*cor (tanh(r1*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v)) 
         = cnj(Rep_PoincareDisc v)* cnj(cor (tanh(r1*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v))"
        by auto
     moreover have " cnj((Rep_PoincareDisc v)*cor (tanh(r1*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v)) 
         = cnj(Rep_PoincareDisc v)* (cor (tanh(r1*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v))"
       by simp
   moreover have " cnj((Rep_PoincareDisc v)*cor (tanh(r2*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v)) 
         = cnj(Rep_PoincareDisc v)* cnj(cor (tanh(r2*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v))"
        by auto
     moreover have " cnj((Rep_PoincareDisc v)*cor (tanh(r2*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v)) 
         = cnj(Rep_PoincareDisc v)* (cor (tanh(r2*artanh(cmod(Rep_PoincareDisc v))))/cmod(Rep_PoincareDisc v))"
       by simp

     let ?iz1 = "cor (tanh(r1*artanh(cmod(Rep_PoincareDisc v))))*(Rep_PoincareDisc v)/cmod(Rep_PoincareDisc v)"
     let ?iz2 ="cor (tanh(r2*artanh(cmod(Rep_PoincareDisc v))))*(Rep_PoincareDisc v)/cmod(Rep_PoincareDisc v)"
     have "?iz1*(cnj ?iz2) = ?iz2 *(cnj ?iz1)"
       by simp
     moreover have "1+?iz1*(cnj ?iz2) = 1+?iz2*(cnj ?iz1)"
       using calculation(8) by presburger
     moreover have "(1+?iz1*(cnj ?iz2))/(1+?iz2*(cnj ?iz1)) = 1"
       by (metis Rep_PoincareDisc calculation(1) calculation(2) calculation(8) divide_self_if mem_Collect_eq mobius_gyroauto_help3 norm_zero zero_neq_one)
     ultimately show ?thesis 
       using m_gyr_def m_gyr'_def[of ?iz1 ?iz2]
       by (metis eq_id_iff mult.commute mult_1)
   qed
   show ?thesis 
     by (metis (no_types, opaque_lifting) \<open>m_gyr' (Rep_PoincareDisc (r1 \<otimes>\<^sub>m v)) (Rep_PoincareDisc (r2 \<otimes>\<^sub>m v)) = id\<close> add_0_left add_0_right complex_cnj_zero div_by_1 eq_id_iff m_gyr_def m_left_id m_oplus'_def m_oplus_def m_ozero'_def m_ozero.rep_eq map_fun_apply mult_zero_left)
 qed

lemma help8:
  assumes "cmod(u)<1" "cmod(v)<1"
  shows "cmod((1+ (cnj u)*( v))/(1+u*(cnj v))) = 1"
proof-
  have "cmod((1+ (cnj u)*( v))/(1+u*(cnj v))) = cmod((1+ (cnj u)*( v)))/cmod(1+u*(cnj v))"
    using norm_divide by auto
  moreover have "((1+(cnj u)*v) * (cnj (1+(cnj u)*v))) = (1+(cnj u)*v) * ((cnj 1) + (u)*(cnj v))"
    by simp
  moreover have "((1+u*(cnj v))*(cnj (1+u*(cnj v)))) = (1+u*(cnj v)) * ((cnj 1) + (cnj u)*v)"
    by simp
  moreover have "((1+(cnj u)*v) * (cnj (1+(cnj u)*v))) = ((1+u*(cnj v))*(cnj (1+u*(cnj v))))"
    by simp
  moreover have "cmod(((1+u*(cnj v)))) * cmod(((1+u*(cnj v)))) =
        cmod(((1+(cnj u)*v)))*cmod(((1+(cnj u)*v))) "
    by (metis calculation(2) calculation(3) complex_cnj_one complex_mod_cnj mult_cancel_left)
  moreover have "cmod(((1+u*(cnj v)))) =  cmod(((1+(cnj u)*v)))"
    by (metis abs_norm_cancel calculation(5) real_sqrt_abs2)
  moreover have "cmod(((1+u*(cnj v)))) /cmod(((1+(cnj u)*v))) =1"
    by (simp add: assms(1) assms(2) calculation(6) den_not_zero)
  ultimately show ?thesis
    by presburger
qed

lemma m_gyr_gyrospace2:
  shows "m_gyr u v ( r  \<otimes>\<^sub>m a) = r  \<otimes>\<^sub>m (m_gyr u v a)"
  using m_otimes'_def m_otimes'_k_def
proof-
  have "m_gyr u v a=Abs_PoincareDisc (((1+ (Rep_PoincareDisc u)*(cnj (Rep_PoincareDisc v)))/
  (1+(cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v))) * (Rep_PoincareDisc a))"
    by (metis Moebius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
  moreover have "cmod (Rep_PoincareDisc (m_gyr u v a)) = cmod ((((1+ (Rep_PoincareDisc u)*(cnj (Rep_PoincareDisc v)))/
  (1+(cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v))))) * cmod(Rep_PoincareDisc a)"
    by (metis m_gyr'_def m_gyr.rep_eq norm_mult)
  moreover have "cmod (Rep_PoincareDisc (m_gyr u v a)) = cmod(Rep_PoincareDisc a)"
    by (metis Rep_PoincareDisc calculation(2) mem_Collect_eq mobius_gyroauto_help3 mult.commute mult_1)
  let ?iz1 = "cmod((Rep_PoincareDisc (m_gyr u v a)))"
  let ?iz2 = " (m_gyr u v a) "
  have "r  \<otimes>\<^sub>m (m_gyr u v a) = (Abs_PoincareDisc ((cor((1+?iz1)powr r- (1-?iz1)powr r)/
      ((1+?iz1)powr r + (1-?iz1)powr r)) * ((Rep_PoincareDisc (m_gyr u v a)))/(cor (cmod(Rep_PoincareDisc (m_gyr u v a))))))"
    using m_otimes_def 
    by (metis (no_types, lifting) Moebius_gyrodom'.of_dom m_otimes'_def m_otimes'_k_def m_otimes.rep_eq mult_eq_0_iff of_real_divide times_divide_eq_right)
  moreover have "r  \<otimes>\<^sub>m (m_gyr u v a) = (Abs_PoincareDisc ((cor((1+cmod(Rep_PoincareDisc a))powr r- (1-cmod(Rep_PoincareDisc a))powr r)/
      ((1+cmod(Rep_PoincareDisc a))powr r + (1-cmod(Rep_PoincareDisc a))powr r)) *
 ((Rep_PoincareDisc (m_gyr u v a)))/(cor (cmod(Rep_PoincareDisc a)))))"
    using \<open>cmod (Rep_PoincareDisc (m_gyr u v a)) = cmod (Rep_PoincareDisc a)\<close> calculation(3) by presburger
  moreover have "r  \<otimes>\<^sub>m (m_gyr u v a) = Abs_PoincareDisc ((Rep_PoincareDisc (r  \<otimes>\<^sub>m a)) * 
    (((1+ (Rep_PoincareDisc u)*(cnj (Rep_PoincareDisc v)))/
  (1+(cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v)))))"
    using m_otimes_def
    by (smt (verit, ccfv_threshold) Moebius_gyrodom'.of_dom \<open>cmod (Rep_PoincareDisc (m_gyr u v a)) = cmod (Rep_PoincareDisc a)\<close> ab_semigroup_mult_class.mult_ac(1) m_gyr'_def m_gyr.rep_eq m_otimes'_def m_otimes'_k_def m_otimes.rep_eq mult.commute mult_eq_0_iff times_divide_eq_right)
  ultimately show ?thesis 
    by (metis Moebius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq mult.commute)
qed

definition m_gyroplus_r :: "real \<Rightarrow> real \<Rightarrow> real" (infixl "\<oplus>\<^sub>m\<^sub>r" 100) where 
  "r1 \<oplus>\<^sub>m\<^sub>r r2 = (r1 + r2) / (1 + r1*r2)"

interpretation Moebious_gyrovector_space: gyrovector_space Abs_PoincareDisc "\<lambda> z. cmod z < 1" Rep_PoincareDisc m_otimes (*m_gyroplus_r *)
"(Abs_PoincareDisc \<circ> cor)" "(cmod \<circ> Rep_PoincareDisc)"
proof
  fix a :: PoincareDisc
  show "1 \<otimes>\<^sub>m a = a"
    by transfer (auto simp add: m_otimes'_def m_otimes'_k_def)
next
  fix r1 r2 a
  show "(r1 + r2) \<otimes>\<^sub>m a = r1 \<otimes>\<^sub>m a \<oplus> r2 \<otimes>\<^sub>m a"
    using gyroplus_PoincareDisc_def m_otimes_distrib by auto
next
  fix r1 r2 a
  show "(r1 * r2) \<otimes>\<^sub>m a = r1 \<otimes>\<^sub>m (r2 \<otimes>\<^sub>m a)"
    by (simp add: m_otimes_assoc)
next
  fix r a
  show "r\<noteq>0 \<longrightarrow>(Rep_PoincareDisc (abs r \<otimes>\<^sub>m a) /\<^sub>R gyrodom'.gyronorm Rep_PoincareDisc (r \<otimes>\<^sub>m a)) =
         ((Rep_PoincareDisc a) /\<^sub>R  (gyrodom'.gyronorm Rep_PoincareDisc a))"
    using mobius_scale_prop[of r a]
    by (metis Moebius_gyrodom'.gyrodom'_axioms Moebius_gyrodom'.gyronorm_def divide_inverse_commute gyrodom'.gyronorm_def of_real_inverse scaleR_conv_of_real)
next
  fix u v r a
  have "m_gyr u v (r \<otimes>\<^sub>m a) = r \<otimes>\<^sub>m m_gyr u v a"
    using m_gyr_gyrospace2 
    by auto
  then show "gyr u v (r \<otimes>\<^sub>m a) = r \<otimes>\<^sub>m gyr u v a"
    using gyr_PoincareDisc_def by auto
next
  fix r1 r2 v
  have "m_gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) = id"
    using m_gyr_gyrospace
    by simp
  then show "gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) = id"
    by (simp add: gyr_PoincareDisc_def)
next
  fix r a
  show " gyrodom'.gyronorm Rep_PoincareDisc (r \<otimes>\<^sub>m a) =
           (cmod \<circ> Rep_PoincareDisc)
            (\<bar>r\<bar> \<otimes>\<^sub>m (Abs_PoincareDisc \<circ> cor) (gyrodom'.gyronorm Rep_PoincareDisc a))"
    using moebius_homogenity[of r a]
    using Moebius_gyrodom'.gyrodom'_axioms Moebius_gyrodom'.gyronorm_def gyrodom'.gyronorm_def by fastforce   
next
  fix a b
  show " gyrodom'.gyronorm Rep_PoincareDisc (a \<oplus> b)
           \<le> (cmod \<circ> Rep_PoincareDisc)
               ((Abs_PoincareDisc \<circ> cor) (gyrodom'.gyronorm Rep_PoincareDisc a) \<oplus>
                (Abs_PoincareDisc \<circ> cor) (gyrodom'.gyronorm Rep_PoincareDisc b))"
    using moebius_triangle[of a b]
    using Moebius_gyrodom'.gyrodom'_axioms Moebius_gyrodom'.gyronorm_def gyrodom'.gyronorm_def gyroplus_PoincareDisc_def by fastforce 
qed

definition m_gyr_general::"PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
    "m_gyr_general u v w = \<ominus>\<^sub>m(u\<oplus>\<^sub>mv)\<oplus>\<^sub>m(u \<oplus>\<^sub>m(v \<oplus>\<^sub>m w))"

lemma m_gyr_general_same_m_gyr:
  shows "m_gyr_general u v w = m_gyr u v w"
  by (simp add: Moebius_gyrogroup.gyr_def m_gyr_general_def)

definition m_plus_full::"complex\<Rightarrow>complex \<Rightarrow>complex" where 
    "m_plus_full u v = ((1+2*inner u v + (norm v)^2)  *\<^sub>R  u + (1-(norm u)^2) *\<^sub>R v)/
      (1+2*inner u v + (norm u)^2 * (norm v)^2)"

lemma two_inner_cnj:
  shows "2*inner u v = (cnj u)*v + (cnj v)*u"
  by (smt (verit) cnj.simps(1) cnj.simps(2) cnj_add_mult_eq_Re inner_complex_def mult.commute mult_minus_left times_complex.simps(1))

lemma m_plus_full_m_plus:
  shows "(u\<oplus>\<^sub>mv) = Abs_PoincareDisc 
(m_plus_full (Rep_PoincareDisc u) (Rep_PoincareDisc v))"
proof-
  have "2*inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) =(cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v) +
     (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u) "
    using two_inner_cnj by auto
  moreover have "(1+2*inner (Rep_PoincareDisc u) (Rep_PoincareDisc v) + (norm (Rep_PoincareDisc v))^2)
       *(Rep_PoincareDisc u) = (1+ (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v) +
     (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u) + (norm (Rep_PoincareDisc v))^2) 
       * (Rep_PoincareDisc u)"

    using \<open>cor (2 * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) = cnj (Rep_PoincareDisc u) * Rep_PoincareDisc v + cnj (Rep_PoincareDisc v) * Rep_PoincareDisc u\<close> by auto

  moreover have "(1+ 2*(inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) + 
(norm (Rep_PoincareDisc u))^2 * (norm (Rep_PoincareDisc v))^2) = 
      1+ (cnj(Rep_PoincareDisc u))*(Rep_PoincareDisc v) + (cnj(Rep_PoincareDisc v))*(Rep_PoincareDisc u) +
     (norm (Rep_PoincareDisc u))^2  * (norm (Rep_PoincareDisc v))^2 "
    using \<open>cor (2 * inner (Rep_PoincareDisc u) (Rep_PoincareDisc v)) = cnj (Rep_PoincareDisc u) * Rep_PoincareDisc v + cnj (Rep_PoincareDisc v) * Rep_PoincareDisc u\<close> by auto
  moreover have " (1+ (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v) +
     (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u) + (norm (Rep_PoincareDisc v))^2) 
       * (Rep_PoincareDisc u) + (1-(norm (Rep_PoincareDisc u))^2)  *  (Rep_PoincareDisc v) =
      (1+ (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u))*((Rep_PoincareDisc u)+(Rep_PoincareDisc v))"
  proof-
    have *:"(1+ (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v) +
     (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u) + (norm (Rep_PoincareDisc v))^2) 
       * (Rep_PoincareDisc u) = (Rep_PoincareDisc u) + (norm (Rep_PoincareDisc u))^2
    * (Rep_PoincareDisc v) + (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u)^2 + (norm (Rep_PoincareDisc v))^2 * (Rep_PoincareDisc u)"
      by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) comm_semiring_class.distrib complex_norm_square mult.commute mult_cancel_right1 power2_eq_square)
    moreover have  ***:" (1+ (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u))*((Rep_PoincareDisc u)+(Rep_PoincareDisc v)) =
        (Rep_PoincareDisc u) + (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u)*(Rep_PoincareDisc u) +
        (Rep_PoincareDisc v) +  (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u) * (Rep_PoincareDisc v)"
      by (simp add: distrib_left ring_class.ring_distribs(2))
    moreover have "(Rep_PoincareDisc u) + (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v)*(Rep_PoincareDisc u) +
        (Rep_PoincareDisc v) +  (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v) * (Rep_PoincareDisc v) =
        (Rep_PoincareDisc u) +  (cnj (Rep_PoincareDisc u)) * (Rep_PoincareDisc v)^2 +
        (norm (Rep_PoincareDisc u))^2 * (Rep_PoincareDisc v) + (Rep_PoincareDisc v)"
      by (simp add: mobius_gyroauto_help1 mult.commute power2_eq_square)
    moreover have **:"(1-(norm (Rep_PoincareDisc u))^2)  *  (Rep_PoincareDisc v) =
        (Rep_PoincareDisc v) - (norm (Rep_PoincareDisc u))^2 * (Rep_PoincareDisc v)"
      by (simp add: mult.commute right_diff_distrib')
    moreover have " (1+ (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v) +
     (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u) + (norm (Rep_PoincareDisc v))^2) 
       * (Rep_PoincareDisc u) + (1-(norm (Rep_PoincareDisc u))^2)  *  (Rep_PoincareDisc v)  = (Rep_PoincareDisc u) + (norm (Rep_PoincareDisc u))^2
    * (Rep_PoincareDisc v) + (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u)^2 + (norm (Rep_PoincareDisc v))^2 * (Rep_PoincareDisc u) 
    + (Rep_PoincareDisc v) - (norm (Rep_PoincareDisc u))^2 * (Rep_PoincareDisc v)"
      using * **
      by force
    moreover have ****:"(1+ (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v) +
     (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u) + (norm (Rep_PoincareDisc v))^2) 
       * (Rep_PoincareDisc u) + (1-(norm (Rep_PoincareDisc u))^2)  *  (Rep_PoincareDisc v) 
      = (Rep_PoincareDisc u) + (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u)^2 + (norm (Rep_PoincareDisc v))^2 * (Rep_PoincareDisc u) 
    + (Rep_PoincareDisc v)  "
      using "*" "**" by auto
    moreover have "(1+ (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u))*((Rep_PoincareDisc u)+(Rep_PoincareDisc v)) =
        (Rep_PoincareDisc u) + (norm (Rep_PoincareDisc v))^2 *(Rep_PoincareDisc u) +
        (Rep_PoincareDisc v) +  (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u)^2"
      using ***
      by (simp add: mobius_gyroauto_help1 mult.commute power2_eq_square)
    ultimately show ?thesis
      by auto
  qed

  moreover have " 1+ (cnj(Rep_PoincareDisc u))*(Rep_PoincareDisc v) + (cnj(Rep_PoincareDisc v))*(Rep_PoincareDisc u) +
     (norm (Rep_PoincareDisc u))^2  * (norm (Rep_PoincareDisc v))^2  = (1+ (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v))*
    (1+(cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u))"
  proof-
    have "(1+ (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v))*
    (1+(cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u)) = 1+ (cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v)
      + (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u) + (cnj (Rep_PoincareDisc v))*(Rep_PoincareDisc u)*(cnj (Rep_PoincareDisc u))*(Rep_PoincareDisc v)"
   
      by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) add.assoc mult.commute mult_cancel_right1 ring_class.ring_distribs(2))
    then show ?thesis
      by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) complex_cnj_mult mobius_gyroauto_help1 mult.commute norm_mult power_mult_distrib) 
  qed
  
  ultimately show ?thesis 
    using m_oplus_def m_oplus'_def
    by (metis (no_types, lifting) Rep_PoincareDisc Rep_PoincareDisc_inverse den_not_zero divide_divide_eq_left' m_oplus.rep_eq m_plus_full_def mem_Collect_eq nonzero_mult_div_cancel_left scaleR_conv_of_real)
qed


end