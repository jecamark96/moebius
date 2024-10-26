theory MobiusGyroGroup
  imports Complex_Main HOL.Real_Vector_Spaces HOL.Transcendental
          GyroGroup GyroVectorSpace GammaFactor 
begin

lemmas div_help = nonzero_divide_mult_cancel_left

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

(* ------------------------------------------------------------------ *)


typedef PoincareDisc = "{z::complex. cmod z < 1}"
  by (rule_tac x=0 in exI, auto)

setup_lifting type_definition_PoincareDisc

abbreviation to_complex :: "PoincareDisc \<Rightarrow> complex" where 
  "to_complex \<equiv> Rep_PoincareDisc" 
abbreviation of_complex :: "complex \<Rightarrow> PoincareDisc" where 
  "of_complex \<equiv> Abs_PoincareDisc" 

definition m_inner' :: "complex \<Rightarrow> complex \<Rightarrow> real" where
  "m_inner' z1 z2 = Re z1 * Re z2 + Im z1 * Im z2"

lemma m_inner'_def1: 
  shows "m_inner' z1 z2 = (z1 * cnj z2 + z2 * cnj z1) / 2"
proof-
  obtain "a" "b" where ab: "Re z1 = a \<and> Im z1 = b"
    by blast
  obtain "c" "d" where cd: "Re z2 = c \<and> Im z2 = d"
    by blast
  have "Re (z1 * cnj z2) = a*c + b*d" "Re (z2 * cnj z1) = a*c + b*d"
       "Im (z1 * cnj z2) = b*c - a*d" "Im (z2 * cnj z1) = -b*c + a*d"
    using ab cd
    by simp+
  then have "(z1 * cnj z2 + z2 * cnj z1) / 2 =  a*c + b*d"
    using complex_eq_iff by force
  then show ?thesis
    using ab cd m_inner'_def
    by presburger
qed

lemma m_inner'_def2:
  shows "m_inner' z1 z2 = Re (cnj z1 * z2)"
  by (simp add: m_inner'_def)

lemma m_inner'_def3:
  shows "m_inner' z1 z2 = inner z1 z2"
  by (simp add: inner_complex_def m_inner'_def)

lift_definition m_inner :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> real" (infixl "\<cdot>\<^sub>m" 100) is inner
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


interpretation Moebius_gyrodom': gyrodom' where
  to_dom = to_complex and
  of_dom = of_complex and
  in_dom = "\<lambda> z. cmod z < 1" 
rewrites
  "Moebius_gyrodom'.gyroinner = m_inner" and
  "Moebius_gyrodom'.gyronorm = m_norm"
proof-
  show *: "gyrodom' to_complex of_complex (\<lambda>z. cmod z < 1)"
  proof
    fix b
    assume "cmod b < 1"
    then show "to_complex (of_complex b) = b"
      by (simp add: Abs_PoincareDisc_inverse)
  next
    fix a
    show "of_complex (to_complex a) = a"
      by (simp add: Rep_PoincareDisc_inverse)
  next
    show "to_complex 0\<^sub>g = 0"
      by (simp add: gyrozero_PoincareDisc_def m_ozero'_def m_ozero.rep_eq)
  qed

  show "gyrodom'.gyroinner to_complex = (\<cdot>\<^sub>m)"
    apply rule
    apply rule
    unfolding gyrodom'.gyroinner_def[OF *]
    apply transfer
    by (simp add: inner_complex_def m_inner'_def)

  show "gyrodom'.gyronorm to_complex = m_norm"
    apply rule
    unfolding gyrodom'.gyronorm_def[OF *]
    apply transfer
    by (simp add: m_norm'_def)
qed

lemma mobius_gyroauto:
  shows "m_gyr u v a \<cdot>\<^sub>m m_gyr u v b = a \<cdot>\<^sub>m b"
proof-
  have "m_gyr u v a \<cdot>\<^sub>m m_gyr u v b = Re((cnj (to_complex (m_gyr u v a))) * (to_complex (m_gyr u v b)))"
    using m_inner.rep_eq
    by (simp add: inner_complex_def)
  moreover have "m_gyr u v a = of_complex(((1 + (to_complex u) * cnj (to_complex v)) / (1 + (cnj (to_complex u)) * to_complex v)) *
    (to_complex a))"
    by (metis Moebius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
  moreover have "m_gyr u v b = of_complex(((1 + (to_complex u) * cnj (to_complex v)) / (1 + (cnj (to_complex u)) * to_complex v)) *
    (to_complex b))"
    by (metis Moebius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
  moreover have "(cnj (to_complex (m_gyr u v a))) = cnj ((1 + (to_complex u) * cnj (to_complex v)) / (1 + (cnj (to_complex u)) * to_complex v)) *
    cnj (to_complex a)"
    by (simp add: m_gyr'_def m_gyr.rep_eq)
  moreover have " (cnj ((1 + (to_complex u) * cnj (to_complex v)) / (1 + (to_complex v)*(cnj (to_complex u))) ))*  ((1 + (to_complex u) * cnj (to_complex v)) / (1 + (to_complex v)*(cnj (to_complex u)))) = 1"
  proof-
    have *: "cmod (to_complex u) < 1"
      using Rep_PoincareDisc by blast
    moreover have **:"cmod (to_complex v) < 1"
      using Rep_PoincareDisc by blast
    moreover have "cmod (((1 + (to_complex u) * cnj (to_complex v)) / (1 +  (to_complex v)*(cnj (to_complex u))))) =1"
      using  mobius_gyroauto_help[OF * **] 
      by force
    ultimately show ?thesis using cnj_cmod_1
      by (metis mult.commute)
  qed
  moreover have "m_gyr u v a \<cdot>\<^sub>m m_gyr u v b = Re((cnj (to_complex a))*(to_complex b))"
    using calculation(1) calculation(5) m_gyr'_def m_gyr.rep_eq by force
  moreover have "a \<cdot>\<^sub>m b = Re((cnj (to_complex a))*(to_complex b))"
    by (simp add: inner_complex_def m_inner.rep_eq)
  ultimately show ?thesis
    by presburger
qed

(* --------------------------------------------------------- *)
interpretation Moebius_gyrodom: gyrodom to_complex of_complex "\<lambda> z. cmod z < 1"
proof
  fix u v a b
  have "gyr u v a \<cdot>\<^sub>m gyr u v b = a \<cdot>\<^sub>m b"
    by (simp add: gyr_PoincareDisc_def mobius_gyroauto)
  then show "gyrodom'.gyroinner to_complex (gyr u v a) (gyr u v b) =
             gyrodom'.gyroinner to_complex a b"  
    using Moebius_gyrodom'.gyrodom'_axioms Moebius_gyrodom'.gyroinner_def gyrodom'.gyroinner_def by fastforce
qed


(* --------------------------------------------------------- *)
  
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
  "m_otimes' r z = (if z = 0 then 0 else cor (m_otimes'_k r z) * (z / cmod z))"

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

lemma mobius_scale_prop:
  fixes r :: real
  assumes "r \<noteq> 0"
  shows "to_complex (\<bar>r\<bar> \<otimes>\<^sub>m a) / \<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m  = to_complex a / \<llangle>a\<rrangle>\<^sub>m"
proof-
  let ?f = "\<lambda> r a. tanh (r * artanh (cmod (to_complex a)))"

  have *: "to_complex (\<bar>r\<bar> \<otimes>\<^sub>m a) = ?f \<bar>r\<bar> a * (to_complex a / \<llangle>a\<rrangle>\<^sub>m)"
    using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc m_otimes'_def m_otimes'_k_tanh m_otimes.rep_eq
    by force
  then have "\<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m = cmod (?f r a * (to_complex a / \<llangle>a\<rrangle>\<^sub>m))"
    by (metis (no_types, lifting) Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc cmod_m_otimes' m_otimes'_def m_otimes'_k_tanh m_otimes.rep_eq mem_Collect_eq norm_mult norm_of_real)
  then have "\<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m = \<bar>?f r a / \<llangle>a\<rrangle>\<^sub>m\<bar> * cmod (to_complex a)"
    by (metis (no_types, opaque_lifting) norm_mult norm_of_real of_real_divide times_divide_eq_left times_divide_eq_right)

  have "?f \<bar>r\<bar> a = tanh(\<bar>r\<bar> * \<bar>artanh (cmod (to_complex a))\<bar>)"
    by (smt (verit) Rep_PoincareDisc artanh_nonneg mem_Collect_eq norm_ge_zero)
  then have "?f \<bar>r\<bar> a = \<bar>?f r a\<bar>"
    by (metis abs_mult tanh_real_abs)

  have "\<bar>?f r a / \<llangle>a\<rrangle>\<^sub>m\<bar> = ?f \<bar>r\<bar> a / \<llangle>a\<rrangle>\<^sub>m"
    by (metis Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_divide abs_le_self_iff abs_mult_pos abs_norm_cancel artanh_nonneg dual_order.refl mem_Collect_eq  tanh_real_abs)
  then have **:"?f \<bar>r\<bar> a / \<llangle>a\<rrangle>\<^sub>m = \<bar>?f r a / \<llangle>a\<rrangle>\<^sub>m\<bar>"
    by simp

  show ?thesis
  proof (cases "to_complex a = 0")
    case True
    then show ?thesis
      using assms
      by (simp add: m_otimes'_def m_otimes.rep_eq)
  next
    case False
    then have "\<bar>?f r a / \<llangle>a\<rrangle>\<^sub>m\<bar> \<noteq>0"
      using assms
      by (metis artanh_0 Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_norm_cancel artanh_not_0 artanh_tanh_real divide_eq_0_iff linorder_not_less mem_Collect_eq mult_eq_0_iff norm_eq_zero not_less_iff_gr_or_eq zero_less_abs_iff)
    then show ?thesis
      using * ** Moebius_gyrodom'.gyronorm_def 
            \<open>\<llangle>r \<otimes>\<^sub>m a\<rrangle>\<^sub>m = \<bar>?f r a / \<llangle>a\<rrangle>\<^sub>m\<bar> * cmod (to_complex a)\<close> 
      by fastforce
  qed
qed

lemma gamma_factor_eq1_lemma1:
  shows "cmod(1 + cnj a * b)*cmod(1 + cnj a * b) - cmod(a+b)*cmod(a+b) =
         (1 - cmod a * cmod a) * (1 - cmod b * cmod b)"
proof-
  have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b) * cnj(1+(cnj a)*b)"
    by (metis complex_norm_square power2_eq_square)
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) = (1+(cnj a)*b)*(1+(cnj(cnj a))* (cnj b))"
    using complex_cnj_add complex_cnj_mult complex_cnj_one by presburger
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b)= 1+a*(cnj b)+(cnj a)*b + (cnj a)*b*a*(cnj b)"
    by (simp add: field_simps)
  moreover 
  have "cmod(a+b)*cmod(a+b) = (a+b)*cnj(a+b)"
    by (metis complex_norm_square power2_eq_square)
  then have "cmod(a+b)*cmod(a+b) = a*(cnj a) + a*(cnj b) + b*(cnj a) + b*(cnj b)"
    by (simp add: field_simps)
  then have "cmod(a+b)*cmod(a+b) = cmod(a)*cmod(a) + a*(cnj b) + b*(cnj a) + cmod(b)*cmod(b)"
    by (metis complex_norm_square power2_eq_square)
  ultimately have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = 
    (1+a*(cnj b)+(cnj a)*b + (cnj a)*b*a*(cnj b))-( cmod(a)*cmod(a) + a*(cnj b) + b*(cnj a) + cmod(b)*cmod(b))"
    by auto
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cnj a)*a*(b*(cnj b)) - cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by fastforce
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cmod(a)*cmod(a))*(b*(cnj b))-cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by (metis (mono_tags, opaque_lifting) complex_norm_square mult.assoc mult.left_commute power2_eq_square)
  then have "cmod(1+(cnj a)*b)*cmod(1+(cnj a)*b) - cmod(a+b)*cmod(a+b) = (1+(cmod(a)*cmod(a))*(cmod(b)*cmod(b))-cmod(a)*cmod(a) - cmod(b)*cmod(b))"
    by (smt (verit) Re_complex_of_real cmod_power2 complex_In_mult_cnj_zero complex_mod_cnj complex_mod_mult_cnj diff_add_cancel cnj_cmod norm_mult norm_zero of_real_1 plus_complex.sel(1) times_complex.sel(1))
  moreover
  have "(1-cmod(a)*cmod(a))*(1-cmod(b)*cmod(b)) = 1+(cmod(a)*cmod(a))*(cmod(b)*cmod(b))-cmod(a)*cmod(a)-cmod(b)*cmod(b)"
    by (simp add: field_simps)
  ultimately
  show ?thesis 
    by presburger
qed

lemma gamma_factor_eq1_lemma2:
  fixes x y::real
  assumes "y > 0"  
  shows "1 / sqrt(1 - (x*x)/(y*y)) = abs y / sqrt(y*y - x*x)"
proof-
  have "1 - ((x*x)/(y*y)) = (y*y-x*x) / (y*y)"
    using assms
    by (metis diff_divide_distrib div_0 divide_less_cancel divide_self no_zero_divisors)
  then have "sqrt (1 - (x*x)/(y*y)) = sqrt(y*y-x*x)/sqrt(y*y)"
    using real_sqrt_divide by presburger
  then have "sqrt(1 - (x*x)/(y*y)) = sqrt(y*y-x*x)/abs(y)"
    using real_sqrt_abs2 by presburger
  then show ?thesis
    by auto
qed

lemma gamma_factor_eq1:
  shows "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>\<^sub>m) = 
         \<gamma> (to_complex a) *  
         \<gamma> (to_complex b) * 
         cmod (1 + cnj (to_complex a) * (to_complex b))"
proof-
  let ?a = "to_complex a" and ?b = "to_complex b"
  have "norm (\<llangle>a \<oplus>\<^sub>m b\<rrangle>\<^sub>m) < 1"
    using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_square_less_1
    by fastforce
  then have *: "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>\<^sub>m) = 
                1 / sqrt(1 - cmod (?a+?b) / cmod (1 + cnj ?a *?b) * cmod (?a+?b) / cmod (1 + cnj ?a *?b))"
    using Moebius_gyrodom'.gyronorm_def gamma_factor_def m_oplus'_def m_oplus.rep_eq norm_divide norm_eq_zero norm_le_zero_iff norm_of_real real_norm_def 
    by (smt (verit, del_insts) power2_eq_square times_divide_eq_right)
  also have "\<dots> =  
           cmod(1 + cnj ?a * ?b) /
           sqrt(cmod (1 + cnj ?a * ?b) * cmod (1 + cnj ?a * ?b) -
                cmod (?a+?b) * cmod (?a+?b))"
  proof-
    let ?iz1 = "cmod (?a+?b) * cmod (?a+?b)"
    let ?iz2 = "cmod (1 + cnj ?a * ?b) * cmod (1 + cnj ?a * ?b)"
    have "?iz1 \<ge> 0"
      by force
    moreover
    have "?iz2 > 0"
      using den_not_zero Rep_PoincareDisc
      by auto
    ultimately show ?thesis
      using zero_less_mult_iff
      by (smt (verit, best) divide_divide_eq_left gamma_factor_eq1_lemma2 norm_not_less_zero times_divide_eq_left)
  qed
  also have "\<dots> = cmod(1 + cnj ?a * ?b) / sqrt((1 - cmod ?a * cmod ?a) * (1 - cmod ?b * cmod ?b))"    
    using gamma_factor_eq1_lemma1
    by presburger
  also have "\<dots> =
         \<gamma> (to_complex a) *  
         \<gamma> (to_complex b) * 
         cmod (1 + cnj (to_complex a) * (to_complex b))"
  proof-
    have "cmod (to_complex a) < 1" "cmod (to_complex b) < 1"
      using Rep_PoincareDisc
      by auto
    then show ?thesis
      unfolding gamma_factor_def
      by (simp add: power2_eq_square real_sqrt_mult)
  qed
  finally show ?thesis
    .
qed

lemma gamma_factor_ineq1_lemma:
  fixes x y ::real
  assumes "x \<ge> 0" "x < 1" "y \<ge> 0" "y < 1"
  shows "1 / sqrt (1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y))) = 
         (1+x*y) / (sqrt (1-x*x) * sqrt (1-y*y))"
proof-
  have "1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y)) = ((1+x*y)*(1+x*y) - (x+y)*(x+y)) / ((1+x*y)*(1+x*y))"
    by (smt (verit, ccfv_threshold) add_divide_distrib assms div_self mult_eq_0_iff mult_nonneg_nonneg)
  then have "1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y)) = ((1-x*x)*(1-y*y)) / ((1+x*y)*(1+x*y))"
    by (simp add: field_simps)
  then have "sqrt(1 - ((x+y)*(x+y))/((1+x*y)*(1+x*y))) = 
             (sqrt(1-x*x)*sqrt(1-y*y)) / (sqrt((1+x*y)*(1+x*y)))"
    using assms real_sqrt_divide real_sqrt_mult
    by presburger
  then show ?thesis
    using assms
    by simp
qed

lemma gamma_factor_ineq1:
  shows "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>\<^sub>m) \<le> \<gamma> (to_complex ((of_complex (\<llangle>a\<rrangle>\<^sub>m)) \<oplus>\<^sub>m (of_complex (\<llangle>b\<rrangle>\<^sub>m))))"
proof-
  have "\<gamma> (to_complex ((of_complex (\<llangle>a\<rrangle>\<^sub>m)) \<oplus>\<^sub>m (of_complex (\<llangle>b\<rrangle>\<^sub>m)))) =
        \<gamma> (\<llangle>a\<rrangle>\<^sub>m) * \<gamma> (\<llangle>b\<rrangle>\<^sub>m) * (1 + \<llangle>a\<rrangle>\<^sub>m * \<llangle>b\<rrangle>\<^sub>m)"
  proof-
    let ?expr1 =  "((\<llangle>a\<rrangle>\<^sub>m) + (\<llangle>b\<rrangle>\<^sub>m)) / (1 + (\<llangle>a\<rrangle>\<^sub>m)*(\<llangle>b\<rrangle>\<^sub>m))"
    let ?expr2 = "to_complex (of_complex (\<llangle>a\<rrangle>\<^sub>m) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>\<^sub>m))"
    have *: "?expr1 = ?expr2"
      using Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.to_dom Rep_PoincareDisc m_oplus'_def m_oplus.rep_eq
      by auto

    have **: "norm (\<llangle>a\<rrangle>\<^sub>m) < 1" "norm (\<llangle>b\<rrangle>\<^sub>m) < 1"
      using Rep_PoincareDisc abs_square_less_1 m_norm'_def m_norm.rep_eq 
      by fastforce+
    then have ***: "\<gamma> (\<llangle>a\<rrangle>\<^sub>m) = 1 / sqrt(1 - (\<llangle>a\<rrangle>\<^sub>m) * (\<llangle>a\<rrangle>\<^sub>m))"
                   "\<gamma> (\<llangle>b\<rrangle>\<^sub>m) = 1 / sqrt(1 - (\<llangle>b\<rrangle>\<^sub>m) * (\<llangle>b\<rrangle>\<^sub>m))"
      unfolding gamma_factor_def
      by (auto simp add: power2_eq_square) 

    have "\<gamma> ?expr1 = 1 / sqrt(1 - ((cmod (?expr1)) * cmod(?expr1)))"
      using * **
      by (metis Rep_PoincareDisc gamma_factor_def mem_Collect_eq power2_eq_square)
    moreover
    have "cmod ?expr1 = ?expr1"
      by (smt (verit, ccfv_threshold) Moebius_gyrodom'.gyronorm_def mult_less_0_iff norm_divide norm_not_less_zero norm_of_real of_real_1 of_real_add of_real_divide of_real_mult)
    ultimately
    have "\<gamma> ?expr1 = 1 / sqrt (1 - (Re ?expr1 * Re ?expr1))"
       by (metis Re_complex_of_real)
    then have "\<gamma> ?expr1 = (1 + \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m) / (sqrt (1-\<llangle>a\<rrangle>\<^sub>m*\<llangle>a\<rrangle>\<^sub>m) * sqrt (1-\<llangle>b\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m))"
       using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc gamma_factor_ineq1_lemma
       using \<open>cmod ?expr1 = ?expr1\<close> 
       by force

    then show ?thesis
      using \<open>?expr1 = ?expr2\<close> ***
      by simp
  qed

  moreover

  have "\<gamma> (\<llangle>a\<rrangle>\<^sub>m) * \<gamma> (\<llangle>b\<rrangle>\<^sub>m) * (1 + \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m) \<ge> 
        \<gamma> (to_complex a) * \<gamma> (to_complex b) * cmod (1  + cnj (to_complex a) * (to_complex b))"
  proof-
    have *: "\<gamma> (\<llangle>a\<rrangle>\<^sub>m) = \<gamma> (to_complex a)"
            "\<gamma> (\<llangle>b\<rrangle>\<^sub>m) = \<gamma> (to_complex b)"
       by (auto simp add: Moebius_gyrodom'.gyronorm_def gamma_factor_def)
     
     have "cmod (1 + cnj (to_complex a) * (to_complex b)) \<le> 
           cmod 1 + cmod (cnj (to_complex a) * (to_complex b))"
       using norm_triangle_ineq
       by blast
     also have "\<dots> = 1 + cmod (to_complex a) * cmod (to_complex b)"
       by (simp add: norm_mult)
     also have "\<dots> = 1 + \<llangle>a\<rrangle>\<^sub>m*\<llangle>b\<rrangle>\<^sub>m"
       using Moebius_gyrodom'.gyronorm_def
       by force
     finally show ?thesis
       using *
       by (smt (verit, best) gamma_factor_def gamma_factor_positive mult_eq_0_iff mult_le_cancel_left_pos mult_sign_intros(5) power_less_one_iff)
   qed

   ultimately show ?thesis 
     using gamma_factor_eq1
     by presburger
qed

lemma moebius_triangle:
  shows "(\<llangle>a \<oplus>\<^sub>m b\<rrangle>\<^sub>m) \<le> cmod (to_complex (of_complex (\<llangle>a\<rrangle>\<^sub>m) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>\<^sub>m)))"
proof (cases "to_complex a = - to_complex b")
  case True
  then show ?thesis
   by (simp add: Moebius_gyrodom'.gyronorm_def m_oplus'_def m_oplus.rep_eq)
next
  case False
  let ?e1 = "(\<llangle>a \<oplus>\<^sub>m b\<rrangle>\<^sub>m)"
  let ?e2 = "cmod (to_complex (of_complex (\<llangle>a\<rrangle>\<^sub>m) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>\<^sub>m)))"
  have "?e1 > 0"
    by (smt (verit, best) Moebius_gyrodom'.gyronorm_def \<open>to_complex a \<noteq> - to_complex b\<close> ab_left_minus add_right_cancel divide_eq_0_iff gamma_factor_eq1 gamma_factor_positive m_oplus'_def m_oplus.rep_eq norm_eq_zero norm_le_zero_iff of_real_0 zero_less_mult_iff)
  moreover
  have "?e2 > 0"
    by (metis Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc \<open>0 < \<llangle>a \<oplus>\<^sub>m b\<rrangle>\<^sub>m\<close> dual_order.refl gamma_factor_increasing gamma_factor_ineq1 linorder_not_le mem_Collect_eq of_real_0 zero_less_norm_iff)
  moreover
  have "?e1 < 1" "?e2 < 1"
    using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc 
    by auto
  ultimately 
  show ?thesis
    using gamma_factor_increase_reverse[of ?e1 ?e2]
    by (smt (verit, del_insts) gamma_factor_def gamma_factor_increasing gamma_factor_ineq1 norm_of_real)
qed

lemma mobius_gyroauto_norm:
  shows "\<llangle>m_gyr a b v\<rrangle>\<^sub>m = \<llangle>v\<rrangle>\<^sub>m"
  using Moebius_gyrodom.norm_gyr gyr_PoincareDisc_def
  by auto

lemma moebius_homogenity:
  shows "\<llangle>(r \<otimes>\<^sub>m a)\<rrangle>\<^sub>m = cmod (to_complex (\<bar>r\<bar> \<otimes>\<^sub>m of_complex (\<llangle>a\<rrangle>\<^sub>m)))"
proof (cases "a = 0\<^sub>m")
  case True
  then show ?thesis
    using Moebius_gyrodom'.gyronorm_def m_otimes'_def m_otimes.rep_eq m_ozero'_def m_ozero.rep_eq m_ozero_def
    by force
next
  case False
  have "\<llangle>(r \<otimes>\<^sub>m a)\<rrangle>\<^sub>m = \<bar>tanh (r * artanh (\<llangle>a\<rrangle>\<^sub>m))\<bar>"
    using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc cmod_m_otimes' m_otimes'_k_tanh m_otimes.rep_eq
    by force
  moreover
  have "to_complex (\<bar>r\<bar> \<otimes>\<^sub>m of_complex (\<llangle>a\<rrangle>\<^sub>m)) = tanh (\<bar>r\<bar> * artanh (\<llangle>a\<rrangle>\<^sub>m))"
  proof-
    have "to_complex (\<bar>r\<bar> \<otimes>\<^sub>m of_complex (\<llangle>a\<rrangle>\<^sub>m)) = 
          m_otimes'_k \<bar>r\<bar> (\<llangle>a\<rrangle>\<^sub>m) * ((\<llangle>a\<rrangle>\<^sub>m) / cmod (\<llangle>a\<rrangle>\<^sub>m))" 
      using m_otimes_def m_otimes'_def
      using Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.to_dom Rep_PoincareDisc m_otimes.rep_eq
      by force 
    moreover
    have "cmod (cmod (to_complex a)) = cmod (to_complex a)"
      by simp
    then have "(\<llangle>a\<rrangle>\<^sub>m) / cmod (\<llangle>a\<rrangle>\<^sub>m) = 1"
      using \<open>a \<noteq> 0\<^sub>m\<close>
      by (metis Moebius_gyrodom'.gyronorm_def Moebius_gyrodom'.of_dom divide_self_if m_ozero'_def m_ozero_def norm_eq_zero)
    ultimately
    have "to_complex ((abs r)  \<otimes>\<^sub>m ( of_complex (cor(\<llangle>a\<rrangle>\<^sub>m)))) = cor (m_otimes'_k \<bar>r\<bar> (cor (\<llangle>a\<rrangle>\<^sub>m)))"
      by auto
    then show ?thesis
      using Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc m_otimes'_k_tanh
      by auto
  qed
  moreover 
  have "\<bar>tanh(r * artanh (cmod (to_complex a))) / \<llangle>a\<rrangle>\<^sub>m\<bar> = tanh (\<bar>r\<bar> * artanh (cmod (to_complex a))) / \<llangle>a\<rrangle>\<^sub>m"
    by (metis Moebius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_divide abs_le_self_iff abs_mult_pos abs_norm_cancel artanh_nonneg dual_order.refl mem_Collect_eq  tanh_real_abs)
  ultimately 
  show ?thesis
    by (smt (verit, best) norm_of_real real_compex_cmod tanh_real_abs)
qed

lemma m_gyr_gyrospace:
  shows "m_gyr (r1 \<otimes>\<^sub>m v) (r2 \<otimes>\<^sub>m v) = id"
proof-
  have "m_gyr' (to_complex (r1 \<otimes>\<^sub>m v)) (to_complex (r2 \<otimes>\<^sub>m v)) = id"
  proof-
    let ?v = "to_complex v"
    let ?e1 = "?v * tanh (r1 * artanh (cmod ?v)) /cmod(to_complex v)"
    let ?e2 = "?v * tanh (r2 * artanh (cmod ?v)) /cmod(to_complex v)"

    have "to_complex (r1 \<otimes>\<^sub>m v) = ?e1"
         "to_complex (r2 \<otimes>\<^sub>m v) = ?e2"
      using Rep_PoincareDisc m_otimes'_def m_otimes'_k_tanh m_otimes.rep_eq
      by auto

    moreover

    have "cnj ?e1 = cnj ?v * cnj (tanh (r1 * artanh (cmod ?v))) / cmod ?v"
         "cnj ?e2 = cnj ?v * cnj (tanh (r2 * artanh (cmod ?v))) / cmod ?v"
        by auto

    moreover

    have "(1 + ?e1 * (cnj ?e2)) / (1 + ?e2 * (cnj ?e1)) = 1"
    proof-
      have "1 + ?e1 * (cnj ?e2) = 1 + ?e2 * (cnj ?e1)"
        by simp
      moreover
      have "1 + ?e2 * (cnj ?e1) \<noteq> 0"
        using \<open>to_complex (r1 \<otimes>\<^sub>m v) =?e1\<close> \<open>to_complex (r2 \<otimes>\<^sub>m v) = ?e2\<close>
        by (metis Rep_PoincareDisc  div_by_0 divide_eq_1_iff mem_Collect_eq mobius_gyroauto_help norm_zero)
      ultimately
      show ?thesis
        by simp
    qed

    ultimately show ?thesis 
       using m_gyr_def m_gyr'_def
       by (metis eq_id_iff mult.commute mult_1)
   qed

   then show ?thesis 
     by (metis (no_types, opaque_lifting) add_0_left add_0_right complex_cnj_zero div_by_1 eq_id_iff m_gyr_def m_left_id m_oplus'_def m_oplus_def m_ozero'_def m_ozero.rep_eq map_fun_apply mult_zero_left)
qed

lemma help8:
  assumes "cmod u < 1" "cmod v < 1"
  shows "cmod ((1 + cnj u * v) / (1 + u * cnj v)) = 1"
  using assms norm_divide
  by (simp add: mobius_gyroauto_help mult.commute)

lemma m_gyr_gyrospace2:
  shows "m_gyr u v (r \<otimes>\<^sub>m a) = r \<otimes>\<^sub>m (m_gyr u v a)"
proof-
  let ?u = "to_complex u" and ?v = "to_complex v" and ?a = "to_complex a"
  let ?e1 = "m_gyr u v a"
  let ?e2 = "cmod (to_complex ?e1)"

  have "?e1 = of_complex ((1 + ?u * cnj ?v) / (1 + cnj ?u *?v) * ?a)"
    by (metis Moebius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
  then have "?e2 = cmod ((1 + ?u * cnj ?v) / (1 + cnj ?u *?v)) * cmod ?a"
    by (metis m_gyr'_def m_gyr.rep_eq norm_mult)
  then have "?e2 = cmod ?a"
    using Moebius_gyrodom'.gyronorm_def mobius_gyroauto_norm 
    by presburger
  then have "r \<otimes>\<^sub>m ?e1 = of_complex (((1+cmod ?a) powr r - (1-cmod ?a) powr r) /
                                    ((1+cmod ?a) powr r + (1-cmod ?a) powr r) * to_complex ?e1 / ?e2)"
    using m_otimes_def 
    by (metis (no_types, lifting) Moebius_gyrodom'.of_dom m_otimes'_def m_otimes'_k_def m_otimes.rep_eq mult_eq_0_iff times_divide_eq_right)
  then have "r \<otimes>\<^sub>m ?e1 = of_complex (to_complex (r \<otimes>\<^sub>m a) * ((1 + ?u * cnj ?v) / (1 + cnj ?u * ?v)))"
    using m_otimes_def
    using \<open>?e2 = cmod ?a\<close>
    by (smt (verit, ccfv_threshold) Moebius_gyrodom'.of_dom  ab_semigroup_mult_class.mult_ac(1) m_gyr'_def m_gyr.rep_eq m_otimes'_def m_otimes'_k_def m_otimes.rep_eq mult.commute mult_eq_0_iff times_divide_eq_right)
  then show ?thesis 
    by (metis Moebius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq mult.commute)
qed

definition m_gyroplus_r :: "real \<Rightarrow> real \<Rightarrow> real" (infixl "\<oplus>\<^sub>m\<^sub>r" 100) where 
  "r1 \<oplus>\<^sub>m\<^sub>r r2 = (r1 + r2) / (1 + r1*r2)"

interpretation Moebious_gyrovector_space:
 gyrovector_space of_complex "\<lambda> z. cmod z < 1" to_complex m_otimes "of_complex \<circ> cor" "cmod \<circ> to_complex"
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
  fix r :: real and a
  assume "r \<noteq> 0" 
  then show "to_complex (abs r \<otimes>\<^sub>m a) /\<^sub>R gyrodom'.gyronorm to_complex (r \<otimes>\<^sub>m a) =
             to_complex a /\<^sub>R  gyrodom'.gyronorm to_complex a"
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
  show " gyrodom'.gyronorm to_complex (r \<otimes>\<^sub>m a) =
           (cmod \<circ> to_complex)
            (\<bar>r\<bar> \<otimes>\<^sub>m (of_complex \<circ> cor) (gyrodom'.gyronorm to_complex a))"
    using moebius_homogenity[of r a]
    using Moebius_gyrodom'.gyrodom'_axioms Moebius_gyrodom'.gyronorm_def gyrodom'.gyronorm_def by fastforce   
next
  fix a b
  show " gyrodom'.gyronorm to_complex (a \<oplus> b)
           \<le> (cmod \<circ> to_complex)
               ((of_complex \<circ> cor) (gyrodom'.gyronorm to_complex a) \<oplus>
                (of_complex \<circ> cor) (gyrodom'.gyronorm to_complex b))"
    using moebius_triangle[of a b]
    using Moebius_gyrodom'.gyrodom'_axioms Moebius_gyrodom'.gyronorm_def gyrodom'.gyronorm_def gyroplus_PoincareDisc_def by fastforce 
qed

(* ---------------------------------------------------------------------------- *)

definition m_gyr_general :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
  "m_gyr_general u v w = \<ominus>\<^sub>m(u\<oplus>\<^sub>mv) \<oplus>\<^sub>m (u \<oplus>\<^sub>m(v \<oplus>\<^sub>m w))"

lemma m_gyr_general_m_gyr:
  shows "m_gyr_general u v w = m_gyr u v w"
  by (simp add: Moebius_gyrogroup.gyr_def m_gyr_general_def)

definition m_oplus'_full :: "complex \<Rightarrow> complex \<Rightarrow> complex" where 
  "m_oplus'_full u v = ((1 + 2*inner u v + (norm v)^2) *\<^sub>R u + (1 - (norm u)^2) *\<^sub>R v) /
                        (1 + 2*inner u v + (norm u)^2 * (norm v)^2)"

lemma m_oplus'_full:
  assumes "cmod u < 1" "cmod v < 1"
  shows "m_oplus'_full u v = m_oplus' u v"
proof-
  have *: "2 * inner u v = cnj u * v + cnj v * u"
    using two_inner_cnj
    by auto
  
  have "(1 + 2*inner u v + (norm v)^2) * u =
        (1 + cnj u *v + cnj v * u + (norm v)^2) * u"
    using *
    by auto

  moreover

  have "1 + 2*inner u v + (norm u)^2 * (norm v)^2 = 
        1 + cnj u * v + cnj v * u + (norm u)^2 * (norm v)^2"
    using *
    by auto

  moreover

  have "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1 - (norm u)^2) * v =
        (1 + cnj v * u) * (u + v)"
  proof-
    have *: "(1 + cnj u * v + cnj v * u + (norm v)^2) * u = 
             u + (norm u)^2 * v + cnj v * u^2 + (norm v)^2 * u"
      by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) comm_semiring_class.distrib complex_norm_square mult.commute mult_cancel_right1 power2_eq_square)
    have **: "(1 + cnj v * u) * (u + v) = u + cnj v * u * u + v + cnj v * u * v"
      by (simp add: distrib_left ring_class.ring_distribs(2))
    have "u + cnj u * v *u + v + cnj u* v * v = u + cnj u * v^2 + (norm u)^2 * v + v"
      by (simp add: cnj_cmod mult.commute power2_eq_square)
    have ***: "(1 - (norm u)^2) * v = v - (norm u)^2 * v"
      by (simp add: mult.commute right_diff_distrib')
    have "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1 - (norm u)^2) * v =
          u + (norm u)^2 * v + (cnj v) * u^2 + (norm v)^2 * u + v - (norm u)^2 * v"
      using * ***
      by force
    have ****: "(1 + cnj u * v + cnj v * u + (norm v)^2) * u + (1-(norm u)^2) * v =
                u + cnj v *u^2 + (norm v)^2 * u + v"
      using * *** 
      by auto

    have "(1 + cnj v * u) * (u+v) = u + (norm v)^2 *u + v + cnj v * u^2"
      using **
      by (simp add: cnj_cmod mult.commute power2_eq_square)

    then show ?thesis
      using ****
      by auto
  qed

  moreover have "1 + cnj u * v + cnj v *u + (norm u)^2 * (norm v)^2  =
                (1 + cnj u * v) * (1 + cnj v * u)"
    by (smt (verit, del_insts) cnj_cmod comm_semiring_class.distrib complex_cnj_cnj complex_cnj_mult complex_mod_cnj is_num_normalize(1) mult.commute mult_numeral_1 norm_mult numeral_One power_mult_distrib)
  
  ultimately
  show ?thesis 
    using assms
    unfolding m_oplus'_full_def m_oplus'_def
    by (metis (no_types, lifting) den_not_zero divide_divide_eq_left' nonzero_mult_div_cancel_left scaleR_conv_of_real)
qed

lemma times2_m: "2 \<otimes>\<^sub>m u = u \<oplus>\<^sub>m u"
  using Moebious_gyrovector_space.times2 gyroplus_PoincareDisc_def
  by simp
(*
proof transfer
  fix u
  assume "cmod u < 1"
  show "m_otimes' 2 u = m_oplus' u u"
  proof (cases "u = 0")
    case True
    then show ?thesis
      unfolding m_otimes'_def m_otimes'_k_def m_oplus'_def
      by auto
  next
    case False
    have "(1 + (cmod u))\<^sup>2 - (1 - (cmod u))\<^sup>2 = 4 * cmod u"
      by (simp add: power2_eq_square field_simps)
    moreover
    have "(1 + (cmod u))\<^sup>2 + (1 - (cmod u))\<^sup>2 = 2 * (1 + (cmod u)\<^sup>2)"
      by (simp add: power2_eq_square field_simps)
    ultimately
    have "m_otimes' 2 u = 4 * u / (2 * (1 + (cmod u)\<^sup>2))"
      using False \<open>cmod u < 1\<close>
      unfolding m_otimes'_def m_otimes'_k_def
      by auto
    also have "\<dots> = 2 * (2 * u) / (2 * (1 + (cmod u)\<^sup>2))"
      by (simp add: field_simps)
    also have "\<dots> = 2 * u / (1 + (cmod u)\<^sup>2)"
      by (smt (verit, ccfv_threshold) divide_divide_eq_right mult.commute mult_2 nonzero_mult_div_cancel_left of_real_add of_real_diff of_real_divide of_real_mult of_real_numeral of_real_power times_divide_eq_left times_divide_eq_right zero_neq_numeral)
    finally show ?thesis
      using False
      unfolding m_otimes'_def m_otimes'_k_def m_oplus'_def
      using complex_norm_square 
      by fastforce
  qed
qed
*)


lift_definition m_gammma_factor :: "PoincareDisc \<Rightarrow> real" ("\<gamma>\<^sub>m") is gamma_factor
  done

definition m_half' :: "complex \<Rightarrow> complex" where
  "m_half' v = (\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v"

lift_definition m_half :: "PoincareDisc \<Rightarrow> PoincareDisc" is m_half'
  unfolding m_half'_def
proof-
  fix v
  assume "cmod v < 1"
  let ?k = "\<gamma> v / (1 + \<gamma> v)"
  have "abs ?k < 1"
    using \<open>cmod v < 1\<close> gamma_factor_positive by fastforce
  then show "cmod (?k *\<^sub>R v) < 1"
    using \<open>cmod v < 1\<close>
    by (metis mult_closed_for_unit_disc norm_of_real scaleR_conv_of_real)
qed

lemma two_times_half:
  shows "2 \<otimes>\<^sub>m (m_half v) = v"
proof-
  have "2 \<otimes>\<^sub>m (m_half v) = m_half v \<oplus>\<^sub>m m_half v"
    using times2_m
    by simp
  also have "\<dots> = v"
  proof transfer
    fix v :: complex 
    assume assms: "cmod v < 1"
    have *: "\<gamma> v \<noteq> 0" "1 + \<gamma> v \<noteq> 0"
      using assms gamma_factor_positive 
      by fastforce+
    let ?k = "\<gamma> v / (1 + \<gamma> v)"
    have "1 + cnj (?k * v) * (?k * v) = 1 + ?k^2 * (cmod v)\<^sup>2"
      by (simp add: cnj_cmod mult.commute power2_eq_square)
    also have "\<dots> = 1 + (\<gamma> v)\<^sup>2 / (1 + \<gamma> v)\<^sup>2 * (1 - 1 / (\<gamma> v)\<^sup>2)"
      using norm_square_gamma_factor[OF assms]
      by (simp add: power_divide)
    also have "\<dots> = 1 + ((\<gamma> v)\<^sup>2 * ((\<gamma> v)\<^sup>2 - 1)) / ((\<gamma> v)\<^sup>2 * (1 + \<gamma> v)\<^sup>2)"
      using *
      by (simp add: field_simps)
    also have "\<dots> = 1 + ((\<gamma> v)\<^sup>2 - 1) / (1 + \<gamma> v)\<^sup>2"
      using *
      by simp
    also have "\<dots> = 1 + ((\<gamma> v - 1) * (\<gamma> v + 1)) / ((\<gamma> v + 1) * (\<gamma> v + 1))"
      by (simp add: power2_eq_square field_simps)
    also have "\<dots> = 1 + (\<gamma> v - 1) / (\<gamma> v + 1)"
      using *
      by simp
    also have "\<dots> = 2 * ?k"
      using *
      by (simp add: field_simps)
    finally show "m_oplus' (m_half' v) (m_half' v) = v"
      unfolding m_oplus'_def m_half'_def
      using * \<open>1 + cnj (?k * v) * (?k * v) = 1 + ?k\<^sup>2 * (cmod v)\<^sup>2\<close>
      by (smt (verit)  mult_eq_0_iff nonzero_mult_div_cancel_left of_real_eq_0_iff power2_eq_square scaleR_conv_of_real scaleR_left_distrib)
  qed
  finally show ?thesis
    .
qed

lemma m_half:
  shows "m_half v = (1/2) \<otimes>\<^sub>m v"
  by (metis Moebious_gyrovector_space.scale_assoc mult_2 real_scaleR_def scaleR_half_double two_times_half)



end
