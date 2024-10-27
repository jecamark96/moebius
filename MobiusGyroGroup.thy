theory MobiusGyroGroup
  imports Complex_Main HOL.Real_Vector_Spaces HOL.Transcendental MoreComplex
          GyroGroup Poincare
begin

definition m_oplus' :: "complex \<Rightarrow> complex \<Rightarrow> complex"  where
  "m_oplus' a z = (a + z) / (1 + (cnj a) * z)"

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

interpretation Mobius_gyrogroup: gyrogroup m_ozero m_oplus m_ominus m_gyr
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

interpretation Mobius_gyrocommutative_gyrogroup: gyrocommutative_gyrogroup m_ozero m_oplus m_ominus m_gyr
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

end
