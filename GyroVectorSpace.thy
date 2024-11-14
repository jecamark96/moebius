theory GyroVectorSpace
  imports GyroGroup "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces 
begin

locale gyrocarrier' = 
  fixes to_carrier :: "'a::gyrocommutative_gyrogroup \<Rightarrow> 'b::real_inner"
  fixes of_carrier :: "'b \<Rightarrow> 'a"
  fixes in_domain :: "'b \<Rightarrow> bool"
  assumes to_carrier: "\<And> b. in_domain b \<Longrightarrow> to_carrier (of_carrier b) = b"
  assumes of_carrier [simp]: "\<And> a. of_carrier (to_carrier a) = a"
  assumes to_carrier_zero [simp]: "to_carrier 0\<^sub>g = 0"
begin

definition gyronorm :: "'a \<Rightarrow> real" ("\<llangle>_\<rrangle>" [100] 100) where
  "\<llangle>a\<rrangle> = norm (to_carrier a)"
definition gyroinner :: "'a \<Rightarrow> 'a \<Rightarrow> real" (infixl "\<cdot>" 100) where
  "a \<cdot> b = inner (to_carrier a) (to_carrier b)"

lemma norm_inner: "\<llangle>a\<rrangle> = sqrt (a \<cdot> a)"
  using gyroinner_def gyronorm_def norm_eq_sqrt_inner by auto

lemma to_carrier_zero_iff:
  assumes "to_carrier a = 0"
  shows "a = 0\<^sub>g"
  using assms
  by (metis of_carrier to_carrier_zero)

lemma norm_zero:
  shows "\<llangle>0\<^sub>g\<rrangle> = 0"
  by (simp add: gyronorm_def)

lemma norm_zero_iff:
  assumes "\<llangle>a\<rrangle> = 0"
  shows "a = 0\<^sub>g"
  using assms
  by (simp add: gyronorm_def to_carrier_zero_iff)

definition norms :: "real set" where 
 "norms = {x. \<exists> a. x = \<llangle>a\<rrangle>}"
end

locale gyrocarrier'' = gyrocarrier' + 
  fixes of_real :: "real \<Rightarrow> 'a"
  fixes to_real :: "'a \<Rightarrow> real"
  assumes to_real: "\<And> x. x \<in> norms \<Longrightarrow> to_real (of_real x) = x"

locale gyrocarrier = gyrocarrier'' +  
  assumes inner_gyroauto_invariant: "\<And> u v a b. (gyr u v a) \<cdot> (gyr u v b) = a \<cdot> b"
begin
lemma norm_gyr: "\<llangle>gyr u v a\<rrangle> = \<llangle>a\<rrangle>"
  by (metis inner_gyroauto_invariant norm_inner)
end

print_locale! gyrocarrier

locale gyrovector_space = 
  gyrocarrier +
  fixes scale :: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 105) 
  assumes scale_1: "\<And> a :: 'a. 1 \<otimes> a = a"
  assumes scale_distrib: "\<And> (r1 :: real) (r2 :: real) (a :: 'a). (r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus> r2 \<otimes> a"
  assumes scale_assoc: "\<And> (r1 :: real) (r2 :: real) (a :: 'a). (r1 * r2) \<otimes> a = r1 \<otimes> (r2 \<otimes> a)"
  assumes scale_prop1: "\<And> (r :: real) (a :: 'a). r \<noteq> 0 \<Longrightarrow> to_carrier (\<bar>r\<bar> \<otimes> a) /\<^sub>R \<llangle>r \<otimes> a\<rrangle> = to_carrier a /\<^sub>R \<llangle>a\<rrangle>" 
  assumes gyroauto_property: "\<And> (u :: 'a) (v :: 'a) (r :: real) (a :: 'a). gyr u v (r \<otimes> a) = r \<otimes> (gyr u v a)"
  assumes gyroauto_id: "\<And> (r1 :: real) (r2 :: real) (v :: 'a). gyr (r1 \<otimes> v) (r2 \<otimes> v) = id"
  assumes homogeneity: "\<And> (r :: real) (a :: 'a). \<llangle>r \<otimes> a\<rrangle> = to_real (\<bar>r\<bar> \<otimes> (of_real (\<llangle>a\<rrangle>)))"
  assumes gyrotriangle: "\<And> (a :: 'a) (b :: 'a). \<llangle>(a \<oplus> b)\<rrangle> \<le> to_real ((of_real (\<llangle>a\<rrangle>)) \<oplus> (of_real (\<llangle>b\<rrangle>)))"
begin

abbreviation add_real (infixl "\<oplus>\<^sub>R" 100) where 
  "add_real r1 r2 \<equiv> to_real (of_real r1 \<oplus> of_real r2)"

abbreviation mult_real (infix "\<otimes>\<^sub>R" 100) where
  "mult_real r a \<equiv> to_real (r \<otimes> of_real a)"

lemma scale_minus1: 
  shows "(-1) \<otimes> a = \<ominus> a"
  by (metis add.right_inverse add_cancel_right_left gyrogroup_class.gyro_left_cancel' gyrogroup_class.gyro_right_id scale_1 scale_distrib)

lemma minus_norm: 
  shows "\<llangle>\<ominus>a\<rrangle> = \<llangle>a\<rrangle>"
proof-
   have "-1\<noteq>(0::int)"
    by simp
  have " (to_carrier (abs (-1) \<otimes> a) /\<^sub>R \<llangle>(-1) \<otimes> a\<rrangle>) = ((to_carrier a) /\<^sub>R \<llangle>a\<rrangle>)"
    using scale_prop1 
    by (metis zero_neq_neg_one)
  then show ?thesis 
    using to_carrier_zero_iff scale_1 scale_minus1 by fastforce
qed

text \<open>(6.3)\<close>
lemma scale_minus: 
  shows "(-r) \<otimes> a = \<ominus> (r \<otimes> a)"
  by (metis minus_mult_commute mult_1 scale_assoc scale_minus1)

lemma scale_minus': 
  shows "k \<otimes> (\<ominus> a) = \<ominus> (k \<otimes> a)"
  by (metis mult.commute scale_assoc scale_minus1)

lemma zero_otimes [simp]: 
  shows "0 \<otimes> x = 0\<^sub>g"
  by (metis add.right_inverse gyro_rigth_inv scale_distrib scale_minus)

lemma times_zero [simp]: 
  shows "t \<otimes> 0\<^sub>g = 0\<^sub>g"
  by (metis mult_zero_right scale_assoc zero_otimes)

text \<open>Theorem 6.4 (6.4)\<close>
lemma monodistributive:
  shows "r \<otimes> (r1 \<otimes> a \<oplus> r2 \<otimes> a) = r \<otimes> (r1 \<otimes> a) \<oplus> r \<otimes> (r2 \<otimes> a)"
  by (metis ring_class.ring_distribs(1) scale_assoc scale_distrib)

lemma times2: "2 \<otimes> a = a \<oplus> a"
  by (metis mult_2_right scale_1 scale_assoc scale_distrib)

lemma twosum: "2 \<otimes> (a \<oplus> b) = a \<oplus> (2 \<otimes> b \<oplus> a)"
proof-
  have "a \<oplus> (2 \<otimes> b \<oplus> a) = a \<oplus> ((b \<oplus> b) \<oplus> a)"
    by (simp add: times2)
  also have "... = a \<oplus> (b \<oplus> (b \<oplus> gyr b b a))"
    by (simp add: gyro_right_assoc)
  also have "... = a \<oplus> (b \<oplus> (b \<oplus> a))"
    by simp
  also have "... = (a \<oplus> b) \<oplus> gyr a b (b \<oplus> a)"
    using gyro_left_assoc by blast
  also have "... = (a \<oplus> b) \<oplus> (a \<oplus> b)"
    by (metis gyro_commute)
  finally show ?thesis
    by (metis times2)
qed

definition gyrodistance :: "'a \<Rightarrow> 'a \<Rightarrow> real" ("d\<^sub>\<oplus>") where 
  "d\<^sub>\<oplus> a b = \<llangle>\<ominus> a \<oplus> b\<rrangle>"

lemma "d\<^sub>\<oplus> a b = \<llangle>b \<ominus>\<^sub>b a\<rrangle>"
  by (metis gyrodistance_def gyrogroup_class.gyrominus_def gyro_commute norm_gyr)

lemma gyrodistance_metric_nonneg: 
  shows "d\<^sub>\<oplus> a b \<ge> 0"
  by (simp add: gyrodistance_def gyronorm_def)

lemma gyrodistance_metric_zero_iff:
  shows "d\<^sub>\<oplus> a b = 0 \<longleftrightarrow> a = b"
  unfolding gyrodistance_def gyronorm_def
  by (metis gyrogroup_class.gyro_left_cancel' gyrogroup_class.gyro_right_id gyronorm_def norm_zero_iff real_normed_vector_class.norm_zero to_carrier_zero)

lemma gyrodistance_metric_sym:
  shows "d\<^sub>\<oplus> a b = d\<^sub>\<oplus> b a"
  by (metis gyrodistance_def gyrogroup_class.gyro_inv_idem gyrogroup_class.gyrominus_def gyrogroup_class.gyroplus_inv minus_norm norm_gyr)

lemma gyrodistance_gyrotriangle:
  shows "d\<^sub>\<oplus> a c \<le> d\<^sub>\<oplus> a b  \<oplus>\<^sub>R d\<^sub>\<oplus> b c"
proof-
  have "\<llangle>\<ominus>a \<oplus> c\<rrangle> = \<llangle>(\<ominus>a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus>b \<oplus> c)\<rrangle>"
    using gyro_polygonal_addition_lemma[of a b c]
    by auto
  also have "... \<le>  (\<llangle>\<ominus>a \<oplus> b\<rrangle>) \<oplus>\<^sub>R (\<llangle>gyr (\<ominus>a) b (\<ominus>b \<oplus> c)\<rrangle>)"
    by (simp add: gyrotriangle)
  finally show ?thesis
    unfolding gyrodistance_def norm_gyr
    by meson
qed

lemma equation_solving:
  assumes "x \<oplus> y = a" "\<ominus> x \<oplus> y = b"
  shows "x = (1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<and> y = (1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b"
proof-
  have "y = x \<oplus> b"
    using assms(2) gyro_equation_right by auto
  then have "a = x \<oplus> (x \<oplus> b)"
    using assms(1) by auto
  then have "a = (2 \<otimes> x) \<oplus> b"
    by (simp add: gyro_left_assoc times2)
  then have "x = (1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b)"
    by (smt (verit) gyro_equation_left nonzero_eq_divide_eq scale_1 scale_assoc)
  then show ?thesis
    using \<open>y = x \<oplus> b\<close>
    by simp
qed

lemma double_plus: "(2 \<otimes> a) \<oplus> b = a \<oplus> (a \<oplus> b)"
 by (simp add: gyro_left_assoc times2)

lemma I6_33:
  shows "(1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) = (-1/2) \<otimes> (b \<ominus>\<^sub>c\<^sub>b a)"
  by (metis (no_types, opaque_lifting) div_by_1 divide_divide_eq_right divide_minus1 gyrogroup_class.gyro_equation_left gyrogroup_class.gyro_left_cancel' scale_assoc scale_minus1 times_divide_eq_left)

lemma I6_34:
  shows "(1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b = (1/2) \<otimes> (b \<ominus>\<^sub>c\<^sub>b a) \<oplus> a"
  by (smt (verit, ccfv_threshold) I6_33 cogyro_right_cancel' double_plus gyro_left_cancel' mult.commute nonzero_eq_divide_eq scale_1 scale_assoc scale_minus1)

lemma I6_35:
  shows "gyr b a = gyr b ((1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b) \<circ> (gyr ((1/2) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b) a)"
  by (metis (no_types, lifting) I6_33 I6_34 divide_minus_left gyr_master_misc2' gyr_misc_2 gyr_right_loop gyro_commute gyro_translate_commute scale_minus)


lemma double_half: 
  shows "2 \<otimes> ((1 / 2) \<otimes> a) = a"
  by (metis field_sum_of_halves mult.commute mult_2_right scale_1 scale_assoc)

lemma I6_38:
  shows "a \<oplus> (1/2) \<otimes> (\<ominus> a \<oplus>\<^sub>c b) = (1/2) \<otimes> (a \<oplus> b)"
proof -
  have "\<And>r r' a. r \<otimes> (r' \<otimes> a) = r' \<otimes> (r \<otimes> a)"
    by (metis (full_types) mult.commute scale_assoc)
  then show ?thesis
    using double_half 
    by (smt (z3) gyrogroup_class.cogyro_commute_iff_gyrocommute gyrogroup_class.cogyro_right_cancel' gyrogroup_class.cogyrominus_def gyro_commute twosum)
qed


lemma I6_39:
  shows "a \<oplus> (1/2) \<otimes> (\<ominus> a \<oplus> b) = (1/2) \<otimes> (a \<oplus>\<^sub>c b)"
  by (metis I6_38 gyro_equation_right gyro_inv_idem)

lemma I6_40:
  shows "gyr ((r + s) \<otimes> a) b x = gyr (r\<otimes>a) (s\<otimes>a \<oplus> b) (gyr (s\<otimes>a) b x)"
  by (metis (mono_tags, opaque_lifting) comp_eq_elim gyroauto_id id_def gyr_nested_1 scale_distrib)

(* ---------------------------------------------------------------------------- *)
definition collinear :: "'a => 'a => 'a => bool" where
  "collinear x y z \<longleftrightarrow> (y = z \<or> (\<exists>t::real. (x = y \<oplus> t \<otimes> (\<ominus> y \<oplus> z))))"

lemma collinear_aab:
  shows "collinear a a b"
  by (metis collinear_def gyro_right_id gyro_rigth_inv scale_distrib scale_minus)

lemma collinear_bab:
  shows "collinear b a b"
  by (metis collinear_def gyro_equation_right scale_1)

lemma T6_20:
  assumes "collinear p1 a b" "collinear p2 a b" "a \<noteq> b" "p1 \<noteq> p2"
  shows "\<forall>x. (collinear x p1 p2 \<longrightarrow> collinear x a b)"
proof safe
  obtain t1 where t1: "p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p1 a b\<close> \<open>a \<noteq> b\<close> collinear_def 
    by auto
  obtain t2 where t2: "p2 = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p2 a b\<close> \<open>a \<noteq> b\<close> collinear_def
    by blast

  fix x
  assume "collinear x p1 p2"
  show "collinear x a b"
  proof-
    obtain t where t: "x = p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2)"
      using \<open>collinear x p1 p2\<close> \<open>p1 \<noteq> p2\<close> collinear_def 
      by blast
    have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> (\<ominus> (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> (a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)))"
      using t1 t2 t
      by simp
    then have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) ((-t1 + t2) \<otimes> (\<ominus> a \<oplus> b))"
      by (smt (verit, best) gyr_def scale_distrib)
    then have "x = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) ((t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b))"
      using gyroauto_property scale_assoc by presburger
    then have "x = a \<oplus> (t1 \<otimes> (\<ominus> a \<oplus> b) \<oplus> ((t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b)))"
      by (simp add: gyro_left_assoc)
    then  have "x = a \<oplus> (t1 + t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b)"
      by (simp add: scale_distrib)
    then show ?thesis  
      using collinear_def by blast
  qed
qed


lemma T6_20_1:
  assumes "collinear p1 a b" "collinear p2 a b" "p1 \<noteq> p2" "a \<noteq> b"
  shows "\<forall>x. (collinear x a b \<longrightarrow> collinear x p1 p2)"
proof safe
  obtain t1 where t1: "p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p1 a b\<close> \<open>a \<noteq> b\<close> collinear_def 
    by auto
  obtain t3 where t3: "p2 = a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)"
    using \<open>collinear p2 a b\<close> \<open>a \<noteq> b\<close> collinear_def
    by blast

  fix x
  assume "collinear x a b"
  show "collinear x p1 p2" 
  proof-
    obtain t2 where "x = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
      using \<open>collinear x a b\<close> \<open>a \<noteq> b\<close> collinear_def
      by blast
    show ?thesis
    proof (cases "t1 = t3")
      case True
      then show ?thesis
        using t1 t3 \<open>p1 \<noteq> p2\<close>
        by blast
    next
      case False
      then obtain t where t: "t = (t2-t1)/(t3-t1)" 
        by simp
      have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> (\<ominus> (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> ( a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)))"
        using t1 t3 by blast
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) (t1 \<otimes> (\<ominus>  (\<ominus> a \<oplus> b)) \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b))"
        by (metis (no_types, lifting) gyro_translation_2a mult.commute scale_assoc scale_minus1)
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) (((-t1+t3)*t) \<otimes> (\<ominus> a \<oplus> b) )"
        by (metis (no_types, opaque_lifting) gyroauto_property minus_mult_commute mult.commute mult.right_neutral scale_assoc scale_distrib scale_minus1)
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> (t1 \<otimes> (\<ominus> a \<oplus> b) \<oplus> ((-t1+t3)*t) \<otimes> (\<ominus> a \<oplus> b)) "
        using gyro_left_assoc by metis
      then have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> (t1 + (-t1+t3)*t) \<otimes> ((\<ominus> a \<oplus> b))"
        using scale_distrib by presburger
      moreover have "t1 + (-t1+t3)*t = t2"
        using \<open>t1 \<noteq> t3\<close> t
        by simp
      ultimately
      have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
        by blast
      then show ?thesis
        using \<open>x = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)\<close> 
        unfolding collinear_def
        by metis
    qed
  qed
qed

lemma collinear_sym1:
  assumes "collinear a b c"
  shows "collinear b a c"
  using T6_20_1 assms collinear_aab collinear_bab collinear_def by blast

lemma collinear_sym2:
  assumes "collinear a b c"
  shows "collinear a c b"
  by (metis T6_20 assms collinear_aab collinear_bab)

lemma collinear_transitive:
  assumes "collinear a b c" "collinear d b c" "b \<noteq> c"
  shows "collinear a d b" 
  by (metis T6_20 assms(1) assms(2) assms(3) collinear_bab collinear_sym1 collinear_sym2)

lemma collinear_translate':
  shows "x = u \<oplus> t \<otimes> (\<ominus> u \<oplus> v) \<longleftrightarrow> 
        (\<ominus> a \<oplus> x) = (\<ominus> a \<oplus> u) \<oplus> t \<otimes> (\<ominus> (\<ominus> a \<oplus> u) \<oplus> (\<ominus> a \<oplus> v))"
  thm gyro_translation_2a
  by (metis (no_types, lifting) gyr_misc_2 gyro_right_assoc gyro_translation_2a gyroauto_property oplus_ominus_cancel)

definition translate where
  "translate a x = \<ominus> a \<oplus> x"

lemma collinear_translate:
  shows "collinear u v w \<longleftrightarrow> collinear (translate a u) (translate a v) (translate a w)"
  unfolding collinear_def translate_def
  by (metis collinear_translate' gyro_left_cancel')

definition gyroline :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "gyroline a b = {x. collinear x a b}"

definition between :: "'a => 'a => 'a => bool" where
  "between x y z \<longleftrightarrow> (\<exists>t::real. 0 \<le> t \<and> t \<le> 1 \<and> y = x \<oplus> t \<otimes> (\<ominus> x \<oplus> z))"

lemma between_xxy [simp]:
  shows "between x x y"
  unfolding between_def
  by (rule_tac x=0 in exI) simp

lemma between_xyy [simp]:
  shows "between x y y"
  unfolding between_def
  by (rule_tac x=1 in exI) (simp add: scale_1)

lemma between_xyx:
  assumes "between x y x"
  shows "y = x"
  using assms
  unfolding between_def
  by auto

lemma between_translate:
  shows "between u v w \<longleftrightarrow> between (translate a u) (translate a v) (translate a w)"
  unfolding between_def translate_def
  using collinear_translate' 
  by auto

definition distance where
  "distance u v = \<llangle>\<ominus> u \<oplus> v\<rrangle>"

lemma distance_translate:
  shows "distance u v = distance (translate a u) (translate a v)"
  unfolding distance_def translate_def
  using gyro_translation_2a norm_gyr 
  by metis

end

end
