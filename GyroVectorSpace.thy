theory GyroVectorSpace
  imports GyroGroup "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces 

begin

locale gyrodom' = 
  fixes to_dom :: "'a::gyrogroup \<Rightarrow> 'b::{real_inner, real_div_algebra}"
  fixes of_dom :: "'b \<Rightarrow> 'a"
  fixes in_dom :: "'b \<Rightarrow> bool"
  assumes to_dom: "\<And> b. in_dom b \<Longrightarrow> to_dom (of_dom b) = b"
  assumes of_dom: "\<And> a. of_dom (to_dom a) = a"
  assumes to_dom_zero [simp]: "to_dom 0\<^sub>g = 0"
begin
definition gyronorm :: "'a \<Rightarrow> real" ("\<llangle>_\<rrangle>" [100] 100) where
  "\<llangle>a\<rrangle> = norm (to_dom a)"
definition gyroinner :: "'a \<Rightarrow> 'a \<Rightarrow> real" (infixl "\<cdot>" 100) where
  "a \<cdot> b = inner (to_dom a) (to_dom b)"
end

locale gyrodom = gyrodom' +  
  assumes inner_gyroauto_invariant: "\<And> u v a b. (gyr u v a) \<cdot> (gyr u v b) = a \<cdot> b"
begin
lemma norm_inner: "\<llangle>a\<rrangle> = sqrt (a \<cdot> a)"
  using gyroinner_def gyronorm_def norm_eq_sqrt_inner by auto
lemma norm_gyr: "\<llangle>gyr u v a\<rrangle> = \<llangle>a\<rrangle>"
  by (metis inner_gyroauto_invariant norm_inner)

lemma to_dom_zero_iff:
  assumes "to_dom a = 0"
  shows "a = 0\<^sub>g"
  using assms
  by (metis of_dom to_dom_zero)


lemma norm_zero:
  shows "\<llangle>0\<^sub>g\<rrangle> = 0"
  by (simp add: gyronorm_def)

lemma norm_zero_iff:
  assumes "\<llangle>a\<rrangle> = 0"
  shows "a = 0\<^sub>g"
  using assms
  by (simp add: gyronorm_def to_dom_zero_iff)

end

locale gyrovector_space = 
  gyrocommutative_gyrogroup "gyrozero :: 'a::gyrogroup" 
                            "gyroplus :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"  
                            "gyroinv :: 'a \<Rightarrow> 'a"
                            "gyr :: 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" + 
  gyrodom to_dom for to_dom :: "'a::gyrogroup \<Rightarrow> 'b::{real_inner, real_div_algebra}" +
  fixes scale :: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 105) 
  fixes of_real :: "real \<Rightarrow> 'a"
  fixes to_real :: "'a \<Rightarrow> real"
  assumes scale_1: "\<And> a :: 'a. 1 \<otimes> a = a"
  assumes scale_distrib: "\<And> (r1 :: real) (r2 :: real) (a :: 'a). (r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus> r2 \<otimes> a"
  assumes scale_assoc: "\<And> (r1 :: real) (r2 :: real) (a :: 'a). (r1 * r2) \<otimes> a = r1 \<otimes> (r2 \<otimes> a)"
  assumes scale_prop1: "\<And> (r :: real) (a :: 'a). (r \<noteq> 0  \<Longrightarrow> (to_dom (abs r \<otimes> a) /\<^sub>R \<llangle>r \<otimes> a\<rrangle>) = ((to_dom a) /\<^sub>R \<llangle>a\<rrangle>))" 
  assumes gyroauto_property: "\<And> (u :: 'a) (v :: 'a) (r :: real) (a :: 'a). gyr u v (r \<otimes> a) = r \<otimes> (gyr u v a)"
  assumes gyroauto_id: "\<And> (r1 :: real) (r2 :: real) (v :: 'a). gyr (r1 \<otimes> v) (r2 \<otimes> v) = id"
  assumes homogeneity: "\<And> (r :: real) (a :: 'a).  (\<llangle>r \<otimes> a\<rrangle>) = (to_real ((abs r) \<otimes> (of_real (\<llangle>a\<rrangle>))))"
  assumes gyrotriangle: "\<And> (a :: 'a) (b :: 'a). \<llangle>(a \<oplus> b)\<rrangle> \<le> to_real ((of_real (\<llangle>a\<rrangle>)) \<oplus> (of_real (\<llangle>b\<rrangle>)))"
begin

abbreviation add_real (infixl "\<oplus>\<^sub>R" 100) where 
  "add_real r1 r2 \<equiv> to_real (of_real r1 \<oplus> of_real r2)"

abbreviation mult_real (infix "\<otimes>\<^sub>R" 100) where
  "mult_real r a \<equiv> to_real (r \<otimes> of_real a)"

thm gyrotriangle
thm homogeneity

lemma scale_minus1: 
  shows "(-1) \<otimes> a = \<ominus> a"
  by (metis add.right_inverse add_cancel_right_left gyrogroup_class.gyro_left_cancel' gyrogroup_class.gyro_right_id scale_1 scale_distrib)

lemma minus_norm: 
  shows "\<llangle>\<ominus>a\<rrangle> = \<llangle>a\<rrangle>"
proof-
   have "-1\<noteq>(0::int)"
    by simp
  have " (to_dom (abs (-1) \<otimes> a) /\<^sub>R \<llangle>(-1) \<otimes> a\<rrangle>) = ((to_dom a) /\<^sub>R \<llangle>a\<rrangle>)"
    using scale_prop1 
    by (metis zero_neq_neg_one)
  then show ?thesis 
    using gyrodom.to_dom_zero_iff gyrodom_axioms scale_1 scale_minus1 by fastforce
qed

text \<open>(6.3)\<close>
lemma scale_minus: 
  shows "(-r) \<otimes> a = \<ominus> (r \<otimes> a)"
  by (metis minus_mult_commute mult_1 scale_assoc scale_minus1)

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
  by (metis gyrogroup_class.gyro_left_cancel' gyrogroup_class.gyro_right_id gyronorm_def norm_zero_iff real_normed_vector_class.norm_zero to_dom_zero)

lemma gyrodistance_metric_sym:
  shows "d\<^sub>\<oplus> a b = d\<^sub>\<oplus> b a"
  by (metis gyrodistance_def gyrogroup_class.gyro_inv_idem gyrogroup_class.gyrominus_def gyrogroup_class.gyroplus_inv minus_norm norm_gyr)

lemma gyrodistance_gyrotriangle:
  shows "d\<^sub>\<oplus> a c \<le> d\<^sub>\<oplus> a b  \<oplus>\<^sub>R d\<^sub>\<oplus> b c"
proof-
  have "\<llangle>\<ominus>a \<oplus> c\<rrangle> = \<llangle>(\<ominus>a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus>b \<oplus> c)\<rrangle>"
    using gyro_polygonal_addition_lemma by auto
  also have "... \<le>  (\<llangle>\<ominus>a \<oplus> b\<rrangle>) \<oplus>\<^sub>R (\<llangle>gyr (\<ominus>a) b (\<ominus>b \<oplus> c)\<rrangle>)"
    by (simp add: gyrotriangle)
  finally show ?thesis
    unfolding gyrodistance_def norm_gyr
    by meson
qed

lemma equation_solving:
  assumes "x\<oplus>y = a" "\<ominus> x \<oplus> y = b"
  shows "x = (1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<and> y = (1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b"
proof-
  have "y= x \<oplus> b"
    using assms(2) local.gyro_equation_right by auto
  moreover have "a=x \<oplus> ( x \<oplus> b)"
    using assms(1) calculation by auto
  moreover have "a=(2\<otimes>x)\<oplus> b"
    using assms(1) calculation(1) local.gyro_left_assoc times2 by auto
  moreover have "x = (1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b)"
    by (metis (no_types, opaque_lifting) calculation(3) div_self divide_divide_eq_right gyrogroup_class.gyro_equation_left scale_1 scale_assoc times_divide_eq_left zero_neq_numeral)
  ultimately show ?thesis 
    by presburger
qed

lemma I6_33:
  shows "(1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) = (-1/2::real) \<otimes> (b \<ominus>\<^sub>c\<^sub>b a) "
  by (metis (no_types, opaque_lifting) div_by_1 divide_divide_eq_right divide_minus1 gyrogroup_class.gyro_equation_left gyrogroup_class.gyro_left_cancel' scale_assoc scale_minus1 times_divide_eq_left)

lemma I6_34:
  shows "(1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b  = (1/2::real) \<otimes> (b \<ominus>\<^sub>c\<^sub>b a) \<oplus> a "
proof -
  have f1: "\<And>a aa. 2 \<otimes> a \<oplus> aa = a \<oplus> (a \<oplus> aa)"
    by (simp add: local.gyro_left_assoc times2)
  have "\<And>a. 2 \<otimes> ((1 / 2) \<otimes> a) = a"
    by (metis (no_types) equation_solving gyrogroup_class.cogyro_right_cancel' gyrogroup_class.gyro_right_id mult.commute scale_assoc times2)
  then show ?thesis
    using f1 by (smt (z3) equation_solving gyrogroup_class.cogyro_right_cancel' local.gyro_equation_right scale_minus)
qed


lemma I6_35:
  shows "gyr b a = gyr b ((1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b) \<circ> (gyr ((1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b) \<oplus> b) a)"
proof-
  obtain "x" "y" where "x\<oplus>y = a \<and> \<ominus> x \<oplus> y = b"
    by (metis (no_types, opaque_lifting) I6_34 gyrogroup_class.coautomorphic_inverse gyrogroup_class.cogyrominus_def gyrogroup_class.gyro_inv_idem gyrogroup_class.gyro_left_cancel' mult_minus_right scale_1 scale_assoc scale_minus)
  moreover have "x\<oplus>y = a"
    by (simp add: calculation)
  moreover have "\<ominus> x \<oplus> y = b"
    by (simp add: calculation(1))

  moreover have "gyr b a = gyr  (\<ominus> x \<oplus> y ) (x\<oplus>y)"
    by (simp add: calculation(2) calculation(3))
  moreover have " gyr  (\<ominus> x \<oplus> y ) (x\<oplus>y) =  gyr (\<ominus> x \<oplus> y) y \<circ> gyr y (x \<oplus> y)"
    using local.gyr_master_misc2'' by blast
  moreover have " gyr (\<ominus> x \<oplus> y) y \<circ> gyr y (x \<oplus> y) =  gyr b ((1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b)\<oplus> b)\<circ> (gyr ((1/2::real) \<otimes> (a \<ominus>\<^sub>c\<^sub>b b)\<oplus> b) a )" 
    by (metis calculation(1) equation_solving)
  ultimately show ?thesis 
    by presburger
qed


lemma I6_38:
  shows " a \<oplus> (1/2::real) \<otimes> (\<ominus> a \<oplus>\<^sub>c b) = (1/2::real) \<otimes> (a \<oplus> b)"
proof -
  have f1: "\<And>r ra a. r \<otimes> (ra \<otimes> a) = ra \<otimes> (r \<otimes> a)"
    by (metis (full_types) mult.commute scale_assoc)
  then have "\<And>a. 2 \<otimes> ((1 / 2) \<otimes> a) = a"
    by (metis (no_types) equation_solving gyrogroup_class.cogyrominus_def gyrogroup_class.gyro_right_cancel'_dual gyrogroup_class.gyrominus_def local.gyro_left_cancel' local.gyro_rigth_inv times2)
  then show ?thesis
    using f1 by (smt (z3) gyrogroup_class.cogyro_commute_iff_gyrocommute gyrogroup_class.cogyro_right_cancel' gyrogroup_class.cogyrominus_def local.gyro_commute twosum)
qed


lemma I6_39:
  shows "a \<oplus> (1/2::real) \<otimes> (\<ominus> a \<oplus> b) = (1/2::real) \<otimes> (a \<oplus>\<^sub>c b)"
  by (metis I6_38 local.gyro_equation_right local.gyro_inv_idem)

lemma I6_40:
  shows "gyr ((r+s)\<otimes>a) b x = gyr (r\<otimes>a) (s\<otimes>a \<oplus> b) (gyr (s\<otimes>a) b x) "
  by (metis (mono_tags, opaque_lifting) comp_eq_elim gyroauto_id id_def local.gyr_nested_1 scale_distrib)

definition colinear :: "'a => 'a => 'a => bool" where
  "colinear x y z \<longleftrightarrow> (y = z \<or> (\<exists>t::real. (x = y \<oplus> t \<otimes> (\<ominus> y \<oplus> z))))"

lemma colinear_aab:
  shows "colinear a a b"
  by (metis colinear_def local.gyro_right_id local.gyro_rigth_inv scale_distrib scale_minus)

lemma colinear_bab:
  shows "colinear b a b"
  by (metis colinear_def local.gyro_equation_right scale_1)

lemma T6_20:
  assumes "colinear p1 a b" "colinear p2 a b" "a \<noteq> b" "p1 \<noteq> p2"
  shows "\<forall>x. (colinear x p1 p2 \<longrightarrow> colinear x a b)"
proof
  fix x
  show "colinear x p1 p2 \<longrightarrow> colinear x a b"
  proof-
    obtain "t1" where "p1 =  a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)"
      using assms(1) colinear_def 
      using assms(3) by auto
    moreover  obtain "t2" where "p2 =  a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
      using assms(2) colinear_def
      using assms(3) by blast
    moreover
    {
    assume "colinear x p1 p2"
    then have "colinear x a b"
    proof-
      obtain "t" where "x =  p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2)"
        using \<open>colinear x p1 p2\<close> colinear_def 
        using assms(4) by blast
      moreover have "x = ( a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b))  \<oplus> t \<otimes> (\<ominus> ( a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> (a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)))"
        by (simp add: \<open>p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)\<close> \<open>p2 = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)\<close> calculation)
      moreover have "x = ( a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b))  \<oplus> t  \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b))  ( t1 \<otimes>(\<ominus> (\<ominus> a \<oplus> b)) \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)) "
        by (metis \<open>p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)\<close> \<open>p2 = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)\<close> calculation(1) local.gyro_translation_2a mult.right_neutral mult_minus_right scale_assoc scale_minus scale_minus1)
     
      moreover have "x = ( a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b))  \<oplus> t  \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b))  (  (-t1 + t2) \<otimes> (\<ominus> a \<oplus> b)) "
        using \<open>p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)\<close> \<open>p2 = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)\<close> calculation(1) local.gyro_translation_2a scale_distrib scale_minus by presburger
      moreover have "x = ( a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b))  \<oplus>  gyr a (t1 \<otimes> (\<ominus> a \<oplus> b))  (  (t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b))"
        using calculation(4) gyroauto_property scale_assoc by presburger
      moreover have "x =  a \<oplus> (t1 \<otimes> (\<ominus> a \<oplus> b)  \<oplus>   (  (t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b)))"
        by (simp add: calculation(5) local.gyro_left_assoc)
      moreover have "x =   a \<oplus> (t1 + t*(-t1 + t2)) \<otimes> (\<ominus> a \<oplus> b)"
          using calculation(6) scale_distrib by auto
      ultimately  show ?thesis 
          using colinear_def by blast
    qed
    }
    ultimately show ?thesis 
      by blast
  qed
qed


lemma T6_20_1:
   assumes "colinear p1 a b" "colinear p2 a b" "p1 \<noteq> p2"  "a \<noteq> b"
   shows "\<forall>x. (colinear x a b \<longrightarrow> colinear x p1 p2)"
proof
  fix x
  show "colinear x a b \<longrightarrow> colinear x p1 p2"
  proof-
    obtain "t1" where "p1 =  a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)"
    using assms(1) colinear_def 
    using assms(4) by blast
    moreover  obtain "t3" where "p2 =  a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)"
      using assms(2) colinear_def 
      using assms(4) by blast
    moreover {
      assume "colinear x a b"
      then have "colinear x p1 p2" 
      proof-
          obtain "t2" where "x= a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)"
            using \<open>colinear x a b\<close> colinear_def
            using assms(4) by blast
          moreover have "t3\<noteq>t1 \<or> t3 = t1" by blast
          moreover {
            assume "t3=t1" 
            then have ?thesis 
              using \<open>p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)\<close> \<open>p2 = a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)\<close> assms(3) by blast
          } moreover {
            assume "t3\<noteq>t1"
            then obtain "t" where "t = (t2-t1)/(t3-t1)" 
              by simp
            moreover have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (  a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> (\<ominus> ( a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> ( a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)))"
              using \<open>p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)\<close> \<open>p2 = a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)\<close> by blast
             
            moreover have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) =  (  a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus> t \<otimes> gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) (t1 \<otimes> (\<ominus>  (\<ominus> a \<oplus> b)) \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b) )"
              by (metis \<open>p1 = a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)\<close> \<open>p2 = a \<oplus> t3 \<otimes> (\<ominus> a \<oplus> b)\<close> local.gyro_inv_idem local.gyro_translation_2a mult_minus_right scale_assoc scale_minus scale_minus1)
           
            moreover have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = (  a \<oplus> t1 \<otimes> (\<ominus> a \<oplus> b)) \<oplus>  gyr a (t1 \<otimes> (\<ominus> a \<oplus> b)) (( (-t1+t3)*t) \<otimes> (\<ominus> a \<oplus> b) )"
              by (metis (no_types, opaque_lifting) calculation(3) gyroauto_property minus_mult_commute mult.commute mult.right_neutral scale_assoc scale_distrib scale_minus1)
          
            moreover have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) =  a \<oplus>  ( t1 \<otimes> (\<ominus> a \<oplus> b)  \<oplus>  ( (-t1+t3)*t) \<otimes> (\<ominus> a \<oplus> b)) "
              using calculation(4) local.gyro_left_assoc by presburger

            moreover have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = a \<oplus> (t1 +  (-t1+t3)*t) \<otimes> ( (\<ominus> a \<oplus> b))"
              using calculation(5) scale_distrib by presburger
            moreover have "t1 +  (-t1+t3)*t = t2"
              by (simp add: \<open>t3 \<noteq> t1\<close> calculation(1))
            moreover have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) =  a \<oplus> t2 \<otimes>  (\<ominus> a \<oplus> b) "
              using calculation(6) calculation(7) by blast
            moreover have "p1 \<oplus> t \<otimes> (\<ominus> p1 \<oplus> p2) = x"
              using \<open>x = a \<oplus> t2 \<otimes> (\<ominus> a \<oplus> b)\<close> calculation(8) by blast
            ultimately have ?thesis
              using colinear_def by blast
          }
              
          ultimately show ?thesis by blast
      qed
    }
    ultimately show ?thesis 
      by blast
  qed
qed

lemma colinear_sym1:
  assumes "colinear a b c"
  shows "colinear b a c"
  using T6_20_1 assms colinear_aab colinear_bab colinear_def by blast

lemma colinear_sym2:
  assumes "colinear a b c"
  shows "colinear a c b"
  by (metis T6_20 assms colinear_aab colinear_bab)

lemma colinear_transitive:
  assumes "colinear a b c" "colinear d b c" "b \<noteq> c"
  shows "colinear a d b" 
  by (metis T6_20 assms(1) assms(2) assms(3) colinear_bab colinear_sym1 colinear_sym2)
    
definition gyroline :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "gyroline a b = {x. colinear x a b}"

end
  
end
