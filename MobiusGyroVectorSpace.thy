theory MobiusGyroVectorSpace
imports Main MobiusGyroGroup  GyroVectorSpace GammaFactor HyperbolicFunctions
begin

(* --------------------------------------------------------- *)

lift_definition inner_p :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> real" (infixl "\<cdot>" 100) is inner
  done

lift_definition norm_p :: "PoincareDisc \<Rightarrow> real"  ("\<llangle>_\<rrangle>" [100] 100) is norm
  done

lemma norm_lt_one:
  shows "\<llangle>u\<rrangle> < 1"
  by transfer simp

lemma norm_geq_zero:
  shows "\<llangle>u\<rrangle> \<ge> 0"
  by transfer simp

lemma square_norm_inner:
  shows "(\<llangle>u\<rrangle>)\<^sup>2 = u \<cdot> u"
  by transfer (simp add: dot_square_norm)

interpretation Mobius_gyrodom': gyrodom' where
  to_dom = to_complex and
  of_dom = of_complex and
  in_dom = "\<lambda> z. cmod z < 1" 
rewrites
  "Mobius_gyrodom'.gyroinner = inner_p" and
  "Mobius_gyrodom'.gyronorm = norm_p"
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

  show "gyrodom'.gyroinner to_complex = (\<cdot>)"
    apply rule
    apply rule
    unfolding gyrodom'.gyroinner_def[OF *]
    apply transfer
    by (simp add: inner_complex_def)

  show "gyrodom'.gyronorm to_complex = norm_p"
    apply rule
    unfolding gyrodom'.gyronorm_def[OF *]
    apply transfer
    by simp
qed

(* --------------------------------------------------------- *)

lemma moebius_gyroauto:
  shows "m_gyr u v a \<cdot> m_gyr u v b = a \<cdot> b"
proof-
  have "m_gyr u v a \<cdot> m_gyr u v b = Re((cnj (to_complex (m_gyr u v a))) * (to_complex (m_gyr u v b)))"
    using inner_p.rep_eq
    by (simp add: inner_complex_def)
  moreover have "m_gyr u v a = of_complex(((1 + (to_complex u) * cnj (to_complex v)) / (1 + (cnj (to_complex u)) * to_complex v)) *
    (to_complex a))"
    by (metis Mobius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
  moreover have "m_gyr u v b = of_complex(((1 + (to_complex u) * cnj (to_complex v)) / (1 + (cnj (to_complex u)) * to_complex v)) *
    (to_complex b))"
    by (metis Mobius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
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
      using  cmod_mix_cnj[OF * **] 
      by force
    ultimately show ?thesis using cnj_cmod_1
      by (metis mult.commute)
  qed
  moreover have "m_gyr u v a \<cdot> m_gyr u v b = Re((cnj (to_complex a))*(to_complex b))"
    using calculation(1) calculation(5) m_gyr'_def m_gyr.rep_eq by force
  moreover have "a \<cdot> b = Re((cnj (to_complex a))*(to_complex b))"
    by (simp add: inner_complex_def inner_p.rep_eq)
  ultimately show ?thesis
    by presburger
qed

interpretation Mobius_gyrodom: gyrodom to_complex of_complex "\<lambda> z. cmod z < 1"
proof
  fix u v a b
  have "gyr u v a \<cdot> gyr u v b = a \<cdot> b"
    by (simp add: gyr_PoincareDisc_def moebius_gyroauto)
  then show "gyrodom'.gyroinner to_complex (gyr u v a) (gyr u v b) =
             gyrodom'.gyroinner to_complex a b"  
    using Mobius_gyrodom'.gyrodom'_axioms Mobius_gyrodom'.gyroinner_def gyrodom'.gyroinner_def by fastforce
qed

(* --------------------------------------------------------- *)
definition otimes'_k :: "real \<Rightarrow> complex \<Rightarrow> real" where
  "otimes'_k r z = ((1 + cmod z) powr r - (1 - cmod z) powr r) /
                   ((1 + cmod z) powr r + (1 - cmod z) powr r)" 

lemma otimes'_k_tanh: 
  assumes "cmod z < 1"
  shows "otimes'_k r z = tanh (r * artanh (cmod z))"
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
    unfolding otimes'_k_def tanh_real_altdef artanh_def
    by (simp add: powr_minus_divide)
qed

lemma cmod_otimes'_k: 
  assumes "cmod z < 1"
  shows "cmod (otimes'_k r z) < 1"
  by (smt assms divide_less_eq_1_pos divide_minus_left otimes'_k_def norm_of_real powr_gt_zero zero_less_norm_iff)

definition otimes' :: "real \<Rightarrow> complex \<Rightarrow> complex" where
  "otimes' r z = (if z = 0 then 0 else cor (otimes'_k r z) * (z / cmod z))"

lemma cmod_otimes':
  assumes "cmod z < 1"
  shows "cmod (otimes' r z) = abs (otimes'_k r z)"
proof (cases "z = 0")
  case True
  thus ?thesis
    by (simp add: otimes'_def otimes'_k_def)
next
  case False
  hence "cmod (cor (otimes'_k r z)) = abs (otimes'_k r z)"
    by simp
  then show ?thesis
    using False
    unfolding otimes'_def
    by (simp add: norm_divide norm_mult)
qed

lift_definition otimes :: "real \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" (infixl "\<otimes>" 105) is otimes'
  using cmod_otimes' cmod_otimes'_k by auto

lemma otimes_distrib_lemma':
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

lemma otimes_distrib_lemma:
  assumes "cmod a < 1"
  shows "otimes'_k (r1 + r2) a = m_oplus' (otimes'_k r1 a) (otimes'_k r2 a)"
  unfolding otimes'_k_def m_oplus'_def
  unfolding powr_add
  apply (subst otimes_distrib_lemma')
  apply (smt powr_gt_zero powr_non_neg)
  apply (smt powr_gt_zero powr_non_neg)
  apply simp
  done

lemma otimes_distrib:
  shows "(r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus>\<^sub>m r2 \<otimes> a" 
proof transfer
  fix r1 r2 a
  assume "cmod a < 1"
  show "otimes' (r1 + r2) a = m_oplus' (otimes' r1 a) (otimes' r2 a)"
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: otimes'_def m_oplus'_def)
  next
    case False
    let ?p = "1 + cmod a" and ?m = "1 - cmod a"
    have "cor (otimes'_k (r1 + r2) a) * a / cor (cmod a) = 
          m_oplus' (otimes'_k r1 a) (otimes'_k r2 a) * a / cor (cmod a)"
      by (simp add: \<open>cmod a < 1\<close> otimes_distrib_lemma)
    moreover
    have "cor (otimes'_k r1 a) * cnj a * (cor (otimes'_k r2 a) * a) / (cor (cmod a) * cor (cmod a)) = 
          cor (otimes'_k r1 a) * cor (otimes'_k r2 a)"
      by (smt False complex_mod_cnj complex_mod_mult_cnj complex_norm_square mult.commute nonzero_mult_div_cancel_left norm_mult of_real_mult times_divide_times_eq zero_less_norm_iff)
    ultimately
     show ?thesis
      using False
      unfolding otimes'_def m_oplus'_def
      by (smt complex_cnj_complex_of_real complex_cnj_divide complex_cnj_mult distrib_right times_divide_eq_left times_divide_eq_right times_divide_times_eq)
  qed      
qed

lemma otimes_assoc:
  shows "(r1 * r2) \<otimes> a = r1 \<otimes> (r2 \<otimes> a)"
proof transfer
  fix r1 r2 a
  assume "cmod a < 1"
  show "otimes' (r1 * r2) a = otimes' r1 (otimes' r2 a)"
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: otimes'_def)
  next
    case False
    show ?thesis
    proof (cases "r2 = 0")
      case True
      thus ?thesis
        by (simp add: \<open>cmod a < 1\<close> otimes'_def otimes'_k_tanh)
    next
      case False
      let ?a2 = "otimes' r2 a"
      let ?k2 = "otimes'_k r2 a"
      have "cmod ?a2 = abs ?k2"
        using \<open>cmod a < 1\<close> cmod_otimes'
        by blast
      hence "cmod ?a2 < 1"
        using \<open>cmod a < 1\<close> cmod_otimes'_k
        by auto
      have "(1 + cmod a) / (1 - cmod a) > 1"
        using `a \<noteq> 0`
        by (simp add: \<open>cmod a < 1\<close>)
      hence "artanh (cmod a) > 0"
        by (simp add: artanh_def)
      hence "?k2 \<noteq> 0"
        using `cmod a < 1` `a \<noteq> 0` otimes'_k_tanh[of a r2] `r2 \<noteq> 0`
        by auto
      hence "?a2 \<noteq> 0"
        using `a \<noteq> 0`
        unfolding otimes'_def
        by simp
      have "sgn ?k2 = sgn r2"
        using otimes'_k_tanh[OF `cmod a < 1`, of r2]
        by (smt \<open>0 < artanh (cmod a)\<close> \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> \<open>?a2 \<noteq> 0\<close> mult_nonneg_nonneg mult_nonpos_nonneg sgn_neg sgn_pos tanh_0 tanh_real_neg_iff zero_less_norm_iff)
      have "otimes' r1 (otimes' r2 a) = 
             cor (otimes'_k r1 (cor ?k2 * a / cor (cmod a))) *
             (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using False `?a2 \<noteq> 0`
        using \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> 
        unfolding otimes'_def
        by auto
      also have "... = cor (tanh (r1 * \<bar>r2 * artanh (cmod a)\<bar>)) *  
                 (cor ?k2 * a) / (cor (cmod a) * abs ?k2)"
        using cmod_otimes'[of a r2] `cmod a < 1` `a \<noteq> 0`
        unfolding otimes'_def
        using \<open>cmod ?a2 < 1\<close> \<open>cmod ?a2 = \<bar>?k2\<bar>\<close> otimes'_k_tanh 
        using \<open>cmod a < 1\<close> otimes'_k_tanh[of a r2]
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
        by (simp add: \<open>cmod a < 1\<close> otimes'_def otimes'_k_tanh)
    qed
  qed
qed

lemma otimes_scale_prop:
  fixes r :: real
  assumes "r \<noteq> 0"
  shows "to_complex (\<bar>r\<bar> \<otimes> a) / \<llangle>r \<otimes> a\<rrangle>  = to_complex a / \<llangle>a\<rrangle>"
proof-
  let ?f = "\<lambda> r a. tanh (r * artanh (cmod (to_complex a)))"

  have *: "to_complex (\<bar>r\<bar> \<otimes> a) = ?f \<bar>r\<bar> a * (to_complex a / \<llangle>a\<rrangle>)"
    using Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc otimes'_def otimes'_k_tanh otimes.rep_eq
    by force
  then have "\<llangle>r \<otimes> a\<rrangle> = cmod (?f r a * (to_complex a / \<llangle>a\<rrangle>))"
    by (metis (no_types, lifting) Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc cmod_otimes' otimes'_def otimes'_k_tanh otimes.rep_eq mem_Collect_eq norm_mult norm_of_real)
  then have "\<llangle>r \<otimes> a\<rrangle> = \<bar>?f r a / \<llangle>a\<rrangle>\<bar> * cmod (to_complex a)"
    by (metis (no_types, opaque_lifting) norm_mult norm_of_real of_real_divide times_divide_eq_left times_divide_eq_right)

  have "?f \<bar>r\<bar> a = tanh(\<bar>r\<bar> * \<bar>artanh (cmod (to_complex a))\<bar>)"
    by (smt (verit) Rep_PoincareDisc artanh_nonneg mem_Collect_eq norm_ge_zero)
  then have "?f \<bar>r\<bar> a = \<bar>?f r a\<bar>"
    by (metis abs_mult tanh_real_abs)

  have "\<bar>?f r a / \<llangle>a\<rrangle>\<bar> = ?f \<bar>r\<bar> a / \<llangle>a\<rrangle>"
    by (metis Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_divide abs_le_self_iff abs_mult_pos abs_norm_cancel artanh_nonneg dual_order.refl mem_Collect_eq  tanh_real_abs)
  then have **:"?f \<bar>r\<bar> a / \<llangle>a\<rrangle> = \<bar>?f r a / \<llangle>a\<rrangle>\<bar>"
    by simp

  show ?thesis
  proof (cases "to_complex a = 0")
    case True
    then show ?thesis
      using assms
      by (simp add: otimes'_def otimes.rep_eq)
  next
    case False
    then have "\<bar>?f r a / \<llangle>a\<rrangle>\<bar> \<noteq>0"
      using assms
      by (metis artanh_0 Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_norm_cancel artanh_not_0 artanh_tanh_real divide_eq_0_iff linorder_not_less mem_Collect_eq mult_eq_0_iff norm_eq_zero not_less_iff_gr_or_eq zero_less_abs_iff)
    then show ?thesis
      using * ** Mobius_gyrodom'.gyronorm_def 
            \<open>\<llangle>r \<otimes> a\<rrangle> = \<bar>?f r a / \<llangle>a\<rrangle>\<bar> * cmod (to_complex a)\<close> 
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
  shows "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>) = 
         \<gamma> (to_complex a) *  
         \<gamma> (to_complex b) * 
         cmod (1 + cnj (to_complex a) * (to_complex b))"
proof-
  let ?a = "to_complex a" and ?b = "to_complex b"
  have "norm (\<llangle>a \<oplus>\<^sub>m b\<rrangle>) < 1"
    using Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_square_less_1
    by fastforce
  then have *: "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>) = 
                1 / sqrt(1 - cmod (?a+?b) / cmod (1 + cnj ?a *?b) * cmod (?a+?b) / cmod (1 + cnj ?a *?b))"
    using Mobius_gyrodom'.gyronorm_def gamma_factor_def m_oplus'_def m_oplus.rep_eq norm_divide norm_eq_zero norm_le_zero_iff norm_of_real real_norm_def 
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
  shows "\<gamma> (\<llangle>a \<oplus>\<^sub>m b\<rrangle>) \<le> \<gamma> (to_complex ((of_complex (\<llangle>a\<rrangle>)) \<oplus>\<^sub>m (of_complex (\<llangle>b\<rrangle>))))"
proof-
  have "\<gamma> (to_complex ((of_complex (\<llangle>a\<rrangle>)) \<oplus>\<^sub>m (of_complex (\<llangle>b\<rrangle>)))) =
        \<gamma> (\<llangle>a\<rrangle>) * \<gamma> (\<llangle>b\<rrangle>) * (1 + \<llangle>a\<rrangle> * \<llangle>b\<rrangle>)"
  proof-
    let ?expr1 =  "((\<llangle>a\<rrangle>) + (\<llangle>b\<rrangle>)) / (1 + (\<llangle>a\<rrangle>)*(\<llangle>b\<rrangle>))"
    let ?expr2 = "to_complex (of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>))"
    have *: "?expr1 = ?expr2"
      using Mobius_gyrodom'.gyronorm_def Mobius_gyrodom'.to_dom Rep_PoincareDisc m_oplus'_def m_oplus.rep_eq
      by auto

    have **: "norm (\<llangle>a\<rrangle>) < 1" "norm (\<llangle>b\<rrangle>) < 1"
      using Rep_PoincareDisc abs_square_less_1 norm_p.rep_eq 
      by fastforce+
    then have ***: "\<gamma> (\<llangle>a\<rrangle>) = 1 / sqrt(1 - (\<llangle>a\<rrangle>) * (\<llangle>a\<rrangle>))"
                   "\<gamma> (\<llangle>b\<rrangle>) = 1 / sqrt(1 - (\<llangle>b\<rrangle>) * (\<llangle>b\<rrangle>))"
      unfolding gamma_factor_def
      by (auto simp add: power2_eq_square) 

    have "\<gamma> ?expr1 = 1 / sqrt(1 - ((cmod (?expr1)) * cmod(?expr1)))"
      using * **
      by (metis Rep_PoincareDisc gamma_factor_def mem_Collect_eq power2_eq_square)
    moreover
    have "cmod ?expr1 = ?expr1"
      by (smt (verit, ccfv_threshold) Mobius_gyrodom'.gyronorm_def mult_less_0_iff norm_divide norm_not_less_zero norm_of_real of_real_1 of_real_add of_real_divide of_real_mult)
    ultimately
    have "\<gamma> ?expr1 = 1 / sqrt (1 - (Re ?expr1 * Re ?expr1))"
       by (metis Re_complex_of_real)
    then have "\<gamma> ?expr1 = (1 + \<llangle>a\<rrangle>*\<llangle>b\<rrangle>) / (sqrt (1-\<llangle>a\<rrangle>*\<llangle>a\<rrangle>) * sqrt (1-\<llangle>b\<rrangle>*\<llangle>b\<rrangle>))"
       using Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc gamma_factor_ineq1_lemma
       using \<open>cmod ?expr1 = ?expr1\<close> 
       by force

    then show ?thesis
      using \<open>?expr1 = ?expr2\<close> ***
      by simp
  qed

  moreover

  have "\<gamma> (\<llangle>a\<rrangle>) * \<gamma> (\<llangle>b\<rrangle>) * (1 + \<llangle>a\<rrangle>*\<llangle>b\<rrangle>) \<ge> 
        \<gamma> (to_complex a) * \<gamma> (to_complex b) * cmod (1  + cnj (to_complex a) * (to_complex b))"
  proof-
    have *: "\<gamma> (\<llangle>a\<rrangle>) = \<gamma> (to_complex a)"
            "\<gamma> (\<llangle>b\<rrangle>) = \<gamma> (to_complex b)"
       by (auto simp add: Mobius_gyrodom'.gyronorm_def gamma_factor_def)
     
     have "cmod (1 + cnj (to_complex a) * (to_complex b)) \<le> 
           cmod 1 + cmod (cnj (to_complex a) * (to_complex b))"
       using norm_triangle_ineq
       by blast
     also have "\<dots> = 1 + cmod (to_complex a) * cmod (to_complex b)"
       by (simp add: norm_mult)
     also have "\<dots> = 1 + \<llangle>a\<rrangle>*\<llangle>b\<rrangle>"
       using Mobius_gyrodom'.gyronorm_def
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
  shows "\<llangle>a \<oplus>\<^sub>m b\<rrangle> \<le> \<llangle>of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>)\<rrangle>"
proof (cases "to_complex a = - to_complex b")
  case True
  then show ?thesis
   by (simp add: Mobius_gyrodom'.gyronorm_def m_oplus'_def m_oplus.rep_eq)
next
  case False
  let ?e1 = "(\<llangle>a \<oplus>\<^sub>m b\<rrangle>)"
  let ?e2 = "cmod (to_complex (of_complex (\<llangle>a\<rrangle>) \<oplus>\<^sub>m of_complex (\<llangle>b\<rrangle>)))"
  have "?e1 > 0"
    by (smt (verit, best) Mobius_gyrodom'.gyronorm_def \<open>to_complex a \<noteq> - to_complex b\<close> ab_left_minus add_right_cancel divide_eq_0_iff gamma_factor_eq1 gamma_factor_positive m_oplus'_def m_oplus.rep_eq norm_eq_zero norm_le_zero_iff of_real_0 zero_less_mult_iff)
  moreover
  have "?e2 > 0"
    by (metis Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc \<open>0 < \<llangle>a \<oplus>\<^sub>m b\<rrangle>\<close> dual_order.refl gamma_factor_increasing gamma_factor_ineq1 linorder_not_le mem_Collect_eq of_real_0 zero_less_norm_iff)
  moreover
  have "?e1 < 1" "?e2 < 1"
    using Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc 
    by auto
  ultimately 
  show ?thesis
    using gamma_factor_increase_reverse[of ?e1 ?e2]
    by (smt (verit, best) gamma_factor_def gamma_factor_increasing gamma_factor_ineq1 norm_p.rep_eq norm_of_real)
qed

lemma moebius_gyroauto_norm:
  shows "\<llangle>m_gyr a b v\<rrangle> = \<llangle>v\<rrangle>"
  using Mobius_gyrodom.norm_gyr gyr_PoincareDisc_def
  by auto

lemma otimes_homogenity:
  shows "\<llangle>(r \<otimes> a)\<rrangle> = cmod (to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>)))"
proof (cases "a = 0\<^sub>m")
  case True
  then show ?thesis
    using Mobius_gyrodom'.gyronorm_def otimes'_def otimes.rep_eq m_ozero'_def m_ozero.rep_eq m_ozero_def
    by force
next
  case False
  have "\<llangle>(r \<otimes> a)\<rrangle> = \<bar>tanh (r * artanh (\<llangle>a\<rrangle>))\<bar>"
    using Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc cmod_otimes' otimes'_k_tanh otimes.rep_eq
    by force
  moreover
  have "to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>)) = tanh (\<bar>r\<bar> * artanh (\<llangle>a\<rrangle>))"
  proof-
    have "to_complex (\<bar>r\<bar> \<otimes> of_complex (\<llangle>a\<rrangle>)) = 
          otimes'_k \<bar>r\<bar> (\<llangle>a\<rrangle>) * ((\<llangle>a\<rrangle>) / cmod (\<llangle>a\<rrangle>))" 
      using otimes_def otimes'_def
      using Mobius_gyrodom'.gyronorm_def Mobius_gyrodom'.to_dom Rep_PoincareDisc otimes.rep_eq
      by force 
    moreover
    have "cmod (cmod (to_complex a)) = cmod (to_complex a)"
      by simp
    then have "(\<llangle>a\<rrangle>) / cmod (\<llangle>a\<rrangle>) = 1"
      using \<open>a \<noteq> 0\<^sub>m\<close>
      by (metis Mobius_gyrodom'.gyronorm_def Mobius_gyrodom'.of_dom divide_self_if m_ozero'_def m_ozero_def norm_eq_zero)
    ultimately
    have "to_complex (\<bar>r\<bar> \<otimes> ( of_complex (cor(\<llangle>a\<rrangle>)))) = cor (otimes'_k \<bar>r\<bar> (cor (\<llangle>a\<rrangle>)))"
      by auto
    then show ?thesis
      using Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc otimes'_k_tanh
      by auto
  qed
  moreover 
  have "\<bar>tanh(r * artanh (cmod (to_complex a))) / \<llangle>a\<rrangle>\<bar> = 
         tanh (\<bar>r\<bar> * artanh (cmod (to_complex a))) / \<llangle>a\<rrangle>"
    by (metis Mobius_gyrodom'.gyronorm_def Rep_PoincareDisc abs_divide abs_le_self_iff abs_mult_pos abs_norm_cancel artanh_nonneg dual_order.refl mem_Collect_eq  tanh_real_abs)
  ultimately 
  show ?thesis
    by (smt (verit, best) norm_of_real real_compex_cmod tanh_real_abs)
qed

lemma m_gyr_gyrospace:
  shows "m_gyr (r1 \<otimes> v) (r2 \<otimes> v) = id"
proof-
  have "m_gyr' (to_complex (r1 \<otimes> v)) (to_complex (r2 \<otimes> v)) = id"
  proof-
    let ?v = "to_complex v"
    let ?e1 = "?v * tanh (r1 * artanh (cmod ?v)) /cmod(to_complex v)"
    let ?e2 = "?v * tanh (r2 * artanh (cmod ?v)) /cmod(to_complex v)"

    have "to_complex (r1 \<otimes> v) = ?e1"
         "to_complex (r2 \<otimes> v) = ?e2"
      using Rep_PoincareDisc otimes'_def otimes'_k_tanh otimes.rep_eq
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
        using \<open>to_complex (r1 \<otimes> v) = ?e1\<close> \<open>to_complex (r2 \<otimes> v) = ?e2\<close>
        by (metis Rep_PoincareDisc  div_by_0 divide_eq_1_iff mem_Collect_eq cmod_mix_cnj norm_zero)
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

lemma m_gyr_gyrospace2:
  shows "m_gyr u v (r \<otimes> a) = r \<otimes> (m_gyr u v a)"
proof-
  let ?u = "to_complex u" and ?v = "to_complex v" and ?a = "to_complex a"
  let ?e1 = "m_gyr u v a"
  let ?e2 = "cmod (to_complex ?e1)"

  have "?e1 = of_complex ((1 + ?u * cnj ?v) / (1 + cnj ?u *?v) * ?a)"
    by (metis Mobius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq)
  then have "?e2 = cmod ((1 + ?u * cnj ?v) / (1 + cnj ?u *?v)) * cmod ?a"
    by (metis m_gyr'_def m_gyr.rep_eq norm_mult)
  then have "?e2 = cmod ?a"
    using Mobius_gyrodom'.gyronorm_def moebius_gyroauto_norm 
    by presburger
  then have "r \<otimes> ?e1 = of_complex (((1+cmod ?a) powr r - (1-cmod ?a) powr r) /
                                    ((1+cmod ?a) powr r + (1-cmod ?a) powr r) * to_complex ?e1 / ?e2)"
    using otimes_def 
    by (metis (no_types, lifting) Mobius_gyrodom'.of_dom otimes'_def otimes'_k_def otimes.rep_eq mult_eq_0_iff times_divide_eq_right)
  then have "r \<otimes> ?e1 = of_complex (to_complex (r \<otimes> a) * ((1 + ?u * cnj ?v) / (1 + cnj ?u * ?v)))"
    using otimes_def
    using \<open>?e2 = cmod ?a\<close>
    by (smt (verit, ccfv_threshold) Mobius_gyrodom'.of_dom  ab_semigroup_mult_class.mult_ac(1) m_gyr'_def m_gyr.rep_eq otimes'_def otimes'_k_def otimes.rep_eq mult.commute mult_eq_0_iff times_divide_eq_right)
  then show ?thesis 
    by (metis Mobius_gyrodom'.of_dom m_gyr'_def m_gyr.rep_eq mult.commute)
qed


interpretation Mobius_gyrovector_space:
 gyrovector_space of_complex "\<lambda> z. cmod z < 1" to_complex otimes "of_complex \<circ> cor" "cmod \<circ> to_complex"
proof
  fix a :: PoincareDisc
  show "1 \<otimes> a = a"
    by transfer (auto simp add: otimes'_def otimes'_k_def)
next
  fix r1 r2 a
  show "(r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus> r2 \<otimes> a"
    using gyroplus_PoincareDisc_def otimes_distrib by auto
next
  fix r1 r2 a
  show "(r1 * r2) \<otimes> a = r1 \<otimes> (r2 \<otimes> a)"
    by (simp add: otimes_assoc)
next
  fix r :: real and a
  assume "r \<noteq> 0" 
  then show "to_complex (abs r \<otimes> a) /\<^sub>R gyrodom'.gyronorm to_complex (r \<otimes> a) =
             to_complex a /\<^sub>R  gyrodom'.gyronorm to_complex a"
    using otimes_scale_prop[of r a]
    by (metis Mobius_gyrodom'.gyrodom'_axioms Mobius_gyrodom'.gyronorm_def divide_inverse_commute gyrodom'.gyronorm_def of_real_inverse scaleR_conv_of_real)
next
  fix u v r a
  have "m_gyr u v (r \<otimes> a) = r \<otimes> m_gyr u v a"
    using m_gyr_gyrospace2 
    by auto
  then show "gyr u v (r \<otimes> a) = r \<otimes> gyr u v a"
    using gyr_PoincareDisc_def by auto
next
  fix r1 r2 v
  have "m_gyr (r1 \<otimes> v) (r2 \<otimes> v) = id"
    using m_gyr_gyrospace
    by simp
  then show "gyr (r1 \<otimes> v) (r2 \<otimes> v) = id"
    by (simp add: gyr_PoincareDisc_def)
next
  fix r a
  show "gyrodom'.gyronorm to_complex (r \<otimes> a) =
           (cmod \<circ> to_complex)
            (\<bar>r\<bar> \<otimes> (of_complex \<circ> cor) (gyrodom'.gyronorm to_complex a))"
    using otimes_homogenity[of r a]
    using Mobius_gyrodom'.gyrodom'_axioms Mobius_gyrodom'.gyronorm_def gyrodom'.gyronorm_def by fastforce   
next
  fix a b
  show " gyrodom'.gyronorm to_complex (a \<oplus> b)
           \<le> (cmod \<circ> to_complex)
               ((of_complex \<circ> cor) (gyrodom'.gyronorm to_complex a) \<oplus>
                (of_complex \<circ> cor) (gyrodom'.gyronorm to_complex b))"
    using moebius_triangle[of a b]
    using Mobius_gyrodom'.gyrodom'_axioms Mobius_gyrodom'.gyronorm_def gyrodom'.gyronorm_def gyroplus_PoincareDisc_def by fastforce 
qed

(* ---------------------------------------------------------------------------- *)

definition m_gyr_general :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
  "m_gyr_general u v w = \<ominus>\<^sub>m(u\<oplus>\<^sub>mv) \<oplus>\<^sub>m (u \<oplus>\<^sub>m(v \<oplus>\<^sub>m w))"

lemma m_gyr_general_m_gyr:
  shows "m_gyr_general u v w = m_gyr u v w"
  by (simp add: Mobius_gyrogroup.gyr_def m_gyr_general_def)

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

lemma times2_m: "2 \<otimes> u = u \<oplus>\<^sub>m u"
  using Mobius_gyrovector_space.times2 gyroplus_PoincareDisc_def
  by simp

lift_definition m_gammma_factor :: "PoincareDisc \<Rightarrow> real" ("\<gamma>\<^sub>m") is gamma_factor
  done

definition half' :: "complex \<Rightarrow> complex" where
  "half' v = (\<gamma> v / (1 + \<gamma> v)) *\<^sub>R v"

lift_definition half :: "PoincareDisc \<Rightarrow> PoincareDisc" is half'
  unfolding half'_def
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
  shows "2 \<otimes> (half v) = v"
proof-
  have "2 \<otimes> (half v) = half v \<oplus>\<^sub>m half v"
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
    finally show "m_oplus' (half' v) (half' v) = v"
      unfolding m_oplus'_def half'_def
      using * \<open>1 + cnj (?k * v) * (?k * v) = 1 + ?k\<^sup>2 * (cmod v)\<^sup>2\<close>
      by (smt (verit)  mult_eq_0_iff nonzero_mult_div_cancel_left of_real_eq_0_iff power2_eq_square scaleR_conv_of_real scaleR_left_distrib)
  qed
  finally show ?thesis
    .
qed

lemma half:
  shows "half v = (1/2) \<otimes> v"
  by (metis Mobius_gyrovector_space.scale_assoc mult_2 real_scaleR_def scaleR_half_double two_times_half)

lemma half':
  assumes "cmod u < 1"
  shows "otimes' (1/2) u = half' u"
  using assms half half.rep_eq[of "of_complex u"] otimes.rep_eq
  by (simp add: Mobius_gyrodom'.to_dom)


definition double' :: "complex \<Rightarrow> complex" where
  "double' v = (2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1)) *\<^sub>R v"

lemma double'_cmod:
  assumes "cmod v < 1"
  shows "2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1) = 2 / (1 + (cmod v)\<^sup>2)" (is "?lhs = ?rhs")
proof-
  have **: "1 - (cmod v)\<^sup>2 > 0"
    using assms
    by (simp add: power_less_one_iff)

  have "?lhs = 2 * (1 / (1 - (cmod v)\<^sup>2)) / (2 * (1 / (1 - (cmod v)\<^sup>2)) - 1)"
    using gamma_factor_square_norm[OF assms]
    by simp
  also have "\<dots> = 2 / (1 + (cmod v)\<^sup>2)"
  proof-
    have "2 * (1 / (1 - (cmod v)\<^sup>2)) = 2 / (1 - (cmod v)\<^sup>2)"
      by simp
    moreover
    have "2 * (1 / (1 - (cmod v)\<^sup>2)) - 1 = 2 / (1 - (cmod v)\<^sup>2) -  (1 - (cmod v)\<^sup>2) / (1 - (cmod v)\<^sup>2)"
      using **
      by simp
    then have "2 * (1 / (1 - (cmod v)\<^sup>2)) - 1 = (1 + (cmod v)\<^sup>2) / (1 - (cmod v)\<^sup>2)"
      using **
      by (simp add: field_simps)
    ultimately
    show ?thesis
      using **
      by (smt (verit, del_insts) divide_divide_eq_left nonzero_mult_div_cancel_left power2_eq_square times_divide_eq_right)
  qed
  finally show ?thesis
    .
qed

lemma cmod_double':
  assumes "cmod v < 1"
  shows "cmod (double' v) = 2*cmod v / (1 + (cmod v)\<^sup>2)"
proof-
  have "cmod (double' v) = 
        abs(2 * (\<gamma> v)\<^sup>2 / (2 * (\<gamma> v)\<^sup>2 - 1)) * cmod v"
    unfolding double'_def
    by simp
  also have "\<dots> = abs (2 / (1 + (cmod v)\<^sup>2)) * cmod v"
    using assms double'_cmod 
    by presburger
  also have "\<dots> = 2*cmod v / (1 + (cmod v)\<^sup>2)"
  proof-
    have "2 / (1 + (cmod v)\<^sup>2) > 0"
      by (metis half_gt_zero_iff power_one sum_power2_gt_zero_iff zero_less_divide_iff zero_neq_one)
    then show ?thesis
      by simp
  qed
  finally show ?thesis
    .
qed

lift_definition double :: "PoincareDisc \<Rightarrow> PoincareDisc" is double'
proof-
  fix v
  assume *: "cmod v < 1"

  have "cmod (double' v) = 2 * cmod v / (1 + (cmod v)\<^sup>2)"
    using * cmod_double'
    by simp
  also have "\<dots> < 1"
  proof-
    have "(1 - cmod v)\<^sup>2 > 0"
      using *
      by simp
    then have "1 - 2* cmod v + (cmod v)\<^sup>2 > 0"
      by (simp add: field_simps power2_eq_square)
    then have "2*cmod v < 1 + (cmod v)\<^sup>2"
      by simp
    moreover
    have "1 + (cmod v)\<^sup>2 > 0"
      by (smt (verit) not_sum_power2_lt_zero)
    ultimately
    show ?thesis
      using divide_less_eq_1 by blast
  qed
  finally
  show "cmod (double' v) < 1"
    by simp
qed

lemma double'_otimes'_2:
  assumes "cmod v < 1"
  shows "double' v = otimes' 2 v"
proof-
  have "v * 2 / (1 + cor (cmod v) * cor (cmod v)) =
        v * 4 / (2 + 2 * (cor (cmod v) * cor (cmod v)))"
    by (metis (no_types, lifting) mult.left_commute nonzero_mult_divide_mult_cancel_left numeral_Bit0_eq_double numeral_One ring_class.ring_distribs(1) zero_neq_numeral)
  then show ?thesis
    using assms
    unfolding double'_def otimes'_def otimes'_k_def double'_cmod[OF assms] scaleR_conv_of_real
    by (auto simp add: field_simps power2_eq_square)
qed

lemma double: 
  shows "double u = 2 \<otimes> u"
  by transfer (simp add: double'_otimes'_2)

end