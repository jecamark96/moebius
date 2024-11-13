theory Poincare
  imports Complex_Main "HOL-Analysis.Inner_Product"
begin

typedef PoincareDisc = "{z::complex. cmod z < 1}"
  by (rule_tac x=0 in exI, auto)

setup_lifting type_definition_PoincareDisc

abbreviation to_complex :: "PoincareDisc \<Rightarrow> complex" where 
  "to_complex \<equiv> Rep_PoincareDisc" 
abbreviation of_complex :: "complex \<Rightarrow> PoincareDisc" where 
  "of_complex \<equiv> Abs_PoincareDisc" 

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

lift_definition inner_p :: "PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> real" (infixl "\<cdot>" 100) is inner
  done

lift_definition norm_p :: "PoincareDisc \<Rightarrow> real"  ("\<llangle>_\<rrangle>" [100] 101) is norm
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

end