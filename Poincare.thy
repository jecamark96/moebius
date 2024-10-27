theory Poincare
  imports Complex_Main
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

end