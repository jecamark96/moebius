theory VectorSpace
  imports Main HOL.Real
begin

locale vector_space_with_domain =
  fixes dom :: "'a set"
    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"      
    and zero :: "'a"
    and smult :: "real \<Rightarrow> 'a \<Rightarrow> 'a"   
  assumes add_closed: "\<lbrakk>x \<in> dom; y \<in> dom\<rbrakk> \<Longrightarrow> add x y \<in> dom" 
    and zero_in_dom: "zero \<in> dom"      
    and add_assoc: "\<lbrakk>x \<in> dom; y \<in> dom; z\<in> dom\<rbrakk> \<Longrightarrow>add (add x y) z = add x (add y z)"
    and add_comm: "\<lbrakk>x \<in> dom; y \<in> dom\<rbrakk> \<Longrightarrow> add x y = add y x"
    and add_zero: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow> add x zero = x"
    and add_inv: "x \<in> dom \<Longrightarrow> \<exists>y \<in> dom. add x y = zero"
    and smult_closed: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow> smult a x \<in> dom"
    and smult_distr_sadd: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow>smult (a + b) x = add (smult a x) (smult b x)"
    and smult_assoc: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow> smult a  (smult b x) = smult (a * b)  x"
    and smult_one: "\<lbrakk>x \<in> dom\<rbrakk> \<Longrightarrow> smult 1 x = x" 

end