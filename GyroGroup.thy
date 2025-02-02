theory GyroGroup
  imports Main 
begin

class gyrogroupoid = 
  fixes gyrozero :: "'a" ("0⇩g")
  fixes gyroplus :: "'a ⇒ 'a ⇒ 'a" (infixl "⊕" 100)
begin
definition gyroaut :: "('a ⇒ 'a) ⇒ bool" where
  "gyroaut f ⟷ 
       (∀ a b. f (a ⊕ b) = f a ⊕ f b) ∧ 
       bij f"
end

class gyrogroup = gyrogroupoid +
  fixes gyroinv :: "'a ⇒ 'a" ("⊖")
  fixes gyr :: "'a ⇒ 'a ⇒ 'a ⇒ 'a"
  assumes gyro_left_id [simp]: "⋀ a. 0⇩g ⊕ a = a"
  assumes gyro_left_inv [simp]: "⋀ a. ⊖a ⊕ a = 0⇩g"
  assumes gyro_left_assoc: "⋀ a b z. a ⊕ (b ⊕ z) = (a ⊕ b) ⊕ (gyr a b z)"
  assumes gyr_left_loop: "⋀ a b. gyr a b = gyr (a ⊕ b) b"
  assumes gyr_gyroaut: "⋀ a b. gyroaut (gyr a b)"
begin

definition gyrominus :: "'a ⇒ 'a ⇒ 'a" (infixl "⊖⇩b" 100) where
  "a ⊖⇩b b = a ⊕ (⊖ b)"

end


context gyrogroup
begin

lemma gyr_distrib [simp]:
  "gyr a b (x ⊕ y) = gyr a b x ⊕ gyr a b y"
  by (metis gyroaut_def gyr_gyroaut)

lemma gyr_inj:
  assumes "gyr a b x = gyr a b y"
  shows "x = y"
  using assms
  by (metis UNIV_I bij_betw_iff_bijections gyr_gyroaut gyroaut_def)

text ‹Def 2.7, (2.2)›
definition cogyroplus (infixr "⊕⇩c" 100) where
  "a ⊕⇩c b = a ⊕ (gyr a (⊖b) b)"

definition cogyrominus :: "'a ⇒ 'a ⇒ 'a" (infixl "⊖⇩c⇩b" 100) where
  "a ⊖⇩c⇩b b = a ⊕⇩c (⊖ b)"

definition cogyroinv ("⊖⇩c") where
  "⊖⇩c a = 0⇩g ⊖⇩c⇩b a"

text ‹Thm 2.8, (1)›
lemma gyro_left_cancel:
  assumes "a ⊕ b = a ⊕ c"
  shows "b = c"
  using assms
(*  by (metis gyr_inj local.gyro_left_assoc local.gyro_left_id local.gyro_left_inv) *)
proof-
  from assms
  have "(⊖a) ⊕ (a ⊕ b) = (⊖a) ⊕ (a ⊕ c)"
    by simp
  then have "(⊖a ⊕ a) ⊕ gyr (⊖a) a b = (⊖a ⊕ a) ⊕ gyr (⊖a) a c"
    using gyro_left_assoc
    by simp
  then have "gyr (⊖a) a b = gyr (⊖a) a c"
    by simp
  then show "b = c"
    using gyr_inj
    by blast
qed


text ‹Thm 2.8, (2)›

definition gyro_is_left_id where
  "gyro_is_left_id z ⟷ (∀ x. z ⊕ x = x)"

lemma gyro_is_left_id_0 [simp]:
  shows "gyro_is_left_id 0⇩g"
  by (simp add: gyro_is_left_id_def)

lemma gyr_id_1':
  assumes "gyro_is_left_id z"
  shows "gyr z a = id"
  using assms
  unfolding gyro_is_left_id_def
  by (metis eq_id_iff gyro_left_cancel gyro_left_assoc)

lemma gyr_id_1 [simp]:
  shows "gyr 0⇩g a = id"
  using gyr_id_1'[of "0⇩g"]
  by simp

text ‹Thm 2.8, (3)›

definition gyro_is_left_inv where
  "gyro_is_left_inv x a ⟷ x ⊕ a = 0⇩g"

definition gyro_is_right_inv where
  "gyro_is_right_inv x a ⟷ a ⊕ x = 0⇩g"

lemma gyro_is_left_inv [simp]:
  shows "gyro_is_left_inv (⊖a) a"
  by (simp add: gyro_is_left_inv_def)

lemma gyr_inv_1':
  assumes "gyro_is_left_inv x a"
  shows "gyr x a = id"
  using assms gyr_left_loop[of x a]
  by (simp add: gyro_is_left_inv_def)

lemma gyr_inv_1 [simp]:
  shows "gyr (⊖a) a = id"
  using gyr_left_loop[of "⊖a" a]
  by simp

text ‹Thm 2.8, (4)›
lemma gyr_id [simp]:
  shows "gyr a a = id"
  by (metis gyr_id_1 gyr_left_loop gyro_left_id)

text ‹Thm 2.8, (5)›
lemma gyro_right_id [simp]:
  shows "a ⊕ 0⇩g = a"
proof-
  have "⊖a ⊕ (a ⊕ 0⇩g) = ⊖a ⊕ a"
    using gyro_left_assoc
    by simp
  thus ?thesis
    using gyro_left_cancel[of "⊖a"]
    by simp
qed

lemma gyro_inv_id [simp]: "⊖ 0⇩g = 0⇩g"
  by (metis gyro_left_inv gyro_right_id)

text ‹Thm 2.8, (6)›
lemma gyro_left_id_unique:
  assumes "gyro_is_left_id z"
  shows "z = 0⇩g"
proof-
  have "0⇩g = z ⊕ 0⇩g"
    using assms
    by (metis gyro_is_left_id_def)
  thus ?thesis
    using gyro_right_id[of z]
    by simp
qed

text ‹Thm 2.8, (7)›
lemma gyro_left_inv_right_inv:
  assumes "gyro_is_left_inv x a"
  shows "gyro_is_right_inv x a"
  using assms
  by (metis gyr_inv_1' gyro_left_cancel gyro_right_id id_apply gyro_is_left_inv_def gyro_is_right_inv_def gyro_left_assoc)

lemma gyro_rigth_inv [simp]:
  shows "a ⊕ (⊖a) = 0⇩g"
  using gyro_is_right_inv_def gyro_left_inv_right_inv
  by simp

text ‹Thm 2.8, (8)›
lemma
  assumes "gyro_is_left_inv x a"
  shows "x = ⊖a"
  using assms
  by (metis gyr_inv_1 id_apply gyro_is_left_inv_def gyro_left_assoc gyro_left_id gyro_left_inv)

text ‹Thm 2.8, (9)›
lemma gyro_left_cancel':
  shows "⊖ a ⊕ (a ⊕ b) = b"
  by (simp add: gyro_left_assoc)

text ‹Thm 2.8, (10)›
lemma gyr_def:
  shows "gyr a b x = ⊖ (a ⊕ b) ⊕ (a ⊕ (b ⊕ x))"
  by (metis gyro_left_cancel' gyro_left_assoc)

text ‹Thm 2.8, (11)›
lemma gyr_id_3:
  shows "gyr a b 0⇩g = 0⇩g"
  by (simp add: gyr_def)

text ‹Thm 2.8, (12)›
lemma gyr_inv_3:
  shows "gyr a b (⊖x) = ⊖ (gyr a b x)"
  by (metis gyroaut_def gyr_gyroaut gyr_id_3 gyro_left_cancel gyro_rigth_inv)

text ‹Thm 2.8, (13)›
lemma gyr_id_2 [simp]:
  shows "gyr a 0⇩g = id"
  by (metis gyro_left_cancel eq_id_iff gyro_left_assoc gyro_left_id gyro_right_id)

lemma gyr_distrib_gyrominus: 
  shows "gyr a b (c ⊖⇩b d) = gyr a b c ⊖⇩b gyr a b d"
  by (metis gyroaut_def gyr_gyroaut gyr_inv_3 gyrominus_def)

lemma gyro_inv_idem [simp]: 
  shows "⊖ (⊖ a) = a"
  by (metis gyr_inv_1 gyro_left_cancel gyro_left_assoc gyro_left_id gyro_left_inv)

lemma gyr_inv_2 [simp]:
  shows "gyr a (⊖ a) = id"
  using gyr_inv_1[of "⊖a"]
  by simp

text ‹(2.3.a)›
lemma cogyro_left_id:
  shows "0⇩g ⊕⇩c a = a"
  by (simp add: cogyroplus_def gyr_id_3)

text ‹(2.3.b)›
lemma cogyro_rigth_id:
  shows "a ⊕⇩c 0⇩g = a"
  by (simp add: cogyroplus_def gyr_id_3)

text ‹(2.4)›
lemma cogyrominus:
  shows "a ⊖⇩c⇩b b = a ⊖⇩b gyr a b b"
  by (simp add: cogyrominus_def cogyroplus_def gyr_inv_3 gyrominus_def)

text ‹(2.7)›
lemma cogyro_right_inv:
  shows "a ⊕⇩c (⊖⇩c a) = 0⇩g"
  by (metis cogyroinv_def cogyrominus_def cogyroplus_def gyr_inv_2 gyro_inv_idem gyro_right_id gyro_rigth_inv iso_tuple_update_accessor_eq_assist_idI gyr_left_loop gyro_left_assoc update_accessor_accessor_eqE)

text ‹(2.6)›
lemma cogyro_left_inv:
  shows "(⊖⇩c a) ⊕⇩c a = 0⇩g"
  by (metis cogyroinv_def cogyro_left_id cogyrominus_def cogyro_right_inv gyro_inv_idem)

text ‹(2.8)›
lemma cogyro_gyro_inv: 
  shows "⊖⇩c a = ⊖ a"
  by (simp add: cogyroinv_def cogyro_left_id cogyrominus_def)

text ‹Thm 2.9, (2.9)›
lemma gyr_nested_1:
  shows "gyr a (b ⊕ c) ∘ gyr b c = gyr (a ⊕ b) (gyr a b c) ∘ gyr a b" (is "?lhs = ?rhs")
proof
  fix x

  have "a ⊕ (b ⊕ (c ⊕ x)) = (a ⊕ b) ⊕ gyr a b (c ⊕ x)"
    by (simp add: gyro_left_assoc[of a b])
  also have "... = (a ⊕ b ⊕ (gyr a b c ⊕ gyr a b x))"
    by simp
  also have "... = ((a ⊕ b) ⊕ gyr a b c) ⊕ gyr (a ⊕ b) (gyr a b c) (gyr a b x)"
    by (simp add: gyro_left_assoc)
  also have "... = (a ⊕ (b ⊕ c)) ⊕ gyr (a ⊕ b) (gyr a b c) (gyr a b x)"
    by (simp add: gyro_left_assoc)
  finally 
  have 1: "a ⊕ (b ⊕ (c ⊕ x)) = (a ⊕ (b ⊕ c)) ⊕ gyr (a ⊕ b) (gyr a b c) (gyr a b x)"
    .


  have "a ⊕ (b ⊕ (c ⊕ x)) = a ⊕ (b ⊕ c ⊕ gyr b c x)"
    by (simp add: gyro_left_assoc)
  also have "... = (a ⊕ (b ⊕ c)) ⊕ gyr a (b ⊕ c) (gyr b c x)"
    by (simp add: gyro_left_assoc)
  finally have 2: "a ⊕ (b ⊕ (c ⊕ x)) = (a ⊕ (b ⊕ c)) ⊕ gyr a (b ⊕ c) (gyr b c x)"
    .

  have "gyr (a ⊕ b) (gyr a b c) (gyr a b x) = gyr a (b ⊕ c) (gyr b c x)"
    using 1 2
    by (metis gyro_left_cancel')

  thus "?lhs x = ?rhs x"
    by simp
qed

text ‹Thm 2.9, (2.15)›
lemma gyr_nested_1': 
  shows "gyr (a ⊕ b) (⊖ (gyr a b b)) ∘ gyr a b = id"
  by (metis comp_id gyr_inv_2 gyr_inv_3 gyr_nested_1 gyr_id_2 gyro_rigth_inv)

text ‹Thm 2.9, (2.10)›
lemma gyr_nested_2: 
  shows "gyr a (⊖ (gyr a b b)) ∘ gyr a b = id"
proof-
  have "gyr (a ⊕ b) (gyr a b (⊖ b)) = gyr a (⊖ (gyr a b b))" 
    by (metis gyr_inv_3 gyro_left_assoc gyr_left_loop gyro_right_id gyro_rigth_inv)
  thus ?thesis
    using gyr_nested_1[of a b "⊖ b"]
    by simp
qed

text ‹Thm 2.9, (2.11)›
lemma gyr_auto_id1: 
  shows "gyr (⊖ a) (a ⊕ b) ∘ gyr a b = id"
  using gyr_nested_1[of "⊖ a" a b]
  by simp

text ‹Thm 2.9, (2.12)›
lemma gyr_auto_id2:
  shows "gyr b (a ⊕ b) ∘ gyr a b = id"
  by (metis gyr_auto_id1 gyro_left_cancel' gyr_left_loop)

text ‹Thm 2.10, (2.18)›
lemma gyro_plus_def_co:
  shows "a ⊕ b = a ⊕⇩c gyr a b b"
  by (simp add: cogyroplus_def gyr_nested_2 pointfree_idE)

text ‹Thm 2.11, (2.21)›
lemma gyro_polygonal_addition_lemma:
  shows "(⊖ a ⊕ b) ⊕ gyr (⊖a) b (⊖ b ⊕ c) = ⊖ a ⊕ c"
proof-
  have "gyr (⊖a) b (⊖ b ⊕ c) = gyr (⊖a) b (⊖ b) ⊕ gyr (⊖ a) b c"
    by simp
  hence "(⊖ a ⊕ b) ⊕ gyr (⊖a) b (⊖ b ⊕ c) = 
        (⊖ a ⊕ b) ⊕ (gyr (⊖a) b (⊖ b) ⊕ gyr (⊖ a) b c)"
    by simp
  also have "... = ((⊖ a ⊕ b) ⊖⇩b gyr (⊖ a) b b) ⊕ (gyr ((⊖ a) ⊕ b) (⊖ (gyr (⊖ a) b b)) ∘ gyr (⊖ a) b) c"
    by (metis calculation gyr_inv_3 gyr_nested_1' gyro_left_cancel' gyrominus_def gyro_right_id id_apply gyro_left_assoc)
  also have "... = (⊖ a ⊕ (b ⊖⇩b b)) ⊕ c"
    by (metis gyr_inv_3 gyr_nested_1' gyrominus_def id_apply gyro_left_assoc)
  also have "... = ⊖ a ⊕ c"
    by (simp add: gyrominus_def)
  finally
  show ?thesis
    .
qed

text ‹Thm 2.12, (2.23)›
lemma gyro_translation_1:
  shows "⊖ (⊖a ⊕ b) ⊕ (⊖a ⊕ c) = gyr (⊖ a) b (⊖b ⊕ c)"
  by (metis gyr_def gyro_left_cancel')

text ‹Thm 3.13, (3.33a)›
lemma gyro_translation_2a:
  shows "⊖ (a ⊕ b) ⊕ (a ⊕ c) = gyr a b (⊖b ⊕ c)"
  by (metis gyr_def gyro_left_cancel')

definition gyro_polygonal_add ("⊕⇩p") where
  "⊕⇩p a b c = (⊖ a ⊕ b) ⊕ gyr (⊖ a) b (⊖ b ⊕ c)"

(* ----------------------- *)

text ‹Thm 2.15, (2.34, 2.35)›
lemma gyro_equation_right:
  shows "a ⊕ x = b ⟷ x = ⊖a ⊕ b"
  by (metis gyro_left_cancel')

text ‹Thm 2.15, (2.36, 2.37)›
lemma gyro_equation_left:
  shows "x ⊕ a = b ⟷ x = b ⊖⇩c⇩b a"
  by (metis cogyrominus gyr_def gyr_inv_3 gyro_equation_right gyrominus_def gyro_right_id gyr_left_loop)

lemma oplus_ominus_cancel [simp]:
  shows "y = x ⊕ (⊖ x ⊕ y)"
  by (metis local.gyro_equation_right)

text ‹(2.39)›
lemma cogyro_right_cancel':
  shows "(b ⊖⇩c⇩b a) ⊕ a = b"
  by (simp add: gyro_equation_left)

text ‹(2.40)›
lemma gyro_right_cancel'_dual:
  shows "(b ⊖⇩b a) ⊕⇩c a = b"
  by (metis cogyrominus_def gyro_equation_left gyro_inv_idem gyrominus_def)

(* ----------------------- *)

text ‹Thm 2.19 (2.48)›
lemma gyroaut_gyr_commute_lemma:
  assumes "gyroaut A"
  shows "A ∘ gyr a b = gyr (A a) (A b) ∘ A" (is "?lhs = ?rhs")
proof
  fix x
  have "(A a ⊕ A b) ⊕ (A ∘ gyr a b) x = A((a ⊕ b) ⊕ gyr a b x)"
    using assms gyroaut_def
    by auto
  also have "... = A (a ⊕ (b ⊕ x))"
    by (simp add: gyro_left_assoc)
  also have "... = A a ⊕ (A b ⊕ A x)"
    using assms gyroaut_def
    by auto
  also have "... = (A a ⊕ A b) ⊕ (gyr (A a) (A b) (A x))"
    by (simp add: gyro_left_assoc)
  finally
  show "?lhs x = ?rhs x"
    using gyro_left_cancel
    by auto
qed

text ‹Thm 2.20›
lemma gyroaut_gyr_commute: 
  assumes "gyroaut A"
  shows "gyr a b = gyr (A a) (A b) ⟷ A ∘ gyr a b = gyr a b ∘ A"
proof
  assume "gyr a b = gyr (A a) (A b)"
  thus "A ∘ gyr a b = gyr a b ∘ A"
    using gyroaut_gyr_commute_lemma[OF assms]
    by metis
next
  assume *: "A ∘ gyr a b = gyr a b ∘ A"
  have "gyr (A a) (A b) = A ∘ gyr a b ∘ (inv A)"
    using gyroaut_gyr_commute_lemma[OF assms, of a b]
    by (metis gyroaut_def assms bij_is_surj comp_id o_assoc surj_iff)
  also have "... = gyr a b"
    using *
    by (metis gyroaut_def assms bij_is_surj comp_assoc comp_id surj_iff)
  finally 
  show "gyr a b = gyr (A a) (A b)"
    by simp
qed

text ‹2.50›
lemma gyr_commute_misc_1:
  shows "gyr (gyr a b a) (gyr a b b) = gyr a b"
  by (metis gyroaut_gyr_commute gyr_gyroaut)

text ‹Thm 2.21 (2.52)›
definition
  "cogyroaut f ⟷ ((∀a b. f (a ⊕⇩c b) = f a ⊕⇩c f b) ∧ bij f)"

lemma gyro_coaut_iff_gyro_aut:
  shows "gyroaut f ⟷ cogyroaut f"
proof
  assume "gyroaut f"
  thus "cogyroaut f"
    unfolding gyroaut_def cogyroaut_def
    by (smt cogyroplus_def gyr_def gyro_left_cancel gyro_right_id gyro_rigth_inv)
next
  assume "cogyroaut f"
  thus "gyroaut f"
    unfolding gyroaut_def cogyroaut_def
    by (metis bij_pointE cogyro_left_id cogyrominus_def cogyro_rigth_id gyro_equation_left gyro_right_cancel'_dual gyro_left_id gyrominus_def)
qed


(* ----------------------- *)

text ‹Thm 2.25, (2.76)›
lemma gyroplus_inv:
  shows "⊖ (a ⊕ b) = gyr a b (⊖ b ⊖⇩b a)"
  by (metis gyr_def gyro_equation_right gyrominus_def gyro_rigth_inv)

text ‹Thm 2.25, (2.77)›
lemma inv_gyr:
  shows "inv (gyr a b) = gyr (⊖b) (⊖a)"
  by (metis fun.map_id0 gyr_auto_id2 gyr_inv_2 gyr_nested_1 gyro_left_cancel' gyrominus_def gyroplus_inv id_apply inv_unique_comp gyr_left_loop)

text ‹Thm 2.26, (2.86)›
lemma gyr_aut_inv_1:
  shows "inv (gyr a b) = gyr a (⊖ (gyr a b b))"
  by (metis comp_eq_dest_lhs eq_id_iff gyr_nested_2 inv_unique_comp)

text ‹Thm 2.26, (2.87)›
lemma gyr_aut_inv_2:
  shows "inv (gyr a b) = gyr (⊖ a) (a ⊕ b)"
  by (metis gyr_auto_id2 gyro_left_cancel' inv_unique_comp gyr_left_loop)

text ‹Thm 2.26, (2.88)›
lemma gyr_aut_inv_3:
  shows "inv (gyr a b) = gyr b (a ⊕ b)"
  by (metis gyr_auto_id2 gyro_left_cancel' inv_unique_comp gyr_left_loop)

text ‹Thm 2.26, (2.89)›
lemma gyr_1:
  shows "gyr a b = gyr b (⊖b ⊖⇩b a)"
  by (metis inv_gyr gyr_aut_inv_2 gyro_inv_idem gyrominus_def)

text ‹Thm 2.26, (2.90)›
lemma gyr_2:
  shows "gyr a b = gyr (⊖a) (⊖b ⊖⇩b a)"
  using inv_gyr gyr_aut_inv_3 gyrominus_def by auto

text ‹Thm 2.26, (2.91)›
lemma gyr_3:
  shows "gyr a b = gyr (⊖ (a ⊕ b)) a"
  by (metis gyr_1 gyro_inv_idem gyro_left_cancel' gyrominus_def)

text ‹Thm 2.27, (2.92)›
lemma gyr_even:
  shows "gyr (⊖ a) (⊖ b) = gyr a b"
  by (metis cogyro_right_cancel' gyr_aut_inv_3 inv_gyr local.gyr_left_loop)

text ‹Thm 2.27, (2.93)›
lemma inv_gyr_sym:
  shows "inv (gyr a b) = gyr b a"
  by (simp add: inv_gyr gyr_even)

text ‹Thm 2.27, (2.94a)›
lemma gyr_nested_3:
  shows "gyr b (⊖ (gyr b a a)) = gyr a b"
  using gyr_aut_inv_1 inv_gyr_sym
  by auto

text ‹Thm 2.27, (2.94b)›
lemma gyr_nested_4:
  shows "gyr b (gyr b (⊖ a) a) = gyr a (⊖ b)"
  by (metis gyr_aut_inv_1 inv_gyr_sym gyr_even gyro_inv_idem)

text ‹Thm 2.27, (2.94c)›
lemma gyr_nested_5:
  shows "gyr (⊖ (gyr a b b)) a = gyr a b"
  by (metis inv_gyr_sym gyr_nested_3)

text ‹Thm 2.27, (2.94d)›
lemma gyr_nested_6:
  shows "gyr (gyr a (⊖ b) b) a = gyr a (⊖ b)"
  by (metis inv_gyr inv_gyr_sym gyr_nested_4 gyro_inv_idem)

text ‹Thm 2.28, (i)›
lemma gyro_right_assoc:
  shows "(a ⊕ b) ⊕ c = a ⊕ (b ⊕ gyr b a c)"
  by (metis gyr_aut_inv_2 inv_gyr_sym gyro_equation_right gyro_left_assoc)

text ‹Thm 2.28, (ii)›
lemma gyr_right_loop:
  shows "gyr a b = gyr a (b ⊕ a)"
  using gyr_aut_inv_3 inv_gyr_sym by auto

text ‹Thm 2.29, (a)›
lemma gyr_left_coloop:
  shows "gyr a b = gyr (a ⊖⇩c⇩b b) b"
  by (metis cogyro_right_cancel' gyr_left_loop)

text ‹Thm 2.29, (b)›
lemma gyr_rigth_coloop:
  shows "gyr a b = gyr a (b ⊖⇩c⇩b a)"
  by (metis inv_gyr_sym gyr_left_coloop)

text ‹Thm 2.30, (2.101a)›
lemma gyr_misc_1:
  shows "gyr (a ⊕ b) (⊖ a) = gyr a b"
  by (metis gyr_aut_inv_2 inv_gyr_sym)

text ‹Thm 2.30, (2.101b)›
lemma gyr_misc_2:
  shows "gyr (⊖ a) (a ⊕ b) = gyr b a"
  using gyr_aut_inv_2 inv_gyr_sym by auto

text ‹Thm 2.31, (2.103)›
lemma coautomorphic_inverse:
  shows "⊖ (a ⊕⇩c b) = (⊖ b) ⊕⇩c (⊖ a)"
proof-
  have "a ⊕⇩c b = a ⊕ gyr a (⊖ b) b"
    by (simp add: cogyroplus_def)
  also have "... = ⊖ (gyr a (gyr a (⊖ b) b) (⊖ (gyr a (⊖ b) b) ⊖⇩b a))"
    by (metis gyro_inv_idem gyroplus_inv)
  also have "... = gyr a (⊖ (gyr a (⊖ b) (⊖b))) (⊖ (⊖ (gyr a (⊖ b) b) ⊖⇩b a))"
    by (simp add: gyr_inv_3)
  also have "... = (inv (gyr a (⊖ b))) (⊖ (⊖ (gyr a (⊖ b) b) ⊖⇩b a))"
    by (simp add: gyr_aut_inv_1)
  also have "... = ⊖ (⊖ b ⊖⇩b (inv (gyr a (⊖ b))) a)"
    by (metis cogyrominus cogyroplus_def inv_gyr_sym gyr_even gyr_inv_3 gyr_nested_3 gyro_equation_left gyro_inv_idem gyro_left_cancel' gyrominus_def cogyro_right_cancel' gyroplus_inv)
  also have "... = ⊖ ((⊖ b) ⊕⇩c (⊖ a))"
    by (simp add: cogyroplus_def inv_gyr_sym gyr_inv_3 gyrominus_def)
  finally 
  have "a ⊕⇩c b = ⊖ ((⊖ b) ⊕⇩c (⊖ a))"
    .
  thus ?thesis
    by simp
qed


text ‹Thm 2.32, (2.105a)›
lemma gyr_misc_3:
  shows "gyr a b b = ⊖ (⊖ (a ⊕ b) ⊕ a)"
  by (metis gyr_3 gyro_inv_idem gyro_left_cancel' gyrominus_def gyroplus_inv)

text ‹Thm 2.32, (2.105b)›
lemma gyr_misc_4: 
  shows "gyr a (⊖ b) b = ⊖ (a ⊖⇩b b) ⊕ a"
  by (simp add: gyr_def gyrominus_def)


text ‹Thm 2.35, (2.124)›
lemma mixed_gyroassoc_law: "(a ⊕⇩c b) ⊕ c = a ⊕ gyr a (⊖ b) (b ⊕ c)"
  by (metis (full_types) cogyroplus_def gyr_nested_6 gyro_right_assoc gyr_distrib)

(* ------------------------------------------------- *)

text ‹Thm 3.2›
lemma gyrocommute_iff_gyroatomorphic_inverse:
  shows "(∀ a b. ⊖ (a ⊕ b) = ⊖ a ⊖⇩b b) ⟷ (∀ a b. a⊕b = gyr a b (b ⊕ a))"
  by (metis gyr_even gyro_inv_idem gyrominus_def gyroplus_inv)

text ‹Thm 3.4›
lemma cogyro_commute_iff_gyrocommute: 
   "(∀ a b. a ⊕⇩c b = b ⊕⇩c a) ⟷ (∀ a b. a⊕b = gyr a b (b ⊕ a))" (is "?lhs ⟷ ?rhs")
proof-
  have "∀ a b. a ⊕⇩c b = b ⊕⇩c a ⟷ ⊖ (⊖b ⊖⇩b gyr b (⊖ a) a) = b ⊕ gyr b (⊖ a) a"
    by (metis coautomorphic_inverse cogyroplus_def gyr_even gyr_inv_3 gyro_inv_idem gyrominus_def)
  thus ?thesis
    by (smt (verit, ccfv_threshold) cogyroplus_def gyr_even gyro_equation_right gyro_inv_idem gyrominus_def gyro_right_cancel'_dual gyroplus_inv)
qed

end

class gyrocommutative_gyrogroup = gyrogroup + 
  assumes gyro_commute: "a ⊕ b = gyr a b (b ⊕ a)"
begin
lemma gyroautomorphic_inverse:
  shows "⊖ (a ⊕ b) = ⊖ a ⊖⇩b b"
  using gyro_commute gyrocommute_iff_gyroatomorphic_inverse 
  by blast

lemma cogyro_commute:
  shows "a ⊕⇩c b = b ⊕⇩c a"
  using cogyro_commute_iff_gyrocommute gyro_commute
  by blast

text ‹Thm 3.5 (3.15)›
lemma gyr_commute_misc_2:
  shows "gyr a b ∘ gyr (b ⊕ a) c = gyr a (b ⊕ c) ∘ gyr b c"
  by (metis gyr_gyroaut gyroaut_gyr_commute_lemma gyr_nested_1 gyro_commute)

text ‹Thm 3.6 (3.17, 3.18)›
lemma gyr_parallelogram:
  assumes "d = (b ⊕⇩c c) ⊖⇩b a"
  shows "gyr a (⊖ b) ∘ gyr b (⊖ c) ∘ gyr c (⊖ d) = gyr a (⊖ d)"
proof-
  have *: "∀ a' b' c'. gyr a' (b' ⊕ a') ∘ gyr (b' ⊕ a') c' = gyr a' (b' ⊕ c') ∘ gyr (b' ⊕ c') c'"
    using gyr_commute_misc_2 gyr_left_loop gyr_right_loop
    by auto
  let ?a' = "⊖ c"
  let ?c' = "⊖ a"
  let ?b' = "b ⊖⇩c⇩b ?a'"

  have "?b' ⊕ ?c' = d"
    by (simp add: assms cogyrominus_def gyrominus_def)
  moreover
  have "b ⊖⇩c⇩b ⊖ c ⊕ ⊖ c = b"
    by (simp add: cogyro_right_cancel')
  ultimately
  have "gyr (⊖ c) b ∘ gyr b (⊖ a) = gyr (⊖ c) d ∘ gyr d (⊖ a)"
    using  *[rule_format, of "?a'" "?b'" "?c'"]
    by simp
  then show ?thesis
    by (smt bij_is_inj gyroaut_def gyr_gyroaut inv_gyr_sym gyr_even gyro_inv_idem o_inv_distrib o_inv_o_cancel)
qed

text ‹Thm 3.8 (3.23, 3.24)›
lemma gyr_parallelogram_iff:
  "d = (b ⊖⇩c⇩b c) ⊖⇩b a ⟷ ⊖c ⊕ d = gyr c (⊖b) (b ⊖⇩b a)"
  oops

text ‹Thm 3.9 (3.26)›
lemma gyr_commute_misc_3:
  "gyr a b (b ⊕ (a ⊕ c)) = (a ⊕ b) ⊕ c"
  using gyr_distrib gyro_commute gyro_left_assoc gyro_right_assoc
  by (metis (no_types, lifting))

text ‹Thm 3.10 (3.28)›
lemma gyro_left_right_cancel:
  shows "(a ⊕ b) ⊖⇩b a = gyr a b b"
  by (metis gyroautomorphic_inverse gyr_misc_3 gyro_inv_idem)

text ‹Thm 3.11 (3.29)›
lemma cogyro_plus_def:
  shows "a ⊕⇩c b = a ⊕ ((⊖ a ⊕ b) ⊕ a)"
  by (metis cogyro_commute_iff_gyrocommute cogyroplus_def gyro_commute gyro_equation_right gyro_right_assoc)

text ‹Thm 3.12 (3.31)›
lemma cogyro_commute_misc1:
  shows "a ⊕⇩c (a ⊕ b) = a ⊕ (b ⊕ a)"
  by (simp add: cogyro_plus_def gyro_left_cancel')

text ‹Thm 3.13 (3.33b)›
lemma gyro_translation_2b:
  shows "(a ⊕ b) ⊖⇩b (a ⊕ c) = gyr a b (b ⊖⇩b c)"
  by (metis gyr_commute_misc_3 gyroautomorphic_inverse gyro_equation_right gyrominus_def)

text ‹Thm 3.14 (3.34)›

text ‹(3.37)›
lemma gyr_commute_misc_4':
  shows "gyr a (b ⊕ c) = gyr a b ∘ gyr (b ⊕ a) c ∘ gyr c b"
proof-
  have "gyr a b ∘ gyr (b ⊕ a) c = gyr (a ⊕ b) (gyr a b c) ∘ gyr a b"
    by (simp add: gyr_commute_misc_2 local.gyr_nested_1)
  hence "gyr a (b ⊕ c) ∘ gyr b c = gyr a b ∘ gyr (b ⊕ a) c"
    by (simp add: gyr_commute_misc_2)
  thus ?thesis
    by (metis comp_assoc comp_id local.gyr_auto_id2 local.gyr_right_loop)
qed

text ‹(3.38)›
lemma gyr_commute_misc_4'':
  shows "gyr (⊖b ⊕ d) (b ⊕ c) = gyr (⊖ b) d ∘ gyr d c ∘ gyr c b"
  by (metis gyr_commute_misc_4' local.gyr_misc_1 local.gyro_inv_idem local.gyro_left_cancel')

text ‹Thm 3.14 (3.34)›
lemma gyro_commute_misc_4:
  shows "gyr (⊖ a ⊕ b) (a ⊖⇩b c) = gyr a (⊖ b) ∘ gyr b (⊖ c) ∘ gyr c (⊖ a)"
  by (metis gyr_commute_misc_4' gyr_even gyr_misc_1 gyro_inv_idem gyro_left_cancel' gyrominus_def)

text ‹Thm 3.15 (3.40)›
lemma gyr_inv_2':
  shows "gyr a (⊖b) = gyr (⊖ a ⊕ b) (a ⊕ b) ∘ gyr a b"
  by (metis comp_id gyr_commute_misc_2 local.gyr_even local.gyr_id local.gyr_misc_1 local.gyro_inv_idem local.gyro_left_cancel')

text ‹Thm 3.17 (3.48)›
lemma gyr_master':
  shows "gyr a x ∘ gyr (⊖ (x ⊕ a)) (x ⊕ b) ∘ gyr x b = gyr (⊖ a) b"
  by (metis gyr_commute_misc_4' gyroautomorphic_inverse gyr_even gyr_misc_1 gyro_left_cancel' gyrominus_def)

text ‹(3.51)›
lemma gyr_master:
  shows "gyr a x ∘ gyr (x ⊕ a) (⊖ (x ⊕ b)) ∘ gyr x b = gyr (⊖ a) b"
  by (metis gyr_master' gyr_even gyro_inv_idem)

text ‹(3.52a)›
lemma gyr_master_misc1':
  shows "gyr (⊖ a) b = gyr (⊖ (a ⊕ a)) (a ⊕ b) ∘ gyr a b"
  by (metis fun.map_id gyr_master' local.gyr_id)

text ‹(3.52b)›
lemma gyr_master_misc1'':
  shows "gyr (⊖ a) b = gyr a b ∘ gyr (b ⊕ a) (⊖ (b ⊕ b))"
  by (metis comp_id gyr_master gyr_id)

text ‹(3.53a)›
lemma gyr_master_misc2':
  shows "gyr (⊖a ⊕ b) (a ⊕ b) = gyr (⊖ a) b ∘ gyr b a"
  by (simp add: gyr_commute_misc_4'')

text ‹(3.53b)›
lemma gyr_master_misc2'':
  shows "gyr (⊖a ⊕ b) (a ⊕ b) = gyr (⊖ a ⊕ b) b ∘ gyr b (a ⊕ b)"
  using gyr_master_misc2' local.gyr_left_loop local.gyr_right_loop
  by auto


text ‹Thm 3.18 (3.60)›
lemma "gyr a x ∘ gyr (⊖ (gyr x a (a ⊖⇩b b))) (x ⊕ b) ∘ gyr x b = gyr a (⊖ b)"
  by (metis gyr_master gyro_translation_2b gyr_even gyr_left_loop gyro_inv_idem gyrominus_def)

definition gyro_covariant :: "nat ⇒ ('a list ⇒ 'a) ⇒ bool" where
  "gyro_covariant n T ⟷ (∀ τ xs. length xs = n ∧ gyroaut τ ⟶ (τ (T xs)) = T (map τ xs)) ∧ 
                        (∀ x xs. length xs = n ⟶ x ⊕ T xs = T (map (λ a. x ⊕ a) xs))"

definition gyro_covariant_3 :: "('a ⇒ 'a ⇒ 'a ⇒ 'a) ⇒ bool" where
  "gyro_covariant_3 T ⟷ (∀ τ a b c. gyroaut τ ⟶ (τ (T a b c)) = T (τ a) (τ b) (τ c)) ∧ 
                          (∀ x a b c. x ⊕ T a b c = T (x ⊕ a) (x ⊕ b) (x ⊕ c))"

lemma gyro_covariant_3: 
  shows "gyro_covariant_3 T ⟷ gyro_covariant 3 (λ xs. T (xs ! 0) (xs ! 1) (xs ! 2))"
  unfolding gyro_covariant_3_def gyro_covariant_def
  apply safe
     apply simp
    apply simp
   apply (erule_tac x="τ" in allE, erule_tac x="[a, b, c]" in allE, simp)
  apply (erule_tac x="x" in allE, erule_tac x="[a, b, c]" in allE, simp)
  done

text ‹Thm 3.19 (3.62)›
lemma gyro_covariant_3_parallelogram:                
  shows "gyro_covariant_3 (λ a b c. (b ⊕⇩c c) ⊖⇩b a)"  
  unfolding gyro_covariant_3_def
proof safe
  fix τ a b c
  assume "gyroaut τ"
  then show "τ ((b ⊕⇩c c) ⊖⇩b a) = (τ b ⊕⇩c τ c) ⊖⇩b τ a"
    by (smt (verit, ccfv_threshold) cogyroaut_def gyro_coaut_iff_gyro_aut local.gyro_left_cancel' local.gyro_left_inv local.gyroaut_def local.gyrominus_def)
next
  fix x a b c
  have "((x ⊕ b) ⊕⇩c (x ⊕ c)) ⊖⇩b (x ⊕ a) = (x ⊕ b) ⊕ gyr (x ⊕ b) (⊖ (x ⊕ c)) ((x ⊕ c) ⊖⇩b (x ⊕ a))"
    by (simp add: gyrominus_def mixed_gyroassoc_law)
  also have "... = (x ⊕ b) ⊕ gyr (x ⊕ b) (⊖ (x ⊕ c)) (gyr x c (c ⊖⇩b a))"
    by (simp add: gyro_translation_2b)
  also have "... = x ⊕ (b ⊕ gyr b x (gyr (x ⊕ b) (⊖ (x ⊕ c)) (gyr x c (c ⊖⇩b a))))"
    using local.gyro_right_assoc by auto
  also have "... = x ⊕ (b ⊕ gyr b x (gyr x b (gyr b (⊖ c) (gyr c x (gyr x c (c ⊖⇩b a))))))"
    unfolding gyrominus_def
    using gyro_commute_misc_4[of "⊖ x" b c]
    by (simp add: gyroautomorphic_inverse local.gyr_even)
  also have "... = x ⊕ (b ⊕ gyr b (⊖ c) (c ⊖⇩b a))"
    by (metis local.gyr_auto_id2 local.gyr_right_loop pointfree_idE)
  finally show "x ⊕ ((b ⊕⇩c c) ⊖⇩b a) = ((x ⊕ b) ⊕⇩c (x ⊕ c)) ⊖⇩b (x ⊕ a)"
    using gyrominus_def mixed_gyroassoc_law 
    by auto
qed

lemma gyro_commute_misc6':
  shows "x ⊕ ((b ⊕⇩c c) ⊖⇩b a) = ((x ⊕ b) ⊕⇩c (x ⊕ c)) ⊖⇩b (x ⊕ a)"
  using gyro_covariant_3_parallelogram
  unfolding gyro_covariant_3_def
  by simp
  
text ‹(3.66)›
lemma gyro_commute_misc6:
  shows "(x ⊕ b) ⊕⇩c (x ⊕ c) = x ⊕ ((b ⊕⇩c c) ⊕ x)"
  using gyro_commute_misc6'[of x b c "⊖ x"]
  by (simp add: gyrominus_def)

text ‹(3.67)›
lemma gyro_commute_misc6'':
  shows "(x ⊕ b) ⊕⇩c (x ⊖⇩b b) = x ⊕ x"
  using gyro_commute_misc6 cogyro_gyro_inv cogyro_right_inv gyro_left_id gyrominus_def 
  by presburger

end

type_synonym 'a rooted_gyrovec = "'a × 'a"

context gyrogroup
begin

text ‹Def 5.2.›
fun head :: "'a rooted_gyrovec ⇒ 'a" where
  "head (p, q) = q"
fun tail :: "'a rooted_gyrovec ⇒ 'a" where
  "tail (p, q) = p"
fun val :: "'a rooted_gyrovec ⇒ 'a" where
  "val (p, q) = ⊖ p ⊕ q"
definition ort :: "'a ⇒ 'a rooted_gyrovec" where
  "ort p = (0⇩g, p)"

fun equiv_rooted_gyro_vec (infixl "∼" 100) where
  "(p, q) ∼ (p', q') ⟷ ⊖p ⊕ q = ⊖p' ⊕ q'"

lemma equivp_equiv_rooted_gyro_vec [simp]:
  shows "equivp (∼)"
  unfolding equivp_def
  by fastforce

end

text ‹Def 5.4.›
quotient_type (overloaded) 'a gyrovec = "'a :: gyrogroup × 'a" / equiv_rooted_gyro_vec
  by auto
                  
lift_definition vec :: "'a::gyrogroup ⇒ 'a ⇒ 'a gyrovec" is "λ p q. (p, q)"
  done

definition ort :: "'a::gyrogroup ⇒ 'a gyrovec" where
  "ort A = vec 0⇩g A"

context gyrocommutative_gyrogroup
begin

text ‹Thm 5.5. (5.4)›
lemma equiv_rooted_gyro_vec_ex_t:
  shows "(p, q) ∼ (p', q') ⟷ (∃ t. p' = gyr p t (t ⊕ p) ∧ q' = gyr p t (t ⊕ q))" (is "?lhs ⟷ ?rhs")
proof-
  let ?t = "⊖p ⊕ p'"

  have "⊖(?t ⊕ p) ⊕ (?t ⊕ q) = gyr ?t p (⊖p ⊕ q)"
    by (metis gyr_def gyro_equation_right)

  hence "⊖p ⊕ q = gyr (⊖ p) (⊖ ?t) (⊖(?t ⊕ p) ⊕ (?t ⊕ q))"
    by (metis gyr_aut_inv_2 gyr_auto_id1 gyr_even inv_gyr_sym pointfree_idE)
  hence "⊖p ⊕ q = gyr p ?t (⊖(?t ⊕ p) ⊕ (?t ⊕ q))"
    using gyr_even by presburger

  show ?thesis
  proof
    assume "(p, q) ∼ (p', q')"
    hence *: "⊖p ⊕ q = ⊖p' ⊕ q'"
      by simp

    have "p' = gyr p ?t (?t ⊕ p)" 
      using *
      using gyro_commute gyro_equation_right gyro_left_cancel by blast

    moreover

    have "q' = gyr p ?t (?t ⊕ q)"
    proof-
      have "q' = p' ⊕ (⊖ p ⊕ q)"
        by (metis "*" gyro_left_cancel')
      also have "... = gyr p ?t (?t ⊕ p) ⊕ (⊖ p ⊕ q)"
        using ‹p' = gyr p (⊖ p ⊕ p') (⊖ p ⊕ p' ⊕ p)› 
        by auto
      also have "... = (gyr p ?t ?t ⊕ gyr p ?t p) ⊕ (⊖ p ⊕ q)"
        by simp
      also have "... = gyr p ?t ?t ⊕ (gyr p ?t p ⊕ gyr (gyr p ?t p) (gyr p ?t ?t) (⊖ p ⊕ q))"
        using gyro_right_assoc by blast
      also have "... = gyr p ?t ?t ⊕ (gyr p ?t p ⊕ gyr p ?t (⊖ p ⊕ q))"
        using gyr_commute_misc_1
        by presburger
      also have "... = gyr p ?t ?t ⊕ gyr p ?t q"
        by (metis gyr_distrib gyro_equation_right)
      finally show "q' = gyr p ?t (?t ⊕ q)"
        by simp
    qed

    ultimately

    show ?rhs
      by blast

  next

    assume ?rhs
    then obtain t where t: "p' = gyr p t (t ⊕ p) ∧ q' = gyr p t (t ⊕ q)"
      by auto

    have "⊖ p ⊕ q = gyr p t (⊖ (t ⊕ p) ⊕ (t ⊕ q))"
      by (metis gyro_left_assoc gyro_left_cancel gyro_right_assoc gyro_translation_2a)
    also have "... = ⊖ (gyr p t (t ⊕ p)) ⊕ gyr p t (t ⊕ q)"
      by (simp add: gyr_inv_3)
    finally show ?lhs
      using t
      by auto
  qed
qed

text ‹Thm 5.5. (5.5)›
lemma gyro_translate_commute:
  assumes "p' = gyr p t (t ⊕ p) ∧ q' = gyr p t (t ⊕ q)"
  shows "t = ⊖p ⊕ p'"
  using assms
  using gyro_commute gyro_equation_right by blast

text ‹Def 5.6.›
fun gyrovec_translation :: "'a ⇒ 'a rooted_gyrovec ⇒ 'a rooted_gyrovec" where
  "gyrovec_translation t (p, q) = (gyr p t (t ⊕ p), gyr p t (t ⊕ q))"
end

lift_definition gyrovec_translation' :: "('a::gyrocommutative_gyrogroup) gyrovec ⇒ 'a rooted_gyrovec ⇒ 'a rooted_gyrovec" is 
  "λ (tp, tq) (p, q). gyrovec_translation (⊖ tp ⊕ tq) (p, q)"
  by force

text ‹(5.14)›
lemma
  shows "tail (gyrovec_translation t (p, q)) = p ⊕ t"
  by (metis gyrovec_translation.simps gyro_commute tail.simps)

text ‹(5.15)›
lemma gyrovec_translation_id:
  shows "gyrovec_translation 0⇩g (p, q) = (p, q)"
  by simp

text ‹Thm 5.7.›
lemma equiv_rooted_gyrovec_t:
  shows "(p, q) ∼ (p', q') ⟷ (p', q') = gyrovec_translation (⊖p ⊕ p') (p, q)"
  using equiv_rooted_gyro_vec_ex_t gyro_translate_commute
  by (metis gyrovec_translation.simps)

text ‹Thm 5.8.›
lemma gyrovec_translation_head:
  assumes "(p', x) = gyrovec_translation t (p, q)"  
  shows "x = p' ⊕ (⊖p ⊕ q)"
  by (metis assms equiv_rooted_gyro_vec_ex_t gyrovec_translation.simps equiv_rooted_gyro_vec.simps gyro_equation_right)

text ‹(5.24)›

context gyrocommutative_gyrogroup
begin

definition gyrovec_translation_inv' :: "'a ⇒ 'a ⇒ 'a" where
  "gyrovec_translation_inv' p t = ⊖ (gyr p t t)"

lemma gyrovec_translation_inv':
  shows "gyrovec_translation (gyrovec_translation_inv' p t) (gyrovec_translation t (p, q)) = (p, q)"
  unfolding gyrovec_translation_inv'_def
proof -
  have f1: "∀a aa. gyr (aa::'a) a (a ⊕ aa) = aa ⊕ a"
    by (metis (no_types) cogyro_commute cogyro_commute_iff_gyrocommute)
  have "∀a aa. ⊖ (gyr (aa::'a) a a) = ⊖ (aa ⊕ a) ⊕ aa"
    by (simp add: gyr_misc_3)
  then have "∀a aa ab. (ab::'a, ab ⊕ (⊖ (ab ⊕ aa) ⊕ a)) = gyrovec_translation (⊖ (gyr ab aa aa)) (ab ⊕ aa, a)"
    using f1 by (metis gyrovec_translation.simps gyr_commute_misc_3 gyro_left_cancel')
  then have "∀a aa ab. gyrovec_translation (⊖ (gyr (ab::'a) aa aa)) (gyrovec_translation aa (ab, a)) = (ab, a)"
    using f1 by (metis gyrovec_translation.simps gyr_commute_misc_3 gyro_left_cancel')
  then show "gyrovec_translation (⊖ (gyr p t t)) (gyrovec_translation t (p, q)) = (p, q)"
    by blast
qed

definition gyrovec_translation_compose' :: "'a ⇒ 'a ⇒ 'a ⇒ 'a" where
  "gyrovec_translation_compose' p t1 t2 = t1 ⊕ gyr t1 p t2"

lemma gyrovec_translation_compose':
  "gyrovec_translation t2 (gyrovec_translation t1 (p, q)) =
        gyrovec_translation (gyrovec_translation_compose' p t1 t2) (p, q)"
  by (smt (verit) comp_eq_dest_lhs gyrovec_translation_compose'_def local.gyr_auto_id2 local.gyr_commute_misc_3 local.gyr_distrib local.gyr_nested_1 local.gyr_right_loop local.gyro_commute local.gyro_right_assoc local.gyrovec_translation.simps pointfree_idE prod.inject)

fun equiv_translate (infixl "~⇩t" 100) where
  "(p1, q1) ~⇩t (p2, q2) ⟷ (∃ t. gyrovec_translation t (p1, q1) = (p2, q2))"

lemma equivp_equiv_translate:
  "equivp (~⇩t)"
proof (rule equivpI)
  show "reflp (~⇩t)"
  proof
    fix x
    show "x ~⇩t x"
      by (metis equiv_translate.elims(3) gyr_commute_misc_3 gyr_id_2 gyro_left_id gyrovec_translation.simps)
  qed
next
  show "symp (~⇩t)"
  proof
    fix a b
    assume "a ~⇩t b"
    thus "b ~⇩t a"
      using gyrovec_translation_inv' 
      by (cases a, cases b, fastforce)
  qed
next
  show "transp (~⇩t)"
  proof
    fix x y z
    assume "x ~⇩t y" "y ~⇩t z"
    thus "x ~⇩t z"
      using gyrovec_translation_compose'
      by (cases x, cases y, cases z, fastforce)
  qed
qed

text ‹(5.39)›
definition vec :: "'a ⇒ 'a ⇒ 'a" where
  "vec a b = ⊖ a ⊕ b"

text ‹(5.40)›
lemma "vec 0⇩g b = b"
  by (simp add: vec_def)

text ‹(5.41)›
lemma
  assumes "vec a b = v" 
  shows "b = a ⊕ v"
  by (metis assms local.gyro_left_cancel' local.vec_def)

text ‹(5.42)›
lemma
  "(a ⊕ v) ⊕ u = a ⊕ (v ⊕ gyr v a u)"
  by (rule gyro_right_assoc)

text ‹(5.43)›
lemma
  assumes "vec a b = v"
  shows "a = ⊖v ⊕⇩c b"
  using assms
  using cogyro_commute cogyrominus_def gyro_equation_left gyro_left_cancel' vec_def
  by force

lemma
  shows "(⊖ a ⊕ b) ⊕ gyr (⊖a) b (⊖ b ⊕ c) = ⊖a ⊕ c"
  by (rule gyro_polygonal_addition_lemma)  


definition torsion_elem::"'a⇒ bool" where
  "torsion_elem g ⟷ g⊕g = 0⇩g"

end

(*torsion_free two_divisible*)
class tf_tw_group = gyrocommutative_gyrogroup +
  assumes a1:"∀a. torsion_elem a ⟶ a =  0⇩g"
  assumes a2:"∀a. ∃b. (b⊕b = a)"
begin

text "T3.32"
lemma unique_half:
  shows "(a⊕a = c ∧ b⊕b = c) ⟶ a=b"
proof
  assume "(a⊕a = c ∧ b⊕b = c)"
  show "a=b"
  proof-
    have "a⊕a = b⊕b"
      by (simp add: ‹a ⊕ a = c ∧ b ⊕ b = c›)
    moreover have "⊖ b ⊕ (a⊕a) = ⊖ b ⊕ (b⊕b)"
      by (simp add: ‹a ⊕ a = c ∧ b ⊕ b = c›)
    moreover have "⊖ b ⊕ a  ⊕ (gyr (⊖ b) a) a =b "
      by (metis ‹a ⊕ a = c ∧ b ⊕ b = c› local.gyro_left_assoc local.gyro_left_cancel')
    moreover have "⊖ b ⊕ a = ⊖ (⊖ b ⊕ a)"
      by (metis calculation(3) local.gyro_plus_def_co local.gyro_right_cancel'_dual local.gyroautomorphic_inverse)
    moreover have "⊖ b ⊕ a  ⊕ ( ⊖ b ⊕ a) =  0⇩g"
      by (metis calculation(4) local.gyro_rigth_inv)
    moreover have " torsion_elem (⊖ b ⊕ a)"
      using calculation(5) local.torsion_elem_def by blast
    moreover have "( ⊖ b ⊕ a) = 0⇩g"
      using a1
      using calculation(6) by blast
    ultimately show ?thesis 
      by (metis local.gyro_left_inv local.oplus_ominus_cancel)
  qed
qed

text "T3.33"
lemma unique_gyro_half:
  assumes "gh⊕gh = g"
      "gyr_h ⊕ gyr_h = gyr a b g"
    shows "gyr a b gh = gyr_h"
  by (metis assms(1) assms(2) local.gyr_distrib unique_half)

text "3.102"
lemma gh_minus:
  assumes "gh⊕gh = ⊖ g"
        "gh2⊕gh2 = g"
      shows " ⊖ gh2 = gh"
  by (metis assms(1) assms(2) local.gyroautomorphic_inverse local.gyrominus_def unique_half)

text "T3.34"
lemma gyration_exclusion:
  assumes "∃g. g≠ 0⇩g"
  shows "∀a b.  gyr a b ≠  ⊖ ∘ id"
proof(rule ccontr)
  assume "¬ (∀a b.  gyr a b ≠  ⊖ ∘ id)"
  have "∃a b.( gyr a b =  ⊖ ∘ id)"
    using ‹¬ (∀a b. gyr a b ≠ ⊖ ∘ id)› by auto
  
  moreover obtain "a" "b" where "gyr a b  = ⊖  ∘ id "
    using calculation by blast
  moreover obtain "bh" where "bh ⊕ bh = b"
    using a2
    by blast
  moreover have "a ⊕ (b ⊖⇩b bh) = (a  ⊕ b)  ⊕ bh "
  proof-
    have "a ⊕ (b ⊖⇩b bh) =  (a  ⊕ b) ⊖⇩b  gyr a b bh "
      by (simp add: local.gyr_inv_3 local.gyro_left_assoc local.gyrominus_def)
    moreover obtain "gh" where "gh ⊕ gh =  gyr a b b"
      using local.a2 by blast
    moreover have "a ⊕ (b ⊖⇩b bh) = (a  ⊕ b) ⊖⇩b  gh"
      using ‹bh ⊕ bh = b› calculation(1) calculation(2) unique_gyro_half by blast
    ultimately show ?thesis 
      by (simp add: ‹gyr a b = ⊖ ∘ id› local.gyrominus_def) 
  qed
  moreover have "a ⊕ (b ⊖⇩b bh) = a  ⊕ bh"
    using calculation(3) local.gyro_left_right_cancel by force
  moreover have "b =  0⇩g"
    by (metis calculation(4) calculation(5) local.cogyro_gyro_inv local.cogyroinv_def local.gyro_equation_left local.gyro_equation_right)
  moreover have "gyr a b = id"
    by (simp add: calculation(6))
  moreover have "gyr a b  = ⊖  ∘ id "
    using calculation(2) by blast
  ultimately show False
    by (metis assms comp_id id_def local.gyro_rigth_inv unique_gyro_half)
qed

text "T3.35"
lemma gyration_exclusion_cons:
  shows "gyr a b b =  ⊖ b ⟶ b = 0⇩g"
proof
  assume "gyr a b b =  ⊖ b "
  show "b = 0⇩g"
  proof-
   obtain "bh" where "bh ⊕ bh = b"
    using a2
    by blast
  moreover have "a ⊕ (b ⊖⇩b bh) = (a  ⊕ b)  ⊕ bh "
  proof-
    have "a ⊕ (b ⊖⇩b bh) =  (a  ⊕ b) ⊖⇩b  gyr a b bh "
      by (simp add: local.gyr_inv_3 local.gyro_left_assoc local.gyrominus_def)
    moreover obtain "gh" where "gh ⊕ gh =  gyr a b b"
      using local.a2 by blast
    moreover have "a ⊕ (b ⊖⇩b bh) = (a  ⊕ b) ⊖⇩b  gh"
      using ‹bh ⊕ bh = b› calculation(1) calculation(2) unique_gyro_half by blast
    ultimately show ?thesis 
      by (metis ‹bh ⊕ bh = b› ‹gyr a b b = ⊖ b› gh_minus local.gyro_inv_idem local.gyrominus_def)
  qed
  moreover have "a ⊕ (b ⊖⇩b bh) = a  ⊕ bh"
    using calculation(1) local.gyro_left_right_cancel by force
  ultimately show ?thesis 
    by (metis local.gyr_right_loop local.gyro_commute local.gyro_left_cancel local.gyro_right_id)
qed
qed

text "T3.36"
lemma equation_t3_36:
  shows " x  ⊖⇩b (y  ⊖⇩b x) = y ⟷ x = y"
  by (metis gyration_exclusion_cons local.gyr_commute_misc_3 local.gyr_misc_1 local.gyr_misc_3 local.gyro_right_id local.gyro_rigth_inv local.gyrominus_def)



end

locale gyrogroup_isomorphism = 
  fixes φ :: "'a::gyrocommutative_gyrogroup ⇒ 'b" 
  fixes gyrozero' :: "'b" ("0⇩g⇩1")
  fixes gyroplus' :: "'b ⇒ 'b ⇒ 'b" (infixl "⊕⇩1" 100)
  fixes gyroinv' :: "'b ⇒ 'b" ("⊖⇩1")
  assumes φzero [simp]: "φ 0⇩g = 0⇩g⇩1"
  assumes φplus [simp]: "φ (a ⊕ b) = (φ a) ⊕⇩1 (φ b)"
  assumes φminus [simp]: "φ (⊖ a) = ⊖⇩1 (φ a)"
  assumes φbij [simp]: "bij φ"
begin

definition gyr' where
 "gyr' a b x = ⊖⇩1 (a ⊕⇩1 b) ⊕⇩1 (a ⊕⇩1 (b ⊕⇩1 x))"

lemma φgyr [simp]:
  shows "φ (gyr a b z) = gyr' (φ a) (φ b) (φ z)"
  by (simp add: gyr'_def gyr_def)

end

sublocale gyrogroup_isomorphism ⊆ gyrogroupoid gyrozero' gyroplus'
  by unfold_locales

sublocale gyrogroup_isomorphism ⊆ gyrocommutative_gyrogroup gyrozero' gyroplus' gyroinv' gyr'
proof
  fix a
  show "0⇩g⇩1 ⊕⇩1 a = a"
    by (metis φbij φplus φzero bij_iff gyro_left_id)
next
  fix a
  show "⊖⇩1 a ⊕⇩1 a = 0⇩g⇩1"
    by (metis φbij φminus φplus φzero bij_iff gyro_left_inv)
next
  fix a b z
  show "a ⊕⇩1 (b ⊕⇩1 z) = a ⊕⇩1 b ⊕⇩1 gyr' a b z"
    using φgyr[of "inv φ a" "inv φ b" "inv φ z"]
    by (metis φbij φplus bij_inv_eq_iff gyro_left_assoc)
next
  fix a b
  show "gyr' a b = gyr' (a ⊕⇩1 b) b"
  proof
    fix z
    show "gyr' a b z = gyr' (a ⊕⇩1 b) b z"
      using φgyr[of "inv φ a" "inv φ b" "inv φ z"]
      by (smt (z3) φbij φgyr φplus bij_inv_eq_iff gyr_aut_inv_3 inv_gyr_sym)
  qed
next
  fix a b
  have *: "gyr' a b = φ ∘ (gyr (inv φ a) (inv φ b)) ∘ (inv φ)"
  proof
    fix z
    show "gyr' a b z = (φ ∘ gyr (inv φ a) (inv φ b) ∘ inv φ) z"
      by (metis φbij φgyr bij_inv_eq_iff comp_def)
  qed
  show "gyroaut (gyr' a b)"
    unfolding gyroaut_def
  proof safe
    show "bij (gyr' a b)"
      using * φbij gyr_gyroaut
      by (metis bij_comp bij_imp_bij_inv gyrogroupoid_class.gyroaut_def)
  next
    fix x y
    show "gyr' a b (x ⊕⇩1 y) = gyr' a b x ⊕⇩1 gyr' a b y"
      using *
      by (smt (verit, del_insts) φbij φplus bij_inv_eq_iff comp_def gyr_distrib)
  qed
next
  fix a b
  show "a ⊕⇩1 b = gyr' a b (b ⊕⇩1 a)"
    using φgyr[of "inv φ a" "inv φ b" "inv φ (b ⊕⇩1 a)"]
    by (metis (no_types, lifting) φbij φplus bij_inv_eq_iff gyro_commute)
qed

end
