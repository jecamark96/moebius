theory MobiusColinear
  imports Complex_Main MobiusGyroGroup GyroGroup GyroVectorSpace HOL.Real_Vector_Spaces
      HOL.Transcendental

begin
definition moebius_translation::"PoincareDisc \<Rightarrow> PoincareDisc \<Rightarrow> PoincareDisc" where
  "moebius_translation u v =  \<ominus>\<^sub>m u  \<oplus>\<^sub>m v"


lemma cpmt_help1:
  shows "x = u  \<oplus>\<^sub>m t \<otimes>\<^sub>m ( \<ominus>\<^sub>m u  \<oplus>\<^sub>m v) \<longleftrightarrow> ( \<ominus>\<^sub>m a  \<oplus>\<^sub>m x) =  (\<ominus>\<^sub>m a  \<oplus>\<^sub>m u) \<oplus>\<^sub>m t \<otimes>\<^sub>m ( \<ominus>\<^sub>m( \<ominus>\<^sub>m a  \<oplus>\<^sub>m u)
   \<oplus>\<^sub>m  ( \<ominus>\<^sub>m a  \<oplus>\<^sub>m v))"
  by (metis Moebius_gyrogroup.gyro_left_cancel Moebius_gyrogroup.gyro_translation_2a m_gyr_gyrospace2 m_gyro_left_assoc)


(*
lemma(in gyrovector_space ) colinear_preserved_moebius_translation:
  shows "colinear x y z \<longleftrightarrow> colinear (moebius_translation u x) (moebius_translation u y) (moebius_translation  u z)"
  sorry
*)


end
