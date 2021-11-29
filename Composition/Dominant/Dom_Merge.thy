theory Dom_Merge
  imports "../Dominant" "../../Lifter/Lifter_Instances"
begin

locale dominant2_merge_lr_sig =
  fixes l1 :: "('a, 'b1, 'c :: Pord) lifting"
  fixes l2 :: "('a, 'b2, 'c :: Pord) lifting"
  fixes S :: "'a \<Rightarrow> 'c set"
  fixes X :: "'a set"
  fixes l_other :: "('a, 'b3, 'c :: Pord) lifting"
  fixes S_other :: "'a \<Rightarrow> 'c set"

locale dominant2_merge_left = 
  dominant2_merge_lr_sig + 
  dominant2 +
  V_other : lifting_valid l_other S_other +
  Orth : l_ortho l1 S l_other S_other

sublocale dominant2_merge_left \<subseteq> out : dominant2 "merge_l l1 l_other" "l2" (*"\<lambda> s . S s \<inter> S_other s"*) X
proof

  term "l1" term "l_other"

  fix a1_3 :: "('b * 'e)"
  fix a2 
  fix b :: "'c"
  fix x
  assume Xin : "x \<in> X"
  (*assume Bin : "b \<in> S x \<inter> S_other x"

  then have Bin1 : "b \<in> S x" and Bin3 : "b \<in> S_other x"
    by auto
*)

  obtain a1 a3 where A1_3 : "a1_3 = (a1, a3)"
    by(cases a1_3; auto)

  have 1 : "LUpd l2 x a2 b <[ LUpd l1 x a1 b"
    using dominant_leq[OF Xin]
    by auto

  have 2: "LUpd l1 x a1 b <[ LUpd l_other x a3 (LUpd l1 x a1 b)"
    using V_other.get_put
    by auto

  have 3 : "LUpd l_other x a3 (LUpd l1 x a1 b) = LUpd l1 x a1 (LUpd l_other x a3 b)"
    using Orth.compat
    by simp

  show " LUpd l2 x a2 b <[ LUpd (merge_l l1 l_other) x a1_3 b"
    using leq_trans[OF 1 2] 3 A1_3
    by(auto simp add: merge_l_def leq_refl)
qed

lemma (in dominant2_merge_left) ax :
  shows "dominant2 (merge_l l1 l_other) l2  (\<lambda> s . S s \<inter> S_other s) X"
  using out.dominant2_axioms
  by auto

locale dominant2_merge_right = 
  dominant2_merge_lr_sig + 
  dominant2 +
  V_other : lifting_valid l_other S_other +
  Orth : l_ortho l1 S l_other S_other

sublocale dominant2_merge_right \<subseteq> out : dominant2 "merge_l l_other l1" "l2" "\<lambda> s . S_other s \<inter> S s" X
proof

  fix a3_1 :: "('e * 'b)"
  fix a2 
  fix b :: "'c"
  fix x
  assume Xin : "x \<in> X"
  assume Bin : "b \<in> S_other x \<inter> S x"

  then have Bin1 : "b \<in> S x" and Bin3 : "b \<in> S_other x"
    by auto

  obtain a1 a3 where A3_1 : "a3_1 = (a3, a1)"
    by(cases a3_1; auto)

  have 1 : "LUpd l2 x a2 b <[ LUpd l1 x a1 b"
    using dominant_leq[OF Xin Bin1]
    by auto

  have 2: "LUpd l1 x a1 b <[ LUpd l_other x a3 (LUpd l1 x a1 b)"
    using V_other.get_put
    by auto

  show "LUpd l2 x a2 b <[ LUpd (merge_l l_other l1) x a3_1 b"
    using leq_trans[OF 1 2] A3_1
    by(simp add: merge_l_def)
qed

lemma (in dominant2_merge_right) ax :
  shows "dominant2 (merge_l l_other l1) l2  (\<lambda> s . S_other s \<inter> S s) X"
  using out.dominant2_axioms
  by auto

(* this third one does not actually hold - hopefully it won't be needed.
 *)
(*
locale dominant2_merge_both_sig =
  fixes l1 :: "('a, 'b1, 'c :: Pord) lifting"
  fixes l2 :: "('a, 'b2, 'c :: Pord) lifting"
  fixes l3 :: "('a, 'b3, 'c :: Pord) lifting"
  fixes S3 :: "'a \<Rightarrow> 'c set"
  fixes X :: "'a set"
  fixes l_other :: "('a, 'b3, 'c :: Pord) lifting"
  fixes S_other :: "'a \<Rightarrow> 'c set"

locale dominant2_merge_both = 
  dominant2_merge_both_sig +
  dom3_1 : dominant2 "l3" "l1" "S3" "X" +
  dom3_2 : dominant2 "l3" "l2" "S3" "X" 

sublocale dominant2_merge_both \<subseteq> dominant2 "l3" "merge_l l1 l2" S3 X
proof
  fix a1_2 :: "'b * 'd"
  fix a3
  fix b :: 'c
  fix x

  assume Xin : "x \<in> X"
  assume Bin : "b \<in> S3 x"

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LUpd (merge_l l1 l2) x a1_2 b <[ LUpd l3 x a3 b"
    using A1_2
    apply(simp add: merge_l_def)
    term "a1_2"
*)
end