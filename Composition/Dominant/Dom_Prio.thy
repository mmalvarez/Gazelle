theory Dom_Prio
  imports "../Dominant" "../../Lifter/Lifter_Instances"
begin

(*
 * Idea: 
 *)

(* We could also (perhaps) prove that if we know dominance on the inner data,
 * then we are dominant over priority liftings with equal data.
 * This probably isn't necessary given the way we use prio, however.
 *)

locale dominant2_prio_sig = 
  fixes f0_1 :: "'a \<Rightarrow> nat"
  fixes f1_1 :: "'a \<Rightarrow> nat \<Rightarrow> nat"
  fixes f0_2 :: "'a \<Rightarrow> nat"
  fixes f1_2 :: "'a \<Rightarrow> nat \<Rightarrow> nat"

locale dominant2_prio = dominant2_sig +
  dominant2_prio_sig +
  assumes dominant_f1 : "\<And> x n . x \<in> X \<Longrightarrow> f1_2 x n < f1_1 x n"

sublocale dominant2_prio \<subseteq> out : dominant2 "prio_l f0_1 f1_1 l1" "prio_l f0_2 f1_2 l2" "prio_l_S S" X
proof
  fix a1 a2 b x
  assume Xin : "x \<in> X"
  assume Bin : "b \<in> prio_l_S S x"

  then obtain pb' b' where B' : "b = mdp pb' b'" "b' \<in> S x"
    by(cases b; auto simp add: prio_l_S_def)

  then show "LUpd (prio_l f0_2 f1_2 l2) x a2 b <[
        LUpd (prio_l f0_1 f1_1 l1) x a1 b"
    using dominant_f1[OF Xin, of pb']
    by(auto simp add: prio_l_def prio_pleq)
qed
end