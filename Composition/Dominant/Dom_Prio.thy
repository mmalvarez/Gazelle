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
  fixes f0_1 :: "'a1 \<Rightarrow> nat"
  fixes f1_1 :: "'a1 \<Rightarrow> nat \<Rightarrow> nat"
  fixes f0_2 :: "'a2 \<Rightarrow> nat"
  fixes f1_2 :: "'a2 \<Rightarrow> nat \<Rightarrow> nat"

locale dominant2_prio = dominant2_sig +
  dominant2_prio_sig +
  assumes dominant_f1 : "\<And> x n . x \<in> X \<Longrightarrow> f1_2 (t2 x) n < f1_1 (t1 x) n"

sublocale dominant2_prio \<subseteq> out : dominant2 "prio_l f0_1 f1_1 l1" t1 "prio_l f0_2 f1_2 l2" t2 X
proof
  fix a1 a2 
  fix b :: "'c md_prio"
  fix x
  assume Xin : "x \<in> X"

    obtain pb' b' where B' : "b = mdp pb' b'"
    by(cases b; auto simp add: prio_l_S_def)

  then show "LUpd (prio_l f0_2 f1_2 l2) (t2 x) a2 b <[
       LUpd (prio_l f0_1 f1_1 l1) (t1 x) a1 b"
    using dominant_f1[OF Xin, of pb']
    by(auto simp add: prio_l_def prio_pleq)
qed

lemma (in dominant2_prio) ax :
  shows "dominant2 (prio_l f0_1 f1_1 l1) t1 (prio_l f0_2 f1_2 l2) t2 X"
  using out.dominant2_axioms
  by auto

end