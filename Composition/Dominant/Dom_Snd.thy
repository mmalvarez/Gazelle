theory Dom_Snd
  imports "../Dominant" "../../Lifter/Lifter_Instances"
begin

locale dominant2_snd = dominant2

sublocale dominant2_snd \<subseteq> out : dominant2 "snd_l l1" t1 "snd_l l2" t2 X
proof
  fix a1 a2 
  fix b :: "('g :: {Pord, Pord_Weakb}) * 'c"
  fix x
  assume Xin : "x \<in> X"

  then obtain b'1 b'2 where B' : "b = (b'1, b'2)" 
    by(cases b; auto simp add: snd_l_S_def)

  then show "LUpd (snd_l l2) (t2 x) a2 b <[
       LUpd (snd_l l1) (t1 x) a1 b"
    using dominant_leq[OF Xin]
    by(auto simp add: snd_l_def prod_pleq leq_refl)
qed

lemma (in dominant2_snd) ax :
  shows "dominant2 (snd_l l1) t1 (snd_l l2) t2 X"
  using out.dominant2_axioms
  by auto


end