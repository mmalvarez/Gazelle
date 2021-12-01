theory Dom_Fst
  imports "../Dominant" "../../Lifter/Lifter_Instances"
begin

locale dominant2_fst = dominant2

sublocale dominant2_fst \<subseteq> out : dominant2 "fst_l l1" t1 "fst_l l2" t2 X
proof
  fix a1 a2
  fix b :: "'c * ('g :: {Pord, Pord_Weakb})"
  fix x
  assume Xin : "x \<in> X"

  then obtain b'1 b'2 where B' : "b = (b'1, b'2)" 
    by(cases b; auto simp add: fst_l_S_def)

  then show "LUpd (fst_l l2) (t2 x) a2 b <[
       LUpd (fst_l l1) (t1 x) a1 b"
    using dominant_leq[OF Xin]
    by(auto simp add: fst_l_def prod_pleq leq_refl)
qed

lemma (in dominant2_fst) ax :
  shows "dominant2 (fst_l l1) t1 (fst_l l2) t2 X"
  using out.dominant2_axioms
  by auto

end