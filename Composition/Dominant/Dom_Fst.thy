theory Dom_Fst
  imports "../Dominant" "../../Lifter/Lifter_Instances"
begin

locale dominant2_fst = dominant2

sublocale dominant2_fst \<subseteq> out : dominant2 "fst_l l1" "fst_l l2" "fst_l_S S" X
proof
  fix a1 a2 
  fix b :: "'c * ('e :: {Pord, Pord_Weakb})"
  fix x
  assume Xin : "x \<in> X"
  assume Bin : "b \<in> fst_l_S S x"

  then obtain b'1 b'2 where B' : "b = (b'1, b'2)" "b'1 \<in> S x"
    by(cases b; auto simp add: fst_l_S_def)

  then show "LUpd (fst_l l2) x a2 b <[
        LUpd (fst_l l1) x a1 b"
    using dominant_leq[OF Xin B'(2)]
    by(auto simp add: fst_l_def prod_pleq leq_refl)
qed

end