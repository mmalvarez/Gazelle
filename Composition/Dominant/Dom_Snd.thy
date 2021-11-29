theory Dom_Snd
  imports "../Dominant" "../../Lifter/Lifter_Instances"
begin

locale dominant2_snd = dominant2

sublocale dominant2_snd \<subseteq> out : dominant2 "snd_l l1" "snd_l l2" "snd_l_S S" X
proof
  fix a1 a2 
  fix b :: "('e :: {Pord, Pord_Weakb}) * 'c"
  fix x
  assume Xin : "x \<in> X"
  assume Bin : "b \<in> snd_l_S S x"

  then obtain b'1 b'2 where B' : "b = (b'1, b'2)" "b'2 \<in> S x"
    by(cases b; auto simp add: snd_l_S_def)

  then show "LUpd (snd_l l2) x a2 b <[
        LUpd (snd_l l1) x a1 b"
    using dominant_leq[OF Xin B'(2)]
    by(auto simp add: snd_l_def prod_pleq leq_refl)
qed

end