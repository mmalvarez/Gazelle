theory Lift_Fst_Snd imports Lift_Fst Lift_Snd
begin

locale fst_l_snd_l_ortho' =
  fixes l1 :: "('a, 'b1, 'c1 :: Pordb) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c1 set"
  fixes l2 :: "('a, 'b2, 'c2 :: Pordb) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c2 set"

locale fst_l_snd_l_ortho = fst_l_snd_l_ortho' +
  in1 : lifting_valid_base_ext l1 S1 +
  in2 : lifting_valid_base_ext l2 S2

sublocale fst_l_snd_l_ortho \<subseteq> out : l_ortho "fst_l l1" "fst_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix s
  show "LBase (fst_l l1) s = LBase (snd_l l2) s"
    using in1.base in2.base
    by(auto simp add: fst_l_def snd_l_def)
next
  fix b :: "'c * 'e"
  fix s :: 'a
  fix a1 :: 'b
  fix a2 :: 'd

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 b) = LUpd (snd_l l2) s a2 (LUpd (fst_l l1) s a1 b)"
    by(auto simp add: fst_l_def snd_l_def)

next

  fix b :: "'c * 'e"
  fix s :: 'a
  fix a1

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LOut (snd_l l2) s (LUpd (fst_l l1) s a1 b) = LOut (snd_l l2) s b"
    by(auto simp add: fst_l_def snd_l_def)
next

  fix b :: "'c * 'e"
  fix s :: 'a
  fix a2 :: 'd


  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LOut (fst_l l1) s (LUpd (snd_l l2) s a2 b) = LOut (fst_l l1) s b"
    by(cases b; auto simp add: fst_l_def snd_l_def)


next
  fix b :: "'c * 'e"
  fix s :: 'a
  fix a1 :: 'b

  assume Bin : "b \<in> snd_l_S S2 s"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show " LUpd (fst_l l1) s a1 b \<in> snd_l_S S2 s" using Bin
    by(auto simp add: fst_l_def snd_l_S_def)
next
  fix b :: "'c * 'e"
  fix s :: 'a
  fix a2 :: 'd

  assume Bin: "b \<in> fst_l_S S1 s"
  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LUpd (snd_l l2) s a2 b \<in> fst_l_S S1 s" using Bin
    by(auto simp add: snd_l_def fst_l_S_def)
qed

lemma (in fst_l_snd_l_ortho) ax :
  shows "l_ortho (fst_l l1) (fst_l_S S1) (snd_l l2) (snd_l_S S2)"
  using out.l_ortho_axioms
  by auto

lemma (in fst_l_snd_l_ortho) ax_g :
  assumes H1 : "\<And> x . S'1 x = fst_l_S S1 x"
  assumes H2 : "\<And> x . S'2 x = snd_l_S S2 x"
  shows "l_ortho (fst_l l1) S'1 (snd_l l2) S'2"
proof-
  have H1' : "S'1 = fst_l_S S1"
    using H1 by auto
  have H2' : "S'2 = snd_l_S S2"
    using H2 by auto
  then show ?thesis using ax unfolding H1' H2'
    by auto
qed

(* commutative *)
lemma (in fst_l_snd_l_ortho) ax_comm :
  shows "l_ortho (snd_l l2) (snd_l_S S2) (fst_l l1) (fst_l_S S1)"
  using out.comm.l_ortho_axioms
  by auto

lemma (in fst_l_snd_l_ortho) ax_g_comm :
  assumes H1 : "\<And> x . S'2 x = snd_l_S S2 x"
  assumes H2 : "\<And> x . S'1 x = fst_l_S S1 x"
  shows "l_ortho (snd_l l2) S'2 (fst_l l1) S'1"
proof-
  have H1' : "S'2 = snd_l_S S2"
    using H1 by auto
  have H2' : "S'1 = fst_l_S S1"
    using H2 by auto
  then show ?thesis using ax_comm unfolding H1' H2'
    by auto
qed


locale fst_l_snd_l_ortho_ok_ext =
  fixes l1 :: "('a, 'b1, 'c1 :: {Pord_Weakb, Okay}) lifting"
  fixes l2 :: "('a, 'b2, 'c2 :: {Pord_Weakb, Okay}) lifting"

sublocale fst_l_snd_l_ortho_ok_ext \<subseteq> out : l_ortho_ok_ext "fst_l l1" "snd_l l2" .

locale fst_l_snd_l_ortho_base_ext =
  fst_l_snd_l_ortho' + 
  in1 : lifting_valid_weak_base l1 S1 +
  in2 : lifting_valid_weak_base l2 S2


sublocale fst_l_snd_l_ortho_base_ext \<subseteq> out : l_ortho_base_ext "fst_l l1" "snd_l l2"
proof
  fix s
  show "LBase (fst_l l1) s = \<bottom>"
    using in1.base
    by(auto simp add: fst_l_def prod_bot)
next
  fix s
  show "LBase (snd_l l2) s = \<bottom>"
    using in2.base
    by(auto simp add: snd_l_def prod_bot)
qed

lemma (in fst_l_snd_l_ortho_base_ext) ax :
  shows "l_ortho_base_ext (fst_l l1) (snd_l l2)"
  using out.l_ortho_base_ext_axioms
  by auto

lemma (in fst_l_snd_l_ortho_base_ext) ax_comm :
  shows "l_ortho_base_ext (snd_l l2) (fst_l l1)"
  using out.comm.l_ortho_base_ext_axioms
  by auto

(*
(* TODO: this was originally lifting_valid_weak_pres, but i think we actually need strength
 * to make this work *)
locale fst_l_snd_l_ortho_pres =
  fst_l_snd_l_ortho +
  in1 : lifting_valid_pres l1 S1 +
  in2 : lifting_valid_pres l2 S2

sublocale fst_l_snd_l_ortho_pres \<subseteq> out : l_ortho_pres "fst_l l1" "fst_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix a1 a2 s
  fix x :: "('c * 'e)"

  obtain x1 x2 where X: "x = (x1, x2)"
    by(cases x; auto)

  have Leq1 : "x1 <[ LUpd l1 s a1 x1"
    using in1.get_put by auto

  have Leq2 : "x2 <[ LUpd l2 s a2 x2"
    using in2.get_put by auto

  show "is_sup {LUpd (fst_l l1) s a1 x, LUpd (snd_l l2) s a2 x} (LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 x))"
  proof(rule is_supI)
    fix w

    assume W: "w \<in> {LUpd (fst_l l1) s a1 x, LUpd (snd_l l2) s a2 x}"

    obtain w1 w2 where "w = (w1, w2)"
      by(cases w; auto)

    show "w <[ LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 x)"
      using W X Leq1 Leq2
      by(auto simp add: fst_l_def snd_l_def prod_pleq leq_refl)
  next
    fix x'
    assume Ub : "is_ub {LUpd (fst_l l1) s a1 x, LUpd (snd_l l2) s a2 x} x'"

    obtain x'1 x'2 where X': "x' = (x'1, x'2)"
      by(cases x'; auto)

    have Leq1 : "LUpd (fst_l l1) s a1 x <[ x'"
      using is_ubE[OF Ub]
      by auto

    have Leq2 : "LUpd (snd_l l2) s a2 x <[ x'"
      using is_ubE[OF Ub]
      by auto

    show "LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 x) <[ x'"
      using X' X Leq1 Leq2
      by(auto simp add: fst_l_def snd_l_def prod_pleq)
  qed
qed
*)

end
