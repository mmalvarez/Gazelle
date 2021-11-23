theory Lift_Snd
  imports "../Lifter"
begin
(*
 * snd
 *)

definition snd_l ::
  "('x, 'a, 'b2 :: Pord_Weak) lifting \<Rightarrow>
   ('x, 'a, ('b1 :: Pord_Weakb) * 'b2) lifting" where
"snd_l t =
      LMake (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (b1, LUpd t s a b2)))
            (\<lambda> s x . (LOut t s (snd x)))
            (\<lambda> s . (\<bottom>, LBase t s))"

definition snd_l_S :: "('x, 'b2 :: Pord_Weak) valid_set \<Rightarrow> ('x, ('b1 :: Pord_Weakb * 'b2)) valid_set" where
"snd_l_S S s =
  { b . case b of (_, b2) \<Rightarrow> (b2 \<in> S s) }"


locale snd_l_valid_weak = lifting_valid_weak

sublocale snd_l_valid_weak \<subseteq> out : lifting_valid_weak "snd_l l" "snd_l_S S"
proof
  fix s a 
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  show "LOut (snd_l l) s (LUpd (snd_l l) s a b) = a"
    using put_get
    by(auto simp add: snd_l_def split:prod.splits)
next
  fix s
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  assume  Hb : "b \<in> snd_l_S S s"
  thus "b <[ LUpd (snd_l l) s (LOut (snd_l l) s b) b"
    using get_put_weak
    by(auto simp add: snd_l_def prod_pleq leq_refl snd_l_S_def split:prod.splits)
next
  fix s a 
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  show "LUpd (snd_l l) s a b \<in> snd_l_S S s"
    using put_S
    by(auto simp add: snd_l_def prod_pleq leq_refl snd_l_S_def split:prod.splits)
qed

lemma (in snd_l_valid_weak) ax :
  shows "lifting_valid_weak (snd_l l) (snd_l_S S)"
  using out.lifting_valid_weak_axioms
  by auto

lemma (in snd_l_valid_weak) ax_g :
  assumes H : "\<And> x . S' x = snd_l_S S x"
  shows "lifting_valid_weak (snd_l l) S'"
proof-
  have "S' = snd_l_S S"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_weak_axioms
    by auto
qed


locale snd_l_valid_ext = lifting_valid_ext

sublocale snd_l_valid_ext \<subseteq> out : lifting_valid_ext "snd_l l" "snd_l_S S"
proof
  fix s a 
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  (*assume  Hb : "b \<in> snd_l_S S s"*)
  show "b <[ LUpd (snd_l l) s a b"
    using get_put
    by(auto simp add: snd_l_def prod_pleq leq_refl snd_l_S_def split:prod.splits)
qed

lemma (in snd_l_valid_ext) ax :
  shows "lifting_valid_ext (snd_l l)"
  using out.lifting_valid_ext_axioms
  by auto

locale snd_l_valid_base_ext = lifting_valid_base_ext
sublocale snd_l_valid_base_ext \<subseteq> out : lifting_valid_base_ext "snd_l l" "snd_l_S S"
proof
  fix s
  show "LBase (snd_l l) s = \<bottom>" using base
    by(auto simp add: snd_l_def prod_bot)
qed

lemma (in snd_l_valid_base_ext) ax :
  shows "lifting_valid_base_ext (snd_l l)"
  using out.lifting_valid_base_ext_axioms
  by auto

locale snd_l_valid_ok_ext = lifting_valid_ok_ext
sublocale snd_l_valid_ok_ext \<subseteq> out : lifting_valid_ok_ext "snd_l l" "snd_l_S S"
proof
  fix s

  show "ok_S \<subseteq> snd_l_S S s" using ok_S_valid
    by(auto simp add: prod_ok_S snd_l_S_def)
next
  fix s a
  fix b :: "('d * 'c)"
  assume B: "b \<in> ok_S" 
  then show "LUpd (snd_l l) s a b \<in> ok_S" using ok_S_put
    by(auto simp add: prod_ok_S snd_l_S_def snd_l_def)
qed

lemma (in snd_l_valid_ok_ext) ax :
  shows "lifting_valid_ok_ext (snd_l l) (snd_l_S S)"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in snd_l_valid_ok_ext) ax_g :
  assumes H: "\<And> x . S' x = snd_l_S S x"
  shows "lifting_valid_ok_ext (snd_l l) S'"
proof-
  have "S' = snd_l_S S"
    using assms by auto
  then show ?thesis
  using out.lifting_valid_ok_ext_axioms
  by auto
qed


locale snd_l_valid_pres_ext = lifting_valid_pres_ext
sublocale snd_l_valid_pres_ext \<subseteq> out : lifting_valid_pres_ext "snd_l l" "snd_l_S S"
proof
  fix v supr :: "('d * 'c)"
  fix V f s

  assume HV : "v \<in> V"
  assume HS : "V \<subseteq> snd_l_S S s"
  assume Hsupr : "is_sup V supr"
  assume Hsupr_S : "supr \<in> snd_l_S S s"
  show "is_sup (LMap (snd_l l) f s ` V) (LMap (snd_l l) f s supr)"
  proof(rule is_supI)

    fix x

    assume Xin : "x \<in> LMap (snd_l l) f s ` V"

    obtain x1 x2 where X: "x = (x1, x2)" by(cases x; auto)

    obtain xi xi1 xi2 where Xi : "xi = (xi1, xi2)" "xi \<in> V" "LMap (snd_l l) f s xi = x"
      using Xin
      by auto

    obtain supr1 supr2 where Supr : "supr = (supr1, supr2)" by(cases supr; auto)

    have "xi <[ supr" using is_supD1[OF Hsupr Xi(2)] by simp

    hence "xi1 <[ supr1" "xi2 <[ supr2"
      using Xi Supr
      by(auto simp add: prod_pleq split: prod.splits)

    have "x1 = xi1" using Xi X
      by(auto simp add: snd_l_def)

    have "x2 = LMap l f s xi2"
      using Xi X
      by(auto simp add: snd_l_def)

    have "LMap (snd_l l) f s supr = (supr1, LMap l f s supr2)"
      using Supr
      by(auto simp add: snd_l_def)

    have Xi1_in : "xi2 \<in> snd ` V"
      using imageI[OF `xi \<in> V`, of snd] Xi
      by(auto)

    have Fst_V_sub : "snd ` V \<subseteq> S s"
      using HS
      by(auto simp add: snd_l_S_def)

    have "supr2 \<in> S s"
      using Hsupr_S Supr
      by(auto simp add: snd_l_S_def)

    have Supr1_sup : "is_sup (snd ` V) supr2"
    proof(rule is_supI)
      fix w2
      assume "w2 \<in> snd ` V"

      then obtain w1 where "(w1, w2) \<in> V"
        by auto

      hence "(w1, w2) <[ supr" using is_supD1[OF Hsupr, of "(w1, w2)"] by auto

      thus "w2 <[ supr2" using Supr by(auto simp add: prod_pleq)
    next

      fix z2

      assume Hub : "is_ub (snd ` V) z2"

      have "is_ub V (supr1, z2)"
      proof(rule is_ubI)
        fix w
        assume "w \<in> V"

        obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

        have "w2 \<in> (snd ` V)"
          using imageI[OF `w \<in> V`, of snd] W by auto

        hence "w2 <[ z2" using is_ubE[OF Hub] by auto

        have "w1 <[ supr1" using is_supD1[OF Hsupr `w \<in> V`] Supr W
          by(auto simp add: prod_pleq)

        then show "w <[ (supr1, z2)" using W `w2 <[ z2`
          by(auto simp add: prod_pleq)
      qed

      show "supr2 <[ z2"
        using is_supD2[OF Hsupr `is_ub V (supr1, z2)`] Supr
        by(auto simp add: prod_pleq)
    qed

    have Supr1_map : "is_sup (LMap l f s ` snd ` V) (LMap l f s supr2)"
      using pres using pres[OF Xi1_in Fst_V_sub Supr1_sup `supr2 \<in> S s` , of f]
      by simp

    have X1_in : "x2 \<in> LMap l f s ` snd ` V"
      using X Xi imageI[OF `xi \<in> V`, of snd]
      by(auto simp add: snd_l_def)

    have "x2 <[ LMap l f s supr2"
      using is_supD1[OF Supr1_map X1_in]
      by simp

    have "x1 <[ supr1" using `x1 = xi1` `xi1 <[ supr1` by simp

    then show "x <[ LMap (snd_l l) f s supr"
      using X Supr `x2 <[ LMap l f s supr2`
      by(auto simp add: snd_l_def prod_pleq)
  next
    fix x

    assume Xub : "is_ub (LMap (snd_l l) f s ` V) x"

    obtain supr1 supr2 where Supr : "supr = (supr1, supr2)" by(cases supr; auto)

  (* TODO: copy-pasted from first case *)
    have "LMap (snd_l l) f s supr = (supr1, LMap l f s supr2)"
      using Supr
      by(auto simp add: snd_l_def)

    have Snd_V_sub : "snd ` V \<subseteq> S s"
      using HS
      by(auto simp add: snd_l_S_def)

    have "supr2 \<in> S s"
      using Hsupr_S Supr
      by(auto simp add: snd_l_S_def)

    have Supr2_sup : "is_sup (snd ` V) supr2"
    proof(rule is_supI)
      fix w2
      assume "w2 \<in> snd ` V"

      then obtain w1 where "(w1, w2) \<in> V"
        by auto

      hence "(w1, w2) <[ supr" using is_supD1[OF Hsupr, of "(w1, w2)"] by auto

      thus "w2 <[ supr2" using Supr by(auto simp add: prod_pleq)
    next

      fix z2

      assume Hub : "is_ub (snd ` V) z2"

      have "is_ub V (supr1, z2)"
      proof(rule is_ubI)
        fix w
        assume "w \<in> V"

        obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

        have "w2 \<in> (snd ` V)"
          using imageI[OF `w \<in> V`, of snd] W by auto

        hence "w2 <[ z2" using is_ubE[OF Hub] by auto

        have "w1 <[ supr1" using is_supD1[OF Hsupr `w \<in> V`] Supr W
          by(auto simp add: prod_pleq)

        then show "w <[ (supr1, z2)" using W `w2 <[ z2`
          by(auto simp add: prod_pleq)
      qed

      show "supr2 <[ z2"
        using is_supD2[OF Hsupr `is_ub V (supr1, z2)`] Supr
        by(auto simp add: prod_pleq)
    qed

    obtain v1 v2 where V : "v = (v1, v2)" "v2 \<in> snd ` V"
      using imageI[OF HV, of snd]
      by(cases v; auto)

    have Supr2_map : "is_sup (LMap l f s ` snd ` V) (LMap l f s supr2)"
      using pres[OF V(2) Snd_V_sub Supr2_sup `supr2 \<in> S s` ] 
      by simp

    obtain x1 x2 where X: "x = (x1, x2)" by(cases x; auto)

    have X2_ub : "is_ub (LMap l f s ` snd ` V) x2"
    proof
      fix w2

      assume W2: "w2 \<in> LMap l f s ` snd ` V"

      then obtain wi wi1 wi2  where Wi : "wi \<in> V" "LMap l f s wi2 = w2" "wi = (wi1, wi2)"
        by(auto)

      have Wi_in : "LMap (snd_l l) f s wi \<in> LMap (snd_l l) f s ` V"
        using imageI[OF Wi(1), of "LMap (snd_l l) f s"] by simp

      have "LMap (snd_l l) f s wi <[ x"
        using is_ubE[OF Xub Wi_in]
        by simp

      then show "w2 <[ x2"
        using W2 Wi X
        by(auto simp add: prod_pleq snd_l_def)
    qed  

    have "LMap l f s supr2 <[ x2"
      using is_supD2[OF Supr2_map X2_ub]
      by simp

    have "is_ub V (x1, supr2)"
    proof(rule is_ubI)
      fix w

      assume Win : "w \<in> V"

      obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

      have W2_in : "w2 \<in> snd ` V"
        using imageI[OF Win, of snd] W by simp

      have "w2 <[ supr2"
        using is_supD1[OF Supr2_sup W2_in] by simp

      have "LMap (snd_l l) f s w <[ x"
        using is_ubE[OF Xub imageI[OF Win]] by simp

      hence "w1 <[ x1" using W X
        by(auto simp add: snd_l_def prod_pleq)

      show "w <[ (x1, supr2)"
        using `w2 <[ supr2` `w1 <[ x1` W
        by(auto simp add: prod_pleq)
    qed

    have "supr1 <[ x1"
      using is_supD2[OF Hsupr `is_ub V (x1, supr2)`] Supr
      by(auto simp add: prod_pleq)


    show "LMap (snd_l l) f s supr <[ x"
      using `LMap l f s supr2 <[ x2` `supr1 <[ x1` X Supr
      by(auto simp add: snd_l_def prod_pleq)
  qed
qed

lemma (in snd_l_valid_pres_ext) ax :
  shows "lifting_valid_pres_ext (snd_l l) (snd_l_S S)"
  using out.lifting_valid_pres_ext_axioms
  by auto

lemma (in snd_l_valid_pres_ext) ax_g :
  assumes H : "\<And> x . S' x = snd_l_S S x"
  shows "lifting_valid_pres_ext (snd_l l) S'"
proof-
  have "S' = snd_l_S S"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_pres_ext_axioms
  by auto
qed


locale snd_l_valid_base_pres_ext = snd_l_valid_pres_ext + snd_l_valid_base_ext + lifting_valid_base_pres_ext
sublocale snd_l_valid_base_pres_ext \<subseteq> out : lifting_valid_base_pres_ext "snd_l l" "snd_l_S S"
proof
  fix s
  show "\<bottom> \<notin> snd_l_S S s"
    using bot_bad[of s]
    by(auto simp add: snd_l_S_def prod_bot)
qed

lemma (in snd_l_valid_base_pres_ext) ax :
  shows "lifting_valid_base_pres_ext (snd_l l) (snd_l_S S)"
  using out.lifting_valid_base_pres_ext_axioms by auto

lemma (in snd_l_valid_base_pres_ext) ax_g :
  assumes H : "\<And> x . S' x = snd_l_S S x"
  shows "lifting_valid_base_pres_ext (snd_l l) S'"
proof-
  have "S' = snd_l_S S"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_base_pres_ext_axioms by auto
qed

(* snd (copy-paste-change from fst) *)
locale snd_l_ortho = l_ortho

sublocale snd_l_ortho \<subseteq> out : l_ortho "snd_l l1" "snd_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix s
  show "LBase (snd_l l1) s = LBase (snd_l l2) s"
    using eq_base
    by(auto simp add: snd_l_def)
next

  fix b :: "('e * 'c)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'd

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LUpd l1 s a1 (LUpd l2 s a2 b2) = LUpd l2 s a2 (LUpd l1 s a1 b2)"
    using compat[of s a1 a2 b2]
    by(auto)

  then show "LUpd (snd_l l1) s a1 (LUpd (snd_l l2) s a2 b) =
       LUpd (snd_l l2) s a2 (LUpd (snd_l l1) s a1 b)"
    using B
    by(auto simp add: snd_l_def)
next

  fix b :: "('e * 'c)"
  fix a1 
  fix s

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LOut l2 s (LUpd l1 s a1 b2) = LOut l2 s b2"
    using put1_get2
    by auto

  then show "LOut (snd_l l2) s (LUpd (snd_l l1) s a1 b) = LOut (snd_l l2) s b"
    using B
    by (auto simp add: snd_l_def)
next
  fix b :: "('e * 'c)"
  fix s a2

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LOut l1 s (LUpd l2 s a2 b2) = LOut l1 s b2"
    using put2_get1
    by auto

  then show "LOut (snd_l l1) s
        (LUpd (snd_l l2) s a2 b) =
       LOut (snd_l l1) s b"
    using B
    by(auto simp add: snd_l_def)
next
  fix b :: "'e * 'c"
  fix s a1

  assume B_in : "b \<in> snd_l_S S2 s"

  then obtain b1 b2 where B : "b = (b1, b2)" "b2 \<in> S2 s"
    by(auto simp add: snd_l_S_def)

  have Compat1 : "LUpd l1 s a1 b2 \<in> S2 s"
    using put1_S2[OF B(2)] by auto

  then show "LUpd (snd_l l1) s a1 b \<in> snd_l_S S2 s"
    using B
    by(auto simp add: snd_l_def snd_l_S_def)
next
  fix b :: "'e * 'c"
  fix s a2

  assume B_in : "b \<in> snd_l_S S1 s"
  then obtain b1 b2 where B : "b = (b1, b2)" "b2 \<in> S1 s"
    by(auto simp add: snd_l_S_def)

  have Compat2 : "LUpd l2 s a2 b2 \<in> S1 s"
    using put2_S1[OF B(2)]
    by auto
  
  then show "LUpd (snd_l l2) s a2 b \<in> snd_l_S S1 s"
    using B
    by(auto simp add: snd_l_def snd_l_S_def)
qed

lemma (in snd_l_ortho) ax :
  shows "l_ortho (snd_l l1) (snd_l_S S1) (snd_l l2) (snd_l_S S2)"
  using out.l_ortho_axioms by auto

lemma (in snd_l_ortho) ax_g :
  assumes H1 : "\<And> x . S'1 x = snd_l_S S1 x"
  assumes H2 : "\<And> x . S'2 x = snd_l_S S2 x"
  shows "l_ortho (snd_l l1) S'1 (snd_l l2) S'2"
proof-
  have H1' : "S'1 = snd_l_S S1"
    using H1 by auto

  have H2' : "S'2 = snd_l_S S2"
    using H2 by auto

  show ?thesis using ax unfolding H1' H2'
    by auto
qed


locale snd_l_ortho_base_ext = l_ortho_base_ext

sublocale snd_l_ortho_base_ext \<subseteq> out : l_ortho_base_ext "snd_l l1" "snd_l l2"
proof
  fix s
  show "LBase (snd_l l1) s = \<bottom>"
    using compat_base1
    by(auto simp add: snd_l_def prod_bot)
next
  fix s
  show "LBase (snd_l l2) s = \<bottom>"
    using compat_base2
    by(auto simp add: snd_l_def prod_bot)
qed

lemma (in snd_l_ortho_base_ext) ax : 
  shows "l_ortho_base_ext (snd_l l1) (snd_l l2)"
  using out.l_ortho_base_ext_axioms
  by auto

locale snd_l_ortho_ok_ext = l_ortho_ok_ext

sublocale snd_l_ortho_ok_ext \<subseteq> out : l_ortho_ok_ext "snd_l l1" "snd_l l2" .

(*
locale snd_l_ortho_pres = snd_l_ortho + l_ortho_pres

sublocale snd_l_ortho_pres \<subseteq> l_ortho_pres "snd_l l1" "snd_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix a1 a2 s
  fix x :: "'e * 'c"
  obtain x1 x2 where X : "x = (x1, x2)"
    by(cases x; auto)

  have Sup : 
    "is_sup {LUpd (l1) s a1 x2, LUpd (l2) s a2 x2}
        (LUpd (l1) s a1 (LUpd (l2) s a2 x2))"
    using compat_pres_sup
    by auto

  have Conc' :
    "is_sup ((\<lambda>w. (x1, w)) ` {LUpd l1 s a1 x2, LUpd l2 s a2 x2}) (x1, LUpd l1 s a1 (LUpd l2 s a2 x2))"
    using is_sup_snd[OF _ Sup]
    by auto

  then show "is_sup {LUpd (snd_l l1) s a1 x, LUpd (snd_l l2) s a2 x}
        (LUpd (snd_l l1) s a1 (LUpd (snd_l l2) s a2 x))"
    using X
    by(auto simp add: snd_l_def)
qed
*)


end