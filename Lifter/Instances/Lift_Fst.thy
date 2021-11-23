theory Lift_Fst
  imports "../Lifter"
begin

(*
 * fst
 *)

definition fst_l ::
  "('x, 'a, 'b1 :: Pord_Weak) lifting \<Rightarrow>
   ('x, 'a, 'b1 * ('b2 :: Pord_Weakb)) lifting" where
"fst_l t =
  LMake (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (LUpd t s a b1, b2)))
            (\<lambda> s x . (LOut t s (fst x)))
            (\<lambda> s . (LBase t s, \<bottom>))"

definition fst_l_S :: "('x, 'b1 :: Pord_Weak) valid_set \<Rightarrow> ('x, ('b1 * 'b2 :: Pord_Weakb)) valid_set" where
"fst_l_S S s =
  { b . case b of (b1, _) \<Rightarrow> (b1 \<in> S s) }"

locale fst_l_valid_weak = lifting_valid_weak

sublocale fst_l_valid_weak \<subseteq> out:lifting_valid_weak "fst_l l" "fst_l_S S"
proof
  fix s a 
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  show "LOut (fst_l l) s (LUpd (fst_l l) s a b) = a"
    using put_get
    by(auto simp add: fst_l_def split:prod.splits)
next
  fix s
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  assume  Hb : "b \<in> fst_l_S S s"
  thus "b <[ LUpd (fst_l l) s (LOut (fst_l l) s b) b"
    using get_put_weak
    by(auto simp add: fst_l_def prod_pleq leq_refl fst_l_S_def split:prod.splits)
next
  fix s a 
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  show "LUpd (fst_l l) s a b \<in> fst_l_S S s"
    using put_S
    by(auto simp add: fst_l_def prod_pleq leq_refl fst_l_S_def split:prod.splits)
qed

lemma (in fst_l_valid_weak) ax:
  shows "lifting_valid_weak (fst_l l) (fst_l_S S)"
  using out.lifting_valid_weak_axioms
  by auto

lemma (in fst_l_valid_weak) ax_g :
  assumes H : "\<And> x . S' x = fst_l_S S x"
  shows "lifting_valid_weak (fst_l l) S'"
proof-
  have "S' = fst_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_weak_axioms assms
    by auto
qed

locale fst_l_valid_ext = lifting_valid_ext

sublocale fst_l_valid_ext \<subseteq> out : lifting_valid_ext "fst_l l" "fst_l_S S"
proof
  fix s a 
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  (*assume  Hb : "b \<in> fst_l_S S s"*)
  show "b <[ LUpd (fst_l l) s a b"
    using get_put
    by(auto simp add: fst_l_def prod_pleq fst_l_S_def leq_refl split:prod.splits)
qed

lemma (in fst_l_valid_ext) ax:
  shows "lifting_valid_ext (fst_l l)"
  using out.lifting_valid_ext_axioms
  by auto

locale fst_l_valid_base_ext = lifting_valid_base_ext

sublocale fst_l_valid_base_ext \<subseteq> out : lifting_valid_base_ext "fst_l l" "fst_l_S S"
proof
  fix s
  show "LBase (fst_l l) s = \<bottom>" using base
    by(auto simp add: fst_l_def prod_bot)
qed

lemma (in fst_l_valid_base_ext) ax :
  shows "lifting_valid_base_ext (fst_l l)"
  using out.lifting_valid_base_ext_axioms
  by auto

locale fst_l_valid_ok_ext = lifting_valid_ok_ext
sublocale fst_l_valid_ok_ext \<subseteq> out : lifting_valid_ok_ext "fst_l l" "fst_l_S S"
proof
  fix s

  show "ok_S \<subseteq> fst_l_S S s" using ok_S_valid
    by(auto simp add: prod_ok_S fst_l_S_def)
next
  fix s a
  fix b :: "('c * 'd)"
  assume B: "b \<in> ok_S" 
  then show "LUpd (fst_l l) s a b \<in> ok_S" using ok_S_put
    by(auto simp add: fst_l_def prod_ok_S)
qed

lemma (in fst_l_valid_ok_ext) ax :
  shows "lifting_valid_ok_ext (fst_l l) (fst_l_S S)"
  using out.lifting_valid_ok_ext_axioms by auto

lemma (in fst_l_valid_ok_ext) ax_g :
  assumes H: "\<And> x . S' x = fst_l_S S x"
  shows "lifting_valid_ok_ext (fst_l l) S'"
proof-
  have "S' = fst_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_ok_ext_axioms assms 
    by auto
qed

locale fst_l_valid_pres_ext = lifting_valid_pres_ext
sublocale fst_l_valid_pres_ext \<subseteq> out : lifting_valid_pres_ext "fst_l l" "fst_l_S S"
proof
  fix v supr :: "('c * 'd)"
  fix V f s

  assume HV : "v \<in> V"
  assume HS : "V \<subseteq> fst_l_S S s"
  assume Hsupr : "is_sup V supr"
  assume Hsupr_S : "supr \<in> fst_l_S S s"
  show "is_sup (LMap (fst_l l) f s ` V) (LMap (fst_l l) f s supr)"
  proof(rule is_supI)

    fix x

    assume Xin : "x \<in> LMap (fst_l l) f s ` V"

    obtain x1 x2 where X: "x = (x1, x2)" by(cases x; auto)

    obtain xi xi1 xi2 where Xi : "xi = (xi1, xi2)" "xi \<in> V" "LMap (fst_l l) f s xi = x"
      using Xin
      by auto

    obtain supr1 supr2 where Supr : "supr = (supr1, supr2)" by(cases supr; auto)

    have "xi <[ supr" using is_supD1[OF Hsupr Xi(2)] by simp

    hence "xi1 <[ supr1" "xi2 <[ supr2"
      using Xi Supr
      by(auto simp add: prod_pleq split: prod.splits)

    have "x2 = xi2" using Xi X
      by(cases l; auto simp add: fst_l_def)

    have "x1 = LMap l f s xi1"
      using Xi X
      by(cases l; auto simp add: fst_l_def)

    have "LMap (fst_l l) f s supr = (LMap l f s supr1, supr2)"
      using Supr
      by(cases l; auto simp add: fst_l_def)

    have Xi1_in : "xi1 \<in> fst ` V"
      using imageI[OF `xi \<in> V`, of fst] Xi
      by(auto simp add: fst_l_S_def)

    have Fst_V_sub : "fst ` V \<subseteq> S s"
      using HS
      by(auto simp add: fst_l_S_def)

    have "supr1 \<in> S s"
      using Hsupr_S Supr
      by(auto simp add: fst_l_S_def)

    have Supr1_sup : "is_sup (fst ` V) supr1"
    proof(rule is_supI)
      fix w1
      assume "w1 \<in> fst ` V"

      then obtain w2 where "(w1, w2) \<in> V"
        by auto

      hence "(w1, w2) <[ supr" using is_supD1[OF Hsupr, of "(w1, w2)"] by auto

      thus "w1 <[ supr1" using Supr by(auto simp add: prod_pleq)
    next

      fix z1

      assume Hub : "is_ub (fst ` V) z1"

      have "is_ub V (z1, supr2)"
      proof(rule is_ubI)
        fix w
        assume "w \<in> V"

        obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

        have "w1 \<in> (fst ` V)"
          using imageI[OF `w \<in> V`, of fst] W by auto

        hence "w1 <[ z1" using is_ubE[OF Hub] by auto

        have "w2 <[ supr2" using is_supD1[OF Hsupr `w \<in> V`] Supr W
          by(auto simp add: prod_pleq)

        then show "w <[ (z1, supr2)" using W `w1 <[ z1`
          by(auto simp add: prod_pleq)
      qed

      show "supr1 <[ z1"
        using is_supD2[OF Hsupr `is_ub V (z1, supr2)`] Supr
        by(auto simp add: prod_pleq)
    qed

    have Supr1_map : "is_sup (LMap l f s ` fst ` V) (LMap l f s supr1)"
      using pres using pres[OF Xi1_in Fst_V_sub Supr1_sup `supr1 \<in> S s` , of f]
      by simp

    have X1_in : "x1 \<in> LMap l f s ` fst ` V"
      using X Xi imageI[OF `xi \<in> V`, of fst]
      by(cases l; auto simp add: fst_l_def)

    have "x1 <[ LMap l f s supr1"
      using is_supD1[OF Supr1_map X1_in]
      by simp

    have "x2 <[ supr2" using `x2 = xi2` `xi2 <[ supr2` by simp

    then show "x <[ LMap (fst_l l) f s supr"
      using X Supr `x1 <[ LMap l f s supr1`
      by(cases l; auto simp add: fst_l_def prod_pleq)
  next
    fix x

    assume Xub : "is_ub (LMap (fst_l l) f s ` V) x"

    obtain supr1 supr2 where Supr : "supr = (supr1, supr2)" by(cases supr; auto)

  (* TODO: copy-pasted from first case *)
    have "LMap (fst_l l) f s supr = (LMap l f s supr1, supr2)"
      using Supr
      by(cases l; auto simp add: fst_l_def)

    have Fst_V_sub : "fst ` V \<subseteq> S s"
      using HS
      by(auto simp add: fst_l_S_def)

    have "supr1 \<in> S s"
      using Hsupr_S Supr
      by(auto simp add: fst_l_S_def)

    have Supr1_sup : "is_sup (fst ` V) supr1"
    proof(rule is_supI)
      fix w1
      assume "w1 \<in> fst ` V"

      then obtain w2 where "(w1, w2) \<in> V"
        by auto

      hence "(w1, w2) <[ supr" using is_supD1[OF Hsupr, of "(w1, w2)"] by auto

      thus "w1 <[ supr1" using Supr by(auto simp add: prod_pleq)
    next

      fix z1

      assume Hub : "is_ub (fst ` V) z1"

      have "is_ub V (z1, supr2)"
      proof(rule is_ubI)
        fix w
        assume "w \<in> V"

        obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

        have "w1 \<in> (fst ` V)"
          using imageI[OF `w \<in> V`, of fst] W by auto

        hence "w1 <[ z1" using is_ubE[OF Hub] by auto

        have "w2 <[ supr2" using is_supD1[OF Hsupr `w \<in> V`] Supr W
          by(auto simp add: prod_pleq)

        then show "w <[ (z1, supr2)" using W `w1 <[ z1`
          by(auto simp add: prod_pleq)
      qed

      show "supr1 <[ z1"
        using is_supD2[OF Hsupr `is_ub V (z1, supr2)`] Supr
        by(auto simp add: prod_pleq)
    qed

    obtain v1 v2 where V : "v = (v1, v2)" "v1 \<in> fst ` V"
      using imageI[OF HV, of fst]
      by(cases v; auto)

    have Supr1_map : "is_sup (LMap l f s ` fst ` V) (LMap l f s supr1)"
      using pres[OF V(2) Fst_V_sub Supr1_sup `supr1 \<in> S s` ] 
      by simp

    obtain x1 x2 where X: "x = (x1, x2)" by(cases x; auto)

    have X1_ub : "is_ub (LMap l f s ` fst ` V) x1"
    proof
      fix w1

      assume W1: "w1 \<in> LMap l f s ` fst ` V"

      then obtain wi wi1 wi2  where Wi : "wi \<in> V" "LMap l f s wi1 = w1" "wi = (wi1, wi2)"
        by(auto)

      have Wi_in : "LMap (fst_l l) f s wi \<in> LMap (fst_l l) f s ` V"
        using imageI[OF Wi(1), of "LMap (fst_l l) f s"] by simp

      have "LMap (fst_l l) f s wi <[ x"
        using is_ubE[OF Xub Wi_in]
        by simp

      then show "w1 <[ x1"
        using W1 Wi X
        by(cases l; auto simp add: prod_pleq fst_l_def)
    qed  

    have "LMap l f s supr1 <[ x1"
      using is_supD2[OF Supr1_map X1_ub]
      by simp

    have "is_ub V (supr1, x2)"
    proof(rule is_ubI)
      fix w

      assume Win : "w \<in> V"

      obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

      have W1_in : "w1 \<in> fst ` V"
        using imageI[OF Win, of fst] W by simp

      have "w1 <[ supr1"
        using is_supD1[OF Supr1_sup W1_in] by simp

      have "LMap (fst_l l) f s w <[ x"
        using is_ubE[OF Xub imageI[OF Win]] by simp

      hence "w2 <[ x2" using W X
        by(cases l; auto simp add: fst_l_def prod_pleq)

      show "w <[ (supr1, x2)"
        using `w1 <[ supr1` `w2 <[ x2` W
        by(auto simp add: prod_pleq)
    qed

    have "supr2 <[ x2"
      using is_supD2[OF Hsupr `is_ub V (supr1, x2)`] Supr
      by(auto simp add: prod_pleq)


    show "LMap (fst_l l) f s supr <[ x"
      using `LMap l f s supr1 <[ x1` `supr2 <[ x2` X Supr
      by(cases l; auto simp add: fst_l_def prod_pleq)
  qed
qed

lemma (in fst_l_valid_pres_ext) ax :
  shows "lifting_valid_pres_ext (fst_l l) (fst_l_S S)"
  using out.lifting_valid_pres_ext_axioms
  by auto

lemma (in fst_l_valid_pres_ext) ax_g :
  assumes H: "\<And> x . S' x = fst_l_S S x"
  shows "lifting_valid_pres_ext (fst_l l) S'"
proof-
  have "S' = fst_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_pres_ext_axioms
    by auto
qed

locale fst_l_valid_base_pres_ext = fst_l_valid_pres_ext + fst_l_valid_base_ext + lifting_valid_base_pres_ext

sublocale fst_l_valid_base_pres_ext \<subseteq> out : lifting_valid_base_pres_ext "fst_l l" "fst_l_S S"
proof
  fix s
  show "\<bottom> \<notin> fst_l_S S s"
    using bot_bad[of s]
    by(auto simp add: fst_l_S_def prod_bot)
qed

lemma (in fst_l_valid_base_pres_ext) ax :
  shows "lifting_valid_base_pres_ext (fst_l l) (fst_l_S S)"
  using out.lifting_valid_base_pres_ext_axioms
  by auto

lemma (in fst_l_valid_base_pres_ext) ax_g :
  assumes H : "\<And> x . S' x = fst_l_S S x"
  shows "lifting_valid_base_pres_ext (fst_l l) S'"
proof-
  have "S' = fst_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_base_pres_ext_axioms
    by auto
qed

locale fst_l_ortho = l_ortho

sublocale fst_l_ortho \<subseteq> out : l_ortho "fst_l l1" "fst_l_S S1" "fst_l l2" "fst_l_S S2"
proof
  fix s
  show "LBase (fst_l l1) s = LBase (fst_l l2) s"
    using eq_base
    by(auto simp add: fst_l_def)
next

  fix b :: "'c * 'e"
  fix s
  fix a1 :: 'b
  fix a2 :: 'd

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)
  have Compat1 : "LUpd l1 s a1 (LUpd l2 s a2 b1) = LUpd l2 s a2 (LUpd l1 s a1 b1)"
    using compat[of s a1 a2 b1]
    by(auto)

  then show "LUpd (fst_l l1) s a1 (LUpd (fst_l l2) s a2 b) =
       LUpd (fst_l l2) s a2 (LUpd (fst_l l1) s a1 b)"
    using B
    by(auto simp add: fst_l_def)
next

  fix b :: "('c * 'e)"
  fix a1 
  fix s

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LOut l2 s (LUpd l1 s a1 b1) = LOut l2 s b1"
    using put1_get2
    by auto

  then show "LOut (fst_l l2) s (LUpd (fst_l l1) s a1 b) = LOut (fst_l l2) s b"
    using B
    by (auto simp add: fst_l_def)
next
  fix b :: "('c * 'e)"
  fix s a2

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LOut l1 s (LUpd l2 s a2 b1) = LOut l1 s b1"
    using put2_get1
    by auto

  then show "LOut (fst_l l1) s
        (LUpd (fst_l l2) s a2 b) =
       LOut (fst_l l1) s b"
    using B
    by(auto simp add: fst_l_def)
next
  fix b :: "'c * 'e"
  fix s a1

  assume B_in : "b \<in> fst_l_S S2 s"

  then obtain b1 b2 where B : "b = (b1, b2)" "b1 \<in> S2 s"
    by(auto simp add: fst_l_S_def)

  have Compat1 : "LUpd l1 s a1 b1 \<in> S2 s"
    using put1_S2[OF B(2)] by auto

  then show "LUpd (fst_l l1) s a1 b \<in> fst_l_S S2 s"
    using B
    by(auto simp add: fst_l_def fst_l_S_def)
next
  fix b :: "'c * 'e"
  fix s a2

  assume B_in : "b \<in> fst_l_S S1 s"
  then obtain b1 b2 where B : "b = (b1, b2)" "b1 \<in> S1 s"
    by(auto simp add: fst_l_S_def)

  have Compat2 : "LUpd l2 s a2 b1 \<in> S1 s"
    using put2_S1[OF B(2)]
    by auto
  
  then show "LUpd (fst_l l2) s a2 b \<in> fst_l_S S1 s"
    using B
    by(auto simp add: fst_l_def fst_l_S_def)
qed

lemma (in fst_l_ortho) ax :
  shows "l_ortho (fst_l l1) (fst_l_S S1) (fst_l l2) (fst_l_S S2)"
  using out.l_ortho_axioms
  by auto

lemma (in fst_l_ortho) ax_g :
  assumes H1 : "\<And> x . S'1 x = fst_l_S S1 x"
  assumes H2 : "\<And> x . S'2 x = fst_l_S S2 x"
  shows "l_ortho (fst_l l1) S'1 (fst_l l2) S'2"
proof-
  have H1' : "S'1 = fst_l_S S1"
    using H1 by auto

  have H2' : "S'2 = fst_l_S S2"
    using H2 by auto

  show ?thesis using ax unfolding H1' H2'
    by auto
qed

locale fst_l_ortho_base_ext = l_ortho_base_ext

sublocale fst_l_ortho_base_ext \<subseteq> out : l_ortho_base_ext "fst_l l1" "fst_l l2"
proof
  fix s
  show "LBase (fst_l l1) s = \<bottom>"
    using compat_base1
    by(auto simp add: fst_l_def prod_bot)
  fix s
  show "LBase (fst_l l2) s = \<bottom>"
    using compat_base2
    by(auto simp add: fst_l_def prod_bot)
qed

lemma (in fst_l_ortho_base_ext) ax :
  shows "l_ortho_base_ext (fst_l l1) (fst_l l2)"
  using out.l_ortho_base_ext_axioms
  by auto

locale fst_l_ortho_ok_ext = l_ortho_ok_ext

sublocale fst_l_ortho_ok_ext \<subseteq> out : l_ortho_ok_ext "fst_l l1" "fst_l l2" .



(*
locale fst_l_ortho_pres = l_ortho_pres_ext

sublocale fst_l_ortho_pres \<subseteq> l_ortho_pres "fst_l l1" "fst_l_S S1" "fst_l l2" "fst_l_S S2"
proof
 fix a1 a2 s 
  fix x :: "('c * 'e)"

  obtain x1 x2 where X : "x = (x1, x2)"
    by(cases x; auto)

  have Sup : 
    "is_sup {LUpd (l1) s a1 x1, LUpd (l2) s a2 x1}
        (LUpd (l1) s a1 (LUpd (l2) s a2 x1))"
    using compat_pres_sup
    by auto

  have Conc' :
    "is_sup ((\<lambda>w. (w, x2)) ` {LUpd l1 s a1 x1, LUpd l2 s a2 x1}) (LUpd l1 s a1 (LUpd l2 s a2 x1), x2)"
    using is_sup_fst[OF _ Sup]
    by auto

  then show "is_sup {LUpd (fst_l l1) s a1 x, LUpd (fst_l l2) s a2 x}
        (LUpd (fst_l l1) s a1 (LUpd (fst_l l2) s a2 x))"
    using X
    by(auto simp add: fst_l_def)
qed
*)


end