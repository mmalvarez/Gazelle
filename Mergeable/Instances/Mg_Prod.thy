theory Mg_Prod
  imports "../Pord" "../Mergeable" "../Bump"
begin

(* For product types, we impose an ordering that requires that _all_ components of
 * product a be less than or equal to their corresponding components of b,
 * in order for a <[ b to hold.
 *
 * In other words, this is _not_ a lexicographic ordering. Lexicographic orderings
 * where the first component is arbitrary create problems around completeness.
 * This is why we work with a more restricted version of a lexicographic-like ordering, md_prio,
 * a pair where the first component is guaranteed to be a natural number, and the ordering
 * is lexicographic (see below)
 *)


instantiation prod :: (Pord_Weak, Pord_Weak) Pord_Weak
begin
  definition prod_pleq : 
  "(x :: 'a * 'b) <[ y =
    (case x of
        (x1, x2) \<Rightarrow> (case y of
                      (y1, y2) \<Rightarrow> (pleq x1 y1 \<and> pleq x2 y2)))"
instance proof
  fix a :: "('a * 'b)"
  show "pleq a a" by (auto simp add:prod_pleq leq_refl split:prod.splits)
next
  fix a b c :: "('a * 'b)"
  assume H1 : "pleq a b"
  assume H2 : "pleq b c"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)
  obtain c1 and c2 where 2 : "c = (c1, c2)" by (cases c; auto)

  show "pleq a c" using H1 H2 0 1 2 leq_trans[of a1 b1 c1] leq_trans[of a2 b2 c2]
    by (auto simp add:prod_pleq)
qed
end

instantiation prod :: (Pord, Pord) Pord
begin
instance proof
  fix a b :: "('a * 'b)"
  assume H1 : "pleq a b"
  assume H2 : "pleq b a"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)

  show "a = b" using H1 H2 0 1 leq_antisym[of a1 b1] leq_antisym[of a2 b2]
    by(auto simp add:prod_pleq)
qed
end

instantiation prod :: (Pordc, Pordc) Pordc
begin
instance proof

  fix a b :: "('a * 'b)"
  assume H : "has_ub {a, b}"

  obtain a1 and a2 where 0 : "a = (a1, a2)" by (cases a; auto)
  obtain b1 and b2 where 1 : "b = (b1, b2)" by (cases b; auto)

  obtain ub where HUb : "is_ub {a, b} ub" using H by (auto simp add:has_ub_def)
  obtain ub1 and ub2 where HUb' : "ub = (ub1, ub2)" by (cases ub; auto)

  have Ub1 : "is_ub {a1, b1} ub1" using H 0 1 HUb HUb'
    by(auto simp add:prod_pleq is_ub_def)
  have Ub2 : "is_ub {a2, b2} ub2" using H 0 1 HUb HUb'
    by(auto simp add:prod_pleq is_ub_def)

  obtain sup1 where Sup1 : "is_sup {a1, b1} sup1" using complete2[of a1 b1] Ub1
    by(auto simp add: has_sup_def has_ub_def)

  obtain sup2 where Sup2 : "is_sup {a2, b2} sup2"
    using complete2[of a2 b2] Ub2
    by(auto simp add: has_sup_def has_ub_def)

  have Sup : "is_sup {(a1, a2), (b1, b2)} (sup1, sup2)" using Sup1 Sup2
    by(auto simp add: prod_pleq is_sup_def is_ub_def is_least_def)

  thus "has_sup {a, b}" using 0 1 by (auto simp add:has_sup_def)
qed
end

lemma is_sup_fst :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_sup Xs supr"
  shows "is_sup ((\<lambda> w . (w, x')) ` Xs) (supr, x')"
proof(rule is_supI)
  fix x

  assume X: "x \<in> (\<lambda>w. (w, x')) ` Xs"

  then obtain x1 where X1 :
    "x = (x1, x')" "x1 \<in> Xs"
    by auto

  have "x1 <[ supr"
    using is_supD1[OF H X1(2)] by auto

  then show "x <[ (supr, x')"
    using X1
    by(auto simp add: prod_pleq leq_refl)
next

  fix y

  assume Y: "is_ub ((\<lambda>w. (w, x')) ` Xs) y"

  obtain y1 y2 where Y1_2 : "y = (y1, y2)"
    by(cases y; auto)

  have "is_ub Xs y1"
  proof(rule is_ubI)
    fix z

    assume Z: "z \<in> Xs"

    then have "(z, x') <[ y"
      using is_ubE[OF Y] by auto

    then show "z <[ y1"
      using Y1_2
      by(auto simp add: prod_pleq)
  qed

  then have "supr <[ y1"
    using is_supD2[OF H]
    by auto

  have "(x, x') <[ y"
    using is_ubE[OF Y] Hnemp
    by auto

  then have "x' <[ y2"
    using Y1_2
    by(auto simp add: prod_pleq)

  show "(supr, x') <[ y"
    using `supr <[ y1` `x' <[ y2` Y1_2
    by(auto simp add: prod_pleq)
qed

lemma is_ub_fst :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_ub Xs ub"
  shows "is_ub ((\<lambda> w . (w, x')) ` Xs) (ub, x')"
proof(rule is_ubI)
  fix x

  assume X: "x \<in> (\<lambda>w. (w, x')) ` Xs"

  then obtain x1 where X1 :
    "x = (x1, x')" "x1 \<in> Xs"
    by auto

  have "x1 <[ ub"
    using is_ubE[OF H X1(2)] by auto

  then show "x <[ (ub, x')"
    using X1
    by(auto simp add: prod_pleq leq_refl)
qed

lemma is_sup_fst' :
  assumes Hnemp : "xy \<in> Xys"
  assumes H : "is_sup Xys (s1, s2)"
  shows "is_sup (fst ` Xys) s1"
proof(rule is_supI)

  fix x

  assume X: "x \<in> fst ` Xys"
  then obtain y where Xy : "(x, y) \<in> Xys"
    by(auto)

  then have "(x, y) <[ (s1, s2)"
    using is_supD1[OF H Xy]
    by auto

  then show "x <[ s1"
    by(auto simp add: prod_pleq)
next

  fix x'

  assume X' : "is_ub (fst ` Xys) x'"

  have Ub' : "is_ub Xys (x', s2)"
  proof(rule is_ubI)

    fix w

    assume W : "w \<in> Xys"

    obtain w1 w2 where W1_2 :
      "w = (w1, w2)"
      by(cases w; auto)

    then have "w1 \<in> fst ` Xys" using imageI[OF W, of fst]
      by auto

    then have "w1 <[ x'"
      using is_ubE[OF X'] by auto

    have "w2 \<in> snd ` Xys" using imageI[OF W, of snd] W1_2
      by auto

    then have "w2 <[ s2"
      using is_supD1[OF H W] W1_2
      by(auto simp add: prod_pleq)

    then show "w <[ (x', s2)"
      using `w1 <[ x'` W1_2
      by(auto simp add: prod_pleq)
  qed

  show "s1 <[ x'"
    using is_supD2[OF H Ub']
    by(auto simp add: prod_pleq)
qed

lemma is_ub_fst' :
  assumes Hnemp : "xy \<in> Xys"
  assumes H : "is_ub Xys (s1, s2)"
  shows "is_ub (fst ` Xys) s1"
proof(rule is_ubI)

  fix x

  assume X: "x \<in> fst ` Xys"
  then obtain y where Xy : "(x, y) \<in> Xys"
    by(auto)

  then have "(x, y) <[ (s1, s2)"
    using is_ubE[OF H Xy]
    by auto

  then show "x <[ s1"
    by(auto simp add: prod_pleq)
qed


lemma is_sup_snd :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_sup Xs supr"
  shows "is_sup ((\<lambda> w . (x', w)) ` Xs) (x', supr)"
proof(rule is_supI)
  fix x

  assume X: "x \<in> (\<lambda>w. (x', w)) ` Xs"

  then obtain x2 where X2 :
    "x = (x', x2)" "x2 \<in> Xs"
    by auto

  have "x2 <[ supr"
    using is_supD1[OF H X2(2)] by auto

  then show "x <[ (x', supr)"
    using X2
    by(auto simp add: prod_pleq leq_refl)
next

  fix y

  assume Y: "is_ub ((\<lambda>w. (x', w)) ` Xs) y"

  obtain y1 y2 where Y1_2 : "y = (y1, y2)"
    by(cases y; auto)

  have "is_ub Xs y2"
  proof(rule is_ubI)
    fix z

    assume Z: "z \<in> Xs"

    then have "(x', z) <[ y"
      using is_ubE[OF Y] by auto

    then show "z <[ y2"
      using Y1_2
      by(auto simp add: prod_pleq)
  qed

  then have "supr <[ y2"
    using is_supD2[OF H]
    by auto

  have "(x', x) <[ y"
    using is_ubE[OF Y] Hnemp
    by auto

  then have "x' <[ y1"
    using Y1_2
    by(auto simp add: prod_pleq)

  show "(x', supr) <[ y"
    using `supr <[ y2` `x' <[ y1` Y1_2
    by(auto simp add: prod_pleq)
qed

lemma is_ub_snd :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_ub Xs ub"
  shows "is_ub ((\<lambda> w . (x', w)) ` Xs) (x', ub)"
proof(rule is_ubI)
  fix x

  assume X: "x \<in> (\<lambda>w. (x', w)) ` Xs"

  then obtain x2 where X2 :
    "x = (x', x2)" "x2 \<in> Xs"
    by auto

  have "x2 <[ ub"
    using is_ubE[OF H X2(2)] by auto

  then show "x <[ (x', ub)"
    using X2
    by(auto simp add: prod_pleq leq_refl)
qed

lemma is_sup_snd' :
  assumes Hnemp : "xy \<in> Xys"
  assumes H : "is_sup Xys (s1, s2)"
  shows "is_sup (snd ` Xys) s2"
proof(rule is_supI)

  fix y

  assume Y: "y \<in> snd ` Xys"
  then obtain x where Xy : "(x, y) \<in> Xys"
    by(auto)

  then have "(x, y) <[ (s1, s2)"
    using is_supD1[OF H Xy]
    by auto

  then show "y <[ s2"
    by(auto simp add: prod_pleq)
next

  fix y'

  assume Y' : "is_ub (snd ` Xys) y'"

  have Ub' : "is_ub Xys (s1, y')"
  proof(rule is_ubI)

    fix w

    assume W : "w \<in> Xys"

    obtain w1 w2 where W1_2 :
      "w = (w1, w2)"
      by(cases w; auto)

    then have "w2 \<in> snd ` Xys" using imageI[OF W, of snd]
      by auto

    then have "w2 <[ y'"
      using is_ubE[OF Y'] by auto

    have "w1 \<in> fst ` Xys" using imageI[OF W, of fst] W1_2
      by auto

    then have "w1 <[ s1"
      using is_supD1[OF H W] W1_2
      by(auto simp add: prod_pleq)

    then show "w <[ (s1, y')"
      using `w2 <[ y'` W1_2
      by(auto simp add: prod_pleq)
  qed

  show "s2 <[ y'"
    using is_supD2[OF H Ub']
    by(auto simp add: prod_pleq)
qed

lemma is_ub_snd' :
  assumes Hnemp : "xy \<in> Xys"
  assumes H : "is_ub Xys (s1, s2)"
  shows "is_ub (snd ` Xys) s2"
proof(rule is_ubI)

  fix y

  assume Y: "y \<in> snd ` Xys"
  then obtain x where Xy : "(x, y) \<in> Xys"
    by(auto)

  then have "(x, y) <[ (s1, s2)"
    using is_ubE[OF H Xy]
    by auto

  then show "y <[ s2"
    by(auto simp add: prod_pleq)
qed


lemma is_sup_prod :
  assumes Hx : "is_sup Xs suprx"
  assumes Hy : "is_sup Ys supry"
  assumes S1 : "fst ` S = Xs"
  assumes S2 : "snd ` S = Ys"
  shows "is_sup S (suprx, supry)"
proof(rule is_supI)
  fix w
  assume W_in : "w \<in> S"

  obtain w1 w2 where W:
    "w = (w1, w2)"
    by(cases w; auto)

  have W_Xs : "w1 \<in> Xs" and W_Ys : "w2 \<in> Ys"
    using S1 S2 W_in W
    using imageI[OF W_in, of fst] imageI[OF W_in, of snd]
    by(auto)

  have "w1 <[ suprx" "w2 <[ supry"
    using is_supD1[OF Hx W_Xs] is_supD1[OF Hy W_Ys] W
    by auto

  then show "w <[ (suprx, supry)"
    using W by(auto simp add: prod_pleq)
next

  fix w'
  assume Ub : "is_ub S w'"

  obtain w'1 w'2 where W':
    "w' = (w'1, w'2)"
    by(cases w'; auto)

  have Ub_Xs : "is_ub Xs w'1"
  proof(rule is_ubI)
    fix x

    assume X : "x \<in> Xs"

    then obtain y where Y: "(x, y) \<in> S"
      using S1
      by(auto)

    have "(x, y) <[ w'"
      using is_ubE[OF Ub Y]
      by auto

    then show "x <[ w'1"
      using W'
      by(auto simp add: prod_pleq)
  qed

  have Ub_Ys : "is_ub Ys w'2"
  proof(rule is_ubI)
    fix y

    assume Y : "y \<in> Ys"

    then obtain x where X: "(x, y) \<in> S"
      using S2
      by(auto)

    have "(x, y) <[ w'"
      using is_ubE[OF Ub X]
      by auto

    then show "y <[ w'2"
      using W'
      by(auto simp add: prod_pleq)
  qed

  have "suprx <[ w'1" "supry <[ w'2"
    using is_supD2[OF Hx Ub_Xs] is_supD2[OF Hy Ub_Ys]
    by auto

  then show "(suprx, supry) <[ w'"
    using W'
    by(auto simp add: prod_pleq)
qed

lemma is_ub_prod :
  assumes Hx : "is_ub Xs ubx"
  assumes Hy : "is_ub Ys uby"
  assumes S1 : "fst ` S = Xs"
  assumes S2 : "snd ` S = Ys"
  shows "is_ub S (ubx, uby)"
proof(rule is_ubI)
  fix w
  assume W_in : "w \<in> S"

  obtain w1 w2 where W:
    "w = (w1, w2)"
    by(cases w; auto)

  have W_Xs : "w1 \<in> Xs" and W_Ys : "w2 \<in> Ys"
    using S1 S2 W_in W
    using imageI[OF W_in, of fst] imageI[OF W_in, of snd]
    by(auto)

  have "w1 <[ ubx" "w2 <[ uby"
    using is_ubE[OF Hx W_Xs] is_ubE[OF Hy W_Ys] W
    by auto

  then show "w <[ (ubx, uby)"
    using W by(auto simp add: prod_pleq)
qed

instantiation prod :: (Pordps, Pordps) Pordps
begin
instance proof
  fix a b c :: "'a * 'b"

  assume "has_sup {a, b}"
  then obtain sup_ab
    where Sup_ab : "is_sup {a, b} sup_ab"
    by(auto simp add: has_sup_def)

  obtain sup_ab1 sup_ab2 where
    Sup_ab12 : "sup_ab = (sup_ab1, sup_ab2)"
    by(cases sup_ab; auto)

  assume Sup_bc : "has_sup {b, c}"
  then obtain sup_bc
    where Sup_bc : "is_sup {b, c} sup_bc"
    by(auto simp add: has_sup_def)

  obtain sup_bc1 sup_bc2 where
    Sup_bc12 : "sup_bc = (sup_bc1, sup_bc2)"
    by(cases sup_bc; auto)

  assume Sup_ac : "has_sup {a, c}"
  then obtain sup_ac
    where Sup_ac : "is_sup {a, c} sup_ac"
    by(auto simp add: has_sup_def)

  obtain sup_ac1 sup_ac2 where
    Sup_ac12 : "sup_ac = (sup_ac1, sup_ac2)"
    by(cases sup_ac; auto)

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain c1 c2 where C: "c = (c1, c2)"
    by(cases c; auto)

  have Has_sup_ab1 :
    "has_sup {a1, b1}"
    using Sup_ab Sup_ab12 A B
      is_sup_fst'[of a "{a, b}" sup_ab1 sup_ab2]
    by(auto simp add: has_sup_def)

  have Has_sup_ab2 :
    "has_sup {a2, b2}"
    using Sup_ab Sup_ab12 A B
      is_sup_snd'[of a "{a, b}" sup_ab1 sup_ab2]
    by(auto simp add: has_sup_def)

  have Has_sup_bc1 :
    "has_sup {b1, c1}"
    using Sup_bc Sup_bc12 B C
      is_sup_fst'[of b "{b, c}" sup_bc1 sup_bc2]
    by(auto simp add: has_sup_def)

  have Has_sup_bc2 :
    "has_sup {b2, c2}"
    using Sup_bc Sup_bc12 B C
      is_sup_snd'[of b "{b, c}" sup_bc1 sup_bc2]
    by(auto simp add: has_sup_def)

  have Has_sup_ac1 :
    "has_sup {a1, c1}"
    using Sup_ac Sup_ac12 A C
      is_sup_fst'[of a "{a, c}" sup_ac1 sup_ac2]
    by(auto simp add: has_sup_def)

  have Has_sup_ac2 :
    "has_sup {a2, c2}"
    using Sup_ac Sup_ac12 A C
      is_sup_snd'[of a "{a, c}" sup_ac1 sup_ac2]
    by(auto simp add: has_sup_def)

  obtain sup1 where Sup1 :
    "is_sup {a1, b1, c1} sup1"
    using pairwise_sup[OF Has_sup_ab1 Has_sup_bc1 Has_sup_ac1]
    by(auto simp add: has_sup_def)

  obtain sup2 where Sup2 :
    "is_sup {a2, b2, c2} sup2"
    using pairwise_sup[OF Has_sup_ab2 Has_sup_bc2 Has_sup_ac2]
    by(auto simp add: has_sup_def)

  have "is_sup {a, b, c} (sup1, sup2)"
    using is_sup_prod[OF Sup1 Sup2, of "{a, b, c}"]
    unfolding A B C
    by auto

  then show "has_sup {a, b, c}"
    by(auto simp add: has_sup_def)
qed
end

instantiation prod :: (Pordpsok, Pordpsok) Pordpsok
begin
instance proof
  fix a b supr :: "('a * 'b)"
  assume Aok : "a \<in> ok_S"
  assume Bok : "b \<in> ok_S"
  assume Sup : "is_sup {a, b} supr"

  obtain a1 a2 where A : "a = (a1, a2)" "a1 \<in> ok_S" "a2 \<in> ok_S"
    using Aok
    by(cases a; auto simp add: prod_ok_S)

  obtain b1 b2 where B : "b = (b1, b2)" "b1 \<in> ok_S" "b2 \<in> ok_S"
    using Bok
    by(cases b; auto simp add: prod_ok_S)

  obtain supr1 supr2 where Supr12 : "supr = (supr1, supr2)"
    by(cases supr; auto)

  have Supr_fst : "is_sup {a1, b1} supr1"
    using is_sup_fst'[of a "{a, b}" supr1 supr2] Sup
    unfolding A B Supr12
    by auto

  then have Supr_fst_ok : "supr1 \<in> ok_S"
    using pairwise_sup_ok[OF A(2) B(2) Supr_fst] by auto

  have Supr_snd : "is_sup {a2, b2} supr2"
    using is_sup_snd'[of a "{a, b}" supr1 supr2] Sup
    unfolding A B Supr12
    by auto

  then have Supr_snd_ok : "supr2 \<in> ok_S"
    using pairwise_sup_ok[OF A(3) B(3) Supr_snd] by auto

  then show "supr \<in> ok_S"
    using Supr_fst_ok Supr_snd_ok Supr12
    by(auto simp add: prod_ok_S)
qed
end


instantiation prod :: (Pord_Weakb, Pord_Weakb) Pord_Weakb
begin
definition prod_bot : 
  "(bot :: 'a * 'b) = (bot, bot)"
instance proof
  fix a :: "'a * 'b"
  show "pleq bot a"
    by(cases a; auto simp add:prod_pleq prod_bot bot_spec)
qed
end

instantiation prod :: (Pordb, Pordb) Pordb
begin
instance proof
qed
end

instantiation prod :: (Mergeableb, Mergeableb) Mergeableb
begin

definition prod_bsup :
"[^ a, b ^] =
  (case a of
    (a1, a2) \<Rightarrow> (case b of
                  (b1, b2) \<Rightarrow> (bsup a1 b1, bsup a2 b2)))"

instance proof
  fix a :: "'a  * 'b"
  fix b :: "'a * 'b"

  obtain a1 and a2 where Ha : "a = (a1, a2)" by(cases a; auto)
  obtain b1 and b2 where Hb : "b = (b1, b2)" by(cases b; auto)

  show "is_bsup a b (bsup a b)"
  proof(rule is_bsupI)

    show "pleq a (bsup a b)" using Ha Hb bsup_leq[OF bsup_spec[of a1 b1]] bsup_leq[OF bsup_spec[of a2 b2]]
      by(auto simp add:prod_bsup prod_pleq split:prod.splits)

  next
    fix bd :: "'a * 'b"
    fix sd :: "'a * 'b"

    obtain a1 and a2 where Ha : "a = (a1, a2)" by(cases a; auto)
    obtain b1 and b2 where Hb : "b = (b1, b2)" by(cases b; auto)
    obtain bd1 and bd2 where Hbd : "bd = (bd1, bd2)" by(cases bd; auto)
    obtain sd1 and sd2 where Hsd : "sd = (sd1, sd2)" by(cases sd; auto)

    obtain bsupv1 and bsupv2 where Hbsup : "bsup a b = (bsupv1, bsupv2)" by (cases "(bsup a b)"; auto)

    assume Hleq : "pleq bd b"
    assume Hsup : "is_sup {a, bd} sd"

    have Hbsv1 : "bsupv1 = bsup a1 b1" using Ha Hb Hbsup
      by(auto simp add:prod_bsup)
    have Hbsv2 : "bsupv2 = bsup a2 b2" using Ha Hb Hbsup
      by(auto simp add:prod_bsup)

    have Sup1 : "is_sup {a1, bd1} sd1" using Ha Hbd Hsd Hsup
      by(auto simp add: prod_pleq is_sup_def is_least_def is_ub_def)

    have Sup2 : "is_sup {a2, bd2} sd2" using Ha Hbd Hsd Hsup
      by(auto simp add: prod_pleq is_sup_def is_least_def is_ub_def)

    have Leq1 : "pleq bd1 b1" using Hb Hbd Hleq
      by(auto simp add: prod_pleq is_sup_def is_least_def is_ub_def)

    have Leq2 : "pleq bd2 b2" using Hb Hbd Hleq
      by(auto simp add: prod_pleq is_sup_def is_least_def is_ub_def)

    have Bsup1 : "is_bsup a1 b1 bsupv1" using Hbsup Ha Hb bsup_spec[of a1 b1]
      by(auto simp add:prod_bsup)

    have Bsup2 : "is_bsup a2 b2 bsupv2" using Hbsup Ha Hb bsup_spec[of a2 b2]
      by(auto simp add:prod_bsup)

    have Conc1 : "pleq sd1 (bsup a1 b1)" using is_bsupD2[OF Bsup1 Leq1 Sup1] Hbsv1
      by(auto simp add:is_bsup_def is_least_def is_bub_def)
      
    have Conc2 : "pleq sd2 (bsup a2 b2)" using is_bsupD2[OF Bsup2 Leq2 Sup2] Hbsv2
      by(auto simp add:is_bsup_def is_least_def is_bub_def)

    show "pleq sd (bsup a b)" using Ha Hb Hbsup Hbsv1 Hbsv2 Hsd Conc1 Conc2
      by(auto simp add: prod_pleq prod_bsup)

  next

      fix x :: "'a * 'b"
      obtain a1 and a2 where Ha : "a = (a1, a2)" by(cases a; auto)
      obtain b1 and b2 where Hb : "b = (b1, b2)" by(cases b; auto)
      obtain x1 and x2 where Hx : "x = (x1, x2)" by(cases x; auto)
      obtain bsupv1 and bsupv2 where Hbsup : "bsup a b = (bsupv1, bsupv2)" by (cases "(bsup a b)"; auto)

      have Hbsv1 : "bsupv1 = bsup a1 b1" using Ha Hb Hbsup
        by(auto simp add:prod_bsup)
      have Hbsv2 : "bsupv2 = bsup a2 b2" using Ha Hb Hbsup
        by(auto simp add:prod_bsup)

      assume Hbub : "is_bub a b x"

      have Hbub1 : "is_bub a1 b1 x1"
      proof(rule is_bubI)
        show "pleq a1 x1" using Hbub Ha Hx by(auto simp add:is_bub_def is_sup_def prod_pleq)
      next
        fix bd1 :: 'a
        fix sd1 :: 'a
        assume H1 : "pleq bd1 b1"
        assume H2 : "is_sup {a1,bd1} sd1"

        have Hpleq' : "pleq (bd1, bot) b" using H1 Hb bot_spec[of b2]
          by (auto simp add: prod_pleq)
        
        have Hsup' : "is_sup {a, (bd1, bot)} (sd1, a2)" using Ha bot_spec[of a2] H2
          by(auto simp add:is_sup_def is_least_def is_ub_def leq_refl prod_pleq)

        show "pleq sd1 x1" using is_bubD2[OF Hbub Hpleq' Hsup'] Hx
          by(simp add:prod_pleq)
      qed
  
      have Hbub2 : "is_bub a2 b2 x2" 
      proof(rule is_bubI)
        show "pleq a2 x2" using Hbub Ha Hx by(auto simp add:is_bub_def is_sup_def prod_pleq)
      next
        fix bd2 :: 'b
        fix sd2 :: 'b
        assume H1 : "pleq bd2 b2"
        assume H2 : "is_sup {a2,bd2} sd2"

        have Hpleq' : "pleq (bot, bd2) b" using H1 Hb bot_spec[of b1]
          by (auto simp add: prod_pleq)
        
        have Hsup' : "is_sup {a, (bot, bd2)} (a1, sd2)" using Ha bot_spec[of a1] H2
          by(auto simp add:is_sup_def is_least_def is_ub_def leq_refl prod_pleq)

        show "pleq sd2 x2" using is_bubD2[OF Hbub Hpleq' Hsup'] Hx
          by(simp add:prod_pleq)
      qed

      show "pleq (bsup a b) x" using Hx Ha Hb Hbub1 Hbub2 bsup_spec[of a1 b1] bsup_spec[of a2 b2]
        by(auto simp add:is_bsup_def is_least_def prod_pleq prod_bsup)
    qed
  qed
end

instantiation prod :: (Pordc_all, Pordc_all) Pordc_all
begin

instance proof
  fix a b :: "'a * 'b"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain ub1 where Ub1 : "is_ub {a1, b1} ub1"
    using ub2_all[of a1 b1]
    by(auto simp add: has_ub_def)

  obtain ub2 where Ub2 : "is_ub {a2, b2} ub2"
    using ub2_all[of a2 b2]
    by(auto simp add: has_ub_def)

  have "is_ub {a, b} (ub1, ub2)"
    using is_ub_prod[OF Ub1 Ub2, of "{a, b}"]
    unfolding A B
    by auto

  then show "has_ub {a, b}"
    by(auto simp add: has_ub_def)
qed
end

instantiation prod :: (Bump, Bump) Bump
begin

definition prod_bump :
  "bump x = (case x of (x1, x2) \<Rightarrow> (bump x1, bump x2))"

instance proof
  fix x :: "'a * 'b"
  show "bump x \<noteq> x"
    by(cases x; auto simp add: prod_bump bump_neq)
next
  fix x :: "'a * 'b"
  show "x <[ bump x"
    by(cases x; auto simp add: prod_bump prod_pleq bump_geq)
qed

end

end