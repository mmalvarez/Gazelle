theory Pord_Facts
  imports Pord
begin

(* Pord_Facts
 * some useful lemmas
 *)

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

