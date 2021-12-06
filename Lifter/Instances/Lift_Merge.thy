theory Lift_Merge
  imports "../Lifter"
begin

(*
 * merge 
 *)


definition merge_l ::
  "('x, 'a1, 'b) lifting \<Rightarrow>
   ('x, 'a2, 'b) lifting \<Rightarrow>
   ('x, 'a1 * 'a2, 'b) lifting" where
"merge_l t1 t2 =
    LMake
      (\<lambda> s a b . 
        (case a of (a1, a2) \<Rightarrow>
          LUpd t1 s a1 (LUpd t2 s a2 b )))
      (\<lambda> s b . (LOut t1 s b, LOut t2 s b))
      (\<lambda> s . LBase t1 s)"

locale merge_l_valid_weak' = 
  fixes l1 :: "('x, 'a1, 'b) lifting" 
  fixes l2 :: "('x, 'a2, 'b) lifting"

locale merge_l_valid_weak =
  merge_l_valid_weak' +
  l_ortho +
  in1 : lifting_valid_weak l1 S1 +
  in2 : lifting_valid_weak l2 S2

sublocale merge_l_valid_weak \<subseteq> out : lifting_valid_weak "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s
  fix a :: "'b * 'd"
  fix b :: "'c"
  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have "LUpd l2 s a2 (LUpd l1 s a1 b) \<in> S1 s"
    unfolding sym[OF compat]
    using in1.put_S
    by auto

  then show "LUpd (merge_l l1 l2) s a b \<in> S1 s \<inter> S2 s" using A in2.put_S
    by(simp add: merge_l_def compat)

next
  fix s b
  fix a :: "'b * 'd"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have "LOut l2 s (LUpd l1 s a1 (LUpd l2 s a2 b)) = a2"
    unfolding compat
    using in2.put_get
    by auto

  then show "LOut (merge_l l1 l2) s (LUpd (merge_l l1 l2) s a b) = a"
    using A in1.put_get 
    by(auto simp add: merge_l_def)

next
  fix s 
  fix b :: "'c"
  assume "b \<in> S1 s \<inter> S2 s"

  then have B1 : "b \<in> S1 s" and B2 : "b \<in> S2 s"
    by auto

  have Leq1 : "b <[ (LUpd l2 s (LOut l2 s b) b)"
    using in2.get_put_weak[OF B2]
    by auto

  have Eq : "LOut l1 s (LUpd l2 s (LOut l2 s b) b) = LOut l1 s b"
    using put2_get1
    by auto

  have Upd_in : "LUpd l2 s (LOut l2 s b) b \<in> S1 s"
    using put2_S1[OF B1]
    by auto

  have "b <[ LUpd l1 s (LOut l1 s b) b"
    using in1.get_put_weak[OF B1] by auto

  show "b <[ LUpd (merge_l l1 l2) s (LOut (merge_l l1 l2) s b) b"
    using leq_trans[OF Leq1 in1.get_put_weak[OF Upd_in]]
    by(auto simp add: merge_l_def Eq)
qed

lemma (in merge_l_valid_weak) ax :
  shows "lifting_valid_weak (merge_l l1 l2) (\<lambda> x . S1 x \<inter> S2 x)"
  using out.lifting_valid_weak_axioms
  by auto

lemma (in merge_l_valid_weak) ax_g :
  assumes H : "\<And> x . S' x = (\<lambda> x . S1 x \<inter> S2 x) x"
  shows "lifting_valid_weak (merge_l l1 l2) S'"
proof-
  have "S' = (\<lambda> x . S1 x \<inter> S2 x)"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_weak_axioms
    by auto
qed

locale merge_l_valid_ext = merge_l_valid_weak' +
  in1 : lifting_valid_ext l1 +
  in2 : lifting_valid_ext l2 

sublocale merge_l_valid_ext \<subseteq> out : lifting_valid_ext "merge_l l1 l2"
proof

  fix s
  fix a :: "'b * 'd"
  fix b :: "'c"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have Leq1 : "b <[ LUpd l2 s a2 b"
    using in2.get_put by auto

  have Leq2 : "LUpd l2 s a2 b <[ LUpd l1 s a1 (LUpd l2 s a2 b)"
    using in1.get_put by auto

  show "b <[ LUpd (merge_l l1 l2) s a b" 
    using A leq_trans[OF Leq1 Leq2]
    by(auto simp add: merge_l_def)
qed

lemma (in merge_l_valid_ext) ax :
  shows "lifting_valid_ext (merge_l l1 l2)"
  using out.lifting_valid_ext_axioms by auto

locale merge_l_valid_base_ext =
  l_ortho_base +
  in1 : lifting_valid_base_ext l1 S1 +
  in2 : lifting_valid_base_ext l2 S2

sublocale merge_l_valid_base_ext \<subseteq> out : lifting_valid_base_ext "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s :: "'a"

  show "LBase (merge_l l1 l2) s = \<bottom>"
    using in1.base
    by(auto simp add: merge_l_def)
qed

lemma (in merge_l_valid_base_ext) ax :
  shows "lifting_valid_base_ext (merge_l l1 l2)"
  using out.lifting_valid_base_ext_axioms
  by auto

locale merge_l_valid_ok_ext = l_ortho_ok +
  in1 : lifting_valid_ok_ext l1 S1 +
  in2 : lifting_valid_ok_ext l2 S2

sublocale merge_l_valid_ok_ext \<subseteq> out : lifting_valid_ok_ext "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s

  show "ok_S \<subseteq> S1 s \<inter> S2 s"
    using in1.ok_S_valid in2.ok_S_valid by auto
next
  fix s 
  fix a :: "'b * 'd"
  fix b :: "'c"

  assume B_ok : "b \<in> ok_S"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  show "LUpd (merge_l l1 l2) s a b \<in> ok_S"
    using A in1.ok_S_put in2.ok_S_put B_ok
    by(auto simp add: merge_l_def)
qed

lemma (in merge_l_valid_ok_ext) ax :
  shows "lifting_valid_ok_ext (merge_l l1 l2) (\<lambda> x . S1 x \<inter> S2 x)"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in merge_l_valid_ok_ext) ax_g :
  assumes H : "\<And> x . S' x = (\<lambda> x . S1 x \<inter> S2 x) x"
  shows "lifting_valid_ok_ext (merge_l l1 l2) S'"
proof-
  have "S' = (\<lambda> x . S1 x \<inter> S2 x)"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_ok_ext_axioms
    by auto
qed

(* TODO: make sure we don't actually need this. *)
(*
locale merge_l_valid_pres_ext = merge_l_valid_weak +
  l_ortho_pres +
  in1 : lifting_valid_pres_ext l1 S1 +
  in2 : lifting_valid_pres_ext l2 S2


sublocale merge_l_valid_pres_ext \<subseteq> out: lifting_valid_pres_ext "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix v supr :: "'c"
  fix V
  fix f :: "'a \<Rightarrow> 'b * 'd \<Rightarrow> 'b * 'd"
  fix s :: 'a
  assume Vin : "v \<in> V"
  assume Vsub : "V \<subseteq> S1 s \<inter> S2 s"
  then have Vsub1 : "V \<subseteq> S1 s" and Vsub2 : "V \<subseteq> S2 s"
    by auto

  assume Supr : "is_sup V supr" 
  assume Supr_in : "supr \<in> S1 s \<inter> S2 s"

  then have Supr_in1 : "supr \<in> S1 s" and Supr_in2 : "supr \<in> S2 s"
    by auto
(*
  obtain f1 f2 where F: "f = (f1, f2)"
    by(cases f; auto)
*)
(*
  show "is_sup (LMap (merge_l l1 l2) f s ` V)
        (LMap (merge_l l1 l2) f s supr)"
    apply(simp add: merge_l_def)
*)

  obtain x1 x2 where X12 : "f s (LOut l1 s supr, LOut l2 s supr) = (x1, x2)"
    by(fastforce)

  have Supr' : "is_sup {LUpd l1 s x1 supr, LUpd l2 s x2 supr} (LUpd l1 s x1 (LUpd l2 s x2 supr))"
    using compat_pres_sup
    by auto


  show "is_sup (LMap (merge_l l1 l2) f s ` V) (LMap (merge_l l1 l2) f s supr)"
(*
    using compat_pres_pair[OF Vin Vsub1 Vsub2 Supr Supr_in, of f]
    by(auto simp add: merge_l_def)
*)
  proof(rule is_supI)
    fix x

    assume X: "x \<in> LMap (merge_l l1 l2) f s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (merge_l l1 l2) f s xo = x"
      by auto

    show "x <[ LMap (merge_l l1 l2) f s supr"
      using Xo
      apply(auto simp add: merge_l_def split: prod.splits)


    qed
*)

locale merge_l_valid_pairwise_ext =
  l_ortho +
  in1 : lifting_valid_pairwise_ext S1 +
  in2 : lifting_valid_pairwise_ext S2

sublocale merge_l_valid_pairwise_ext \<subseteq> out : lifting_valid_pairwise_ext "(\<lambda> x . S1 x \<inter> S2 x)"
proof
  show "\<And>x1 x2 x3 s s12 s23 s13 s123.
       x1 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       x2 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       x3 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       is_sup {x1, x2} s12 \<Longrightarrow>
       s12 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       is_sup {x2, x3} s23 \<Longrightarrow>
       s23 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       is_sup {x1, x3} s13 \<Longrightarrow>
       s13 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       is_sup {x1, x2, x3} s123 \<Longrightarrow> s123 \<in> S1 s \<inter> S2 s"
    using in1.pairwise_S in2.pairwise_S
    by blast
qed

lemma (in merge_l_valid_pairwise_ext) ax :
  shows "lifting_valid_pairwise_ext (\<lambda> x . S1 x \<inter> S2 x)"
  using out.lifting_valid_pairwise_ext_axioms
  by auto

lemma (in merge_l_valid_pairwise_ext) ax_g :
  assumes H: "\<And> x . S' x = (\<lambda> x . S1 x \<inter> S2 x) x"
  shows "lifting_valid_pairwise_ext S'"
proof-
  have "S' = (\<lambda> x . S1 x \<inter> S2 x)"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_pairwise_ext_axioms
    by auto
qed


locale merge_l_ortho' =
  fixes l1 :: "('a, 'b1, 'c :: {Mergeable, Pordps}) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c1 set"
  fixes l2 :: "('a, 'b2, 'c) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c2 set"
  fixes l3 :: "('a, 'b3, 'c) lifting"
  fixes S3 :: "'a \<Rightarrow> 'c3 set"

locale merge_l_ortho = merge_l_ortho' +
  orth1_2 : l_ortho l1 S1 l2 S2 + 
  orth1_3 : l_ortho l1 S1 l3 S3 +
  orth2_3 : l_ortho l2 S2 l3 S3 
  (* + valid3 : lifting_valid_weak_pres l3 S3*)
(* TODO may need more validity assumptions. *)

sublocale merge_l_ortho \<subseteq> out : l_ortho "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x" l3 S3
proof
  fix s

  have Supr : "is_sup {LBase l2 s, LBase l2 s} (LBase l2 s)"
    using sup_singleton[of "LBase l2 s"]
    by auto

  have Supr' : "is_sup {LBase l2 s, LBase l2 s}
     [^ LBase l2 s, LBase l2 s ^]"
    using bsup_sup[OF Supr bsup_spec]
    by auto

  then have "[^ LBase l2 s, LBase l2 s ^] = LBase l2 s"
    using is_sup_unique[OF Supr Supr'] by auto

  then show "LBase (merge_l l1 l2) s = LBase l3 s"
    using orth1_3.eq_base[of s] orth2_3.eq_base[of s]
    by(auto simp add: merge_l_def)

next
  fix b :: 'c
  fix a1_2 :: "'b * 'd"
  fix a3 :: 'e
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LUpd (merge_l l1 l2) s a1_2 (LUpd l3 s a3 b) = LUpd l3 s a3 (LUpd (merge_l l1 l2) s a1_2 b)" using A1_2
    by(auto simp add: merge_l_def orth1_3.compat orth2_3.compat)

next
  fix b :: 'c
  fix a1_2 :: "'b * 'd"
  fix a3 :: 'e
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LOut l3 s (LUpd (merge_l l1 l2) s a1_2 b) = LOut l3 s b" using A1_2
    by(auto simp add: merge_l_def orth1_3.put1_get2 orth2_3.put1_get2)
next

  fix b :: 'c
  fix a1_2 :: "'b * 'd"
  fix a3 :: 'e
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LOut (merge_l l1 l2) s (LUpd l3 s a3 b) = LOut (merge_l l1 l2) s b" using A1_2
    by(auto simp add: merge_l_def orth1_3.put2_get1 orth2_3.put2_get1)
next

  fix b s
  fix a1_2 :: "'b * 'd"
  assume B: "b \<in> S3 s"

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  have Up2 : "(LUpd l2 s a2 b) \<in> S3 s"
    using orth2_3.put1_S2[OF B] by auto

  have Up1 : "(LUpd l1 s a1 (LUpd l2 s a2 b)) \<in> S3 s"
    using orth1_3.put1_S2[OF Up2]
    by auto

  then show "LUpd (merge_l l1 l2) s a1_2 b \<in> S3 s" using A1_2
    by(auto simp add: merge_l_def)
next

  fix b s
  fix a3 :: 'e

  assume B: "b \<in> S1 s \<inter> S2 s"

  then have B1 : "b \<in> S1 s" and B2 : "b \<in> S2 s"
    by auto

  have Conc1 : "LUpd l3 s a3 b \<in> S1 s"
    using orth1_3.put2_S1[OF B1] by auto

  have Conc2 : "LUpd l3 s a3 b \<in> S2 s"
    using orth2_3.put2_S1[OF B2] by auto

  show "LUpd l3 s a3 b \<in> S1 s \<inter> S2 s"
    using Conc1 Conc2
    by auto
qed

lemma (in merge_l_ortho) ax :
  shows "l_ortho (merge_l l1 l2) (\<lambda> x . S1 x \<inter> S2 x) l3 S3"
  using out.l_ortho_axioms
  by auto

lemma (in merge_l_ortho) ax_g :
  assumes H1_2 : "\<And> x . S1_2' x = S1 x \<inter> S2 x"
  assumes H3 : "\<And> x . S3' x = S3 x"
  shows "l_ortho (merge_l l1 l2) S1_2' l3 S3'" 
proof-
  have H1_2' : "S1_2' = (\<lambda> x . S1 x \<inter> S2 x)" using H1_2 by auto
  have H3' : "S3' = S3" using H3 by auto
  show ?thesis
    using ax unfolding H1_2' H3'
    by auto
qed

lemma (in merge_l_ortho) ax_g' :
  assumes H1 : "\<And> x . S1' x = S1 x"
  assumes H2 : "\<And> x . S2' x = S2 x"
  assumes H3 : "\<And> x . S3' x = S3 x"
  shows "l_ortho (merge_l l1 l2) (\<lambda> x . S1' x \<inter> S2' x) l3 S3'" 
proof-
  have H1' : "S1' = S1" using H1 by auto
  have H2' : "S2' = S2" using H2 by auto
  have H3' : "S3' = S3" using H3 by auto
  show ?thesis
    using ax unfolding H1' H2' H3'
    by auto
qed

lemma (in merge_l_ortho) ax_comm :
  shows "l_ortho l3 S3 (merge_l l1 l2) (\<lambda> x . S1 x \<inter> S2 x)"
  using out.comm.l_ortho_axioms
  by auto

lemma (in merge_l_ortho) ax_g_comm :
  assumes H1_2 : "\<And> x . S1_2' x = S1 x \<inter> S2 x"
  assumes H3 : "\<And> x . S3' x = S3 x"
  shows "l_ortho l3 S3' (merge_l l1 l2) S1_2' " 
proof-
  have H1_2' : "S1_2' = (\<lambda> x . S1 x \<inter> S2 x)" using H1_2 by auto
  have H3' : "S3' = S3" using H3 by auto
  show ?thesis
    using ax_comm unfolding H1_2' H3'
    by auto
qed

lemma (in merge_l_ortho) ax_g'_comm :
  assumes H1 : "\<And> x . S1' x = S1 x"
  assumes H2 : "\<And> x . S2' x = S2 x"
  assumes H3 : "\<And> x . S3' x = S3 x"
  shows "l_ortho l3 S3' (merge_l l1 l2) (\<lambda> x . S1' x \<inter> S2' x) " 
proof-
  have H1' : "S1' = S1" using H1 by auto
  have H2' : "S2' = S2" using H2 by auto
  have H3' : "S3' = S3" using H3 by auto
  show ?thesis
    using ax_comm unfolding H1' H2' H3'
    by auto
qed

locale merge_l_ortho_base_ext = merge_l_ortho' +
  orth1_2 : l_ortho_base_ext l1 l2 + 
  orth1_3 : l_ortho_base_ext l1 l3 +
  orth2_3 : l_ortho_base_ext l2 l3
(*
locale merge_l_ortho_base = merge_l_ortho +
  orth1_2 : l_ortho_base l1 S1 l2 S2 + 
  orth1_3 : l_ortho_base l1 S1 l3 S3 +
  orth2_3 : l_ortho_base l2 S2 l3 S3 
*)
sublocale merge_l_ortho_base_ext  \<subseteq> out : l_ortho_base_ext "merge_l l1 l2" l3
proof
  fix s

  show "LBase (merge_l l1 l2) s = \<bottom>"
    using orth1_2.compat_base1
    by(auto simp add: merge_l_def)
next

  fix s

  show "LBase l3 s = \<bottom>"
    using orth1_3.compat_base2
    by(auto)
qed

lemma (in merge_l_ortho_base_ext) ax :
  shows "l_ortho_base_ext (merge_l l1 l2) l3"
  using out.l_ortho_base_ext_axioms by auto

lemma (in merge_l_ortho_base_ext) ax_comm :
  shows "l_ortho_base_ext l3 (merge_l l1 l2)"
  using out.comm.l_ortho_base_ext_axioms by auto

locale merge_l_ortho_ok_ext = merge_l_ortho' +
  orth1_2 : l_ortho_ok_ext l1 l2 + 
  orth1_3 : l_ortho_ok_ext l1 l3 +
  orth2_3 : l_ortho_ok_ext l2 l3

sublocale merge_l_ortho_ok_ext \<subseteq> out : l_ortho_ok_ext "merge_l l1 l2" l3 .



(*
locale merge_l_ortho_pres = merge_l_ortho +
  orth1_2 : l_ortho_pres l1 S1 l2 S2 +
  orth1_3 : l_ortho_pres l1 S1 l3 S3 +
  orth2_3 : l_ortho_pres l2 S2 l3 S3 +
  (* see if we can avoid this presonly assumptions - i don't think we can though. *)
  in1 : lifting_valid_pres l1 S1 +
  in2 : lifting_valid_pres l2 S2 +
  in3 : lifting_valid_pres l3 S3

sublocale merge_l_ortho_pres \<subseteq> l_ortho_pres "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x" l3 S3
proof
  fix a1_2 :: "'b * 'd"
  fix a3 s 
  fix x :: 'c

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  have Merge_eq : "LUpd (merge_l l1 l2) s a1_2 (LUpd l3 s a3 x) = LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x))"
    using A1_2
    by(auto simp add: merge_l_def)

  have Sup23 : "is_sup {LUpd l2 s a2 x, LUpd l3 s a3 x} (LUpd l2 s a2 (LUpd l3 s a3 x))"
    using orth2_3.compat_pres_sup
    by auto

  have Sup123 : "is_sup {LUpd l1 s a1 (LUpd l3 s a3 x), LUpd l2 s a2 (LUpd l3 s a3 x)} (LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x)))"
    using orth1_2.compat_pres_sup
    by auto

  have Sup13 : "is_sup {LUpd l1 s a1 x, LUpd l3 s a3 x} (LUpd l1 s a1 (LUpd l3 s a3 x))"
    using orth1_3.compat_pres_sup
    by auto

  have Eq_123 : "({LUpd l1 s a1 x, LUpd l3 s a3 x} \<union> {LUpd l2 s a2 x, LUpd l3 s a3 x}) = {LUpd l1 s a1 x, LUpd l2 s a2 x, LUpd l3 s a3 x}"
    by auto

  have Sup123' : "is_sup ({LUpd l1 s a1 x, LUpd l2 s a2 x, LUpd l3 s a3 x}) (LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x)))"
    using sup_union1[OF Sup13 Sup23 Sup123]
    unfolding Eq_123
    by auto

  have Sup12 : "is_sup {LUpd l1 s a1 x, LUpd l2 s a2 x} (LUpd l1 s a1 (LUpd l2 s a2 x))"
    using orth1_2.compat_pres_sup
    by auto

  have Sup3 : "is_sup {LUpd l3 s a3 x} (LUpd l3 s a3 x)"
    using sup_singleton
    by auto

  have Eq_123' : "{LUpd l1 s a1 x, LUpd l2 s a2 x, LUpd l3 s a3 x} = {LUpd l1 s a1 x, LUpd l2 s a2 x} \<union> {LUpd l3 s a3 x}"
    by auto

  have Sup123'' : "is_sup ({LUpd l1 s a1 x, LUpd l2 s a2 x} \<union> {LUpd l3 s a3 x}) (LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x)))"
    using Sup123' unfolding Eq_123'
    by auto

  have Conc' : "is_sup {(LUpd l1 s a1 (LUpd l2 s a2 x)), LUpd l3 s a3 x} (LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x)))"
    using sup_union2[OF Sup12 Sup3 Sup123'']
    by auto

  have Merge_eq' : "LUpd (merge_l l1 l2) s a1_2 x = LUpd l1 s a1 (LUpd l2 s a2 x)"
    using A1_2
    by(auto simp add: merge_l_def)

  show "is_sup {LUpd (merge_l l1 l2) s a1_2 x, LUpd l3 s a3 x} (LUpd (merge_l l1 l2) s a1_2 (LUpd l3 s a3 x))"
    using Conc' unfolding Merge_eq Merge_eq'
    by simp
qed
*)

end