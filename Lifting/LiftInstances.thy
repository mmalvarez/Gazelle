theory LiftInstances imports LiftUtils
begin

(* TODOs :
  - proofs for commutativity lifting
  - proofs for associativity lifting
  - proofs for var map lifting
  - proofs about LUBs
*)

(*
identity lifting
*)

definition id_l' ::
  "('a, 'a) lifting'" where
  "id_l' = id"

definition id_pl ::
  "('x, 'a, 'a) plifting" where
"id_pl =
  \<lparr> LUpd = (\<lambda> s a a' . a)
  , LOut = (\<lambda> s a . Some a)
  , LBase = (\<lambda> s . undefined) \<rparr>" 

abbreviation id_l :: "('x, 'a, 'a) lifting" where
"id_l \<equiv> plifting.extend (id_pl :: ('x, 'a, 'a) plifting) \<lparr> LPost = \<lambda> s a . a \<rparr>"

definition id_pv :: "('x, 'a, 'a) pliftingv" where
"id_pv = \<lparr> LOutS = (\<lambda> _ . UNIV) \<rparr>"


lemma id_pl_valid : "plifting_valid (id_pl)"
  apply (rule plifting_valid_intro)
     apply(simp add:id_pl_def)
    apply(simp add:id_pl_def)
  done


lemma id_pl_pv_valid : "plifting_pv_valid id_pl id_pv"
  apply(rule plifting_pv_valid_intro)
    apply(rule id_pl_valid)
   apply(auto simp add: id_pl_def id_pv_def)
  done

lemma id_l_pv_valid : "lifting_pv_valid id_l id_pv"
  apply(rule lifting_pv_valid_intro)
    apply(rule plifting_pv_valid_cast) apply(rule id_pl_pv_valid)
   apply(auto simp add: id_pl_def id_pv_def plifting.defs)
  done

(*
trivial ordering
*)

definition triv_l' ::
  "('a, 'b) lifting' \<Rightarrow> ('a, 'b md_triv) lifting'" where
"triv_l' t' =
  (case_md_triv t')"

definition triv_pl ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> ('x, 'a, 'b md_triv) plifting" where
"triv_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of (mdt b') \<Rightarrow> (mdt ( (LUpd t s a b')))))
  , LOut = (\<lambda> s b . (case b of (mdt b') \<Rightarrow> (LOut t s b')))
  , LBase = (\<lambda> s . mdt (LBase t s)) \<rparr>"

definition triv_l ::
  "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow> ('x, 'a, 'b md_triv) lifting" where
"triv_l t =
  plifting.extend (triv_pl t) \<lparr> LPost = (\<lambda> s b . (case b of (mdt b') \<Rightarrow> mdt (LPost t s b'))) \<rparr>"

definition triv_pv ::
  "('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow> ('x, 'a, 'b md_triv) pliftingv" where
"triv_pv v =
  \<lparr> LOutS = (\<lambda> s . mdt ` LOutS v s) \<rparr>"



lemma triv_pl_valid : "plifting_valid t \<Longrightarrow> plifting_valid (triv_pl t)"
proof(rule plifting_valid_intro)
  fix s a b
  assume H : "plifting_valid t"
  show "LOut (triv_pl t) s (LUpd (triv_pl t) s a b) = Some a"
    using plifting_valid_unfold1[OF H]
    by(auto simp add:triv_pl_def split:md_triv.splits)
next
  fix s a a' b
  assume H : "plifting_valid t"
  show "LUpd (triv_pl t) s a (LUpd (triv_pl t) s a' b) = LUpd (triv_pl t) s a b"
    using plifting_valid_unfold2[OF H]
    by(auto simp add:triv_pl_def split:md_triv.splits)
qed

lemma triv_pl_pv_valid : 
  "plifting_pv_valid (t :: ('x, 'a, 'b, 'z1) plifting_scheme) (v :: ('x, 'a, 'b, 'z2) pliftingv_scheme) \<Longrightarrow> 
   plifting_pv_valid (triv_pl t) (triv_pv v)"
proof(rule plifting_pv_valid_intro)
  assume H : "plifting_pv_valid t v"
  show "plifting_valid (triv_pl t)" using triv_pl_valid[OF plifting_pv_valid_unfold1[OF H]] by auto
next
  fix s a b
  assume H : "plifting_pv_valid t v"
  show "LUpd (triv_pl t) s a b \<in> LOutS (triv_pv v) s"
    using plifting_pv_valid_unfold2[OF H]
    by(auto simp add:triv_pl_def triv_pv_def split:md_triv.splits)
next
  fix s b
  assume H : "plifting_pv_valid t v"
  assume H' : "b \<in> LOutS (triv_pv v) s"
  show "\<exists>out. LOut (triv_pl t) s b = Some out \<and>
                 b = LUpd (triv_pl t) s out b"
    using plifting_pv_valid_unfold3[OF H] H'
    by(auto simp add:triv_pl_def triv_pv_def split:md_triv.splits)
qed

lemma triv_l_pv_valid :
  assumes H : "lifting_pv_valid t v"
  shows "lifting_pv_valid (triv_l t) (triv_pv v)"
proof(rule lifting_pv_valid_intro)
  show "plifting_pv_valid (triv_l t) (triv_pv v)"
    unfolding triv_l_def
  proof(rule plifting_pv_valid_cast)
    show "plifting_pv_valid (triv_pl t) (triv_pv v)"
      using triv_pl_pv_valid[OF lifting_pv_valid_unfold1[OF H]]
      by(auto simp add: triv_l_def triv_pv_def)
  qed
next
  fix s a b
  assume H1 : "b \<in> LOutS (triv_pv v) s"
  show "LPost (triv_l t) s b \<in> LOutS (triv_pv v) s" unfolding triv_l_def
    using lifting_pv_valid_unfold2[OF H] H1
    by(auto simp add: triv_pl_def triv_pv_def plifting.defs split:md_triv.splits)
next
  fix s a b
  assume H1 : "b \<in> LOutS (triv_pv v) s "
  show "LOut (triv_l t) s (LPost (triv_l t) s b) = LOut (triv_l t) s b"
    using lifting_pv_valid_unfold3[OF H] H1
    by(auto simp add: triv_l_def triv_pl_def triv_pv_def plifting.defs split:md_triv.splits)
qed
(*
option ordering
*)

definition option_l' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a, 'b option) lifting'" where
"option_l' t =
  case_option undefined t "

(*
definition option_pl ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> ('x, 'a, 'b option) plifting" where
"option_pl t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              Some b' \<Rightarrow> Some (LUpd t s a b')
              | None \<Rightarrow> Some (LNew t s a)))
  , LOut = (\<lambda> s b . (case b of Some b' \<Rightarrow> LOut t s b'))
  , LBase = (\<lambda> s . None)\<rparr>"
*)

definition option_pl ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> ('x, 'a, 'b option) plifting" where
"option_pl t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              Some b' \<Rightarrow> Some (LUpd t s a b')
              | None \<Rightarrow> Some (LNew t s a)))
  , LOut = (\<lambda> s b . (case b of Some b' \<Rightarrow> LOut t s b'
                      | None \<Rightarrow> None))
  , LBase = (\<lambda> s . None)\<rparr>"

definition option_l ::
  "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow> ('x, 'a, 'b option) lifting" where
"option_l t =
  plifting.extend (option_pl t)
    \<lparr> LPost = (\<lambda> s b . (case b of (Some b') \<Rightarrow> Some (LPost t s b')
                                  | None \<Rightarrow> None)) \<rparr>"

definition option_pv ::
  "('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow> ('x, 'a, 'b option) pliftingv" where
"option_pv v =
  \<lparr> LOutS = (\<lambda> s . Some ` (LOutS v s)) \<rparr>"

lemma option_pl_valid :
  assumes H : "plifting_valid t"
  shows "plifting_valid (option_pl t)"
proof(rule plifting_valid_intro)
  fix s a b
  show "LOut (option_pl t) s (LUpd (option_pl t) s a b) = Some a"
    using plifting_valid_unfold1[OF H]
    by(auto simp add:option_pl_def LNew_def split:option.splits)
next
  fix s a a' b
  show "LUpd (option_pl t) s a (LUpd (option_pl t) s a' b) = LUpd (option_pl t) s a b"
    using plifting_valid_unfold2[OF H]
    by(auto simp add:option_pl_def LNew_def split:option.splits)
qed

lemma option_pl_pv_valid : 
  "plifting_pv_valid (t :: ('x, 'a, 'b, 'z1) plifting_scheme) (v :: ('x, 'a, 'b, 'z2) pliftingv_scheme) \<Longrightarrow> 
   plifting_pv_valid (option_pl t) (option_pv v)"
proof(rule plifting_pv_valid_intro)
  assume H : "plifting_pv_valid t v"
  show "plifting_valid (option_pl t)" using option_pl_valid[OF plifting_pv_valid_unfold1[OF H]] by auto
next
  fix s a b
  assume H : "plifting_pv_valid t v"
  show "LUpd (option_pl t) s a b \<in> LOutS (option_pv v) s"
    using plifting_pv_valid_unfold2[OF H]
    by(auto simp add:option_pl_def option_pv_def LNew_def split:option.splits)
next
  fix s b
  assume H : "plifting_pv_valid t v"
  assume H' : "b \<in> LOutS (option_pv v) s"
  show "\<exists>out. LOut (option_pl t) s b = Some out \<and>
                 b = LUpd (option_pl t) s out b"
    using plifting_pv_valid_unfold3[OF H] H'
    by(auto simp add:option_pl_def option_pv_def)
qed

lemma option_l_pv_valid :
  assumes H : "lifting_pv_valid t v"
  shows "lifting_pv_valid (option_l t) (option_pv v)"
proof(rule lifting_pv_valid_intro)
  show "plifting_pv_valid (option_l t) (option_pv v)"
    unfolding option_l_def
  proof(rule plifting_pv_valid_cast)
    show "plifting_pv_valid (option_pl t) (option_pv v)"
      using option_pl_pv_valid[OF lifting_pv_valid_unfold1[OF H]]
      by(auto)
  qed
next
  fix s a b
  assume H1 : "b \<in> LOutS (option_pv v) s"
  show "LPost (option_l t) s b \<in> LOutS (option_pv v) s" unfolding option_l_def
    using lifting_pv_valid_unfold2[OF H] H1
    by(auto simp add: option_pl_def option_pv_def plifting.defs)
next
  fix s a b
  assume H1 : "b \<in> LOutS (option_pv v) s "
  show "LOut (option_l t) s (LPost (option_l t) s b) = LOut (option_l t) s b"
    using lifting_pv_valid_unfold3[OF H] H1
    by(auto simp add: option_l_def option_pl_def option_pv_def plifting.defs)
qed

(*
priorities
*)

definition prio_l' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a, 'b md_prio) lifting'" where
"prio_l' t =
  (\<lambda> p . (case p of
              mdp m b \<Rightarrow> t b))"

(* note: this only allows setting output priority based on syntax. *)
definition prio_pl ::
 "('x \<Rightarrow> nat) \<Rightarrow>
  ('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
  ('x, 'a, 'b md_prio) plifting" where
"prio_pl f0 t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of
                         mdp m b' \<Rightarrow> mdp m (LUpd t s a b')))
  , LOut =
      (\<lambda> s p . (case p of
                 mdp m b \<Rightarrow> LOut t s b))
  , LBase = (\<lambda> s . mdp (f0 s) (LBase t s)) \<rparr>"

definition prio_l :: "('x \<Rightarrow> nat) \<Rightarrow>
                      ('x \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> 
                      ('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow>
                      ('x, 'a, 'b md_prio) lifting" where
"prio_l f0 f1 t =
  plifting.extend (prio_pl f0 t)
    \<lparr> LPost = (\<lambda> s b . (case b of
                          mdp m b' \<Rightarrow> mdp (f1 s m) (LPost t s b'))) \<rparr>"

definition prio_pv :: "('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow>
                       ('x, 'a, 'b md_prio) pliftingv" where
"prio_pv v = \<lparr> LOutS = (\<lambda> s . { p . \<exists> m b . p = mdp m b \<and> b \<in> LOutS v s}) \<rparr>"

lemma prio_pl_valid :
  assumes H : "plifting_valid t"
  shows "plifting_valid (prio_pl f0 t)"
proof(rule plifting_valid_intro)
  fix s a b
  show "LOut (prio_pl f0 t) s (LUpd (prio_pl f0 t) s a b) = Some a"
    using plifting_valid_unfold1[OF H]
    by(auto simp add:prio_pl_def LNew_def split:md_prio.splits)
next
  fix s a a' b
  show "LUpd (prio_pl f0 t) s a (LUpd (prio_pl f0 t) s a' b) = LUpd (prio_pl f0 t) s a b"
    using plifting_valid_unfold2[OF H]
    by(auto simp add:prio_pl_def LNew_def split:md_prio.splits)
qed

lemma prio_pl_pv_valid : 
  "plifting_pv_valid (t :: ('x, 'a, 'b, 'z1) plifting_scheme) (v :: ('x, 'a, 'b, 'z2) pliftingv_scheme) \<Longrightarrow> 
   plifting_pv_valid (prio_pl f0 t) (prio_pv v)"
proof(rule plifting_pv_valid_intro)
  assume H : "plifting_pv_valid t v"
  show "plifting_valid (prio_pl f0 t)" using prio_pl_valid[OF plifting_pv_valid_unfold1[OF H]] by auto
next
  fix s a b
  assume H : "plifting_pv_valid t v"
  show "LUpd (prio_pl f0 t) s a b \<in> LOutS (prio_pv v) s"
    using plifting_pv_valid_unfold2[OF H]
    by(auto simp add:prio_pl_def prio_pv_def LNew_def split:md_prio.splits)
next
  fix s b
  assume H : "plifting_pv_valid t v"
  assume H' : "b \<in> LOutS (prio_pv v) s"
  show "\<exists>out. LOut (prio_pl f0 t) s b = Some out \<and>
                 b = LUpd (prio_pl f0 t) s out b"
    using plifting_pv_valid_unfold3[OF H] H'
    by(auto simp add:prio_pl_def prio_pv_def)
qed

lemma prio_l_pv_valid :
  assumes H : "lifting_pv_valid t v"
  shows "lifting_pv_valid (prio_l f0 f1 t) (prio_pv v)"
proof(rule lifting_pv_valid_intro)
  show "plifting_pv_valid (prio_l f0 f1 t) (prio_pv v)"
    unfolding prio_l_def
  proof(rule plifting_pv_valid_cast)
    show "plifting_pv_valid (prio_pl f0 t) (prio_pv v)"
      using prio_pl_pv_valid[OF lifting_pv_valid_unfold1[OF H]]
      by(auto)
  qed
next
  fix s a b
  assume H1 : "b \<in> LOutS (prio_pv v) s"
  show "LPost (prio_l f0 f1 t)  s b \<in> LOutS (prio_pv v) s" unfolding option_l_def
    using lifting_pv_valid_unfold2[OF H] H1
    by(auto simp add: prio_l_def prio_pl_def prio_pv_def plifting.defs)
next
  fix s a b
  assume H1 : "b \<in> LOutS (prio_pv v) s "
  show "LOut (prio_l f0 f1 t) s (LPost (prio_l f0 f1 t) s b) = LOut (prio_l f0 f1 t) s b"
    using lifting_pv_valid_unfold3[OF H] H1
    by(auto simp add: prio_l_def prio_pl_def prio_pv_def plifting.defs)
qed


definition prio_l_keep :: "('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_keep =
  prio_l (\<lambda> _ . 0) (\<lambda> _ n . n)"

definition prio_l_inc :: "('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 1 + x)"

definition prio_l_inc2 :: "('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc2 =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 2 + x)"

definition prio_l_incN :: "nat \<Rightarrow> ('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_incN n =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . n + x)"


definition prio_l_case_inc :: "('x \<Rightarrow> nat) \<Rightarrow> ('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_case_inc f =
  prio_l (\<lambda> _ . 0) (\<lambda> s x . (f s) + x)"

definition prio_l_const :: "nat \<Rightarrow> ('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_const n =
  prio_l (\<lambda> _ . n) (\<lambda> _ _ . n)"

definition prio_l_zero ::
"('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_zero =
  prio_l_const 0"

definition prio_l_one ::
"('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_one =
  prio_l_const 1"


(*
products
*)
definition fst_l' ::
  "('a, 'b1) lifting' \<Rightarrow>
   ('a, 'b1 * 'b2) lifting'" where
"fst_l' t =
  (\<lambda> x . t (fst x))"


definition fst_pl ::
  "('x, 'a, 'b1, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a, 'b1 * ('b2 :: Pordb)) plifting" where
"fst_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (LUpd t s a b1, b2)))
  , LOut = (\<lambda> s x . (LOut t s (fst x)))
  , LBase = (\<lambda> s . (LBase t s, \<bottom>)) \<rparr>"

definition fst_l ::
  "('x, 'a, 'b1, 'z) lifting_scheme \<Rightarrow> ('x, 'a, 'b1 * ('b2 :: Pordb)) lifting" where
"fst_l t =
  plifting.extend (fst_pl t)
    \<lparr> LPost = (\<lambda> s b . (case b of (b1, b2) \<Rightarrow> (LPost t s b1, b2))) \<rparr>"

definition fst_pv ::
  "('x, 'a, 'b1, 'z) pliftingv_scheme \<Rightarrow> ('x, 'a, 'b1 * ('b2 :: Pordb)) pliftingv" where
"fst_pv t =
  \<lparr> LOutS = (\<lambda> s . { b . \<exists> b1 b2 . b = (b1, b2) \<and> b1 \<in> LOutS t s} ) \<rparr>"

lemma fst_pl_valid :
  assumes H : "plifting_valid t"
  shows "plifting_valid ((fst_pl t) :: ('x, 'a, 'b1 * ('b2 :: Pordb)) plifting)"
proof(rule plifting_valid_intro)
  fix s a 
  fix b :: "'b1 * 'b2"
  show "LOut (fst_pl t) s (LUpd (fst_pl t) s a b) = Some a"
    using plifting_valid_unfold1[OF H]
    by(auto simp add:fst_pl_def LNew_def split:prod.splits)
next
  fix s a a' 
  fix b :: "'b1 * 'b2"
  show "LUpd (fst_pl t) s a (LUpd (fst_pl t) s a' b) = LUpd (fst_pl t) s a b"
    using plifting_valid_unfold2[OF H]
    by(auto simp add:fst_pl_def LNew_def split:prod.splits)
qed

lemma fst_pl_pv_valid : 
  "plifting_pv_valid (t :: ('x, 'a, 'b1, 'z1) plifting_scheme) (v :: ('x, 'a, 'b1, 'z2) pliftingv_scheme) \<Longrightarrow> 
   plifting_pv_valid ((fst_pl t) :: ('x, 'a, 'b1 * ('b2 :: Pordb)) plifting)
                     ((fst_pv v) :: ('x, 'a, 'b1 * ('b2 :: Pordb)) pliftingv)"
proof(rule plifting_pv_valid_intro)
  assume H : "plifting_pv_valid t v"
  show "plifting_valid (fst_pl t)" using fst_pl_valid[OF plifting_pv_valid_unfold1[OF H]] by auto
next
  fix s a 
  fix b :: "'b1 * 'b2"
  assume H : "plifting_pv_valid t v"
  show "LUpd (fst_pl t) s a b \<in> LOutS (fst_pv v) s"
    using plifting_pv_valid_unfold2[OF H]
    by(auto simp add:fst_pl_def fst_pv_def LNew_def split:prod.splits)
next
  fix s 
  fix b :: "'b1 * 'b2"
  assume H : "plifting_pv_valid t v"
  assume H' : "b \<in> LOutS (fst_pv v) s"
  show "\<exists>out. LOut (fst_pl t) s b = Some out \<and>
                 b = LUpd (fst_pl t) s out b"
    using plifting_pv_valid_unfold3[OF H] H'
    by(auto simp add:fst_pl_def fst_pv_def)
qed

lemma fst_l_pv_valid :
  assumes H : "lifting_pv_valid t v"
  shows "lifting_pv_valid ((fst_l t) :: ('x, 'a, 'b1 * ('b2 :: Pordb)) lifting) 
                          ((fst_pv v) :: ('x, 'a, 'b1 * ('b2 :: Pordb)) pliftingv)"
proof(rule lifting_pv_valid_intro)
  show "plifting_pv_valid (fst_l t) (fst_pv v)"
    unfolding fst_l_def
  proof(rule plifting_pv_valid_cast)
    show "plifting_pv_valid (fst_pl t) (fst_pv v)"
      using fst_pl_pv_valid[OF lifting_pv_valid_unfold1[OF H]]
      by(auto)
  qed
next
  fix s a 
  fix b :: "'b1 * 'b2"
  assume H1 : "b \<in> LOutS (fst_pv v) s"
  show "LPost (fst_l t) s b \<in> LOutS (fst_pv v) s" unfolding option_l_def
    using lifting_pv_valid_unfold2[OF H] H1
    by(auto simp add: fst_l_def fst_pl_def fst_pv_def plifting.defs)
next
  fix s a
  fix b :: "'b1 * 'b2"
  assume H1 : "b \<in> LOutS (fst_pv v) s "
  show "LOut (fst_l t) s (LPost (fst_l t) s b) = LOut (fst_l t) s b"
    using lifting_pv_valid_unfold3[OF H] H1
    by(auto simp add: fst_l_def fst_pl_def fst_pv_def plifting.defs)
qed

definition snd_l' ::
  "('a, 'b2) lifting' \<Rightarrow>
   ('a, 'b1 * 'b2) lifting'" where
"snd_l' t =
  (\<lambda> x . t (snd x))"


definition snd_pl ::
  "('x, 'a, 'b2, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a, ('b1 :: Pordb) * 'b2) plifting" where
"snd_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (b1, LUpd t s a b2)))
  , LOut = (\<lambda> s x . (LOut t s (snd x)))
  , LBase = (\<lambda> s . (\<bottom>, LBase t s)) \<rparr>"

definition snd_l ::
  "('x, 'a, 'b2, 'z) lifting_scheme \<Rightarrow> ('x, 'a, ('b1 :: Pordb) * 'b2) lifting" where
"snd_l t =
  plifting.extend (snd_pl t)
    \<lparr> LPost = (\<lambda> s b . (case b of (b1, b2) \<Rightarrow> (b1, LPost t s b2))) \<rparr>"

definition snd_pv ::
  "('x, 'a, 'b2, 'z) pliftingv_scheme \<Rightarrow> ('x, 'a, ('b1 :: Pordb) * 'b2) pliftingv" where
"snd_pv t =
  \<lparr> LOutS = (\<lambda> s . { b . \<exists> b1 b2 . b = (b1, b2) \<and> b2 \<in> LOutS t s} ) \<rparr>"

lemma snd_pl_valid :
  assumes H : "plifting_valid t"
  shows "plifting_valid ((snd_pl t) :: ('x, 'a, ('b1 :: Pordb) * 'b2) plifting)"
proof(rule plifting_valid_intro)
  fix s a 
  fix b :: "'b1 * 'b2"
  show "LOut (snd_pl t)  s (LUpd (snd_pl t)  s a b) = Some a"
    using plifting_valid_unfold1[OF H]
    by(auto simp add:snd_pl_def LNew_def split:prod.splits)
next
  fix s a a' 
  fix b :: "'b1 * 'b2"
  show "LUpd (snd_pl t)  s a (LUpd (snd_pl t)  s a' b) = LUpd (snd_pl t)  s a b"
    using plifting_valid_unfold2[OF H]
    by(auto simp add:snd_pl_def LNew_def split:prod.splits)
qed

lemma snd_pl_pv_valid : 
  "plifting_pv_valid (t :: ('x, 'a, 'b2, 'z1) plifting_scheme) (v :: ('x, 'a, 'b2, 'z2) pliftingv_scheme) \<Longrightarrow> 
   plifting_pv_valid ((snd_pl t) :: ('x, 'a, ('b1 :: Pordb) * 'b2) plifting)
                     ((snd_pv v) :: ('x, 'a, ('b1 :: Pordb) * 'b2) pliftingv)"
proof(rule plifting_pv_valid_intro)
  assume H : "plifting_pv_valid t v"
  show "plifting_valid (snd_pl t)" using snd_pl_valid[OF plifting_pv_valid_unfold1[OF H]] by auto
next
  fix s a 
  fix b :: "'b1 * 'b2"
  assume H : "plifting_pv_valid t v"
  show "LUpd (snd_pl t) s a b \<in> LOutS (snd_pv v) s"
    using plifting_pv_valid_unfold2[OF H]
    by(auto simp add:snd_pl_def snd_pv_def LNew_def split:prod.splits)
next
  fix s 
  fix b :: "'b1 * 'b2"
  assume H : "plifting_pv_valid t v"
  assume H' : "b \<in> LOutS (snd_pv v) s"
  show "\<exists>out. LOut (snd_pl t) s b = Some out \<and>
                 b = LUpd (snd_pl t) s out b"
    using plifting_pv_valid_unfold3[OF H] H'
    by(auto simp add:snd_pl_def snd_pv_def)
qed

lemma snd_l_pv_valid :
  assumes H : "lifting_pv_valid t v"
  shows "lifting_pv_valid ((snd_l t) :: ('x, 'a, ('b1 :: Pordb) * 'b2) lifting)
                          ((snd_pv v) :: ('x, 'a, ('b1 :: Pordb) * 'b2) pliftingv)"
proof(rule lifting_pv_valid_intro)
  show "plifting_pv_valid (snd_l t) (snd_pv v)"
    unfolding snd_l_def
  proof(rule plifting_pv_valid_cast)
    show "plifting_pv_valid (snd_pl t) (snd_pv v)"
      using snd_pl_pv_valid[OF lifting_pv_valid_unfold1[OF H]]
      by(auto)
  qed
next
  fix s a 
  fix b :: "'b1 * 'b2"
  assume H1 : "b \<in> LOutS (snd_pv v) s"
  show "LPost (snd_l t) s b \<in> LOutS (snd_pv v) s" unfolding option_l_def
    using lifting_pv_valid_unfold2[OF H] H1
    by(auto simp add: snd_l_def snd_pl_def snd_pv_def plifting.defs)
next
  fix s a
  fix b :: "'b1 * 'b2"
  assume H1 : "b \<in> LOutS (snd_pv v) s "
  show "LOut (snd_l t) s (LPost (snd_l t) s b) = LOut (snd_l t) s b"
    using lifting_pv_valid_unfold3[OF H] H1
    by(auto simp add: snd_l_def snd_pl_def snd_pv_def plifting.defs)
qed

definition prod_l' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting' \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2) lifting'" where
"prod_l' t1 t2 =
  (\<lambda> x . (case x of (x1, x2) \<Rightarrow> (t1 x1, t2 x2)))"

definition prod_pl ::
  "('x, 'a1, 'b1, 'z1) plifting_scheme \<Rightarrow>
   ('x, 'a2, 'b2, 'z2) plifting_scheme \<Rightarrow>
   ('x, 'a1 * 'a2, 'b1 * 'b2) plifting" where
"prod_pl t1 t2 =
  \<lparr> LUpd =
    (\<lambda> s a b . (case a of (a1, a2) \<Rightarrow>
                  (case b of (b1, b2) \<Rightarrow>
                    (LUpd t1 s a1 b1, LUpd t2 s a2 b2))))
  , LOut =
    (\<lambda> s b . (case b of (b1, b2) \<Rightarrow>
              (case LOut t1 s b1 of
                None \<Rightarrow> None
                | Some b1o \<Rightarrow> (case LOut t2 s b2 of
                                None \<Rightarrow> None
                                | Some b2o \<Rightarrow> Some (b1o, b2o)))))
  , LBase =
    (\<lambda> s . (LBase t1 s, LBase t2 s)) \<rparr>"

definition prod_l ::
  "('x, 'a1, 'b1, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b2, 'z2) lifting_scheme \<Rightarrow>
   ('x, 'a1 * 'a2, 'b1 * 'b2) lifting" where
"prod_l t1 t2 =
  plifting.extend (prod_pl t1 t2)
    \<lparr> LPost = (\<lambda> s b . (case b of (b1, b2) \<Rightarrow> (LPost t1 s b1, LPost t2 s b2))) \<rparr>"

definition prod_pv ::
  "('x, 'a1, 'b1, 'z1) pliftingv_scheme \<Rightarrow>
   ('x, 'a2, 'b2, 'z2) pliftingv_scheme \<Rightarrow>
   ('x, 'a1 * 'a2, 'b1 * 'b2) pliftingv" where
"prod_pv t1 t2 =
  \<lparr> LOutS = (\<lambda> s . { b . \<exists> b1 b2 . b = (b1, b2) \<and> b1 \<in> LOutS t1 s \<and> b2 \<in> LOutS t2 s }) \<rparr>"

lemma prod_pl_valid : 
  assumes H1 : "plifting_valid t1"
  assumes H2 : "plifting_valid t2"
  shows "plifting_valid (prod_pl t1 t2)"
proof(rule plifting_valid_intro)
  fix s a b
  show "LOut (prod_pl t1 t2) s (LUpd (prod_pl t1 t2) s a b) = Some a"
    using plifting_valid_unfold1[OF H1] plifting_valid_unfold1[OF H2]
    by(auto simp add:prod_pl_def split:prod.splits)
next
  fix s a a' b
  show "LUpd (prod_pl t1 t2) s a (LUpd (prod_pl t1 t2) s a' b) = LUpd (prod_pl t1 t2) s a b"
    using plifting_valid_unfold2[OF H1] plifting_valid_unfold2[OF H2]
    by(auto simp add:prod_pl_def split:prod.splits)
qed
 
lemma prod_pl_pv_valid : 
  assumes H1 : "plifting_pv_valid t1 v1"
  assumes H2 : "plifting_pv_valid t2 v2"
  shows "plifting_pv_valid (prod_pl t1 t2) (prod_pv v1 v2)"
proof(rule plifting_pv_valid_intro)
  show "plifting_valid (prod_pl t1 t2)" 
    using prod_pl_valid[OF plifting_pv_valid_unfold1[OF H1]
                           plifting_pv_valid_unfold1[OF H2]] by auto
next
  fix s a b
  show "LUpd (prod_pl t1 t2) s a b \<in> LOutS (prod_pv v1 v2) s"
    using plifting_pv_valid_unfold2[OF H1] plifting_pv_valid_unfold2[OF H2]
    by(auto simp add:prod_pl_def prod_pv_def split:prod.splits)
next
  fix s b
  assume H' : "b \<in> LOutS (prod_pv v1 v2) s"
  obtain b1 b2 where B : "b = (b1, b2)" by(cases b; auto)

  have B1out : "b1 \<in> LOutS v1 s" using H' B by(auto simp add:prod_pv_def)
  have B2out : "b2 \<in> LOutS v2 s" using H' B by(auto simp add:prod_pv_def)


  show "\<exists>out. LOut (prod_pl t1 t2) s b = Some out \<and>
                 b = LUpd (prod_pl t1 t2) s out b"
    using B
       plifting_pv_valid_unfold3[OF H1 B1out]
       plifting_pv_valid_unfold3[OF H2 B2out] H'

 by(auto simp add:prod_pl_def prod_pv_def split:prod.splits option.splits)

qed

lemma prod_l_pv_valid :
  assumes H1 : "lifting_pv_valid t1 v1"
  assumes H2 : "lifting_pv_valid t2 v2"  
  shows "lifting_pv_valid (prod_l t1 t2) (prod_pv v1 v2)"
proof(rule lifting_pv_valid_intro)
  show "plifting_pv_valid (prod_l t1 t2) (prod_pv v1 v2)"
    unfolding prod_l_def
  proof(rule plifting_pv_valid_cast)
    show "plifting_pv_valid (prod_pl t1 t2) (prod_pv v1 v2)"
      using prod_pl_pv_valid[OF lifting_pv_valid_unfold1[OF H1]
                                lifting_pv_valid_unfold1[OF H2]]
      by(auto simp add: prod_pl_def prod_pv_def)
  qed
next
  fix s a b
  assume H' : "b \<in> LOutS (prod_pv v1 v2) s"
  show "LPost (prod_l t1 t2) s b \<in> LOutS (prod_pv v1 v2) s" unfolding triv_l_def
    using lifting_pv_valid_unfold2[OF H1]
          lifting_pv_valid_unfold2[OF H2] H'
    by(auto simp add: prod_l_def prod_pv_def plifting.defs split:prod.splits)
next
  fix s a b
  assume H' : "b \<in> LOutS (prod_pv v1 v2) s "

  obtain b1 b2 where B : "b = (b1, b2)" by(cases b; auto)
  have B1out : "b1 \<in> LOutS v1 s" using H' B by(auto simp add:prod_pv_def)
  have B2out : "b2 \<in> LOutS v2 s" using H' B by(auto simp add:prod_pv_def)

  show "LOut (prod_l t1 t2) s (LPost (prod_l t1 t2) s b) = LOut (prod_l t1 t2) s b"
    using lifting_pv_valid_unfold3[OF H1 B1out]
          lifting_pv_valid_unfold3[OF H2 B2out] H' B
    by(auto simp add: prod_l_def prod_pl_def prod_pv_def plifting.defs split:prod.splits option.splits)
qed


definition syn_prod :: "('x \<Rightarrow> 'x1) \<Rightarrow> ('x \<Rightarrow> 'x2) \<Rightarrow> ('x \<Rightarrow> ('x1 * 'x2))"
  where
"syn_prod f1 f2 x = (f1 x, f2 x)"

(* commutators for product liftings  *)
definition prod_commb_l' ::
  "('a1 * 'a2, 'b1 * 'b2) lifting' \<Rightarrow>
   ('a1 * 'a2, 'b2 * 'b1) lifting'" where
"prod_commb_l' t =
  (\<lambda> x . (case x of (x1, x2) \<Rightarrow> t (x2, x1)))"

(* TODO: do we need to define another version of this that commutes the a? *)
definition prod_commb_pl ::
  "('x, 'a, 'b1 * 'b2, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a, 'b2 * 'b1) plifting" where
"prod_commb_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> 
                        (case (LUpd t s a (b2, b1)) of
                          (b2', b1') \<Rightarrow> (b1', b2'))))
  , LOut = (\<lambda> s b . (case b of (b1, b2) \<Rightarrow> (LOut t s (b2, b1))))
  , LBase = (\<lambda> s . (case (LBase t s) of
                      (b1, b2) \<Rightarrow> (b2, b1))) \<rparr>"

definition prod_commb_l ::
  "('x, 'a, 'b1 * 'b2, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a, 'b2 * 'b1) lifting" where
"prod_commb_l t =
  plifting.extend (prod_commb_pl t)
    \<lparr> LPost = (\<lambda> s b . (case b of (b1, b2) \<Rightarrow> 
                        (case (LPost t s (b2, b1)) of
                          (b2', b1') \<Rightarrow> (b1', b2')))) \<rparr>"

definition prod_commb_pv ::
  "('x, 'a, 'b1 * 'b2, 'z) pliftingv_scheme \<Rightarrow>
   ('x, 'a, 'b2 * 'b1) pliftingv" where
"prod_commb_pv t =
  \<lparr> LOutS = 
    (\<lambda> s . { b . \<exists> b1 b2 . b = (b1, b2) \<and> (b2, b1) \<in> LOutS t s }) \<rparr>"

definition prod_comma_l' ::
  "('a1 * 'a2, 'b) lifting' \<Rightarrow>
   ('a2 * 'a1, 'b) lifting'" where
"prod_comma_l' t =
  (\<lambda> x . (case (t x) of (x1, x2) \<Rightarrow> (x2, x1)))"

definition prod_comma_pl ::
  "('x, 'a1 * 'a2, 'b, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a2 * 'a1, 'b) plifting" where
"prod_comma_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case a of (a1, a2) \<Rightarrow> LUpd t s (a2, a1) b))
  , LOut = (\<lambda> s b . (case (LOut t s b) of (Some (a1, a2)) \<Rightarrow> Some (a2, a1) | None \<Rightarrow> None))
  , LBase = LBase t\<rparr>"

definition prod_comma_l ::
  "('x, 'a1 * 'a2, 'b, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a2 * 'a1, 'b) lifting" where
"prod_comma_l t =
  plifting.extend (prod_comma_pl t)
    \<lparr> LPost = LPost t \<rparr>"

definition prod_comma_pv ::
  "('x, 'a1 * 'a2, 'b, 'z) pliftingv_scheme \<Rightarrow>
   ('x, 'a2 * 'a1, 'b) pliftingv" where
"prod_comma_pv t =
  \<lparr> LOutS = 
    LOutS t \<rparr>"

(* associators for product liftings *)
definition prod_deassocb_pl ::
  "('x, 'a, ('b1 * 'b2) * 'b3, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a, 'b1 * 'b2 * 'b3) plifting" where
"prod_deassocb_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of (b1, b2, b3) \<Rightarrow>
                        (case (LUpd t s a ((b1, b2), b3)) of
                          ((b1', b2'), b3') \<Rightarrow> (b1', b2', b3'))))
  , LOut = (\<lambda> s b . (case b of (b1, b2, b3) \<Rightarrow> LOut t s ((b1, b2), b3)))
  , LBase = (\<lambda> s . (case (LBase t s) of ((b1, b2), b3) \<Rightarrow> (b1, b2, b3))) \<rparr>"

definition prod_deassocb_l ::
  "('x, 'a, ('b1 * 'b2) * 'b3, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a, 'b1 * 'b2 * 'b3) lifting" where
"prod_deassocb_l t =
  plifting.extend (prod_deassocb_pl t)
    \<lparr> LPost = (\<lambda> s b . (case b of (b1, b2, b3) \<Rightarrow>
                        (case (LPost t s ((b1, b2), b3)) of
                          ((b1', b2'), b3') \<Rightarrow> (b1', b2', b3')))) \<rparr>"

definition prod_deassocb_pv ::
"('x, 'a, ('b1 * 'b2) * 'b3, 'z) pliftingv_scheme \<Rightarrow>
 ('x, 'a, 'b1 * 'b2 * 'b3) pliftingv" where
"prod_deassocb_pv v =
  \<lparr> LOutS = (\<lambda> s . { b . \<exists> b1 b2 b3 . b = (b1, b2, b3) \<and> ((b1, b2), b3) \<in> LOutS v s}) \<rparr>"

definition prod_assocb_pl ::
  "('x, 'a, 'b1 * 'b2 * 'b3, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a, ('b1 * 'b2) * 'b3) plifting" where
"prod_assocb_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of ((b1, b2), b3) \<Rightarrow>
                        (case (LUpd t s a (b1, b2, b3)) of
                          (b1', b2', b3') \<Rightarrow> ((b1', b2'), b3'))))
  , LOut = (\<lambda> s b . (case b of ((b1, b2), b3) \<Rightarrow> LOut t s (b1, b2, b3)))
  , LBase = (\<lambda> s . (case (LBase t s) of (b1, b2, b3) \<Rightarrow> ((b1, b2), b3))) \<rparr>"

definition prod_assocb_l ::
  "('x, 'a, 'b1 * 'b2 * 'b3, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a, ('b1 * 'b2) * 'b3) lifting" where
"prod_assocb_l t =
  plifting.extend (prod_assocb_pl t)
    \<lparr> LPost = (\<lambda> s b . (case b of ((b1, b2), b3) \<Rightarrow>
                        (case (LPost t s (b1, b2, b3)) of
                          (b1', b2', b3') \<Rightarrow> ((b1', b2'), b3')))) \<rparr>"

definition prod_assocb_pv ::
"('x, 'a, 'b1 * 'b2 * 'b3, 'z) pliftingv_scheme \<Rightarrow>
 ('x, 'a, ('b1 * 'b2) * 'b3) pliftingv" where
"prod_assocb_pv v =
  \<lparr> LOutS = (\<lambda> s . { b . \<exists> b1 b2 b3 . b = ((b1, b2), b3) \<and> (b1, b2, b3) \<in> LOutS v s}) \<rparr>"

definition prod_deassoca_pl ::
  "('x, ('a1 * 'a2) * 'a3, 'b, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a1 * 'a2 * 'a3, 'b) plifting" where
"prod_deassoca_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case a of (a1, a2, a3) \<Rightarrow> LUpd t s ((a1, a2), a3) b))
  , LOut = (\<lambda> s b . (case LOut t s b of (Some ((a1, a2), a3)) \<Rightarrow> Some (a1, a2, a3) | None \<Rightarrow> None))
  , LBase = LBase t \<rparr>"

definition prod_deassoca_l ::
  "('x, ('a1 * 'a2) * 'a3, 'b, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a1 * 'a2 * 'a3, 'b) lifting" where
"prod_deassoca_l t =
  plifting.extend (prod_deassoca_pl t)
    \<lparr> LPost = LPost t \<rparr>"

definition prod_deassoca_pv ::
  "('x, ('a1 * 'a2) * 'a3, 'b, 'z) pliftingv_scheme \<Rightarrow>
   ('x, 'a1 * 'a2 * 'a3, 'b) pliftingv" where
"prod_deassoca_pv v =
  \<lparr> LOutS = LOutS v \<rparr>"

definition prod_assoca_pl ::
  "('x, 'a1 * 'a2 * 'a3, 'b, 'z) plifting_scheme \<Rightarrow>
   ('x, ('a1 * 'a2) * 'a3, 'b) plifting" where
"prod_assoca_pl t =
  \<lparr> LUpd = (\<lambda> s a b . (case a of ((a1, a2), a3) \<Rightarrow> LUpd t s (a1, a2, a3) b))
  , LOut = (\<lambda> s b . (case LOut t s b of (Some (a1, a2, a3)) \<Rightarrow> Some ((a1, a2), a3)
                                        | None \<Rightarrow> None))
  , LBase = LBase t \<rparr>"

definition prod_assoca_l ::
  "('x, 'a1 * 'a2 * 'a3, 'b, 'z) lifting_scheme \<Rightarrow>
   ('x, ('a1 * 'a2) * 'a3, 'b) lifting" where
"prod_assoca_l t =
  plifting.extend (prod_assoca_pl t)
    \<lparr> LPost = LPost t \<rparr>"

definition prod_assoca_pv ::
  "('x, 'a1 * 'a2 * 'a3, 'b, 'z) pliftingv_scheme \<Rightarrow>
   ('x, ('a1 * 'a2) * 'a3, 'b) pliftingv" where
"prod_assoca_pv v =
  \<lparr> LOutS = LOutS v \<rparr>"



(* TODO: revisit these. it is possible they need to be
more general - paritcularly, this is suited for merging together
a product in one language with a fst in another.
*)
(*
declare [[show_types]]

lemma sup_l_prod_fst :
  fixes f :: "'x \<Rightarrow> 'x1"
  fixes f' :: "'x \<Rightarrow> 'x2"
  fixes l1  :: "('x1, 'a1, 'b1 :: Mergeableb) lifting"
  fixes l1' :: "('x2, 'a2, 'b1 :: Mergeableb) lifting"
  fixes l2  :: "('x1, 'a3, 'b2 :: Mergeableb) lifting"
  assumes H : "sup_l f f' l1 l1'"
  shows "sup_l f f' (prod_l l1 l2) (fst_l l1')"
proof(rule sup_l_intro)
  fix s :: "'x"
  fix a1 :: "('a1 \<times> 'a3)" 
  fix a2 :: "'a2"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub where Hub : "is_sup {LIn1 l1 (f s) x1, LIn1 l1' (f' s) a2} ub"
      using sup_l_unfold1[OF H, of "s" x1] Hx
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)
  
  have "is_sup {LIn1 (prod_l l1 l2) (f s) a1, LIn1 (fst_l l1') (f' s) a2} (ub, LIn1 l2 (f s) x2)" using  Hub Hx
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1 (prod_l l1 l2) (f s) a1, LIn1 (fst_l l1') (f' s) a2}" by (auto simp add:has_sup_def)
next
  fix s :: "'x"
  fix a1::"'a1 \<times> 'a3"
  fix a2::"'a2"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub1 : "has_sup {y1, z1}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2 l1 (f s) x1 y1, LIn2 l1' (f' s) a2 z1} ub"
      using sup_l_unfold2[OF H Hub1, of s x1] Hx Hy Hz
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)

  have "is_sup {LIn2 (prod_l l1 l2) (f s) a1 b1, LIn2 (fst_l l1') (f' s) a2 b2} (ub, LIn2 l2 (f s) x2 y2)" using  Hub Hx Hy Hz
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2 (prod_l l1 l2) (f s) a1 b1, LIn2 (fst_l l1') (f' s) a2 b2}" by (auto simp add:has_sup_def)
qed

lemma sup_lg_prod_snd :
  fixes f :: "'x \<Rightarrow> 'x1"
  fixes f' :: "'x \<Rightarrow> 'x2"
  fixes l1  :: "('x1, 'a1, 'b1 :: Mergeableb) lifting"
  fixes l2  :: "('x1, 'a2, 'b2 :: Mergeableb) lifting"
  fixes l2' :: "('x2, 'a3, 'b2 :: Mergeableb) lifting"
  assumes H : "sup_l f f' l2 l2'"
  shows "sup_l f f' (prod_l l1 l2) (snd_l l2')"
proof(rule sup_l_intro)
  fix s :: "'x"
  fix a1 :: "('a1 \<times> 'a2)" 
  fix a2 :: "'a3"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub :: 'b2 where Hub : "is_sup {LIn1 l2 (f s) x2, LIn1 l2' (f' s) a2} ub"
      using sup_l_unfold1[OF H, of s x2] Hx
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)
  
  have "is_sup {LIn1 (prod_l l1 l2) (f s) a1, LIn1 (snd_l l2') (f' s) a2} (LIn1 l1 (f s) x1, ub)" using  Hub Hx
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def snd_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1 (prod_l l1 l2) (f s) a1, LIn1 (snd_l l2') (f' s) a2}" by (auto simp add:has_sup_def)
next
  fix s :: "'x"
  fix a1::"'a1 \<times> 'a2"
  fix a2::"'a3"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub2 : "has_sup {y2, z2}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2 l2 (f s) x2 y2, LIn2 l2' (f' s) a2 z2} ub"
      using sup_l_unfold2[OF H Hub2, of s x2] Hx Hy Hz
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)

  have "is_sup {LIn2 (prod_l l1 l2) (f s) a1 b1, LIn2 (snd_l l2') (f' s) a2 b2} (LIn2 l1 (f s) x1 y1, ub)" using  Hub Hx Hy Hz
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def snd_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2 (prod_l l1 l2) (f s) a1 b1, LIn2 (snd_l l2') (f' s) a2 b2}" by (auto simp add:has_sup_def)
qed

lemma prio_sup :
  fixes b1 b2 :: "('b :: Pordb) md_prio"
  shows "has_sup {b1, b2}"
proof-
  obtain b1p and b1' where Hb1 : "b1 = mdp b1p b1'" by(cases b1; auto)
  obtain b2p and b2' where Hb2 : "b2 = mdp b2p b2'" by (cases b2; auto)

  have "is_ub {b1, b2} (mdp ((max b1p b2p) + 1) \<bottom>)"
    using Hb1 Hb2
    by(auto simp  add: is_ub_def prio_pleq prio_bot)

  hence "has_ub {b1, b2}" by (auto simp add:has_ub_def)

  thus "has_sup {b1, b2}" by(rule complete2; auto)
qed

lemma sup_l_prio :
  fixes f :: "'x \<Rightarrow> 'y1"
  fixes f' :: "'x \<Rightarrow> 'y2"
  fixes l1 :: "('y1, 'a1, 'b :: Pordb) lifting"
  fixes l2 :: "('y2, 'a2, 'b :: Pordb) lifting"
  shows "sup_l f f' (prio_l f0_1 f1_1 l1) (prio_l f0_2 f1_2 l2)"
proof(rule sup_l_intro)
  fix s :: "'x"
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  show "has_sup {LIn1 (prio_l f0_1 f1_1 l1) (f s) a1, LIn1 (prio_l f0_2 f1_2 l2) (f' s) a2}"
    by(rule prio_sup)
next
  fix s :: "'x"
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  fix b1 b2 :: "'b md_prio"
  assume H : "has_sup {b1, b2}"
  show "has_sup {LIn2 (prio_l f0_1 f1_1 l1) (f s) a1 b1, LIn2 (prio_l f0_2 f1_2 l2) (f' s) a2 b2}"
    by(rule prio_sup)
qed

lemma sup_l_inc_zero :
  fixes l1 :: "('y1, 'a1, 'b :: Mergeableb) lifting"
  fixes l2:: "('y2, 'a2, 'b :: Mergeableb) lifting"
  shows "sup_l f f' (prio_l_zero l1) (prio_l_inc l2)"
  unfolding prio_l_zero_def prio_l_inc_def prio_l_const_def
  by(rule sup_l_prio)
(* prios = sort of different
   we probably need to relate the details of the functions?
   (or do we not? md_prio always has an upper bound *)
(*
lemma sup_l_inc_zero :
  fixes l1 :: "('a1, 'b :: Mergeableb) lifting"
  fixes l2:: "('a2, 'b :: Mergeableb) lifting"
  shows "sup_l (prio_l_zero l1) (prio_l_inc l2)"
proof(rule sup_l_intro)
  fix a1 :: "'a1"
  fix a2 :: "'a2"

  (* this is kind of a bogus case *)
  have "is_ub {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2} (mdp 1 \<bottom>)"
    by(auto simp add:prio_l_zero_def prio_l_const_def prio_l_def prio_l_inc_def
            has_sup_def is_sup_def is_least_def is_ub_def prio_pleq bot_spec split:md_prio.splits)

  hence 0 : "has_ub {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2}"
    by(auto simp add:has_ub_def)

  obtain lub where
    "is_sup {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2} lub" 
    using complete2[OF 0] by(auto simp add:has_sup_def)
  

  thus "has_sup {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2}"
    by(auto simp add:has_sup_def)
next
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  fix b1 :: "'b md_prio"
  fix b2 :: "'b md_prio"
  assume Hsup : "has_sup {b1, b2}"


  have "is_ub {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2} (LIn2 (prio_l_inc l2) a2 b2)"
    by(auto simp add:prio_l_zero_def prio_l_const_def prio_l_def prio_l_inc_def
            leq_refl
            has_sup_def is_sup_def is_least_def is_ub_def prio_pleq bot_spec split:md_prio.splits)

  hence 0 : "has_ub  {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2}"
    by(auto simp add:has_ub_def)

  obtain lub where
    "is_sup {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2} lub"
    using complete2[OF 0] by(auto simp add:has_sup_def)

  thus "has_sup {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2}"
    by(auto simp add:has_sup_def)
qed
*)
*)

(*
variable maps
*)

(* simplest case for lifting into variable map. only allows 
   dispatch based on syntax. *)
(* TODO: is this definition of out going to cause problems? *)
definition oalist_pl ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b) oalist) plifting" where
"oalist_pl f t =
  \<lparr> LUpd = (\<lambda> s a l .
            (case (f s) of
              Some k \<Rightarrow>
                (case get l k of
                  None \<Rightarrow> (update k (LNew t s a) l)
                  | Some v \<Rightarrow> (update k (LUpd t s a v) l))
              | None \<Rightarrow> l))
  , LOut = (\<lambda> s l . (case (f s) of
                      Some k \<Rightarrow> (case get l k of 
                                  Some a \<Rightarrow> LOut t s a
                                  | None \<Rightarrow> None)
                      | None \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . (case (f s) of
                      Some k \<Rightarrow> update k (LBase t s) empty
                      | None \<Rightarrow> empty)) \<rparr>"

(* TODO: if we can't find the key, what do we do with LPost?
   I think either obvious choice (LPost on LBase, or leave empty) meets spec *)
definition oalist_l ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b) oalist) lifting" where
"oalist_l f t =
  plifting.extend (oalist_pl f t)
    \<lparr> LPost = (\<lambda> s l . (case f s of
                          Some k \<Rightarrow> (case get l k of 
                                       Some a \<Rightarrow> update k (LPost t s a) l
                                       | None \<Rightarrow> l)
                          | None \<Rightarrow> l)) \<rparr>"

definition oalist_pv ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b) oalist) pliftingv" where
"oalist_pv f v =
  \<lparr> LOutS = (\<lambda> s . { l . \<exists> k a . f s = Some k \<and> get l k = Some a \<and> a \<in> LOutS v s }) \<rparr>"

(*
lemma oalist_l_valid :
  fixes f :: "('x \<Rightarrow> 'k :: linorder)"
  fixes lv :: "('x, 'a, 'b) lifting"
  assumes Hv : "lifting_valid lv"
  shows "lifting_valid (oalist_l f lv)"
proof(rule lifting_valid_intro)
  fix s :: 'x
  fix a :: 'a
  show "LOut1 (oalist_l f lv) s (LIn1 (oalist_l f lv) s a) = a" using lifting_valid_unfold1[OF Hv]
    by(auto simp add:oalist_l_def Let_def get_update split:prod.splits option.splits)
next
  fix s :: 'x
  fix a :: 'a
  fix b :: "('k, 'b) oalist"
  show "LOut1 (oalist_l f lv) s (LIn2 (oalist_l f lv) s a b) = a" using 
        lifting_valid_unfold1[OF Hv]
        lifting_valid_unfold2[OF Hv]
    by(auto simp add:oalist_l_def Let_def get_update split:prod.splits option.splits)
qed
*)

(* allows more interesting dispatch (based on state), but
   at the cost of storing the key, which means we cannot
   merge semantics that update keys in a different order *)
(*
definition oalist_k_l ::
  "('x, 'a, 'k :: linorder) lifting \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow>
   ('x, 'a, ('k * ('k, 'b) oalist)) lifting" where
"oalist_k_l tk tv =
  \<lparr> LIn1 = (\<lambda> s a . (let k = LIn1 tk s a in
                     (k, update k (LIn1 tv s a) empty)))
  , LIn2 = (\<lambda> s a k'l .
            (case k'l of
              (k', l) \<Rightarrow>
                (let k = LIn2 tk s a k' in
                (case get l k of
                  None \<Rightarrow> (k, update k (LIn1 tv s a) l)
                  | Some v \<Rightarrow> (k, update k (LIn2 tv s a v) l)))))
  , LOut1 = (\<lambda> s kl .
              (case kl of
                (k, l) \<Rightarrow> (case get l k of Some a \<Rightarrow> LOut1 tv s a)))\<rparr>"


lemma oalist_k_l_valid :
  fixes lk :: "('x, 'a, 'k :: linorder) lifting"
  fixes lv :: "('x, 'a, 'b) lifting"
  assumes Hk : "lifting_valid lk"
  assumes Hv : "lifting_valid lv"
  shows "lifting_valid (oalist_k_l lk lv)"
proof(rule lifting_valid_intro)
  fix s :: 'x
  fix a :: 'a
  show "LOut1 (oalist_k_l lk lv) s (LIn1 (oalist_k_l lk lv) s a) = a" using lifting_valid_unfold1[OF Hv]
    by(auto simp add:oalist_k_l_def Let_def get_update split:prod.splits option.splits)
next
  fix s :: 'x
  fix a :: 'a
  fix b :: "'k * ('k, 'b) oalist"
  show "LOut1 (oalist_k_l lk lv) s (LIn2 (oalist_k_l lk lv) s a b) = a" using 
        lifting_valid_unfold1[OF Hv]
        lifting_valid_unfold2[OF Hv]
    by(auto simp add:oalist_k_l_def Let_def get_update split:prod.splits option.splits)
qed
*)

(* utilities for interfacing with Gensyn *)
definition prod_fan_pl ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow>
   ('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a, ('c * 'b)) plifting"
  where
"prod_fan_pl f t =
  \<lparr> LUpd = (\<lambda> x a cb . (f x a, LUpd t x a (snd cb)))
  , LOut = (\<lambda> x cb . LOut t x (snd cb))
  , LBase = (\<lambda> x . ((case LOut t x (LBase t x) of
                      Some out \<Rightarrow> f x out)
                   , LBase t x)) \<rparr>"

definition prod_fan_l ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow>
   ('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a, ('c * 'b)) lifting" where
"prod_fan_l f t =
  plifting.extend (prod_fan_pl f t)
    \<lparr> LPost =
      (\<lambda> s cb . ((case (LOut t s (LPost t s (snd cb))) of
                        Some out \<Rightarrow> f s out)
                , LPost t s (snd cb))) \<rparr>"

definition prod_fan_pv ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow>
   ('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow>
   ('x, 'a, ('c * 'b)) pliftingv" where
"prod_fan_pv f t v =
  \<lparr> LOutS = (\<lambda> s . { cb . \<exists> c b out . cb = (c, b) \<and> b \<in> LOutS v s \<and> 
                          LOut t s b = Some out \<and> c = f s out}) \<rparr>"
(*
lemma prod_fan_l_valid :
  fixes f :: "('x \<Rightarrow> 'a \<Rightarrow> 'c)"
  fixes l :: "('x, 'a, 'b) lifting"
  assumes H :"lifting_valid l"
  shows "lifting_valid (prod_fan_l f l)"
  using H by (auto simp add: lifting_valid_def prod_fan_l_def)
*)
definition l_reverse ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
   'x \<Rightarrow> 'b \<Rightarrow> 'a" where
"l_reverse l s b =
  (case LOut l s b of Some a \<Rightarrow> a)"

(* finally, here we allow keymaps, which might enable more interesting merges
   however we will need to reset the kmap in between commands. *)
(* should double check this *)
(*
definition oalist_kmap_l ::
  "('x, 'a, 'k :: linorder) lifting \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow>
   ('x, 'a, ('k kmap * ('k, 'b) oalist)) lifting" where
"oalist_kmap_l tk tv =
  \<lparr> LIn1 = (\<lambda> s a . (let k = LIn1 tk s a in
                     (to_oalist [(k, ())], update k (LIn1 tv s a) empty)))
  , LIn2 = (\<lambda> s a k'l .
            (case k'l of
              (k', l) \<Rightarrow>
                (let k = kmap_singleton k' in
                (case get l k of
                  None \<Rightarrow> (k' , update k (LIn1 tv s a) l)
                  | Some v \<Rightarrow> (k', update k (LIn2 tv s a v) l)))))
  , LOut1 = (\<lambda> s kl .
              (case kl of
                (km, l) \<Rightarrow> (case get l (kmap_singleton km) of Some a \<Rightarrow> LOut1 tv s a)))\<rparr>"
*)

(* another approach would be to return sets. this might we worth exploring later. *)

end