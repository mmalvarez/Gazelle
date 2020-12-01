theory LiftInstances imports LiftUtils
begin

(* TODOs :
  - proofs for commutativity lifting
  - proofs for associativity lifting
  - proofs for var map lifting
  - proofs about LUBs
*)

(* typeclass for data that we can supply "bogus" default values
   for (instead of undefined)
*)

class Bogus =
  fixes bogus :: "'a"

instantiation nat :: Bogus begin
definition nat_bogus : "bogus = (0 :: nat)"
instance proof qed
end

instantiation bool :: Bogus begin
definition bool_bogus : "bogus = True"
instance proof qed
end

instantiation int :: Bogus begin
definition int_bogus : "bogus = (0 :: int)"
instance proof qed
end

instantiation unit :: Bogus begin
definition unit_bogus : "bogus = ()"
instance proof qed
end

instantiation prod :: (Bogus, Bogus) Bogus begin
definition prod_bogus : "bogus = (bogus, bogus)"
instance proof qed
end

instantiation sum :: (Bogus, _) Bogus begin
definition sum_bogus : "bogus = Inl bogus"
instance proof qed
end


(* TODO: which option instance?
   (list instance should probably be [] but also could use
   revisiting)
*)
(*
instantiation option :: (_) Bogus begin
definition option_bogus : "bogus = None"
instance proof qed
end
*)

instantiation option :: (Bogus) Bogus begin
definition option_bogus : "bogus = Some bogus"
instance proof qed
end

instantiation list :: (_) Bogus begin
definition list_bogus : "bogus = []"
instance proof qed
end

instantiation md_triv :: (Bogus) Bogus begin
definition md_triv_bogus : "bogus = mdt bogus"
instance proof qed
end

instantiation md_prio :: (Bogus) Bogus begin
definition md_prio_bogus : "bogus = mdp 0 bogus"
instance proof qed
end

instantiation oalist :: (linorder, _) Bogus begin
definition oalist_bogus : "bogus = (empty :: (_, _) oalist)"
instance proof qed
end

instantiation String.literal :: Bogus begin
definition string_literal_bogus :
"bogus = STR ''''"
instance proof qed
end


(*
identity lifting
*)


definition id_l' ::
  "('a, 'a) syn_lifting" where
  "id_l' = id"

definition id_l ::
  "('x, 'a :: {Pord, Bogus}, 'a) lifting" where
"id_l =
  \<lparr> LUpd = (\<lambda> s a a' . a)
  , LOut = (\<lambda> s a . a)
  , LBase = (\<lambda> s . bogus) \<rparr>" 

definition id_lv :: "('x, 'a :: {Pord, Bogus}, 'a) liftingv" where
"id_lv = lifting.extend id_l \<lparr> LOutS = (\<lambda> _ . UNIV) \<rparr>"


lemma id_pl_valid : "lifting_valid (id_lv)"
  apply (rule lifting_validI)
  apply(simp add:id_l_def id_lv_def)
   apply(simp add:id_l_def id_lv_def)
   apply(simp add:id_l_def id_lv_def leq_refl)
  done

(*
trivial ordering
*)

definition triv_l' ::
  "('a, 'b) syn_lifting \<Rightarrow> ('a, 'b md_triv) syn_lifting" where
"triv_l' t' =
  (case_md_triv t')"

definition triv_l ::
  "('x, 'a :: Bogus, 'a md_triv) lifting" where
"triv_l =
  \<lparr> LUpd = (\<lambda> s a _ . mdt a)
  , LOut = (\<lambda> s b . (case b of (mdt b') \<Rightarrow> b'))
  , LBase = (\<lambda> s . mdt bogus) \<rparr>"

definition triv_lv ::
  "('x, 'a :: Bogus, 'a md_triv) liftingv" where
"triv_lv =
  lifting.extend (triv_l) \<lparr> LOutS = (\<lambda> s . UNIV) \<rparr>"

lemma triv_pl_valid : 
  shows "lifting_valid (triv_lv :: ('x, 'a :: Bogus, 'a md_triv) liftingv)"
proof(rule lifting_validI)
  fix s :: 'x
  fix a :: 'a 
  fix b
  show "LUpd (triv_lv) s a b \<in> LOutS (triv_lv) s"
    using lifting_validDSO 
    by(auto simp add:triv_l_def triv_lv_def split:md_triv.splits)
next
  fix s :: 'x
  fix a :: 'a
  fix b
  show "LOut (triv_lv) s (LUpd (triv_lv) s a b) = a"
    by(auto simp add:triv_lv_def triv_l_def split:md_triv.splits)
next
  fix s :: 'x
  fix b :: "'a md_triv"
  assume H' : "b \<in> LOutS (triv_lv) s"

  show "b <[ LUpd (triv_lv) s (LOut (triv_lv) s b) b"
   by(auto simp add:triv_lv_def triv_l_def triv_pleq
          split:md_triv.splits)
qed

(*
option ordering
*)

(* TODO: we could probably use bogus here. *)
definition option_l' ::
  "('a, 'b) syn_lifting \<Rightarrow>
   ('a, 'b option) syn_lifting" where
"option_l' t =
  case_option undefined t "

definition option_l ::
  "('x, 'a, 'b:: {Pord}, 'z) lifting_scheme \<Rightarrow> ('x, 'a, 'b option) lifting" where
"option_l t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              Some b' \<Rightarrow> Some (LUpd t s a b')
              | None \<Rightarrow> Some (LNew t s a)))
  , LOut = (\<lambda> s b . (case b of Some b' \<Rightarrow> LOut t s b'
                      | None \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . None)\<rparr>"

definition option_lv ::
  "('x, 'a, 'b :: {Pord}, 'z) liftingv_scheme \<Rightarrow> ('x, 'a, 'b option) liftingv" where
"option_lv v = lifting.extend (option_l v)
  \<lparr> LOutS = (\<lambda> s . Some ` (LOutS v s))\<rparr>"

lemma option_l_valid :
  assumes H : "lifting_valid (t :: ('x, 'a, 'b :: {Bogus, Pord}, 'z) liftingv_scheme)"
  shows "lifting_valid (option_lv t)"
proof(rule lifting_validI)
  fix s a b
  show "LUpd (option_lv t) s a b \<in> LOutS (option_lv t) s"
    using lifting_validDSO[OF H]
    by(auto simp add:option_l_def option_lv_def LNew_def split:option.splits)
next
  fix s a b
  show "LOut (option_lv t) s (LUpd (option_lv t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add:option_l_def option_lv_def LNew_def split:option.splits)
next
  fix s b
  assume H' : "b \<in> LOutS (option_lv t) s"
  then obtain b' where Hb' : "b = Some b'" and Hb'in : "b' \<in> LOutS t s"
    by(auto simp add:option_l_def option_lv_def LNew_def option_pleq split:option.splits)

  show "b <[ LUpd (option_lv t) s (LOut (option_lv t) s b) b"
    using lifting_validDI[OF H Hb'in] Hb'
    by(auto simp add:option_l_def option_lv_def LNew_def option_pleq split:option.splits)
qed

(* sum types *)

definition inl_l ::
  "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> 
   ('x, 'a, ('b + 'c :: Pord)) lifting" where
"inl_l t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              Inl b' \<Rightarrow> Inl (LUpd t s a b')
              | _ \<Rightarrow> Inl (LNew t s a)))
  , LOut = (\<lambda> s b . (case b of Inl b' \<Rightarrow> LOut t s b'
                      | _ \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . Inl (LBase t s))\<rparr>"

definition inl_lv ::
  "('x, 'a, 'b :: Pord, 'z) liftingv_scheme \<Rightarrow> ('x, 'a, 'b + 'c :: Pord) liftingv" where
"inl_lv v =
  lifting.extend (inl_l v)
  \<lparr> LOutS = (\<lambda> s . Inl ` (LOutS v s))\<rparr>"

lemma inl_l_valid :
  assumes H : "lifting_valid (t :: ('x, 'a, 'b :: {Pord}, 'z) liftingv_scheme)"
  shows "lifting_valid (inl_lv t :: ('x, 'a, 'b + 'c :: Pord) liftingv)"
proof(rule lifting_validI)
  fix s a
  fix b :: "'b + 'c"
  show "LUpd (inl_lv t) s a b \<in> LOutS (inl_lv t) s"
    using lifting_validDSO[OF H]
    by(auto simp add:inl_l_def inl_lv_def LNew_def split:sum.splits)
next
  fix s a 
  fix b :: "'b + 'c"

  show "LOut (inl_lv t) s (LUpd (inl_lv t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add:inl_l_def inl_lv_def LNew_def split:sum.splits)
next
  fix s
  fix b :: "'b + 'c"
  assume H' : "b \<in> LOutS (inl_lv t) s"
  then obtain b' where Hb' : "b = Inl b'" and Hb'in : "b' \<in> LOutS t s"
    by(auto simp add:inl_l_def inl_lv_def LNew_def split:sum.splits)

  show "b <[ LUpd (inl_lv t) s (LOut (inl_lv t) s b) b"
    using lifting_validDI[OF H Hb'in] Hb'
    by(auto simp add:inl_l_def inl_lv_def LNew_def sum_pleq split:sum.splits)
qed

definition inr_l ::
  "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> 
   ('x, 'a, ('c :: Pord+ 'b)) lifting" where
"inr_l t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              Inr b' \<Rightarrow> Inr (LUpd t s a b')
              | _ \<Rightarrow> Inr (LNew t s a)))
  , LOut = (\<lambda> s b . (case b of Inr b' \<Rightarrow> LOut t s b'
                      | _ \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . Inr (LBase t s))\<rparr>"

definition inr_lv ::
  "('x, 'a, 'b :: Pord, 'z) liftingv_scheme \<Rightarrow> ('x, 'a, 'c :: Pord + 'b :: Pord) liftingv" where
"inr_lv v =
  lifting.extend (inr_l v)
  \<lparr> LOutS = (\<lambda> s . Inr ` (LOutS v s))\<rparr>"

lemma inr_l_valid :
  assumes H : "lifting_valid (t :: ('x, 'a, 'b :: {Pord}, 'z) liftingv_scheme)"
  shows "lifting_valid (inr_lv t :: ('x, 'a, 'c :: Pord + 'b) liftingv)"
proof(rule lifting_validI)
  fix s a
  fix b :: "'c + 'b"
  show "LUpd (inr_lv t) s a b \<in> LOutS (inr_lv t) s"
    using lifting_validDSO[OF H]
    by(auto simp add:inr_l_def inr_lv_def LNew_def split:sum.splits)
next
  fix s a 
  fix b :: "'c + 'b"

  show "LOut (inr_lv t) s (LUpd (inr_lv t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add:inr_l_def inr_lv_def LNew_def split:sum.splits)
next
  fix s
  fix b :: "'c + 'b"
  assume H' : "b \<in> LOutS (inr_lv t) s"
  then obtain b' where Hb' : "b = Inr b'" and Hb'in : "b' \<in> LOutS t s"
    by(auto simp add:inr_l_def inr_lv_def LNew_def split:sum.splits)

  show "b <[ LUpd (inr_lv t) s (LOut (inr_lv t) s b) b"
    using lifting_validDI[OF H Hb'in] Hb'
    by(auto simp add:inr_l_def inr_lv_def LNew_def sum_pleq split:sum.splits)
qed


definition prio_l' ::
  "('a, 'b) syn_lifting \<Rightarrow>
   ('a, 'b md_prio) syn_lifting" where
"prio_l' t =
  (\<lambda> p . (case p of
              mdp m b \<Rightarrow> t b))"

(* note: this only allows setting output priority based on syntax. *)
definition prio_l ::
 "('x \<Rightarrow> nat) \<Rightarrow>
  ('x \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
  ('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
  ('x, 'a, 'b md_prio) lifting" where
"prio_l f0 f1 t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of
                         mdp m b' \<Rightarrow> mdp (f1 s m) (LUpd t s a b')))
  , LOut =
      (\<lambda> s p . (case p of
                 mdp m b \<Rightarrow> LOut t s b))
  , LBase = (\<lambda> s . mdp (f0 s) (LBase t s)) \<rparr>"

definition prio_lv :: "('x \<Rightarrow> nat) \<Rightarrow>
                       ('x \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
                       ('x, 'a, 'b :: Pord, 'z) liftingv_scheme \<Rightarrow>
                       ('x, 'a, 'b md_prio) liftingv" where
"prio_lv f0 f1 v = lifting.extend (prio_l f0 f1 v)
              \<lparr> LOutS = (\<lambda> s . { p . \<exists> m b . p = mdp m b \<and> b \<in> LOutS v s})\<rparr>"

lemma prio_pl_valid :
  assumes H : "lifting_valid t"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_valid (prio_lv f0 f1 t)"
proof(rule lifting_validI)
  fix s a b
  show "LUpd (prio_lv f0 f1 t) s a b \<in> LOutS (prio_lv f0 f1 t) s"
    using lifting_validDSO[OF H]
    by(auto simp add:prio_l_def prio_lv_def LNew_def split:md_prio.splits)
next
  fix s a b
  show "LOut (prio_lv f0 f1 t) s (LUpd (prio_lv f0 f1 t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add:prio_l_def prio_lv_def LNew_def split:md_prio.splits)

next
  fix s b

  assume H' : "b \<in> LOutS (prio_lv f0 f1 t) s"
  then obtain b' p where Hb' : "b = mdp p b'" and H'' : "b' \<in> LOutS t s"
    by(auto simp add:prio_l_def prio_lv_def LNew_def split:md_prio.splits)

  hence "b' <[ LUpd t s (LOut t s b') b'"
    using lifting_validDI[OF H H'']
    by(auto simp add:prio_l_def prio_lv_def LNew_def split:md_prio.splits)

  thus "b <[ LUpd (prio_lv f0 f1 t) s (LOut (prio_lv f0 f1 t) s b) b" using Hb' Hmono[of p s]
    by(auto simp add:prio_l_def prio_lv_def prio_pleq LNew_def split:md_prio.splits)
qed

definition prio_l_keep :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_keep =
  prio_l (\<lambda> _ . 0) (\<lambda> _ n . n)"

definition prio_l_inc :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc =
  prio_l (\<lambda> _ . 1) (\<lambda> _ x . 1 + x)"

definition prio_l_inc2 :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc2 =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 2 + x)"

definition prio_l_incN :: "nat \<Rightarrow> ('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_incN n =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . n + x)"

definition prio_l_case_inc :: "('x \<Rightarrow> nat) \<Rightarrow> ('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_case_inc f =
  prio_l (\<lambda> _ . 0) (\<lambda> s x . (f s) + x)"



(*
products
*)

definition fst_l' ::
  "('a, 'b1) syn_lifting \<Rightarrow>
   ('a, 'b1 * 'b2) syn_lifting" where
"fst_l' t =
  (\<lambda> x . t (fst x))"

definition fst_l ::
  "('x, 'a, 'b1 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a, 'b1 * ('b2 :: Pordb)) lifting" where
"fst_l t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (LUpd t s a b1, b2)))
  , LOut = (\<lambda> s x . (LOut t s (fst x)))
  , LBase = (\<lambda> s . (LBase t s, \<bottom>)) \<rparr>"

definition fst_lv ::
  "('x, 'a, 'b1 :: Pord, 'z) liftingv_scheme \<Rightarrow> ('x, 'a, 'b1 * ('b2 :: Pordb)) liftingv" where
"fst_lv t =
  lifting.extend (fst_l t)
  \<lparr> LOutS = (\<lambda> s . { b . \<exists> b1 b2 . b = (b1, b2) \<and> b1 \<in> LOutS t s} ) \<rparr>"

lemma fst_l_valid :
  assumes H : "lifting_valid v"
  shows "lifting_valid ((fst_lv v) :: ('x, 'a, ('b1 :: Pord) * ('b2 :: Pordb)) liftingv)"
proof(rule lifting_validI)
  fix s a 
  fix b :: "'b1 * 'b2"

  show "LUpd (fst_lv v) s a b \<in> LOutS (fst_lv v) s"
    using lifting_validDSO[OF H] by(auto simp add: fst_lv_def fst_l_def split:prod.splits)
next
  fix s a
  fix b :: "'b1 * 'b2"

  show "LOut (fst_lv v) s (LUpd (fst_lv v) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add: fst_lv_def fst_l_def split:prod.splits)

next
  fix s
  fix b :: "'b1 * 'b2"

  assume H' : "b \<in> LOutS (fst_lv v) s"

  then obtain b'1 b'2 where Hb' : "b = (b'1, b'2)" and H'' : "b'1 \<in> LOutS v s"
    by(auto simp add: fst_lv_def fst_l_def split:prod.splits)

  show "b <[ LUpd (fst_lv v) s (LOut (fst_lv v) s b) b"
    using lifting_validDI[OF H H''] Hb'
    by(auto simp add: fst_lv_def fst_l_def prod_pleq leq_refl split:prod.splits)
qed


definition snd_l' ::
  "('a, 'b2) syn_lifting \<Rightarrow>
   ('a, 'b1 * 'b2) syn_lifting" where
"snd_l' t =
  (\<lambda> x . t (snd x))"

definition snd_l ::
  "('x, 'a, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a, ('b1 :: Pordb) * 'b2) lifting" where
"snd_l t =
  \<lparr> LUpd = (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (b1, LUpd t s a b2)))
  , LOut = (\<lambda> s x . (LOut t s (snd x)))
  , LBase = (\<lambda> s . (\<bottom>, LBase t s)) \<rparr>"

definition snd_lv ::
  "('x, 'a, 'b2 :: Pord, 'z) liftingv_scheme \<Rightarrow> ('x, 'a, ('b1 :: Pordb) * 'b2) liftingv" where
"snd_lv t =
  lifting.extend (snd_l t)
  \<lparr> LOutS = (\<lambda> s . { b . \<exists> b1 b2 . b = (b1, b2) \<and> b2 \<in> LOutS t s} )\<rparr>"

lemma snd_pl_valid :
  assumes H : "lifting_valid v"
  shows "lifting_valid ((snd_lv v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pord)) liftingv)"
proof(rule lifting_validI)
  fix s a
  fix b :: "'b1 * 'b2"
  show "LUpd (snd_lv v) s a b \<in> LOutS (snd_lv v) s"
    using lifting_validDSO[OF H] by(auto simp add: snd_lv_def snd_l_def split:prod.splits)
next
  fix s a
  fix b :: "'b1 * 'b2"

  show "LOut (snd_lv v) s (LUpd (snd_lv v) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add: snd_lv_def snd_l_def split:prod.splits)

next
  fix s
  fix b :: "'b1 * 'b2"

  assume H' : "b \<in> LOutS (snd_lv v) s"

  then obtain b'1 b'2 where Hb' : "b = (b'1, b'2)" and H'' : "b'2 \<in> LOutS v s"
    by(auto simp add: snd_lv_def snd_l_def split:prod.splits)

  show "b <[ LUpd (snd_lv v) s (LOut (snd_lv v) s b) b"
    using lifting_validDI[OF H H''] Hb'
    by(auto simp add: snd_lv_def snd_l_def prod_pleq leq_refl split:prod.splits)
qed


lemma fst_snd_ortho :
  assumes H1 : "lifting_valid l1"
  assumes H2 : "lifting_valid l2"
  shows "l_ortho (fst_lv (l1 :: ('x, 'a1, 'b1 :: Mergeableb, 'z1) liftingv_scheme))
                 (snd_lv (l2 :: ('x, 'a2, 'b2 :: Mergeableb, 'z2) liftingv_scheme))"
proof(rule l_orthoI)
  fix s :: 'x
  fix a1 :: 'a1 
  fix a2 :: 'a2
  fix b :: "('b1 * 'b2)"

  obtain b1 b2 where B : "b = (b1, b2)" by(cases b; auto)

  (* idea:
     Z here needs to be bsup (?) 
     ugh... actually i don't think this works.
     since updating the other component theoretically could reduce it
     could strengthen definition of Lifting laws...*)

  have "is_sup {LUpd (fst_lv l1) s a1 b, LUpd (snd_lv l2) s a2 b} 
               (LUpd l1 s a1 b1, LUpd l2 s a2 b2)"
  proof(rule is_sup_intro)
    fix x
    assume "x \<in> {LUpd (fst_lv l1) s a1 b, LUpd (snd_lv l2) s a2 b}"
    thus "x <[ (LUpd l1 s a1 b1, LUpd l2 s a2 b2)" using B
      apply(auto simp add: fst_lv_def fst_l_def snd_lv_def snd_l_def
               leq_refl
               prod_bot prod_pleq prod_bsup split:prod.splits)

  show "\<exists>z. is_sup {LUpd (fst_lv l1) s a1 b, LUpd (snd_lv l2) s a2 b} z \<and>
           z \<in> LOutS (fst_lv l1) s \<and>
           z \<in> LOutS (snd_lv l2) s \<and> LOut (fst_lv l1) s z = a1 \<and> LOut (snd_lv l2) s z = a2"
  apply(auto simp add: fst_lv_def fst_l_def snd_lv_def snd_l_def
             prod_bot prod_pleq prod_bsup split:prod.splits)

qed

lemma snd_fst_ortho :
  "l_ortho (snd_lv (l1 :: ('x, 'a1, 'b :: Mergeableb, 'z1) liftingv_scheme))
           (fst_lv (l2 :: ('x, 'a2, 'b :: Mergeableb, 'z2) liftingv_scheme))"

*)
(* merging
   note that the orthogonality condition required for validity
   is rather strong here. *)
definition merge_l ::
  "('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b :: Mergeable, 'z2) lifting_scheme \<Rightarrow>
   ('x, 'a1 * 'a2, 'b) lifting" where
"merge_l t1 t2 =
  \<lparr> LUpd =
    (\<lambda> s a b . 
      (case a of (a1, a2) \<Rightarrow>
        [^ (LUpd t1 s a1 b), (LUpd t2 s a2 b) ^]))
  , LOut =
    (\<lambda> s b . (LOut t1 s b, LOut t2 s b))
  , LBase =
    (\<lambda> s . [^ LBase t1 s, LBase t2 s ^]) \<rparr>"

definition merge_lv ::
  "('x, 'a1, 'b :: Mergeable, 'z1) liftingv_scheme \<Rightarrow>
   ('x, 'a2, 'b :: Mergeable, 'z2) liftingv_scheme \<Rightarrow>
   ('x, 'a1 * 'a2, 'b) liftingv" where
"merge_lv v1 v2 =
  lifting.extend (merge_l v1 v2)
  \<lparr> LOutS = (\<lambda> s . LOutS v1 s \<inter> LOutS v2 s) \<rparr>"

lemma merge_lv_valid :
  assumes H1 : "lifting_valid (l1 :: ('x, 'a1, 'b :: Mergeable, 'z1) liftingv_scheme)"
  assumes H2 : "lifting_valid (l2 :: ('x, 'a2, 'b :: Mergeable, 'z2) liftingv_scheme)"
  assumes Hort : "l_ortho l1 l2"
  shows "lifting_valid (merge_lv l1 l2)"
proof(rule lifting_validI)
  fix s :: 'x
  fix a :: "'a1 * 'a2"
  fix b :: "'b"

  obtain a1 a2 where A : "a = (a1, a2)" by (cases a; auto)

  obtain z where
    Zsup : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z" and
    ZS1 : "z \<in> LOutS l1 s" and
    ZS2 : "z \<in> LOutS l2 s" and
    Z1 : "LOut l1 s z = a1" and
    Z2 : "LOut l2 s z = a2"
    using l_orthoD[OF Hort] by blast

  have "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} [^ LUpd l1 s a1 b, LUpd l2 s a2 b ^]"
    using bsup_sup[OF Zsup bsup_spec] by auto

  hence "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = z"
    using is_sup_unique[OF Zsup] by auto

  thus "LUpd (merge_lv l1 l2) s a b \<in> LOutS (merge_lv l1 l2) s"
    using ZS1 ZS2 A
    by(auto simp add: merge_lv_def merge_l_def split:prod.splits)  
next
  fix s :: 'x
  fix a :: "'a1 * 'a2"
  fix b :: "'b"

  obtain a1 a2 where A : "a = (a1, a2)" by (cases a; auto)

  obtain z where
    Zsup : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z" and
    ZS1 : "z \<in> LOutS l1 s" and
    ZS2 : "z \<in> LOutS l2 s" and
    Z1 : "LOut l1 s z = a1" and
    Z2 : "LOut l2 s z = a2"
    using l_orthoD[OF Hort] by blast

  have "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} [^ LUpd l1 s a1 b, LUpd l2 s a2 b ^]"
    using bsup_sup[OF Zsup bsup_spec] by auto

  hence "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = z"
    using is_sup_unique[OF Zsup] by auto

  thus "LOut (merge_lv l1 l2) s (LUpd (merge_lv l1 l2) s a b) = a"
    using Z1 Z2 A
    by(auto simp add: merge_lv_def merge_l_def split:prod.splits)
next
  fix s :: 'x
  fix b :: 'b

  assume Belem : "b \<in> LOutS (merge_lv l1 l2) s"

  have Be1 : "b \<in> LOutS l1 s"
    using Belem
    by(auto simp add: merge_lv_def)

  have Be2 : "b \<in> LOutS l2 s"
    using Belem
    by(auto simp add: merge_lv_def)

  obtain a1 where A1 : "LOut l1 s b = a1" by auto
  obtain a2 where A2 : "LOut l2 s b = a2" by auto

  obtain z where
    Zsup : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z" and
    ZS1 : "z \<in> LOutS l1 s" and
    ZS2 : "z \<in> LOutS l2 s" and
    Z1 : "LOut l1 s z = a1" and
    Z2 : "LOut l2 s z = a2"
    using l_orthoD[OF Hort] by blast

  have "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} [^ LUpd l1 s a1 b, LUpd l2 s a2 b ^]"
    using bsup_sup[OF Zsup bsup_spec] by auto

  hence Meq : "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = z"
    using is_sup_unique[OF Zsup] by auto

  (* slightly odd - for this part we don't actually need Be2 *)
  have Leq1 :
    "b <[ LUpd l1 s a1 b" using lifting_validDI[OF H1 Be1] A1
    by auto

  have Leq2 :
    "LUpd l1 s a1 b <[ z" using is_sup_unfold1[OF Zsup]
    by auto

  hence Leq : "b <[ z"
    using leq_trans[OF Leq1 Leq2] by auto

  thus "b <[ LUpd (merge_lv l1 l2) s (LOut (merge_lv l1 l2) s b) b"
    using A1 A2 Meq
    by(auto simp add: merge_lv_def merge_l_def split:prod.splits)
qed
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
(*
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
                                  | None \<Rightarrow> LOut t s (LBase t s))
                      | None \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . (case (f s) of
                      Some k \<Rightarrow> update k (LBase t s) empty
                      | None \<Rightarrow> empty)) \<rparr>"
*)

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
                                  | None \<Rightarrow> LOut t s (LBase t s))
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
  , LBase = (\<lambda> x . (f x (LOut t x (LBase t x)), LBase t x)) \<rparr>"

definition prod_fan_l ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow>
   ('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a, ('c * 'b)) lifting" where
"prod_fan_l f t =
  plifting.extend (prod_fan_pl f t)
    \<lparr> LPost =
      (\<lambda> s cb . (f s (LOut t s (LPost t s (snd cb))), LPost t s (snd cb))) \<rparr>"

definition prod_fan_pv ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow>
   ('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
   ('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow>
   ('x, 'a, ('c * 'b)) pliftingv" where
"prod_fan_pv f t v =
  \<lparr> LOutS = (\<lambda> s . { cb . \<exists> c b . cb = (c, b) \<and> b \<in> LOutS v s \<and> c = f s (LOut t s b)}) \<rparr>"
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
"l_reverse l =
  LOut l"


definition roalist_pl ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b, 'd) roalist) plifting" where
"roalist_pl f t =
  \<lparr> LUpd = (\<lambda> s a l .
            (case (f s) of
              Some k \<Rightarrow>
                (case roalist_get_v l k of
                  Some v \<Rightarrow> (roalist_update_v k (LUpd t s a v) l)
                  | None \<Rightarrow> (roalist_update_v k (LNew t s a) l))
              | None \<Rightarrow> l))
  , LOut = (\<lambda> s l . (case (f s) of
                      Some k \<Rightarrow> (case roalist_get_v l k of 
                                  Some a \<Rightarrow> LOut t s a
                                  | None \<Rightarrow> LOut t s (LBase t s))
                      | None \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . (case (f s) of
                        Some k \<Rightarrow> roalist_update_v k (LBase t s) roalist_empty
                        | None \<Rightarrow> roalist_empty)) \<rparr>"
(*
  , LOut = (\<lambda> s l . (case (f s) of
                      Some k \<Rightarrow> (case roalist_get l k of 
                                  Some a \<Rightarrow> LOut t s a
                                  | None \<Rightarrow> LOut t s (LBase t s))
                      | None \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . (case (f s) of
                      Some k \<Rightarrow> roalist_update k (LBase t s) empty
                      | None \<Rightarrow> empty)) \<rparr>"
*)

(* TODO: if we can't find the key, what do we do with LPost?
   I think either obvious choice (LPost on LBase, or leave empty) meets spec *)
definition roalist_l ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b, 'd) roalist) lifting" where
"roalist_l f t =
  plifting.extend (roalist_pl f t)
    \<lparr> LPost = (\<lambda> s l . (case f s of
                          Some k \<Rightarrow> (case roalist_get_v l k of 
                                       Some a \<Rightarrow> roalist_update_v k (LPost t s a) l
                                       | None \<Rightarrow> l)
                          | None \<Rightarrow> l)) \<rparr>"

definition roalist_pv ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b, 'd) roalist) pliftingv" where
"roalist_pv f v =
  \<lparr> LOutS = (\<lambda> s . { l . \<exists> k a . f s = Some k \<and> roalist_get_v l k = Some a \<and> a \<in> LOutS v s }) \<rparr>"

(* idea: we want a list head lifting that never modifies head. just pushes result. 
   does this meet our validity criteria? no; update not idempotent.
   however, we could perhaps have a "pre-pass" that pushes a bogus element onto
   the stack first, if we need write-only access
*)

definition list_hd_pl ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> ('x, 'a, 'b list) plifting" where
"list_hd_pl t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              b' # rest \<Rightarrow> (LUpd t s a b')#rest
              | [] \<Rightarrow> [(LNew t s a)]))
  , LOut = (\<lambda> s b . (case b of b' # rest \<Rightarrow> (LOut t s b')
                      | [] \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . [])\<rparr>"


definition list_hd_l ::
  "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow> ('x, 'a, 'b list) lifting" where
"list_hd_l t =
  plifting.extend (list_hd_pl t)
    \<lparr> LPost = (\<lambda> s b . (case b of (b'#rest) \<Rightarrow> (LPost t s b')#rest
                                  | [] \<Rightarrow> [])) \<rparr>"

definition list_hd_pv ::
  "('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow> ('x, 'a, 'b list) pliftingv" where
"list_hd_pv v =
  \<lparr> LOutS = 
    (\<lambda> s . { l . \<exists> h t . h \<in> LOutS v s \<and> l = h#t}) \<rparr>"

(* another approach to "list-head" lifting:
   have a "scratch" area that is updated by Upd.
   Then have Post actually push to the list.
   "sc" here is short for "scratch"
*)

definition list_hd_sc_pl ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> ('x, 'a, ('b * 'b list)) plifting" where
"list_hd_sc_pl t =
  \<lparr> LUpd = (\<lambda> s a b .
              (case b of (bh, bl) \<Rightarrow> (LUpd t s a bh, bl)))
  , LOut = (\<lambda> s b . (case b of (bh, bl) \<Rightarrow> (LOut t s bh)))
  , LBase = (\<lambda> s . (LBase t s, [])) \<rparr>"

definition list_hd_sc_l ::
  "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow> ('x, 'a, ('b * 'b list)) lifting" where
"list_hd_sc_l t =
  plifting.extend (list_hd_sc_pl t)
    \<lparr> LPost = (\<lambda> s b . (case b of (bh, bl) \<Rightarrow> (LPost t s bh, LPost t s bh # bl))) \<rparr>"

definition list_hd_sc_pv ::
  "('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow> ('x, 'a, ('b * 'b list)) pliftingv" where
"list_hd_sc_pv v =
  \<lparr> LOutS =
    (\<lambda> s . { b . (\<exists> bh bl . bh \<in> LOutS v s \<and> (b = (bh, bl)))}) \<rparr>"

(* Convenience definitions for accessing members of structures. *)
fun t1_l :: "('x, 'a, 'e1, 'z) lifting_scheme \<Rightarrow>
             ('x, 'a, 'e1 * 'rest :: Pordb) lifting" where
"t1_l l = fst_l l"

fun t2_l :: "('x, 'a, 'e2, 'z) lifting_scheme \<Rightarrow>
             ('x, 'a, 'e1 :: Pordb * 'e2 * 'rest :: Pordb) lifting" where
"t2_l l = (snd_l (t1_l l))" 

fun t3_l :: "('x, 'a, 'e3, 'z) lifting_scheme \<Rightarrow>
             ('x, 'a, 'e1 :: Pordb * 'e2 :: Pordb * 'e3 * 'rest :: Pordb) lifting" where
"t3_l l = snd_l (t2_l l)" 

fun t4_l :: "('x, 'a, 'e4, 'z) lifting_scheme \<Rightarrow>
             ('x, 'a, 'e1 :: Pordb * 'e2 :: Pordb * 'e3 :: Pordb * 
                      'e4 * 'rest :: Pordb) lifting" where
"t4_l l = (snd_l (t3_l l))" 

fun t5_l :: "('x, 'a, 'e5, 'z) lifting_scheme \<Rightarrow>
             ('x, 'a, 'e1 :: Pordb * 'e2 :: Pordb * 'e3 :: Pordb *
                      'e4 :: Pordb * 'e5 * 'rest :: Pordb) lifting" where
"t5_l l = (snd_l (t4_l l))" 


(* convenience lifting for standard wrapping (swr) *)
fun ot_l :: "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow>
             ('x, 'a, 'b md_triv option) lifting" where
"ot_l l =
  (option_l o triv_l) l"

(* Liftings for mapping over data structures *)

(* a lifting for mapping over an entire list, needed e.g. when relating a
   list of wrapped values to an unwrapped one *)

(* i'm not sure there is a reasonable way to implement this, however...
maybe we can have one specific to swr/products/sums?
i don't know that this can be done for all liftings necessarily.
e.g. when updating, what happens if we are given a list of a different length?

one idea: check the length of the input list. if it is equal, do an actual update
otherwise construct a list of LNew values
we could probably have a more precise/robust one, but that should at least meet
the laws.
*)

definition list_map_pl ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> ('x, 'a list, 'b list) plifting" where
"list_map_pl t =
  \<lparr> LUpd = (\<lambda> s a b .
                if length a = length b
                then map2 (LUpd t s) a b
                else map (LNew t s) a)
  , LOut = (\<lambda> s b . map (LOut t s) b)
  , LBase = (\<lambda> s . [])\<rparr>"

definition list_map_l ::
  "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow> ('x, 'a list, 'b list) lifting" where
"list_map_l t =
  plifting.extend (list_map_pl t)
    \<lparr> LPost = (\<lambda> s b . map (LPost t s) b) \<rparr>"

definition list_map_pv ::
  "('x, 'a, 'b, 'z) pliftingv_scheme \<Rightarrow> ('x, 'a list, 'b list) pliftingv" where
"list_map_pv v =
  \<lparr> LOutS = 
    (\<lambda> s . {l . list_all (\<lambda> x . x \<in> (LOutS v s)) l}) \<rparr>"

(* sum map-lifting *)
definition sum_map_pl ::
  "('x, 'a1, 'b1, 'z1) plifting_scheme \<Rightarrow>
   ('x, 'a2, 'b2, 'z2) plifting_scheme \<Rightarrow>
   ('x, 'a1 + 'a2, 'b1 + 'b2) plifting" where
"sum_map_pl t1 t2 =
  \<lparr> LUpd = (\<lambda> s a b . 
    (case b of
      Inl bl \<Rightarrow> (case a of
                  Inl al \<Rightarrow> Inl (LUpd t1 s al bl)
                  | Inr ar \<Rightarrow> Inr (LNew t2 s ar))
      | Inr br \<Rightarrow> (case a of
                  Inl al \<Rightarrow> Inl (LNew t1 s al)
                  | Inr ar \<Rightarrow> Inr (LUpd t2 s ar br))))
  , LOut = (\<lambda> s a . (case a of
                      Inl al \<Rightarrow> Inl (LOut t1 s al)
                      | Inr ar \<Rightarrow> Inr (LOut t2 s ar)))
  , LBase = (\<lambda> s . Inl (LBase t1 s))
  \<rparr>"

definition sum_map_l ::
  "('x, 'a1, 'b1, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b2, 'z2) lifting_scheme \<Rightarrow>
   ('x, 'a1 + 'a2, 'b1 + 'b2) lifting" where
"sum_map_l t1 t2 =
  plifting.extend (sum_map_pl t1 t2)
    \<lparr> LPost =
      (\<lambda> s b . (case b of
                  Inl bl \<Rightarrow> Inl (LPost t1 s bl)
                  | Inr br \<Rightarrow> Inr (LPost t2 s br))) \<rparr>"

definition sum_map_pv ::
  "('x, 'a1, 'b1, 'z1) pliftingv_scheme \<Rightarrow>
   ('x, 'a2, 'b2, 'z2) pliftingv_scheme \<Rightarrow>
   ('x, 'a1 + 'a2, 'b1 + 'b2) pliftingv" where
"sum_map_pv t1 t2 =
  \<lparr> LOutS = (\<lambda> s . (Inl ` (LOutS t1 s)) \<union> (Inr ` (LOutS t2 s))) \<rparr>"

(* ROAlist map-lifting
   does not use the ability to parameterize mapping based on keys. *)

(* helper used to implement upd *)
(* unsure if this should have a 'x (syntax) parameter, but
   that seems like the most straightforward thing *)
fun roalist_fuse' ::
"('x, 'v1, 'v2, 'z1) plifting_scheme \<Rightarrow>
 ('x, 'd1, 'd2, 'z2) plifting_scheme \<Rightarrow>
 'x \<Rightarrow>
 ('k :: linorder, 'v1, 'd1 option) roalist' \<Rightarrow> 
 ('k :: linorder, 'v2, 'd2 option) roalist' \<Rightarrow>
 ('k :: linorder, 'v2, 'd2 option) roalist'" where
"roalist_fuse' lv ld x [] _ = []"
| "roalist_fuse' lv ld x ((kh1, Inl vh1)#t1) r2 =
  (case map_of r2 kh1 of
    Some (Inl vh2) \<Rightarrow> ((kh1, Inl (LUpd lv x vh1 vh2)))
    | _ \<Rightarrow> ((kh1, Inl (LNew lv x vh1)))) # 
   roalist_fuse' lv ld x t1 r2"
| "roalist_fuse' lv ld x ((kh1, Inr (Some vd1))#t1) r2 =
  (case map_of r2 kh1 of
    Some (Inr (Some vd2)) \<Rightarrow> ((kh1, Inr (Some (LUpd ld x vd1 vd2))))
    | _ \<Rightarrow> ((kh1, Inr (Some (LNew ld x vd1))))) # 
   roalist_fuse' lv ld x t1 r2"
| "roalist_fuse' lv ld x ((kh1, Inr None)#t1) r2 =
    (kh1, Inr None) #
    roalist_fuse' lv ld x t1 r2"

lift_definition roalist_fuse :: 
"('x, 'v1, 'v2, 'z1) plifting_scheme \<Rightarrow>
 ('x, 'd1, 'd2, 'z2) plifting_scheme \<Rightarrow>
 'x \<Rightarrow>
 ('k :: linorder, 'v1, 'd1) roalist \<Rightarrow> 
 ('k :: linorder, 'v2, 'd2) roalist \<Rightarrow>
 ('k :: linorder, 'v2, 'd2) roalist" 
is roalist_fuse' sorry

definition roalist_map_pl ::
  "('x, 'v1, 'v2, 'z1) plifting_scheme \<Rightarrow>
   ('x, 'd1, 'd2, 'z2) plifting_scheme \<Rightarrow>
   ('x, ('k :: linorder, 'v1, 'd1) roalist, ('k :: linorder, 'v2, 'd2) roalist) plifting"
  where
"roalist_map_pl tv td =
  \<lparr> LUpd = (\<lambda> s a b . roalist_fuse tv td s a b)
  , LOut = (\<lambda> s b . roalist_map 
                      (\<lambda> _ v . LOut tv s v)
                      (\<lambda> _ d . LOut td s d)
                      b)
  , LBase = (\<lambda> s . roalist_empty) \<rparr>"
    
definition roalist_map_l ::
"('x, 'v1, 'v2, 'z1) lifting_scheme \<Rightarrow>
 ('x, 'd1, 'd2, 'z2) lifting_scheme \<Rightarrow>
 ('x, ('k :: linorder, 'v1, 'd1) roalist, ('k :: linorder, 'v2, 'd2) roalist) lifting" where
"roalist_map_l tv td =
  plifting.extend (roalist_map_pl tv td)
  \<lparr> LPost = (\<lambda> s b . roalist_map 
                      (\<lambda> _ v . LPost tv s v)
                      (\<lambda> _ d . LPost td s d) 
                      b) \<rparr>"

(* fill this in later; need an analogue of list_all for roalist. *)
(*
definition roalist_map_pv ::
"('x, 'v1, 'v2, 'z1) lifting_scheme \<Rightarrow>
 ('x, 'd1, 'd2, 'z2) lifting_scheme \<Rightarrow>
 ('x, ('k :: linorder, 'v1, 'd1) roalist, ('k :: linorder, 'v2, 'd2) roalist) lifting" where
*)

(* possibly needed later: option, triv, prio *)

(* finally, here we allow keymaps, which might enable more interesting merges
   however we will need to reset the kmap in between commands. *)
(* should double check this *)
(*

*)

(* another approach would be to return sets. this might we worth exploring later. *)

(* new lifting needed: merging an OAlist with an ROAlist
   idea: enable separating control and data for Lambda/SECD
  
*)

end