theory Lifter_Instances imports Lifter
begin

(*
 * In this file, we construct instances of the lifter record (see Lifter.v)
 * that describe how to lift into (and out of) most of the common types we use in Gazelle.
 * Note that some of the lifting instances at the end of this file have proofs admitted.
 * Completing the proofs for oalist and roalist, and eventually purging this development
 * of admits ("sorry") is an important TODO.
 *)

(* Bogus: a typeclass for data that we can supply "bogus" default values for (instead of undefined)
 * as mentioned in Lifter.v, this avoids annoying problems that can crop up in the generated code.
 * The value chosen has no significance; it is just there as a placeholder to avoid
 * crashing or getting stuck at undefined values.
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


(* An alternate option instance, in which the bogus value is None
   (list instance should probably be [] but also could use
   revisiting)
*)
(*
instantiation option :: (_) Bogus begin
definition option_bogus : "bogus = None"
instance proof qed
end
*)

(* Instead we use this instance, where
 * we assume that the contained value also implements bogus.
 * (TODO: why exactly is this better?)
 *)

instantiation option :: (Bogus) Bogus begin
definition option_bogus : "bogus = Some bogus"
instance proof qed
end

(* TODO: why not [bogus]? *)
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


(* Here we implement the simplest lifting, an identity lifting from 'a to 'a.
 * For this lifting (as well as all others below), we give:
 * - a lifting implementation, id_l
 * - a liftingv implementation, id_lv
 * - a proof of validity (in this case weak; id_l_valid_weak)
 * - a restatement of the proof that can sometimes help with automation by increasing the
 *   contexts in which it can apply (id_l_valid_weak_vsg)
 * - another restatement of the proof that uses extensionality (id_l_weak_vsg')
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


(* Note that we could prove validb lemmas if we change the hierarchy so that we
   force base = bogus (i.e. make Pordb depend on Bogus typeclass).
   However, this feels like ascribing "meaning" to the bogus element in a way that
   doesn't seem to be in the spirit of what Bogus is "meant for". *)
lemma id_l_valid_weak :
  shows "lifting_valid_weak' id_l"
proof(rule lifting_valid_weakI)
  show "\<And>s a b. LOut id_l s (LUpd id_l s a b) = a"
    by(auto simp add: id_l_def)
next
  show "\<And>s b. b \<in> UNIV \<Longrightarrow>
           b <[ LUpd id_l s (LOut id_l s b) b"
    by(auto simp add: id_l_def leq_refl)
next
  show "\<And>s a b. LUpd id_l s a b \<in> UNIV"
    by auto
qed

lemma id_l_valid_weak_vsg :
  assumes Hv : "S = (\<lambda> _ . UNIV)"
  shows "lifting_valid_weak id_l S"
  using id_l_valid_weak Hv by auto

lemma id_l_valid_weak_vsg' :
  assumes Hv : "\<And> x . S x = UNIV"
  shows "lifting_valid_weak id_l S"
  using id_l_valid_weak Hv fun_eq_iff[of S "\<lambda> _ . UNIV"] by auto

(* Trivial lifting *)

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

lemma triv_l_valid_weak : 
  shows "lifting_valid_weak' (triv_l :: ('x, 'a :: Bogus, 'a md_triv) lifting)"
proof(rule lifting_valid_weakI)
  fix s :: 'x
  fix a :: 'a
  fix b
  show "LOut (triv_l) s (LUpd (triv_l) s a b) = a"
    by(auto simp add:triv_lv_def triv_l_def split:md_triv.splits)
next
  fix s :: 'x
  fix b :: "'a md_triv"

  show "b <[ LUpd triv_l s (LOut triv_l s b) b"
   by(auto simp add:triv_lv_def triv_l_def triv_pleq
          split:md_triv.splits)
next
  fix s :: 'x
  fix a :: "'a"
  fix b :: "'a md_triv"
  show "LUpd triv_l s a b \<in> UNIV" by auto
qed

lemma triv_l_valid_weak_vsg :
  assumes "S = (\<lambda> x . UNIV)"
  shows "lifting_valid_weak (triv_l :: ('x, 'a :: Bogus, 'a md_triv) lifting) S"
  using assms triv_l_valid_weak
  by(auto)

(* an alternate version using extensionality *)
lemma triv_l_valid_weak_vsg' :
  assumes "\<And> x . S x = UNIV"
  shows "lifting_valid_weak (triv_l :: ('x, 'a :: Bogus, 'a md_triv) lifting) S"
  using assms triv_l_valid_weak_vsg fun_eq_iff[of S "\<lambda> _ . UNIV"] by auto



(* option lifting - really a lifting-transformer; from a lifting on 'a \<Rightarrow> 'b,
 * we get a lifting 'a \<Rightarrow> 'b option*)

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

definition option_l_S :: "('s, 'b) valid_set \<Rightarrow> ('s, 'b option) valid_set" where
"option_l_S S s = (Some ` S s)"

lemma option_l_valid_weak :
  assumes H : "lifting_valid_weak (t :: ('x, 'a, 'b :: {Pord}, 'z) lifting_scheme) S"
  shows "lifting_valid_weak (option_l t) (option_l_S S)"
proof(rule lifting_valid_weakI)
  fix s a b
  show "LOut (option_l t) s (LUpd (option_l t) s a b) = a"
    using lifting_valid_weakDO[OF H]
    by(auto simp add:option_l_def LNew_def split:option.splits)
next
  fix s b
  assume Hb : "b \<in> option_l_S S s"
  thus "b <[ LUpd (option_l t) s (LOut (option_l t) s b) b"
    using lifting_valid_weakDI[OF H]
    by(auto simp add:option_l_def option_l_S_def LNew_def option_pleq split:option.splits)
next
  fix s :: 'x
  fix a
  fix b :: "'b option"
  show "LUpd (option_l t) s a b \<in> option_l_S S s"
    using lifting_valid_weakDP[OF H]
    by(auto simp add: option_l_def option_l_S_def LNew_def split:option.splits)
qed

lemma option_l_valid_weak_vsg :
  assumes Hv : "S' = option_l_S S"
  assumes H : "lifting_valid_weak (t :: ('x, 'a, 'b :: {Pord}, 'z) lifting_scheme) S"
  shows "lifting_valid_weak (option_l t) S'"
  using assms option_l_valid_weak by auto

(* Option_l is valid (not just valid_weak) *)
lemma option_l_valid :
  assumes H : "lifting_valid (t :: ('x, 'a, 'b :: {Pord}, 'z) lifting_scheme) S"
  shows "lifting_valid (option_l t) (option_l_S S)"
proof(rule lifting_validI)
  fix s a b
  show "LOut (option_l t) s (LUpd (option_l t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add:option_l_def LNew_def split:option.splits)
next
  fix s a b
  assume Hb : "b \<in> (option_l_S S) s"
  thus "b <[ LUpd (option_l t) s a b"
    using lifting_validDI[OF H]
    by(auto simp add:option_l_def option_l_S_def LNew_def option_pleq split:option.splits)
next
  fix s :: 'x
  fix a :: 'a
  fix b :: "'b option"
  show "LUpd (option_l t) s a b \<in> option_l_S S s"
    using lifting_validDP[OF H]
    by(auto simp add:option_l_def option_l_S_def LNew_def option_pleq split:option.splits)
qed

lemma option_l_valid_vsg :
  assumes Hv : "S' = option_l_S S"
  assumes H : "lifting_valid (t :: ('x, 'a, 'b :: {Pord}, 'z) lifting_scheme) S"
  shows "lifting_valid (option_l t) S'"
  using assms option_l_valid by auto

lemma option_l_valid_weakb :
  assumes H : "lifting_valid_weak (t :: ('x, 'a, 'b :: {Pord}, 'z) lifting_scheme) S"
  shows "lifting_valid_weakb (option_l t) (option_l_S S)"
proof(rule lifting_valid_weakbI')
  show "lifting_valid_weak (option_l t) (option_l_S S)"
    using option_l_valid_weak[OF H] by auto
next
  fix s
  show "LBase (option_l t) s = \<bottom>"
    by(simp add: option_l_def option_bot)
qed

lemma option_l_valid_weakb_vsg :
  assumes Hv : "S' = option_l_S S"
  assumes H : "lifting_valid_weak (t :: ('x, 'a, 'b :: {Pord}, 'z) lifting_scheme) S"
  shows "lifting_valid_weakb (option_l t) S'"
  using assms option_l_valid_weakb by auto

lemma option_l_validb :
  assumes H : "lifting_valid (t :: ('x, 'a, 'b :: {Pord}, 'z) lifting_scheme) S"
  shows "lifting_validb (option_l t) (option_l_S S)"
proof(rule lifting_validbI')
  show "lifting_valid (option_l t) (option_l_S S)"
    using option_l_valid[OF H] by auto
next
  fix s
  show "LBase (option_l t) s = \<bottom>"
    by(simp add: option_l_def option_bot)
qed

lemma option_l_validb_vsg :
  assumes Hv : "S' = option_l_S S"
  assumes H : "lifting_valid (t :: ('x, 'a, 'b :: {Pord}, 'z) lifting_scheme) S"
  shows "lifting_validb (option_l t) S'"
  using assms option_l_validb by auto

(* If liftings l2 and l2 are orthogonal, the results of applying the option
 * lifting-transformer to each will be also. *)
lemma option_ortho :
  assumes H1 : "lifting_valid_weak l1 S1"
  assumes H2 : "lifting_valid_weak l2 S2"
  assumes Horth : "l_ortho (l1 :: ('x, 'a1, 'b :: Mergeable) lifting)
                       (l2 :: ('x, 'a2, 'b :: Mergeable) lifting)"
  shows "l_ortho (option_l l1) (option_l l2)"
proof(rule l_orthoI)

  fix s a1 a2 b

  show "LUpd (option_l l1) s a1 (LUpd (option_l l2) s a2 b) =
        LUpd (option_l l2) s a2 (LUpd (option_l l1) s a1 b)"
    using l_orthoDI[OF Horth] l_orthoDB[OF Horth]
    by(auto simp add: option_l_def LNew_def split:option.splits)

next

  fix s
  show "LBase (option_l l1) s = LBase (option_l l2) s"
    by(auto simp add: option_l_def)

qed

(* sum types. We define two liftings, inl and inr. For projection to always be well-defined,
 * note that we require the "other" component (e.g. the "right" component for inl)
 * to have a least element. *)
definition inl_l ::
  "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> 
   ('x, 'a, ('b + 'c :: Pordb)) lifting" where
"inl_l t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              Inl b' \<Rightarrow> Inl (LUpd t s a b')
              | _ \<Rightarrow> Inl (LNew t s a)))
  , LOut = (\<lambda> s b . (case b of Inl b' \<Rightarrow> LOut t s b'
                      | _ \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . Inr \<bottom>)\<rparr>"

definition inl_l_S ::
  "('x, 'b) valid_set \<Rightarrow> ('x, ('b + 'c :: Pordb)) valid_set" where
"inl_l_S S s =
  Inl ` S s"

(* Sum has no least element, so inl/inr liftings cannot have validb versions *)
lemma inl_l_valid_weak :
  assumes H : "lifting_valid_weak t S"
  shows "lifting_valid_weak (inl_l t :: ('x, 'a, ('b :: Pord + 'c :: Pordb)) lifting) (inl_l_S S)"
proof(rule lifting_valid_weakI)
  fix s :: 'x
  fix a :: 'a 
  fix b :: "('b + 'c)"
  show "LOut (inl_l t) s (LUpd (inl_l t) s a b) = a"
    using lifting_valid_weakDO[OF H]
    by(auto simp add: inl_l_def sum_pleq LNew_def split:sum.splits)
next
  fix s :: 'x
  fix b :: "'b + 'c"
  assume Hb : "b \<in> inl_l_S S s"
  show "b <[ LUpd (inl_l t) s (LOut (inl_l t) s b) b"
    using lifting_valid_weakDI[OF H] Hb
    by(auto simp add: inl_l_def inl_l_S_def sum_pleq LNew_def split:sum.splits)
next
  fix s :: 'x
  fix a
  fix b :: "'b + 'c"
  show "LUpd (inl_l t) s a b \<in> inl_l_S S s"
    using lifting_valid_weakDP[OF H]
    by(auto simp add: inl_l_def inl_l_S_def LNew_def split:sum.splits)
qed

lemma inl_l_valid :
  assumes H : "lifting_valid t S"
  shows "lifting_valid (inl_l t :: ('x, 'a, ('b :: Pord + 'c :: Pordb)) lifting) (inl_l_S S)"
proof(rule lifting_validI)
  fix s :: 'x
  fix a :: 'a 
  fix b :: "('b + 'c)"
  show "LOut (inl_l t) s (LUpd (inl_l t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add: inl_l_def sum_pleq LNew_def split:sum.splits)
next
  fix s :: 'x
  fix a
  fix b :: "'b + 'c"
  assume Hb : "b \<in> inl_l_S S s"
  show "b <[ LUpd (inl_l t) s a b"
    using lifting_validDI[OF H] Hb
    by(auto simp add: inl_l_def inl_l_S_def sum_pleq LNew_def split:sum.splits)
next
  fix s :: 'x
  fix a
  fix b :: "'b + 'c"
  show "LUpd (inl_l t) s a b \<in> inl_l_S S s"
    using lifting_validDP[OF H]
    by(auto simp add: inl_l_def inl_l_S_def LNew_def split:sum.splits)
qed

(* The other sum lifting: inr *)
definition inr_l ::
  "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> 
   ('x, 'a, ('c :: Pordb + 'b)) lifting" where
"inr_l t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              Inr b' \<Rightarrow> Inr (LUpd t s a b')
              | _ \<Rightarrow> Inr (LNew t s a)))
  , LOut = (\<lambda> s b . (case b of Inr b' \<Rightarrow> LOut t s b'
                      | _ \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . Inl \<bottom>)\<rparr>"

definition inr_l_S ::
  "('x, 'b) valid_set \<Rightarrow> ('x, ('c :: Pordb + 'b)) valid_set" where
"inr_l_S S s =
  Inr ` S s"

(* Sum has no least element, we inl/inr liftings cannot have validb versions *)
lemma inr_l_valid_weak :
  assumes H : "lifting_valid_weak t S"
  shows "lifting_valid_weak (inr_l t :: ('x, 'a, ('c :: Pordb + 'b :: Pord)) lifting) (inr_l_S S)"
proof(rule lifting_valid_weakI)
  fix s :: 'x
  fix a :: 'a 
  fix b :: "('c + 'b)"
  show "LOut (inr_l t) s (LUpd (inr_l t) s a b) = a"
    using lifting_valid_weakDO[OF H]
    by(auto simp add: inr_l_def sum_pleq LNew_def split:sum.splits)
next
  fix s :: 'x
  fix b :: "'c + 'b"
  assume Hb : "b \<in> inr_l_S S s"
  show "b <[ LUpd (inr_l t) s (LOut (inr_l t) s b) b"
    using lifting_valid_weakDI[OF H] Hb
    by(auto simp add: inr_l_def inr_l_S_def sum_pleq LNew_def split:sum.splits)
next
  fix s :: 'x
  fix a
  fix b :: "'c + 'b"
  show "LUpd (inr_l t) s a b \<in> inr_l_S S s"
    using lifting_valid_weakDP[OF H]
    by(auto simp add: inr_l_def inr_l_S_def LNew_def split:sum.splits)
qed


lemma inr_l_valid :
  assumes H : "lifting_valid t S"
  shows "lifting_valid (inr_l t :: ('x, 'a, ('c :: Pordb + 'b :: Pord)) lifting) (inr_l_S S)"
proof(rule lifting_validI)
  fix s :: 'x
  fix a :: 'a 
  fix b :: "('c + 'b)"
  show "LOut (inr_l t) s (LUpd (inr_l t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add: inr_l_def sum_pleq LNew_def split:sum.splits)
next
  fix s :: 'x
  fix a
  fix b :: "'c + 'b"
  assume Hb : "b \<in> inr_l_S S s"
  show "b <[ LUpd (inr_l t) s a b"
    using lifting_validDI[OF H] Hb
    by(auto simp add: inr_l_def inr_l_S_def sum_pleq LNew_def split:sum.splits)
next
  fix s :: 'x
  fix a
  fix b :: "'c + 'b"
  show "LUpd (inr_l t) s a b \<in> inr_l_S S s"
    using lifting_validDP[OF H]
    by(auto simp add: inr_l_def inr_l_S_def LNew_def split:sum.splits)
qed

(* Priority lifting transformer *)
definition prio_l' ::
  "('a, 'b) syn_lifting \<Rightarrow>
   ('a, 'b md_prio) syn_lifting" where
"prio_l' t =
  (\<lambda> p . (case p of
              mdp m b \<Rightarrow> t b))"

(* Prio_l is rather customizable: it takes
 * - a priority f0 to use on the base element
 * - a priority transformation function f1 to use when updating
 * - a lifting ('a \<Rightarrow> 'b)
 * and returns a lifting ('a \<Rightarrow> 'b md_prio)
 * note: this only allows setting output priority based on syntax. *)
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

definition prio_l_S :: "('x, 'b) valid_set \<Rightarrow> ('x, 'b md_prio) valid_set" where
"prio_l_S S s =
  { p . (case p of
          mdp n x \<Rightarrow> x \<in> S s) }"

(* given a (non-strictly) increasing change of
 * the "priority index" (f1), prio preserves weak and strong liftings. *)
lemma prio_l_valid_weak :
  assumes H : "lifting_valid_weak t S"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_valid_weak (prio_l f0 f1 t) (prio_l_S S)"
proof(rule lifting_valid_weakI)
  fix s a b
  show "LOut (prio_l f0 f1 t) s (LUpd (prio_l f0 f1 t) s a b) = a"
    using lifting_valid_weakDO[OF H]
    by(auto simp add:prio_l_def prio_lv_def LNew_def split:md_prio.splits)
next
  fix s b
  assume Hb : "b \<in> prio_l_S S s"
  show "b <[ LUpd (prio_l f0 f1 t) s (LOut (prio_l f0 f1 t) s b) b"
    using lifting_valid_weakDI[OF H] Hmono Hb
    by(auto simp add:prio_l_def prio_lv_def prio_l_S_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s a b
  show "LUpd (prio_l f0 f1 t) s a b \<in> prio_l_S S s"
    using lifting_valid_weakDP[OF H]
    by(auto simp add: prio_l_def prio_l_S_def LNew_def split:md_prio.splits)
qed

lemma prio_l_valid_weak_vsg :
  assumes Hv : "S' = prio_l_S S"
  assumes H : "lifting_valid_weak t S"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_valid_weak (prio_l f0 f1 t) S'"
  using assms prio_l_valid_weak by blast
  
lemma prio_l_valid :
  assumes H : "lifting_valid t S"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_valid (prio_l f0 f1 t) (prio_l_S S)"
proof(rule lifting_validI)
  fix s a b
  show "LOut (prio_l f0 f1 t) s (LUpd (prio_l f0 f1 t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add:prio_l_def prio_lv_def LNew_def split:md_prio.splits)
next
  fix s a b
  assume Hb : "b \<in> prio_l_S S s"
  show "b <[ LUpd (prio_l f0 f1 t) s a b"
    using lifting_validDI[OF H] Hmono Hb
    by(auto simp add:prio_l_def prio_l_S_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s a b
  show "LUpd (prio_l f0 f1 t) s a b \<in> prio_l_S S s"
    using lifting_validDP[OF H]
    by(auto simp add: prio_l_def prio_l_S_def LNew_def split:md_prio.splits)
qed

lemma prio_l_valid_vsg :
  assumes Hv : "S' = prio_l_S S"
  assumes H : "lifting_valid t S"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_valid (prio_l f0 f1 t) S'"
  using assms prio_l_valid by blast

(* On the other hand, if the increment function f1 is strictly increasing (for all syntax value),
 * prio turns weak liftings into strong ones,
 * and also allows us to ignore side conditions on valid sets (hence (\<lambda> _ . UNIV) in the
 * conclusion below) *)
lemma prio_l_valid_strong :
  fixes t :: "('x, 'a, 'b :: Pord) lifting"
  assumes H : "lifting_valid_weak t S"
  assumes Hmono : "\<And> s p . p < f1 s p"
  shows "lifting_valid (prio_l f0 f1 t) (\<lambda> _ . UNIV)"
proof(rule lifting_validI)
  fix s a b
  show "LOut (prio_l f0 f1 t) s (LUpd (prio_l f0 f1 t) s a b) = a"
    using lifting_valid_weakDO[OF H]
    by(auto simp add:prio_l_def prio_lv_def LNew_def split:md_prio.splits)
next
  fix s a
  fix b :: "'b md_prio"

  obtain x1 p where B : "b = mdp p x1" by(cases b; auto)

  show "b <[ LUpd (prio_l f0 f1 t) s a b"
    using lifting_valid_weakDI[OF H] Hmono[of p s] B
    by(auto simp add:prio_l_def prio_lv_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s a b
  show "LUpd (prio_l f0 f1 t) s a b \<in> UNIV"
    by auto
qed

lemma prio_l_valid_strong_vsg :
  fixes t :: "('x, 'a, 'b :: Pord) lifting"
  assumes Hv : "S' = (\<lambda> _ . UNIV)"
  assumes H : "lifting_valid_weak t S"
  assumes Hmono : "\<And> s p . p < f1 s p"
  shows "lifting_valid (prio_l f0 f1 t) S'"
  using assms prio_l_valid_strong by blast

lemma prio_l_valid_strong_vsg' :
  fixes t :: "('x, 'a, 'b :: Pord) lifting"
  assumes Hv : "\<And> x . S' x = UNIV"
  assumes H : "lifting_valid_weak t S"
  assumes Hmono : "\<And> s p . p < f1 s p"
  shows "lifting_valid (prio_l f0 f1 t) S'"
  using prio_l_valid_strong_vsg[OF _ H Hmono] fun_eq_iff[of S' "\<lambda> _ . UNIV"] Hv 
  by(auto)


lemma prio_l_valid_weakb :
  assumes H : "lifting_valid_weakb t S"
  assumes Hzero : "\<And> s . f0 s = 0"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_valid_weakb (prio_l f0 f1 t) (prio_l_S S)"
proof(rule lifting_valid_weakbI')
  show "lifting_valid_weak (prio_l f0 f1 t) (prio_l_S S)"
    using prio_l_valid_weak[OF lifting_valid_weakbDV[OF H] Hmono]
    by auto
next
  fix s
  show "LBase (prio_l f0 f1 t) s = \<bottom>"
    using Hzero lifting_valid_weakbDB[OF H]
    by(simp add: prio_l_def prio_bot)
qed

lemma prio_l_valid_weakb_vsg :
  assumes Hv : "S' = prio_l_S S"
  assumes H : "lifting_valid_weakb t S"
  assumes Hzero : "\<And> s . f0 s = 0"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_valid_weakb (prio_l f0 f1 t) S'"
  using assms prio_l_valid_weakb by blast

lemma prio_l_validb :
  assumes H : "lifting_validb t S"
  assumes Hzero : "\<And> s . f0 s = 0"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_validb (prio_l f0 f1 t) (prio_l_S S)"
proof(rule lifting_validbI')
  show "lifting_valid (prio_l f0 f1 t) (prio_l_S S)"
    using prio_l_valid[OF lifting_validbDV[OF H] Hmono]
    by auto
next
  fix s
  show "LBase (prio_l f0 f1 t) s = \<bottom>"
    using Hzero lifting_validbDB[OF H]
    by(simp add: prio_l_def prio_bot)
qed

lemma prio_l_validb_vsg :
  assumes Hv : "S' = prio_l_S S"
  assumes H : "lifting_validb t S"
  assumes Hzero : "\<And> s . f0 s = 0"
  assumes Hmono : "\<And> s p . p \<le> f1 s p"
  shows "lifting_validb (prio_l f0 f1 t) S'"
  using assms prio_l_validb by blast


(* prio turns weak liftings into strong ones,
   given a strictly increasing change
   (even when \<bottom> enters the picture)*)
lemma prio_l_validb_strong :
  fixes t :: "('x, 'a, 'b :: Pordbc) lifting"
  assumes H : "lifting_valid_weakb t S"
  assumes Hzero : "\<And> s . f0 s = 0"
  assumes Hmono : "\<And> s p . p < f1 s p"
  shows "lifting_validb (prio_l f0 f1 t) (\<lambda> s . UNIV)"
proof(rule lifting_validbI')
  fix s a b
  show "lifting_valid (prio_l f0 f1 t) (\<lambda> s . UNIV)"
    using prio_l_valid_strong[OF lifting_valid_weakbDV[OF H] Hmono]
    by(auto)
next
  fix s

  show "LBase (prio_l f0 f1 t) s = \<bottom>"
    using Hzero lifting_valid_weakbDB[OF H]
    by(simp add: prio_l_def prio_bot)  
qed

lemma prio_l_validb_strong_vsg :
  fixes t :: "('x, 'a, 'b :: Pordbc) lifting"
  assumes Hv : "S' = (\<lambda> _ . UNIV)"
  assumes H : "lifting_valid_weakb t S"
  assumes Hzero : "\<And> s . f0 s = 0"
  assumes Hmono : "\<And> s p . p < f1 s p"
  shows "lifting_validb (prio_l f0 f1 t) S'"
  using assms prio_l_validb_strong by blast

lemma prio_l_validb_strong_vsg' :
  fixes t :: "('x, 'a, 'b :: Pordbc) lifting"
  assumes Hv : "\<And> x . S' x = UNIV"
  assumes H : "lifting_valid_weakb t S"
  assumes Hzero : "\<And> s . f0 s = 0"
  assumes Hmono : "\<And> s p . p < f1 s p"
  shows "lifting_validb (prio_l f0 f1 t) S'"
  using prio_l_validb_strong_vsg[OF _ H Hzero Hmono] fun_eq_iff[of S' "\<lambda> _ . UNIV"] Hv by auto

(*
 * We could prove prio_ortho - orthogonality for prio -
 * - but it is likely not useful as it would only work in cases where increment function
 * is the same between the two prio liftings being merged.
 * This tends to not be where we use prio.
*)

(*
lemma prio_ortho :
  assumes H : "l_ortho (l1 :: ('x, 'a1, 'b :: Mergeable) lifting) 
                       (l2 :: ('x, 'a2, 'b :: Mergeable) lifting)"
  shows "l_ortho (prio_l l1) (prio_l l2)"
proof(rule l_orthoI)
*)

(* Several useful examples of instantiating prio_l.
*)
definition prio_l_keep :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_keep =
  prio_l (\<lambda> _ . 0) (\<lambda> _ n . n)"

definition prio_l_inc :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 1 + x)"

definition prio_l_inc2 :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc2 =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 2 + x)"

definition prio_l_incN :: "nat \<Rightarrow> ('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_incN n =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . n + x)"

definition prio_l_case_inc :: "('x \<Rightarrow> nat) \<Rightarrow> ('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_case_inc f =
  prio_l (\<lambda> _ . 0) (\<lambda> s x . (f s) + x)"



(* Lifting implementations for product types.
 * As one might expect, there are two main ones, fst and snd.
 * As with sum types, above, we require the "other component" to have a least element.
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

definition fst_l_S :: "('x, 'b1 :: Pord) valid_set \<Rightarrow> ('x, ('b1 * 'b2 :: Pordb)) valid_set" where
"fst_l_S S s =
  { b . case b of (b1, _) \<Rightarrow> (b1 \<in> S s) }"


lemma fst_l_valid_weak  :
  assumes H : "lifting_valid_weak t S"
  shows "lifting_valid_weak ((fst_l t) :: ('x, 'a, ('b1 :: Pord) * ('b2 :: Pordb)) lifting) 
                            (fst_l_S S)"
proof(rule lifting_valid_weakI)
  fix s a 
  fix b :: "('b1 :: Pord) * ('b2 :: Pordb)"
  show "LOut (fst_l t) s (LUpd (fst_l t) s a b) = a"
    using lifting_valid_weakDO[OF H]
    by(auto simp add: fst_l_def split:prod.splits)
next
  fix s
  fix b :: "('b1 :: Pord) * ('b2 :: Pordb)"
  assume  Hb : "b \<in> fst_l_S S s"
  thus "b <[ LUpd (fst_l t) s (LOut (fst_l t) s b) b"
    using lifting_valid_weakDI[OF H]
    by(auto simp add: fst_l_def prod_pleq leq_refl fst_l_S_def split:prod.splits)
next
  fix s a 
  fix b :: "('b1 :: Pord) * ('b2 :: Pordb)"
  show "LUpd (fst_l t) s a b \<in> fst_l_S S s"
    using lifting_valid_weakDP[OF H]
    by(auto simp add: fst_l_def prod_pleq leq_refl fst_l_S_def split:prod.splits)
qed

lemma fst_l_valid_weak_vsg :
  assumes Hv : "S' = (fst_l_S S)"
  assumes H : "lifting_valid_weak t S"
  shows "lifting_valid_weak ((fst_l t) :: ('x, 'a, ('b1 :: Pord) * ('b2 :: Pordb)) lifting) 
                            S'"
  using assms fst_l_valid_weak by auto

lemma fst_l_valid :
  assumes H : "lifting_valid t S"
  shows "lifting_valid ((fst_l t) :: ('x, 'a, ('b1 :: Pord) * ('b2 :: Pordb)) lifting)
                       (fst_l_S S)"
proof(rule lifting_validI)
  fix s a 
  fix b :: "('b1 :: Pord) * ('b2 :: Pordb)"
  show "LOut (fst_l t) s (LUpd (fst_l t) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add: fst_l_def split:prod.splits)
next
  fix s a
  fix b :: "('b1 :: Pord) * ('b2 :: Pordb)"
  assume  Hb : "b \<in> fst_l_S S s"
  thus "b <[ LUpd (fst_l t) s a b"
    using lifting_validDI[OF H]
    by(auto simp add: fst_l_def prod_pleq fst_l_S_def leq_refl split:prod.splits)
next
  fix s a 
  fix b :: "('b1 :: Pord) * ('b2 :: Pordb)"
  show "LUpd (fst_l t) s a b \<in> fst_l_S S s"
    using lifting_validDP[OF H]
    by(auto simp add: fst_l_def prod_pleq leq_refl fst_l_S_def split:prod.splits)
qed

lemma fst_l_valid_vsg :
  assumes Hv : "S' = fst_l_S S"
  assumes H : "lifting_valid t S"
  shows "lifting_valid ((fst_l t) :: ('x, 'a, ('b1 :: Pord) * ('b2 :: Pordb)) lifting) S'"
  using assms fst_l_valid by auto


lemma fst_l_valid_weakb :
  assumes H : "lifting_valid_weakb t S"
  shows "lifting_valid_weakb ((fst_l t) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pordb)) lifting)
                             (fst_l_S S)"
proof(rule lifting_valid_weakbI')
  show "lifting_valid_weak (fst_l t) (fst_l_S S)"
    using fst_l_valid_weak[OF lifting_valid_weakbDV[OF H]]  by auto
next
  fix s
  show "LBase (fst_l t) s = \<bottom>"
    using lifting_valid_weakbDB[OF H]
    by(auto simp add: fst_l_def prod_bot)
qed

lemma fst_l_valid_weakb_vsg :
  assumes Hv : "S' = fst_l_S S"
  assumes H : "lifting_valid_weakb t S"
  shows "lifting_valid_weakb ((fst_l t) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pordb)) lifting)
                             S'"
  using assms fst_l_valid_weakb by auto

lemma fst_l_validb :
  assumes H : "lifting_validb t S"
  shows "lifting_validb ((fst_l t) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pordb)) lifting)
                        (fst_l_S S)"
proof(rule lifting_validbI')
  show "lifting_valid (fst_l t) (fst_l_S S)"
    using fst_l_valid[OF lifting_validbDV[OF H]]  by auto
next
  fix s
  show "LBase (fst_l t) s = \<bottom>"
    using lifting_validbDB[OF H]
    by(auto simp add: fst_l_def prod_bot)
qed

lemma fst_l_validb_vsg :
  assumes Hv : "S' = fst_l_S S"
  assumes H : "lifting_validb t S"
  shows "lifting_validb ((fst_l t) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pordb)) lifting) S'"
  using assms fst_l_validb by auto  


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

definition snd_l_S :: "('x, 'b2 :: Pord) valid_set \<Rightarrow> ('x, ('b1 :: Pord * 'b2)) valid_set" where
"snd_l_S S s =
  { b . case b of (_, b2) \<Rightarrow> (b2 \<in> S s) }"


lemma snd_l_valid_weak :
  assumes H : "lifting_valid_weak v S"
  shows "lifting_valid_weak ((snd_l v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pord)) lifting)
                            (snd_l_S S)"
proof(rule lifting_valid_weakI)
  fix s a
  fix b :: "'b1 * 'b2"
  show "LOut (snd_l v) s (LUpd (snd_l v) s a b) = a"
    using lifting_valid_weakDO[OF H]
    by(auto simp add: snd_l_S_def snd_l_def split:prod.splits)
next
  fix s a
  fix b :: "'b1 * 'b2"
  assume Hb : "b \<in> snd_l_S S s"
  thus "b <[ LUpd (snd_l v) s (LOut (snd_l v) s b) b"
    using lifting_valid_weakDI[OF H]
    by(auto simp add: snd_l_S_def snd_l_def prod_pleq leq_refl split:prod.splits)
next
  fix s a
  fix b :: "'b1 * 'b2"
  show "LUpd (snd_l v) s a b \<in> snd_l_S S s"
    using lifting_valid_weakDP[OF H]
    by(auto simp add: snd_l_S_def snd_l_def prod_pleq leq_refl split:prod.splits)
qed

lemma snd_l_valid_weak_vsg :
  assumes Hv : "S' = snd_l_S S"
  assumes H : "lifting_valid_weak v S"
  shows "lifting_valid_weak ((snd_l v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pord)) lifting)
                            S'"
  using assms snd_l_valid_weak by auto

lemma snd_l_valid :
  assumes H : "lifting_valid v S"
  shows "lifting_valid ((snd_l v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pord)) lifting)
                       (snd_l_S S)"
proof(rule lifting_validI)
  fix s a
  fix b :: "'b1 * 'b2"
  show "LOut (snd_l v) s (LUpd (snd_l v) s a b) = a"
    using lifting_validDO[OF H]
    by(auto simp add: snd_l_def split:prod.splits)
next
  fix s a
  fix b :: "'b1 * 'b2"
  assume Hb : "b \<in> snd_l_S S s"
  thus "b <[ LUpd (snd_l v) s a b"
    using lifting_validDI[OF H]
    by(auto simp add: snd_l_S_def snd_l_def prod_pleq leq_refl split:prod.splits)
next
  fix s a
  fix b :: "'b1 * 'b2"
  show "LUpd (snd_l v) s a b \<in> snd_l_S S s"
    using lifting_validDP[OF H]
    by(auto simp add: snd_l_S_def snd_l_def prod_pleq leq_refl split:prod.splits)
qed

lemma snd_l_valid_vsg :
  assumes Hv : "S' = snd_l_S S"
  assumes H : "lifting_valid v S"
  shows "lifting_valid ((snd_l v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pord)) lifting)
                       S'"
  using assms snd_l_valid by auto

lemma snd_l_valid_weakb :
  assumes H : "lifting_valid_weakb v S"
  shows "lifting_valid_weakb ((snd_l v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pordb)) lifting)
                             (snd_l_S S)"
proof(rule lifting_valid_weakbI')
  show "lifting_valid_weak (snd_l v) (snd_l_S S)"
    using snd_l_valid_weak[OF lifting_valid_weakbDV[OF H]] by auto
next
  fix s
  show "LBase (snd_l v) s = \<bottom>"
    using lifting_valid_weakbDB[OF H]
    by(auto simp add: snd_l_def prod_bot)
qed

lemma snd_l_valid_weakb_vsg :
  assumes Hv : "S' = snd_l_S S"
  assumes H : "lifting_valid_weakb v S"
  shows "lifting_valid_weakb ((snd_l v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pordb)) lifting)
                             S'"
  using assms snd_l_valid_weakb by auto
  

lemma snd_l_validb :
  assumes H : "lifting_validb v S"
  shows "lifting_validb ((snd_l v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pordb)) lifting)
                        (snd_l_S S)"
proof(rule lifting_validbI')
  show "lifting_valid (snd_l v) (snd_l_S S)"
    using snd_l_valid[OF lifting_validbDV[OF H]] by auto
next
  fix s
  show "LBase (snd_l v) s = \<bottom>"
    using lifting_validbDB[OF H]
    by(auto simp add: snd_l_def prod_bot)
qed

lemma snd_l_validb_vsg :
  assumes Hv : "S' = snd_l_S S"
  assumes H : "lifting_validb v S"
  shows "lifting_validb ((snd_l v) :: ('x, 'a, ('b1 :: Pordb) * ('b2 :: Pordb)) lifting)
                        S'"
  using assms snd_l_validb by auto

(*
 * One important fact about products. Fst and snd are orthogonal regardless of what
 * liftings they wrap. This arguably obvious fact is quite useful in enabling
 * separate reasoning about tuple elements.
 *)

lemma fst_snd_ortho :
  assumes H1 : "lifting_validb l1 S1"
  assumes H2 : "lifting_validb l2 S2"
  shows "l_ortho (fst_l (l1 :: ('x, 'a1, 'b1 :: Mergeableb, 'z1) lifting_scheme))
                 (snd_l (l2 :: ('x, 'a2, 'b2 :: Mergeableb, 'z2) lifting_scheme))"
proof(rule l_orthoI)
  fix s a1 a2 b
  show "LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 b) =
        LUpd (snd_l l2) s a2 (LUpd (fst_l l1) s a1 b)"
    by(simp add: fst_l_def snd_l_def split:prod.splits)
next
  fix s
  show "LBase (fst_l l1) s = LBase (snd_l l2) s"
    using lifting_validbDB[OF H1] lifting_validbDB[OF H2]
    by(simp add: fst_l_def snd_l_def)
qed

lemma snd_fst_ortho :
  assumes H1 : "lifting_validb l1 S1"
  assumes H2 : "lifting_validb l2 S2"
  shows 
  "l_ortho (snd_l (l2 :: ('x, 'a1, 'b :: Mergeableb, 'z1) liftingv_scheme))
           (fst_l (l1 :: ('x, 'a2, 'b :: Mergeableb, 'z2) liftingv_scheme))"
  using l_ortho_comm[OF fst_snd_ortho[OF H1 H2]]
  by auto

(* TODO: do we really need Mergeableb constraint on b2? *)
(* if l1 and l2 are ortho, so are "fst l1" and "fst l2" *)
lemma fst_ortho :
  assumes H1 : "lifting_validb l1 S1"
  assumes H2 : "lifting_validb l2 S2"
  assumes Horth : "l_ortho l1 l2"
  shows "l_ortho (fst_l l1 :: ('x, 'a1, ('b1 :: Mergeableb) * 'b2 :: Mergeableb) lifting)
                 (fst_l l2 :: ('x, 'a2, ('b1 :: Mergeableb) * 'b2 :: Mergeableb) lifting)"
proof(rule l_orthoI)
  fix s :: 'x
  fix a1 :: 'a1
  fix a2 :: 'a2
  fix b :: "'b1 * 'b2"
  show "LUpd (fst_l l1) s a1 (LUpd (fst_l l2) s a2 b) =
        LUpd (fst_l l2) s a2 (LUpd (fst_l l1) s a1 b)"
    using l_orthoDI[OF Horth]
    by(auto simp add: fst_l_def split:prod.splits)
next
  fix s
  show "LBase (fst_l l1) s = LBase (fst_l l2) s"
    using l_orthoDB[OF Horth] by(auto simp add: fst_l_def)
qed

lemma snd_ortho :
  assumes H1 : "lifting_validb l1 S1"
  assumes H2 : "lifting_validb l2 S2"
  assumes Horth : "l_ortho l1 l2"
  shows "l_ortho (snd_l l1 :: ('x, 'a1, ('b1 :: Mergeableb) * 'b2 :: Mergeableb) lifting)
                 (snd_l l2 :: ('x, 'a2, ('b1 :: Mergeableb) * 'b2 :: Mergeableb) lifting)"
proof(rule l_orthoI)
  fix s :: 'x
  fix a1 :: 'a1
  fix a2 :: 'a2
  fix b :: "('b1 * 'b2)"
  show "LUpd (snd_l l1) s a1 (LUpd (snd_l l2) s a2 b) =
        LUpd (snd_l l2) s a2 (LUpd (snd_l l1) s a1 b)"
    using l_orthoDI[OF Horth]
    by(auto simp add: snd_l_def split:prod.splits)
next
  fix s
  show "LBase (snd_l l1) s = LBase (snd_l l2) s"
    using l_orthoDB[OF Horth] by(auto simp add: snd_l_def)
qed


(*
 * One of the more interesting definitions in this file. Merge_l describes
 * how we can "merge" two liftings ('a1 \<Rightarrow> 'b) and ('a2 \<Rightarrow> 'b) into one lifting
 * ('a1 * 'a2 \<Rightarrow> 'b"). This can be done when the two liftings are orthogonal, and have
 * equal valid-sets. It relies on the fact that orthogonality implies the existence of
 * some suprema; since those exist, we can then use the fact that bsup will find
 * that supremum.
 *
 * The desire to have this be a lawful lifting (when possible) motivates many of the
 * seeming peculiarities in the definitions in Lifter.thy.
 *)

definition merge_l ::
  "('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b :: Mergeable, 'z2) lifting_scheme \<Rightarrow>
   ('x, 'a1 * 'a2, 'b) lifting" where
"merge_l t1 t2 =
  \<lparr> LUpd =
    (\<lambda> s a b . 
      (case a of (a1, a2) \<Rightarrow>
        LUpd t2 s a2 (LUpd t1 s a1 b)))
  , LOut =
    (\<lambda> s b . (LOut t1 s b, LOut t2 s b))
  , LBase =
    (\<lambda> s . LBase t1 s) \<rparr>"

(* TODO: do valid sets need to be equal? or is some kind of sub/superset possible? *)
lemma merge_l_valid :
  assumes H1 : "lifting_valid (l1 :: ('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme) S1"
  assumes H2 : "lifting_valid (l2 :: ('x, 'a2, 'b :: Mergeable, 'z2) lifting_scheme) S2"
  assumes Hort : "l_ortho l1 l2"
  assumes Heq  : "S1 = S2"
  shows "lifting_valid (merge_l l1 l2) S1"
proof(rule lifting_validI)
  fix s :: 'x
  fix a :: "'a1 * 'a2"
  fix b :: "'b"

  obtain a1 a2 where A : "a = (a1, a2)" by (cases a; auto)

  have C' : "LOut l1 s (LUpd l2 s a2 (LUpd l1 s a1 b)) = a1"
    using lifting_validDO[OF H1] sym[OF l_orthoDI[OF Hort]]
    by(auto)

  then show "LOut (merge_l l1 l2) s (LUpd (merge_l l1 l2) s a b) = a"
    using A lifting_validDO[OF H1] lifting_validDO[OF H2]
    by(auto simp add: merge_l_def )
next
  fix s :: 'x
  fix a :: "'a1 * 'a2"
  fix b :: 'b

  obtain a1 a2 where A : "a = (a1, a2)" by (cases a; auto)

  assume Hb1 : "b \<in> S1 s"
  hence Hb2 : "b \<in> S2 s" using Heq by auto

  have "(LUpd l1 s a1 b) \<in> S1 s"
    using lifting_validDP[OF H1] by auto

  hence In2: "(LUpd l1 s a1 b) \<in> S2 s" unfolding Heq by auto

  hence Leq2 : "LUpd l1 s a1 b <[ LUpd l2 s a2 (LUpd l1 s a1 b)"
    using lifting_validDI[OF H2 In2] by auto

  have Leq1 : "b <[ LUpd l1 s a1 b"
    using lifting_validDI[OF H1 Hb1] by auto

  show "b <[ LUpd (merge_l l1 l2) s a b" 
    using A leq_trans[OF Leq1 Leq2] by (auto simp add: merge_l_def)
next
  fix s :: 'x
  fix a :: "'a1 * 'a2"
  fix b :: 'b

  obtain a1 a2 where A : "a = (a1, a2)" by (cases a; auto)

  have "(LUpd l1 s a1 b) \<in> S1 s"
    using lifting_validDP[OF H1] by auto

  hence "(LUpd l1 s a1 b) \<in> S2 s" unfolding Heq by auto

  hence "LUpd l2 s a2 (LUpd l1 s a1 b) \<in> S2 s"
    using lifting_validDP[OF H2] by auto

  hence "LUpd l2 s a2 (LUpd l1 s a1 b) \<in> S1 s"
    unfolding Heq by auto

  thus "LUpd (merge_l l1 l2) s a b \<in> S1 s" using A
    by(auto simp add: merge_l_def)
qed

lemma merge_l_valid_vsg :
  assumes H1 : "lifting_valid (l1 :: ('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme) S1"
  assumes H2 : "lifting_valid (l2 :: ('x, 'a2, 'b :: Mergeable, 'z2) lifting_scheme) S2"
  assumes Hort : "l_ortho l1 l2"
  assumes Heq1 : "S1 = S3"
  assumes Heq2 : "S2 = S3"
  shows "lifting_valid (merge_l l1 l2) S3"
  using assms merge_l_valid by auto

(* Liftings for variable maps. These require a mapping from syntax to key (used for lookup
 * and update in the variable map).
 * As with the above instances, there is a restriction here in that we must be able
 * to get the key out of _just_ the syntax, without examining the state.
 * In practice this means that we cannot support notions like "dereferencing a pointer"
 * in a single step.
 *)

(*
definition oalist_l ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b) oalist) lifting" where
"oalist_l f t =
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

(* this one sort of works, but we need to change the base implementation *)
(*
definition oalist_l ::
   "('x \<Rightarrow> ('k :: linorder)) \<Rightarrow>
    ('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b) oalist) lifting" where
"oalist_l f t =
  \<lparr> LUpd = (\<lambda> s a l .
            (let k = f s in
              (case get l k of
                  None \<Rightarrow> (update k (LNew t s a) l)
                  | Some v \<Rightarrow> (update k (LUpd t s a v) l))))
  , LOut = (\<lambda> s l . (let k = f s in
                      (case get l k of 
                        Some a \<Rightarrow> LOut t s a
                        | None \<Rightarrow> LOut t s (LBase t s))))
  , LBase = (\<lambda> s . (let k = f s in update k (LBase t s) empty)) \<rparr>"
*)

definition oalist_l ::
   "('x \<Rightarrow> ('k :: linorder)) \<Rightarrow>
    ('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b) oalist) lifting" where
"oalist_l f t =
  \<lparr> LUpd = (\<lambda> s a l .
            (let k = f s in
              (case get l k of
                  None \<Rightarrow> (update k (LNew t s a) l)
                  | Some v \<Rightarrow> (update k (LUpd t s a v) l))))
  , LOut = (\<lambda> s l . (let k = f s in
                      (case get l k of 
                        Some a \<Rightarrow> LOut t s a
                        | None \<Rightarrow> LOut t s (LBase t s))))
  , LBase = (\<lambda> s . (empty)) \<rparr>"


definition oalist_l_S :: 
   "('x \<Rightarrow> ('k :: linorder)) \<Rightarrow>
    ('x, 'b :: Pord) valid_set \<Rightarrow>
    ('x, ('k, 'b) oalist) valid_set"
   where
"oalist_l_S f S s =
  { l . \<exists> a . get l (f s) = Some a \<and> a \<in> S s }"


lemma oalist_l_valid :
  fixes f :: "('x \<Rightarrow> ('k :: linorder))"
  fixes lv :: "('x, 'a, 'b :: Pord) lifting"
  assumes Hv : "lifting_valid lv S"
  shows "lifting_valid (oalist_l f lv) (oalist_l_S f S)"
proof(rule lifting_validI)
  fix s
  fix a
  fix b
  show " LOut (oalist_l f lv) s (LUpd (oalist_l f lv) s a b) = a"
    using lifting_validDO[OF Hv] lifting_validDO'[OF Hv]
    by(auto simp add:oalist_l_def Let_def get_update split:prod.splits option.splits)
next
  fix s :: 'x
  fix a :: 'a
  fix b :: "('k, 'b) oalist"

  assume Hb : "b \<in> oalist_l_S f S s"

  then obtain datum where Get_Datum : "get b (f s) = Some datum" and Datum_In : "datum \<in> S s"
    unfolding oalist_l_S_def by blast

  have Conc' : "b <[ update (f s) (LUpd lv s a datum) b" using Get_Datum Hb Hv
    unfolding pleq_oalist oalist_l_S_def
  proof(transfer)
    fix b :: "('k * 'b) list"
    fix f s datum S lv a
    assume Hb_t : "strict_order (map fst b)"
    assume Hmap : "map_of b (f s) = Some datum"
    assume Hb_in : "b \<in> {x. (\<exists>a. map_of x (f s) = Some a \<and> a \<in> S s) \<and>
                strict_order (map fst x)}"
    assume Hv_t : "lifting_valid lv S"

    have Datum_s : "datum \<in> S s"
      using Hb_in Hmap
      by(auto)

    have Hmap' : "(f s, datum) \<in> set b "
      using map_of_SomeD[OF Hmap] by simp

    have Datum_leq : "datum <[ (LUpd lv s a datum)"
        using lifting_validDI[OF Hv_t Datum_s] by auto

    show "list_leq b (str_ord_update (f s) (LUpd lv s a datum) b)"
      using update_leq2[OF Hb_t Hmap' Datum_leq] by simp
  qed

  show " b <[ LUpd (oalist_l f lv) s a b" using 
        lifting_validDI[OF Hv Datum_In, of a]
        Get_Datum
        get_update
        Conc'
    by(auto simp add:oalist_l_def Let_def split:prod.splits option.splits)
next
  fix s a b
  show "LUpd (oalist_l f lv) s a b \<in> oalist_l_S f S s"
    using lifting_validDP[OF Hv]
    by(auto simp add: oalist_l_def oalist_l_S_def Let_def LNew_def get_update split: option.splits)
qed


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

(* Utilities for interfacing with Gensyn.
 * prod_fan lets us retain the old "large" of type 'b, while also returning the new "large" value.
 *)
definition prod_fan_l ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'c :: Pord) \<Rightarrow>
   ('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('x, 'a, ('c * 'b)) lifting"
  where
"prod_fan_l f t =
  \<lparr> LUpd = (\<lambda> x a cb . (f x a, LUpd t x a (snd cb)))
  , LOut = (\<lambda> x cb . LOut t x (snd cb))
  , LBase = (\<lambda> x . (f x (LOut t x (LBase t x)), LBase t x)) \<rparr>"

(* TODO: seems weird that we would need a lifting_scheme argument here.
   we haven't anywhere else. *)
definition prod_fan_S ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'c :: Pord) \<Rightarrow>
   ('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('x, 'b :: Pord) valid_set \<Rightarrow>
   ('x, ('c * 'b)) valid_set"
  where
"prod_fan_S f t S s =
  { cb . \<exists> c b . cb = (c, b) \<and> b \<in> S s \<and> c = f s (LOut t s b)}"

(* TODO: show validity here *)
(*
lemma prod_fan_l_valid :
  fixes f :: "('x \<Rightarrow> 'a \<Rightarrow> 'c)"
  fixes l :: "('x, 'a, 'b) lifting"
  assumes H :"lifting_valid l"
  shows "lifting_valid (prod_fan_l f l)"
  using H by (auto simp add: lifting_valid_def prod_fan_l_def)
*)

(* "reversing" a lifting is just a synonym for "LOut".
 * This is mnemonically helpful in some cases when constructing complex liftings,
 * but is a bit of a misnomer since its input and output types don't match. *)
definition l_reverse ::
  "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
   'x \<Rightarrow> 'b \<Rightarrow> 'a" where
"l_reverse l =
  LOut l"

(* Lifting instance for a recursive Oalist. Used in Lambda.thy to express variable maps
 * that might contain closures (which in turn contain variable maps, etc.) *)
(* TODO: finish these correctness proofs. *)
definition roalist_l ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
    ('x, 'a, ('k, 'b, 'd :: Pord) roalist) lifting" where
"roalist_l f t =
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

definition roalist_l_S ::
   "('x \<Rightarrow> ('k :: linorder) option) \<Rightarrow>
    ('x, 'b) valid_set \<Rightarrow>
    ('x, ('k, 'b, 'd) roalist) valid_set" where
"roalist_l_S f S s =
  { l . \<exists> k a . f s = Some k \<and> roalist_get_v l k = Some a \<and> a \<in> S s }"

(* TODO: correctness proof for list_hd_l.
 * This is used in Lambda.
 *)
definition list_hd_l ::
  "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> ('x, 'a, 'b list md_triv) lifting" where
"list_hd_l t =
  \<lparr> LUpd = (\<lambda> s a b . 
            (case b of
              mdt (b' # rest) \<Rightarrow> mdt ((LUpd t s a b')#rest)
              | mdt [] \<Rightarrow> mdt [(LNew t s a)]))
  , LOut = (\<lambda> s b . (case b of mdt (b' # rest) \<Rightarrow> LOut t s b'
                      | mdt [] \<Rightarrow> LOut t s (LBase t s)))
  , LBase = (\<lambda> s . mdt [])\<rparr>"


definition list_hd_l_S ::
  "('x, 'b :: Pord) valid_set \<Rightarrow> ('x, 'b list md_triv) valid_set" where
"list_hd_l_S S s =
  { l . \<exists> h t . h \<in> S s \<and> l = mdt (h#t)}"

(* another approach to "list-head" lifting:
   have a "scratch" area that is updated by Upd.
   Then have Post actually push to the list.
   "sc" here is short for "scratch"
*)
(*
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
*)


(* Liftings for mapping over data structures
 * These are useful, e.g., when relating a
 * list of wrapped values to a list of unwrapped values*)

definition list_map_l ::
  "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> ('x, 'a list, 'b list md_triv) lifting" where
"list_map_l t =
  \<lparr> LUpd = (\<lambda> s a b .
            (case b of
              mdt b \<Rightarrow>
                if length a = length b
                then mdt (map2 (LUpd t s) a b)
                else mdt (map (LNew t s) a)))
  , LOut = (\<lambda> s b . 
               (case b of mdt b \<Rightarrow> map (LOut t s) b))
  , LBase = (\<lambda> s . mdt [])\<rparr>"

definition list_map_S ::
  "('x, 'b :: Pord) valid_set \<Rightarrow> ('x, 'b list md_triv) valid_set" where
"list_map_S S s =
  { l . \<exists> l' . l = mdt l' \<and> list_all (\<lambda> x . x \<in> S s) l'}"


(* sum map-lifting *)
definition sum_map_l ::
  "('x, 'a1, 'b1 :: Pord, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b2 :: Pord, 'z2) lifting_scheme \<Rightarrow>
   ('x, 'a1 + 'a2, 'b1 + 'b2) lifting" where
"sum_map_l t1 t2 =
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

definition sum_map_l_S ::
  "('x, 'b1 :: Pord) valid_set \<Rightarrow>
   ('x, 'b2 :: Pord) valid_set \<Rightarrow>
   ('x, 'b1 + 'b2) valid_set" where
"sum_map_l_S S1 S2 s =
  (Inl ` S1 s) \<union> (Inr ` S2 s)"

(* ROAlist map-lifting
   does not use the ability to parameterize mapping based on keys. *)

(* helper used to implement upd *)
(* unsure if this should have a 'x (syntax) parameter, but
   that seems like the most straightforward thing *)
fun roalist_fuse' ::
"('x, 'v1, 'v2 :: Pord, 'z1) lifting_scheme \<Rightarrow>
 ('x, 'd1, 'd2 :: Pord, 'z2) lifting_scheme \<Rightarrow>
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

(* TODO: complete necessary proofs to show this works. *)
lift_definition roalist_fuse :: 
"('x, 'v1, 'v2 :: Pord, 'z1) lifting_scheme \<Rightarrow>
 ('x, 'd1, 'd2 :: Pord, 'z2) lifting_scheme \<Rightarrow>
 'x \<Rightarrow>
 ('k :: linorder, 'v1, 'd1) roalist \<Rightarrow> 
 ('k :: linorder, 'v2, 'd2) roalist \<Rightarrow>
 ('k :: linorder, 'v2, 'd2) roalist" 
is roalist_fuse' sorry

definition roalist_map_l ::
  "('x, 'v1, 'v2 :: Pord, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'd1, 'd2 :: Pord, 'z2) lifting_scheme \<Rightarrow>
   ('x, ('k :: linorder, 'v1, 'd1) roalist, ('k :: linorder, 'v2, 'd2) roalist) lifting"
  where
"roalist_map_l tv td =
  \<lparr> LUpd = (\<lambda> s a b . roalist_fuse tv td s a b)
  , LOut = (\<lambda> s b . roalist_map 
                      (\<lambda> _ v . LOut tv s v)
                      (\<lambda> _ d . LOut td s d)
                      b)
  , LBase = (\<lambda> s . roalist_empty) \<rparr>"
    

(* fill this in later; need an analogue of list_all for roalist. *)

(* possibly needed later: "map" lifting analogue for option, triv, prio *)

(* TODO: may need a lifting for merging an OAlist with an ROAlist
   this might be helpful for better separating control and data for Lambda/SECD
*)

end