theory Lifter
 imports  "../Mergeable/Mergeable_Instances" "../Mergeable/Mergeable_Oalist" "../Mergeable/Mergeable_Roalist" "../Mergeable/Mono"
begin

(* When we lift syntaxes we reverse the function arrow *)
type_synonym ('a, 'b) syn_lifting = "('b \<Rightarrow> 'a)"

(*
datatype ('syn, 'a, 'b) lifting =
  LMake  (LUpd : "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)")
         (LOut : "('syn \<Rightarrow> 'b \<Rightarrow> 'a)")
         (LBase : "('syn \<Rightarrow> 'b)")
*)

(*
"mappable" typeclass?
*)

(* need a generic way to talk about things over which LMap makes sense.

*)

datatype ('syn, 'a, 'b, 'f) lifting =
  LMake  (LUpd : "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)")
         (LOut : "('syn \<Rightarrow> 'b \<Rightarrow> 'a)")
         (LBase : "('syn \<Rightarrow> 'b)")
         (LFD : "'f \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'a")

type_synonym ('syn, 'a, 'b) lifting' =
  "('syn, 'a, 'b, 'syn \<Rightarrow> 'a \<Rightarrow> 'a) lifting"

(*
definition LUpd ::
  "('syn, 'a, 'b) lifting \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
"LUpd l s a b =
  LMap l (\<lambda> _ _ . a ) s b"
*)


definition LMap ::
  "('x, 'a, 'b, 'f) lifting \<Rightarrow> 'f \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"LMap l f s b =
  LUpd l s (LFD l f s (LOut l s b)) b"


definition LNew :: "('syn, 'a, 'b, 'f) lifting \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b"  where
"LNew l s a = LUpd l s a (LBase l s)"

(* TODO: make sure this is a good idea. *)
declare LNew_def [simp]
declare LMap_def [simp]

type_synonym ('syn, 'b) valid_set =
"'syn \<Rightarrow> 'b set"

(* liftings can have several kinds of validity properties, only some of
   which depend on others.
*)

(* TODO: for inference purposes we are probably going to
 * still have to use something like our current formulation. *)

class Okay =
  fixes ok_S :: "('a) set"


instantiation md_triv :: (_) Okay
begin
definition triv_ok_S : "(ok_S :: 'a md_triv set) = UNIV"
instance proof
qed
end

instantiation md_prio :: (Okay) Okay
begin
definition prio_ok_S : "(ok_S :: 'a md_prio set) = ({x . \<exists> px vx . x = mdp vx px \<and> px \<in> ok_S})"
instance proof qed
end

instantiation option :: (Okay) Okay
begin
definition option_ok_S : "(ok_S :: 'a option set) = (Some ` ok_S)"
instance proof qed
end

instantiation prod :: (Okay, Okay) Okay
begin
definition prod_ok_S : "(ok_S :: ('a * 'b) set) = { x :: 'a * 'b . \<exists> a' b' . x = (a', b') \<and> a' \<in> ok_S \<and> b' \<in> ok_S}"
instance proof qed
end

instantiation oalist :: (linorder, Okay) Okay
begin

definition oalist_ok_S :
  "(ok_S :: ('a, 'b) oalist set) = { x  :: ('a, 'b) oalist . oalist_all_val (\<lambda> y . y \<in> ok_S) x }"
instance proof qed
end

instantiation unit :: Okay
begin
definition unit_ok_S :
  "(ok_S :: unit set) = UNIV"
instance proof qed
end

(* weak + (strong?) + (base?) + (ok?) + (pres?) *)
(* TODO: support for vsg style reasoning *)
locale lifting_valid_weak =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak, 'f) lifting"
  fixes S :: "('syn, 'b) valid_set"
  assumes put_get : "\<And> a . LOut l s (LUpd l s a b) = a"
  assumes get_put_weak : "\<And> s b . b \<in> S s \<Longrightarrow> b <[ LUpd l s (LOut l s b) b"
  assumes put_S : "\<And> s a b . LUpd l s a b \<in> S s"

locale lifting_valid = lifting_valid_weak +
  assumes get_put : "\<And> s a b . b \<in> S s \<Longrightarrow> b <[ LUpd l s a b"

locale lifting_valid_weak_base = lifting_valid_weak +
  assumes base : "\<And> s . LBase l s = \<bottom>"

locale lifting_valid_base = lifting_valid + lifting_valid_weak_base

locale lifting_valid_weak_ok = lifting_valid_weak +
  assumes ok_S_valid : "\<And> s . ok_S \<subseteq> S s"
  assumes ok_S_put : "\<And> s a b . b \<in> ok_S \<Longrightarrow> LUpd l s a b \<in> ok_S"

locale lifting_valid_ok = lifting_valid + lifting_valid_weak_ok

locale lifting_valid_weak_base_ok = lifting_valid_weak_ok + lifting_valid_weak_base

locale lifting_valid_base_ok = lifting_valid_ok + lifting_valid_base

locale lifting_valid_weak_pres = lifting_valid_weak +
  assumes pres :
    "\<And> v V supr f s . 
         v \<in> V \<Longrightarrow>
         V \<subseteq> S s \<Longrightarrow>
         is_sup V supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup (LMap l f s ` V) (LMap l f s supr)"

locale lifting_valid_pres = lifting_valid + lifting_valid_weak_pres

locale lifting_valid_weak_base_pres = lifting_valid_weak_pres + lifting_valid_weak_base +
  assumes bot_bad : "\<And> s . \<bottom> \<notin> S s"

locale lifting_valid_base_pres = lifting_valid_pres + lifting_valid_weak_base_pres

locale lifting_valid_weak_ok_pres = lifting_valid_weak_pres + lifting_valid_weak_ok

locale lifting_valid_ok_pres = lifting_valid_pres + lifting_valid_ok

locale lifting_valid_weak_base_ok_pres =
  lifting_valid_weak_base_pres + lifting_valid_weak_base_ok

(* generally we are assuming we won't be using ok and pres separately.
 * we could if we wanted to though. *)
locale lifting_valid_base_ok_pres =
  lifting_valid_base_pres + lifting_valid_base_ok

(* orthogonality, used to define merge correctness *)

locale l_ortho' =
  fixes l1 :: "('a, 'b1, 'c :: Pord_Weak, 'f1) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c set"
  fixes l2 :: "('a, 'b2, 'c :: Pord_Weak, 'f2) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c set"

locale l_ortho =
  l_ortho' +
(*
if we need these validity assumptions we can add them back.
+
  in1 : lifting_valid_weak l1 S1 +
  in2 : lifting_valid_weak l2 S2 +
*)
(* TODO: do we need membership hypothesis (s1 \<union> s2)?
seems like we need:
if we start in S1, then updating using l2 is still in S1
and vice versa. might need something stronger but let's see where
that gets us.
 *)
(* do we need put1_get2/put2_get1? *)

  assumes eq_base : "\<And> s . LBase l1 s = LBase l2 s"
  assumes compat : "\<And> s a1 a2 . has_sup {LUpd l1 s a1 b, LUpd l2 s a2 b}"
  (* compat_S could also be generalized a bit. *)
  assumes compat_S : "\<And> s a1 a2 supr . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
                      supr \<in> (S1 s \<inter> S2 s)"
(* TODO: need these set membership constraints? *)
  assumes compat_get1 : "\<And> s a1 a2 supr . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
                      LOut l1 s supr = a1"
  assumes compat_get2 : "\<And> s a1 a2 supr . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
                      LOut l2 s supr = a2"
  (*assumes put1_get2 : "\<And> s a b . b \<in> S2 s \<Longrightarrow> LOut l2 s (LUpd l1 s a b) = LOut l2 s b"
  assumes put2_get1 : "\<And> s a b . b \<in> S1 s \<Longrightarrow> LOut l1 s (LUpd l2 s a b) = LOut l1 s b"*)
  assumes put1_S2 : "\<And> s a b . b \<in> S2 s \<Longrightarrow> LUpd l1 s a b \<in> S2 s"
  assumes put2_S1 : "\<And> s a b . b \<in> S1 s \<Longrightarrow> LUpd l2 s a b \<in> S1 s"

locale l_ortho_base' =
  fixes l1 :: "('a, 'b1, 'c :: Pord_Weakb, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"

locale l_ortho_base = l_ortho + l_ortho_base' +
  assumes compat_bases : "\<And> s . is_sup {LBase l1 s, LBase l2 s} \<bottom>"

locale l_ortho_ok' =
  fixes l1 :: "('a, 'b1, 'c :: {Pord_Weakb, Okay}, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"

locale l_ortho_ok = l_ortho + l_ortho_ok' +
  assumes compat_ok :
    "\<And> s a1 a2 b supr . \<comment> \<open> b \<in> ok_S \<Longrightarrow> \<close>
    is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow> supr \<in> ok_S"
  

(* lift_map_s is LMap plus a syntax translation *)
definition lift_map_s ::
  "('b1 \<Rightarrow> 'a1) \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'f) lifting \<Rightarrow>
   'f \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"lift_map_s l' l sem syn st =
  LMap l sem (l' syn) st"


(* TODO: can we define some other notion of orthogonality that will be useful
 * for "squishing together" multiple liftings into one when merging semantics?
 *)

(*
locale l_ortho =
  fixes l1 :: "('a, 'b1, 'c :: Mergeable) lifting"
  fixes l2 :: "('a, 'b2, 'c) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c set"
  fixes S2 :: "'a \<Rightarrow> 'c set"
  assumes pres2 :
    "\<And> v V supr f1 f2 s . 
         v \<in> V \<Longrightarrow>
         V \<subseteq> S1 s \<Longrightarrow>
         V \<subseteq> S2 s \<Longrightarrow>
         is_sup V supr \<Longrightarrow>
         supr \<in> S1 s \<Longrightarrow>
         supr \<in> S2 s \<Longrightarrow>
         \<exists> result . is_sup ({LMap l1 f1 s supr, LMap l2 f2 s supr}) result \<and>
                    is_sup (LMap l1 f1 s ` V \<union> LMap l2 f2 s ` V) (result)"
*)
end