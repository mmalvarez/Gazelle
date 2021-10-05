theory Lifter_New 
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

locale l_ortho =
  fixes l1 :: "('a, 'b1, 'c :: Mergeable, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c :: Mergeable, 'f2) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c set"
  fixes S2 :: "'a \<Rightarrow> 'c set"
  (* TODO: this originally was a weaker version that had b1 = b2 instead of
   * b1 and b2 having a sup. *)
(*
  assumes compat : "\<And> s a1 a2 b1 b2 bs.
    is_sup {b1, b2} bs \<Longrightarrow> has_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b2}"
*)
  assumes compat : "\<And> s a1 . has_sup {LUpd l1 s a1 b, LUpd l2 s a2 b}"


  (* TODO: I think these are wrong. - should they look more like compat? *)
  assumes put2_get1 : "\<And> s a1 a2 b supr . 
    is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
    LOut l1 s supr = a1"
  assumes put1_get2 : "\<And> s a1 a2 b supr .
    is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
    LOut l2 s supr = a2"
  assumes put2_S1 : "\<And> s a1 a2 b supr . 
    is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
    supr \<in> S1 s"
  assumes put1_S2 : "\<And> s a1 a2 b supr . 
    is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
    supr \<in> S2 s"

locale l_ortho_base' =
  fixes l1 :: "('a, 'b1, 'c :: Mergeableb, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"

locale l_ortho_base = l_ortho + l_ortho_base' +
  assumes bases_compat : "\<And> s . is_sup {LBase l1 s, LBase l2 s} \<bottom>"

locale l_ortho_ok' =
  fixes l1 :: "('a, 'b1, 'c :: {Mergeable, Okay}, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"

locale l_ortho_ok = l_ortho + l_ortho_ok' +
  assumes ok_compat :
    "\<And> s a1 a2 b supr . b \<in> ok_S \<Longrightarrow>
    is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow> supr \<in> ok_S"
  



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