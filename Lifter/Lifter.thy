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

locale lifting_putonly =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak, 'f) lifting"
  fixes S :: "('syn, 'b) valid_set"
  assumes put_S : "\<And> s a b . LUpd l s a b \<in> S s"

locale lifting_presonly =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak, 'f) lifting"
  fixes S :: "('syn, 'b) valid_set"
  assumes pres :
    "\<And> v V supr f s . 
         v \<in> V \<Longrightarrow>
         V \<subseteq> S s \<Longrightarrow>
         is_sup V supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup (LMap l f s ` V) (LMap l f s supr)"
    

(* reduced version of lifting-valid, for use with
 * improper merges (when using merge_l as a tool for combining
 * semantics) *)
locale lifting_valid_presonly =
  lifting_putonly + lifting_presonly

(* weak + (strong?) + (base?) + (ok?) + (pres?) *)
(* TODO: support for vsg style reasoning *)
locale lifting_valid_weak =
  lifting_putonly +
  assumes put_get : "\<And> a . LOut l s (LUpd l s a b) = a"
  assumes get_put_weak : "\<And> s b . b \<in> S s \<Longrightarrow> b <[ LUpd l s (LOut l s b) b"

(* NB: making a huge change w/r/t lifting strength def here (getting rid of \<in> S s assumption) *)
locale lifting_valid = lifting_valid_weak +
  assumes get_put : "\<And> s a b . b <[ LUpd l s a b"

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
  lifting_presonly

(* valid set being closed under <[ *)
locale lifting_valid_weak_clos = lifting_valid_weak +
  assumes clos_S : "\<And> a b s . a <[ b \<Longrightarrow> a \<in> S s \<Longrightarrow> b \<in> S s"

(*
sublocale lifting_valid_weak_pres \<subseteq> lifting_valid_presonly
proof
  show "\<And>s a b. LUpd l s a b \<in> S s"
    using put_S by auto
next
  show "\<And>v V supr f s.
       v \<in> V \<Longrightarrow>
       V \<subseteq> S s \<Longrightarrow>
       is_sup V supr \<Longrightarrow>
       supr \<in> S s \<Longrightarrow>
       is_sup (LMap l f s ` V)
        (LMap l f s supr)"
    using pres 
    by auto
qed
*)

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
(*
these were originally pord_weak, but this was
(i think) insufficient to prove fst_l_ortho;
the strengthening to pord shouldn't be an issue though.
*)
locale l_ortho' =
  fixes l1 :: "('a, 'b1, 'c :: Pord, 'f1) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c set"
  fixes l2 :: "('a, 'b2, 'c :: Pord, 'f2) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c set"

locale l_ortho =
  l_ortho' +

assumes eq_base : "\<And> s . LBase l1 s = LBase l2 s"
  assumes compat : "\<And> s a1 a2 . LUpd l1 s a1 (LUpd l2 s a2 b) = LUpd l2 s a2 (LUpd l1 s a1 b)"
  assumes put1_get2 : "\<And> s a1 . LOut l2 s (LUpd l1 s a1 b) = LOut l2 s b"
  assumes put2_get1 : "\<And> s a2 . LOut l1 s (LUpd l2 s a2 b) = LOut l1 s b"
  assumes put1_S2 : "\<And> s a1 . b \<in> S2 s \<Longrightarrow> LUpd l1 s a1 b \<in> S2 s"
  assumes put2_S1 : "\<And> s a2 . b \<in> S1 s \<Longrightarrow> LUpd l2 s a2 b \<in> S1 s"

locale l_ortho_base' =
  fixes l1 :: "('a, 'b1, 'c :: Pord_Weakb, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"


(* TODO: l_ortho_pres - but we may not need it. *)
locale l_ortho_pres = l_ortho +
  assumes compat_pres1 : "\<And> s f1 f2 s1 s2 v V . 
    v \<in> V \<Longrightarrow>
         V \<subseteq> S1 s \<Longrightarrow>
         V \<subseteq> S2 s \<Longrightarrow>
    is_sup (LMap l1 f1 s ` V) s1 \<Longrightarrow>
    s1 \<in> S1 s \<inter> S2 s \<Longrightarrow>
    is_sup (LMap l2 f2 s ` V) s2 \<Longrightarrow>
    s2 \<in> S1 s \<inter> S2 s \<Longrightarrow>
    is_sup (LMap l1 f1 s ` (LMap l2 f2 s ` V)) (LMap l1 f1 s s2)"
  assumes compat_pres2 : "\<And> s f1 f2 s1 s2 v V . 
    v \<in> V \<Longrightarrow>
         V \<subseteq> S1 s \<Longrightarrow>
         V \<subseteq> S2 s \<Longrightarrow>
    is_sup (LMap l1 f1 s ` V) s1 \<Longrightarrow>
    s1 \<in> S1 s \<inter> S2 s \<Longrightarrow>
    is_sup (LMap l2 f2 s ` V) s2 \<Longrightarrow>
    s2 \<in> S1 s \<inter> S2 s \<Longrightarrow>
    is_sup (LMap l2 f2 s ` (LMap l1 f1 s ` V)) (LMap l2 f2 s s1)"
  (* TODO: this third one may be all that's needed. *)
  assumes compat_pres_sup :
  "\<And> a1 a2 s x . is_sup {LUpd l1 s a1 x, LUpd l2 s a2 x} (LUpd l1 s a1 (LUpd l2 s a2 x))"
(*
  assumes compat_pres2 : 
    "    v \<in> V \<Longrightarrow>
         V \<subseteq> S1 s \<Longrightarrow>
         V \<subseteq> S2 s \<Longrightarrow>
    is_sup (LMap l1 f1 s ` V) s1 \<Longrightarrow>
    is_sup (LMap l2 f2 s ` V) s2 \<Longrightarrow>
    is_sup (LMap l2 f2 s ` (LMap l1 f1 s ` V)) (LMap l2 f2 s s1)"
*)

locale l_ortho_base = l_ortho + l_ortho_base' +
  assumes compat_base1 : "\<And> s . LBase l1 s = \<bottom>"
  assumes compat_base2 : "\<And> s . LBase l2 s = \<bottom>"

locale l_ortho_ok' =
  fixes l1 :: "('a, 'b1, 'c :: {Pord_Weakb, Okay}, 'f1) lifting"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"

(* l_ortho_ok? i think we actually don't need any further properties!
*)

locale l_ortho_ok = l_ortho + l_ortho_ok'

(* lift_map_s is LMap plus a syntax translation *)
definition lift_map_s ::
  "('b1 \<Rightarrow> 'a1) \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'f) lifting \<Rightarrow>
   'f \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"lift_map_s l' l sem syn st =
  LMap l sem (l' syn) st"


(* commutativity of l_ortho *)
sublocale l_ortho \<subseteq> comm :
  l_ortho l2 S2 l1 S1
proof

  fix s
  show "LBase l2 s = LBase l1 s"
    using eq_base by auto
next

  fix b s a1 a2

  show "LUpd l2 s a1 (LUpd l1 s a2 b) = LUpd l1 s a2 (LUpd l2 s a1 b)"
    using compat 
    by auto

next

  fix b s a1
  show "LOut l1 s (LUpd l2 s a1 b) = LOut l1 s b"
    using put2_get1
    by auto
next

  fix b s a2
  show "LOut l2 s (LUpd l1 s a2 b) = LOut l2 s b"
    using put1_get2
    by auto

next

  fix b s a1
  assume "b \<in> S1 s"

  then show "LUpd l2 s a1 b \<in> S1 s"
    using put2_S1 by auto
next

  fix b s a2
  assume "b \<in> S2 s"

  then show "LUpd l1 s a2 b \<in> S2 s"
    using put1_S2 by auto
qed

sublocale l_ortho_base \<subseteq> comm :
  l_ortho l2 S2 l1 S1
proof qed

sublocale l_ortho_pres \<subseteq> comm :
  l_ortho_pres l2 S2 l1 S1
proof
  fix s f1 f2 
  fix s1 s2 v :: 'c
  fix V :: "'c set"

  assume Vin : "v \<in> V"
  assume Vsub2 : "V \<subseteq> S2 s"
  assume Vsub1 : "V \<subseteq> S1 s"
  assume Sup1 : "is_sup (LMap l2 f1 s ` V) s1"
  assume Sup1_in : "s1 \<in> S2 s \<inter> S1 s"
  assume Sup2 : "is_sup (LMap l1 f2 s ` V) s2"
  assume Sup2_in : "s2 \<in> S2 s \<inter> S1 s"

  have Sup1_in' : "s1 \<in> S1 s \<inter> S2 s"
    using Sup1_in by auto

  have Sup2_in' : "s2 \<in> S1 s \<inter> S2 s"
    using Sup2_in by auto

  show "is_sup (LMap l2 f1 s ` LMap l1 f2 s ` V) (LMap l2 f1 s s2)"
    using compat_pres2[OF Vin Vsub1 Vsub2 Sup2 Sup2_in' Sup1 Sup1_in']
    by auto
next
  fix s f1 f2 
  fix s1 s2 v :: 'c
  fix V :: "'c set"

  assume Vin : "v \<in> V"
  assume Vsub2 : "V \<subseteq> S2 s"
  assume Vsub1 : "V \<subseteq> S1 s"
  assume Sup1 : "is_sup (LMap l2 f1 s ` V) s1"
  assume Sup1_in : "s1 \<in> S2 s \<inter> S1 s"
  assume Sup2 : "is_sup (LMap l1 f2 s ` V) s2"
  assume Sup2_in : "s2 \<in> S2 s \<inter> S1 s"

  have Sup1_in' : "s1 \<in> S1 s \<inter> S2 s"
    using Sup1_in by auto

  have Sup2_in' : "s2 \<in> S1 s \<inter> S2 s"
    using Sup2_in by auto

  show "is_sup (LMap l1 f2 s ` LMap l2 f1 s ` V) (LMap l1 f2 s s1)"
    using compat_pres1[OF Vin Vsub1 Vsub2 Sup2 Sup2_in' Sup1 Sup1_in']
    by auto
next
  fix a1 a2 s x

  have Comm1 : "{LUpd l2 s a1 x, LUpd l1 s a2 x} = {LUpd l1 s a2 x, LUpd l2 s a1 x}"
    by auto

  have Conc' : "is_sup {LUpd l1 s a2 x, LUpd l2 s a1 x} (LUpd l1 s a2 (LUpd l2 s a1 x))"
    using compat_pres_sup
    by auto

  then show "is_sup {LUpd l2 s a1 x, LUpd l1 s a2 x} (LUpd l2 s a1 (LUpd l1 s a2 x))"
    unfolding Comm1
    using compat
    by auto
qed
end