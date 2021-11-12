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
  (*i think we can't have these set membership premises, but not having them creates problems for fst_snd_ortho *)
  assumes compat : "\<And> s a1 a2 . \<comment> \<open> b \<in> S1 s \<Longrightarrow> b \<in> S2 s \<Longrightarrow> \<close> has_sup {LUpd l1 s a1 b, LUpd l2 s a2 b}"
  (* compat_S premise was sup.
upper bound isn't quite what we want either. nor, i think, do we want the
more general statement that the sup of anything in S1 and anything in S2
are in the intersection... we need to take into account the particulars of the
liftings involved

perhaps a "one-sided" version? that is, one of the two needs to explicitly
be an update, but the other merely needs to be in its valid set
i don't think this really solves anything

i also am not sure i fully understand the role of valid sets at this point.
especially in light of having ok_S
 *)
(*
  assumes compat_S : "\<And> s a1 a2 supr . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
                      supr \<in> (S1 s \<inter> S2 s)"
*)
(*
  assumes compat_S1 : "\<And> s x1 a2 supr . x1 \<in> S1 s \<Longrightarrow> is_sup {x1, LUpd l2 s a2 b} supr \<Longrightarrow>
                      supr \<in> (S1 s \<inter> S2 s)"
  assumes compat_S2 : "\<And> s x2 a1 supr . x2 \<in> S2 s \<Longrightarrow> is_sup {LUpd l1 s a1 b, x2} supr \<Longrightarrow>
                      supr \<in> (S1 s \<inter> S2 s)"
*)
(*
  assumes compat_S : "\<And> s x1 x2 supr . x1 \<in> S1 s \<Longrightarrow> x2 \<in> S2 s \<Longrightarrow>
    is_sup {x1, x2} supr \<Longrightarrow> supr \<in> (S1 s \<inter> S2 s)"
*)
(*
  assumes compat_S : "\<And> s x1 x2 supr . x1 \<in> S1 s  \<Longrightarrow> 
    x2 \<in> S2 s \<Longrightarrow>
    is_sup {x1, x2} supr \<Longrightarrow> supr \<in> (S1 s \<inter> S2 s)"
*)

  assumes compat_S1 : "\<And> s x2 a1 b supr .
    is_sup {LUpd l1 s a1 b, x2} supr \<Longrightarrow> supr \<in> S1 s"

  assumes compat_S2 : "\<And> s x1 a2 b supr .
    is_sup {x1, LUpd l2 s a2 b} supr \<Longrightarrow> supr \<in> S2 s"



(* TODO: need these set membership constraints? originally there were some. *)
  assumes compat_get1 : "\<And> s a1 a2 supr . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
                      LOut l1 s supr = a1"
  assumes compat_get2 : "\<And> s a1 a2 supr . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
                      LOut l2 s supr = a2"
  (*assumes put1_get2 : "\<And> s a b . b \<in> S2 s \<Longrightarrow> LOut l2 s (LUpd l1 s a b) = LOut l2 s b"
  assumes put2_get1 : "\<And> s a b . b \<in> S1 s \<Longrightarrow> LOut l1 s (LUpd l2 s a b) = LOut l1 s b"*)
  assumes put1_S2 : "\<And> s a b . b \<in> S2 s \<Longrightarrow> LUpd l1 s a b \<in> S2 s"
  assumes put2_S1 : "\<And> s a b . b \<in> S1 s \<Longrightarrow> LUpd l2 s a b \<in> S1 s"
(*
assumes compat'1 :
  "\<And> s a1 a2 b . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} (LUpd l1 s a1 (LUpd l2 s a2 b))"
assumes compat'2 :
  "\<And> s a1 a2 b . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} (LUpd l2 s a2 (LUpd l1 s a1 b))"
*)
(* TODO: are these compat'1 compat'2 even necessary anymore? *)
(*
assumes compat'1 :
  "\<And> s a1 a2 supr . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
    \<exists> b' . LUpd l1 s a1 b' = supr"

assumes compat'2 :
  "\<And> s a1 a2 supr . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow>
    \<exists> b' . LUpd l2 s a2 b' = supr"
*)
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
    "\<And> s a1 a2 b supr . b \<in> ok_S \<Longrightarrow> 
    is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr \<Longrightarrow> supr \<in> ok_S"
  

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

  have Comm : "{LUpd l2 s a1 b, LUpd l1 s a2 b} = 
               {LUpd l1 s a2 b, LUpd l2 s a1 b}"
    by auto

  show "has_sup
        {LUpd l2 s a1 b,
         LUpd l1 s a2 b}"
    using compat[of s a2 b a1]
    unfolding Comm
    by auto

(*
next
  fix b s a1 a2 supr

  assume Sup : "is_sup {LUpd l2 s a1 b, LUpd l1 s a2 b} supr"

  have Comm : "{LUpd l2 s a1 b, LUpd l1 s a2 b} = 
               {LUpd l1 s a2 b, LUpd l2 s a1 b}"
    by auto

  show "supr \<in> S2 s \<inter> S1 s"
    using compat_S[OF Sup[unfolded Comm]]
    by auto
*)
next

  fix b s a1 a2 supr

  assume Sup : "is_sup {LUpd l2 s a1 b, LUpd l1 s a2 b} supr"

  have Comm : "{LUpd l2 s a1 b, LUpd l1 s a2 b} = 
               {LUpd l1 s a2 b, LUpd l2 s a1 b}"
    by auto

  show "LOut l2 s supr = a1"
    using compat_get2[OF Sup[unfolded Comm]]
    by auto

next

  fix b s a1 a2 supr

  assume Sup : "is_sup {LUpd l2 s a1 b, LUpd l1 s a2 b} supr"

  have Comm : "{LUpd l2 s a1 b, LUpd l1 s a2 b} = 
               {LUpd l1 s a2 b, LUpd l2 s a1 b}"
    by auto

  show "LOut l1 s supr = a2"
    using compat_get1[OF Sup[unfolded Comm]]
    by auto

next

  fix s a b

  show "b \<in> S1 s \<Longrightarrow>
       LUpd l2 s a b \<in> S1 s"
    using put2_S1[of b s a]
    by auto

next

  fix s a b

  show "b \<in> S2 s \<Longrightarrow>
       LUpd l1 s a b \<in> S2 s"
    using put1_S2[of b s a]
    by auto

next

  fix s
  fix x2 b :: 'c
  fix a1
  fix supr

  assume Supr: "is_sup {LUpd l2 s a1 b, x2} supr"

  have Comm : "{LUpd l2 s a1 b, x2} = {x2, LUpd l2 s a1 b}"
    by auto


  show "supr \<in> S2 s"
    using compat_S2 Supr unfolding Comm
    by auto
next

  fix s
  fix x1 b :: 'c
  fix a2
  fix supr

  assume Supr: "is_sup {x1, LUpd l1 s a2 b} supr"

  have Comm : "{x1, LUpd l1 s a2 b} = {LUpd l1 s a2 b, x1}"
    by auto


  show "supr \<in> S1 s"
    using compat_S1 Supr unfolding Comm
    by auto
qed
(*
next

  fix s a1 a2 b supr

  assume Sup : "is_sup
        {LUpd l2 s a1 b, LUpd l1 s a2 b}
        supr"

  have Comm : "{LUpd l2 s a1 b, LUpd l1 s a2 b} = 
               {LUpd l1 s a2 b, LUpd l2 s a1 b}"
    by auto

  show "\<exists>b'. LUpd l2 s a1 b' = supr" using Sup
    unfolding Comm
    using compat'2[of s a2 b a1, unfolded Comm]
    by auto

next
  fix s a1 a2 b supr

  assume Sup : "is_sup
        {LUpd l2 s a1 b, LUpd l1 s a2 b}
        supr"


  have Comm : "{LUpd l2 s a1 b, LUpd l1 s a2 b} = 
               {LUpd l1 s a2 b, LUpd l2 s a1 b}"
    by auto

  show "\<exists>b'. LUpd l1 s a2 b' = supr" using Sup
    unfolding Comm
    using compat'1[of s a2 b a1, unfolded Comm]
    by auto
qed
*)

sublocale l_ortho_base \<subseteq> comm :
  l_ortho_base l2 S2 l1 S1
proof
  fix s

  have Comm : "{LBase l2 s, LBase l1 s} = {LBase l1 s, LBase l2 s}"
    by auto

  show "is_sup {LBase l2 s, LBase l1 s} \<bottom>"
    using compat_bases unfolding Comm
    by auto
qed

sublocale l_ortho_ok \<subseteq> comm :
  l_ortho_ok l2 S2 l1 S1
proof
  fix s a1 a2 b supr

  assume Sup : "is_sup {LUpd l2 s a1 b, LUpd l1 s a2 b} supr"

  assume Bok : "b \<in> ok_S"

  have Comm : "{LUpd l2 s a1 b, LUpd l1 s a2 b} = 
               {LUpd l1 s a2 b, LUpd l2 s a1 b}"
    by auto

  show "supr \<in> ok_S"
    using compat_ok[OF Bok Sup[unfolded Comm]]
    by auto
qed
(*
lemma (in l_ortho) compat'_comm :
  shows "LUpd l1 s a1 (LUpd l2 s a2 b) = LUpd l2 s a2 (LUpd l1 s a1 b)"
  using is_sup_unique[OF compat'1 compat'2]
  by auto
*)
end