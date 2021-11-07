theory Lifter
  imports  "../Mergeable/Mergeable_Instances" "../Mergeable/Mergeable_Oalist" "../Mergeable/Mergeable_Roalist" "../Mergeable/Mono"
"../Composition/Composition"
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

datatype ('syn, 'a, 'b) lifting =
  LMake  (LUpd : "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)")
         (LOut : "('syn \<Rightarrow> 'b \<Rightarrow> 'a)")
         (LBase : "('syn \<Rightarrow> 'b)")

type_synonym ('syn, 'a, 'b) lifting' =
  "('syn, 'a, 'b) lifting"

(*
definition LUpd ::
  "('syn, 'a, 'b) lifting \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" where
"LUpd l s a b =
  LMap l (\<lambda> _ _ . a ) s b"
*)

definition LMap :: "('syn, 'a, 'b) lifting \<Rightarrow> ('syn \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('syn \<Rightarrow> 'b \<Rightarrow> 'b)"
  where
"LMap l f s b =
  LUpd l s (f s (LOut l s b)) b"

definition LNew :: "('syn, 'a, 'b) lifting \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b"  where
"LNew l s a = LUpd l s a (LBase l s)"

(* TODO: make sure this is a good idea. *)
declare LNew_def [simp]
declare LMap_def [simp]

type_synonym ('syn, 'b) valid_set =
"'syn \<Rightarrow> 'b set"

(* liftings can have several kinds of validity properties, only some of
   which depend on others.
*)

instantiation oalist :: (linorder, Okay) Okay
begin

definition oalist_ok_S :
  "(ok_S :: ('a, 'b) oalist set) = { x  :: ('a, 'b) oalist . oalist_all_val (\<lambda> y . y \<in> ok_S) x }"
instance proof qed
end

locale lifting_putonly =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak) lifting"
  fixes S :: "('syn, 'b) valid_set"
  assumes put_S : "\<And> s a b . LUpd l s a b \<in> S s"

locale lifting_presonly =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak) lifting"
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

locale lifting_pairwise = 
  fixes S :: "('syn, 'b :: Pordpsc) valid_set"
  assumes pairwise_S :
    "\<And> x1 x2 x3 s s12 s23 s13 s123 .
      x1 \<in> S s \<Longrightarrow>
      x2 \<in> S s \<Longrightarrow>
      x3 \<in> S s \<Longrightarrow>
      is_sup {x1, x2} s12 \<Longrightarrow>
      s12 \<in> S s \<Longrightarrow>
      is_sup {x2, x3} s23 \<Longrightarrow>
      s23 \<in> S s \<Longrightarrow>
      is_sup {x1, x3} s13 \<Longrightarrow>
      s13 \<in> S s \<Longrightarrow>
      is_sup {x1, x2, x3} s123 \<Longrightarrow>
      s123 \<in> S s"
(*
lemma (in lifting_pairwise) pairwise_finite_S :
  fixes Vs :: "'b set"
  fixes s :: 'syn
  fixes supr_vs :: "'b"
  assumes Fin : "finite Vs"
  assumes Nemp : "v \<in> Vs"
  assumes Sub : "Vs \<subseteq> S s"
  assumes Pairwise : "\<And> x1 x2 supr . x1 \<in> Vs \<Longrightarrow> x2 \<in> Vs \<Longrightarrow> is_sup {x1, x2} supr \<Longrightarrow> supr \<in> S s"
  assumes Sup : "is_sup Vs supr_vs"
  shows "supr_vs \<in> S s"
proof-

  obtain l where L: "set l = Vs"
    using finite_list[OF Fin]
    by auto

  have Sub' : "set l \<subseteq> S s" using Sub L by auto

  have Pairwise' : "\<And> x1 x2 supr . x1 \<in> set l \<Longrightarrow> x2 \<in> set l \<Longrightarrow> is_sup {x1, x2} supr \<Longrightarrow> supr \<in> S s"
    using Pairwise L
    by auto

  have Sup' : "is_sup (set l) supr_vs"
    using Sup L by auto

  have Nemp' : "v \<in> set l"
    using Nemp L by auto

  show "supr_vs \<in> S s"
    using Sub' Pairwise' Sup' Nemp'
  proof(induction l arbitrary: v supr_vs)
    case Nil
    then show ?case by auto
  next
    case (Cons lh lt)

    show ?case
    proof(cases lt)
      case Nil' : Nil

      have S1 :"is_sup {lh} lh"
        using sup_singleton by auto

      have S2:"is_sup {lh} supr_vs"
        using Cons.prems Nil' by auto

      have "lh = supr_vs"
        using is_sup_unique[OF S1 S2] by auto

      then show ?thesis using Cons.prems
        by auto
    next
      case Cons' : (Cons lh' lt' )

      have Lt_sub : "set lt \<subseteq> S s"
        using Cons.prems
        by auto
  
      have Pairwise : "(\<And>x1 x2 supr. x1 \<in> set (lt) \<Longrightarrow> x2 \<in> set (lt) \<Longrightarrow> is_sup {x1, x2} supr \<Longrightarrow> supr \<in> S s)"
      proof-
        fix x1 x2 supr :: 'b
        assume X1 : "x1 \<in> set (lt)"
        assume X2 : "x2 \<in> set (lt)"
        assume Sup : "is_sup {x1, x2} supr"
        show "supr \<in> S s"
          using Cons.prems(2)[OF _ _ Sup] X1 X2
          by(auto)
      qed

      have Lt : "lh' \<in> set lt"
        using Cons' by auto

      have "has_sup (set lt)"
        using has_sup_subset[OF _ Cons.prems(3), of "set lt" lh'] using Cons'
        by(auto simp add: has_sup_def)

      then obtain supr_vs' where Supr_vs' : "is_sup (set lt) supr_vs'"
        by(auto simp add: has_sup_def)

      have "supr_vs' \<in> S s"
        using Cons.IH[OF Lt_sub Pairwise Supr_vs' Lt]
        by(auto)

      then show ?thesis using Cons.prems
    qed
  *)

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
  fixes l1 :: "('a, 'b1, 'c :: Pord) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c set"
  fixes l2 :: "('a, 'b2, 'c :: Pord) lifting"
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
  fixes l1 :: "('a, 'b1, 'c :: Pord_Weakb) lifting"
  fixes l2 :: "('a, 'b2, 'c) lifting"


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
  fixes l1 :: "('a, 'b1, 'c :: {Pord_Weakb, Okay}) lifting"
  fixes l2 :: "('a, 'b2, 'c) lifting"

(* l_ortho_ok? i think we actually don't need any further properties!
*)

locale l_ortho_ok = l_ortho + l_ortho_ok'

(* lift_map_s is LMap plus a syntax translation *)
definition lift_map_s ::
  "('b1 \<Rightarrow> 'a1) \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
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