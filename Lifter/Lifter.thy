theory Lifter
  imports  "../Mergeable/Mergeable_Instances" "../Mergeable/Mergeable_Oalist" "../Mergeable/Mergeable_Roalist" "../Mergeable/Mono"
"../Composition/Composition_Weak"
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

locale lifting_sig =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak) lifting"
  fixes S :: "('syn, 'b) valid_set"

locale lifting_putonly = lifting_sig +
  assumes put_S : "\<And> s a b . LUpd l s a b \<in> S s"

(* TODO: we are basically phasing this out. *)
locale lifting_presonly = lifting_sig +
  assumes pres :
    "\<And> v V supr f s . 
         v \<in> V \<Longrightarrow>
         V \<subseteq> S s \<Longrightarrow>
         is_sup V supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup (LMap l f s ` V) (LMap l f s supr)"

locale lifting_valid_presonly =
  lifting_putonly + lifting_presonly

(* weak + (strong?) + (base?) + (ok?) + (pres?) + (pairwise?) *)
(* TODO: support for vsg style reasoning *)
locale lifting_valid_weak =
  lifting_putonly +
  assumes put_get : "\<And> a . LOut l s (LUpd l s a b) = a"
  assumes get_put_weak : "\<And> s b . b \<in> S s \<Longrightarrow> b <[ LUpd l s (LOut l s b) b"

locale lifting_valid_ext = lifting_sig +
  assumes get_put : "\<And> s a b . b <[ LUpd l s a b"

locale lifting_valid = lifting_valid_weak + lifting_valid_ext

locale lifting_valid_base_ext = lifting_sig +
  assumes base : "\<And> s . LBase l s = \<bottom>"

locale lifting_valid_weak_base = lifting_valid_weak + lifting_valid_base_ext

locale lifting_valid_base = lifting_valid + lifting_valid_base_ext

locale lifting_valid_ok_ext = 
  lifting_sig +
  assumes ok_S_valid : "\<And> s . ok_S \<subseteq> S s"
  assumes ok_S_put : "\<And> s a b . b \<in> ok_S \<Longrightarrow> LUpd l s a b \<in> ok_S"

locale lifting_valid_weak_ok = lifting_valid_weak + lifting_valid_ok_ext

locale lifting_valid_ok = lifting_valid + lifting_valid_ok_ext

locale lifting_valid_weak_base_ok = 
  lifting_valid_weak + lifting_valid_base_ext + lifting_valid_ok_ext

locale lifting_valid_base_ok = 
  lifting_valid + lifting_valid_base_ext + lifting_valid_ok_ext 

locale lifting_valid_pres_ext = lifting_presonly

locale lifting_valid_weak_pres = lifting_valid_weak +
  lifting_valid_pres_ext


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
  qed
*)

(*
(* valid set being closed under <[ *)
locale lifting_valid_weak_clos = lifting_valid_weak +
  assumes clos_S : "\<And> a b s . a <[ b \<Longrightarrow> a \<in> S s \<Longrightarrow> b \<in> S s"
*)

locale lifting_valid_pres = lifting_valid + lifting_valid_pres_ext

locale lifting_valid_base_pres_ext = lifting_valid_pres_ext +
  assumes bot_bad : "\<And> s . \<bottom> \<notin> S s"

locale lifting_valid_weak_base_pres = 
  lifting_valid_weak + lifting_valid_base_ext + lifting_valid_base_pres_ext 

locale lifting_valid_base_pres = 
  lifting_valid + lifting_valid_base_ext + lifting_valid_base_pres_ext

locale lifting_valid_weak_ok_pres = 
  lifting_valid_weak + lifting_valid_ok_ext + lifting_valid_pres_ext

locale lifting_valid_ok_pres = 
  lifting_valid + lifting_valid_ok_ext + lifting_valid_pres_ext

locale lifting_valid_weak_base_ok_pres =
  lifting_valid_weak + lifting_valid_base_ext + lifting_valid_ok_ext + lifting_valid_base_pres_ext

(* generally we are assuming we won't be using ok and pres separately.
 * we could if we wanted to though. *)
locale lifting_valid_base_ok_pres =
  lifting_valid + lifting_valid_base_ext + lifting_valid_ok_ext + lifting_valid_base_pres_ext

locale lifting_valid_pairwise_ext = 
  fixes S :: "('syn, 'b :: {Pordc, Pordps}) valid_set"
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


(* pairwise doesn't interact with the other components - we keep
 * it separated (otherwise the number of instances we'd have to
 * juggle here would get rather large
 * TODO: if this becomes a problem, we can probably use Velocity to
 * generate the instances.
 *)
locale lifting_valid_weak_pairwise = lifting_valid_weak + lifting_valid_pairwise_ext
locale lifting_valid_pairwise = lifting_valid + lifting_valid_pairwise_ext
locale lifting_valid_weak_base_pairwise = lifting_valid_weak_base + lifting_valid_pairwise_ext
locale lifting_valid_base_pairwise = lifting_valid_base + lifting_valid_pairwise_ext
locale lifting_valid_weak_ok_pairwise = lifting_valid_weak_ok + lifting_valid_pairwise_ext
locale lifting_valid_ok_pairwise = lifting_valid_ok + lifting_valid_pairwise_ext
locale lifting_valid_weak_base_ok_pairwise = lifting_valid_weak_base_ok + lifting_valid_pairwise_ext
locale lifting_valid_base_ok_pairwise = lifting_valid_base_ok + lifting_valid_pairwise_ext
locale lifting_valid_weak_pres_pairwise = lifting_valid_weak_pres + lifting_valid_pairwise_ext
locale lifting_valid_pres_pairwise = lifting_valid_pres +  lifting_valid_pairwise_ext
locale lifting_valid_weak_base_pres_pairwise = lifting_valid_weak_base_pres + lifting_valid_pairwise_ext
locale lifting_valid_base_pres_pairwise = lifting_valid_base_pres + lifting_valid_pairwise_ext
locale lifting_valid_weak_ok_pres_pairwise = lifting_valid_weak_ok_pres + lifting_valid_pairwise_ext
locale lifting_valid_ok_pres_pairwise = lifting_valid_ok_pres + lifting_valid_pairwise_ext
locale lifting_valid_weak_base_ok_pres_pairwise = lifting_valid_weak_base_ok_pres + lifting_valid_pairwise_ext
locale lifting_valid_base_ok_pres_pairwise = lifting_valid_base_ok_pres + lifting_valid_pairwise_ext


(* orthogonality, used to define merge correctness *)
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



(* do we need both components of V to be subset of both sets? *)
locale l_ortho_pres' = 
  fixes l1 :: "('a, 'b1, 'c :: Pordb) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c set"
  fixes l2 :: "('a, 'b2, 'c :: Pordb) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c set"
(*
  assumes compat_pres_pair :
    "\<And> supr s v (V :: 'c set). 
     \<And> f :: ('a \<Rightarrow> 'b1 * 'b2 \<Rightarrow> 'b1 * 'b2) .
      v \<in> V \<Longrightarrow>
      V \<subseteq> S1 s \<Longrightarrow>
      V \<subseteq> S2 s \<Longrightarrow>
      is_sup V supr \<Longrightarrow>
      supr \<in> S1 s \<inter> S2 s \<Longrightarrow>
      is_sup ((\<lambda> x . case (f s (LOut l1 s x, LOut l2 s x)) of
                     (r1, r2) \<Rightarrow> LUpd l1 s r1 (LUpd l2 s r2 x)) ` V) 
              (case (f s (LOut l1 s supr, LOut l2 s supr)) of (r1, r2) \<Rightarrow> LUpd l1 s r1 (LUpd l2 s r2 supr))"
*)

locale l_ortho_pres_ext = l_ortho_pres' + 
  assumes compat_pres_sup :
  "\<And> a1 a2 s x . is_sup {LUpd l1 s a1 x, LUpd l2 s a2 x} (LUpd l1 s a1 (LUpd l2 s a2 x))"

locale l_ortho_base' =
  fixes l1 :: "('a, 'b1, 'c :: Pord_Weakb) lifting"
  fixes l2 :: "('a, 'b2, 'c) lifting"

locale l_ortho_base_ext = l_ortho_base' +
  assumes compat_base1 : "\<And> s . LBase l1 s = \<bottom>"
  assumes compat_base2 : "\<And> s . LBase l2 s = \<bottom>"

locale l_ortho_ok' =
  fixes l1 :: "('a, 'b1, 'c :: {Pord_Weakb, Okay}) lifting"
  fixes l2 :: "('a, 'b2, 'c) lifting"

(* l_ortho_ok? i think we actually don't need any further properties!
*)

locale l_ortho_ok_ext = l_ortho_ok'


locale l_ortho_pres = l_ortho + l_ortho_pres_ext
locale l_ortho_base = l_ortho + l_ortho_base_ext
locale l_ortho_base_pres = l_ortho + l_ortho_base_ext + l_ortho_pres_ext
locale l_ortho_ok = l_ortho + l_ortho_ok_ext
locale l_ortho_base_ok = l_ortho + l_ortho_base_ext + l_ortho_ok_ext
locale l_ortho_ok_pres = l_ortho + l_ortho_ok_ext + l_ortho_pres_ext
locale l_ortho_base_ok_pres = l_ortho + l_ortho_base_ext + l_ortho_ok_ext + l_ortho_pres_ext

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

sublocale l_ortho_base_ext \<subseteq> comm :
  l_ortho_base_ext l2 l1
proof
  show "\<And>s. LBase l2 s = \<bottom>"
    using compat_base1 compat_base2 by auto
next
  show "\<And>s. LBase l1 s = \<bottom>"
    using compat_base1 compat_base2 by auto
qed

(*
sublocale l_ortho_pres_ext \<subseteq> comm :
  l_ortho_pres_ext l2 S2 l1 S1
proof
  fix a1 a2 s x

  have Comm1 : "{LUpd l2 s a1 x, LUpd l1 s a2 x} = {LUpd l1 s a2 x, LUpd l2 s a1 x}"
    by auto

  have Conc' : "is_sup {LUpd l1 s a2 x, LUpd l2 s a1 x} (LUpd l1 s a2 (LUpd l2 s a1 x))"
    using compat_pres_sup
    by auto

  then show "is_sup {LUpd l2 s a1 x, LUpd l1 s a2 x} (LUpd l2 s a1 (LUpd l1 s a2 x))"
    unfolding Comm1
    using compat
    by fastforce
qed
*)

(* previously I was trying to use this locale-signature to auto-generate
 * useful theorems for composing proofs... in the end i took a more
 * manual approach (see Lifter_Instances.thy, theorems "ax"/"ax_g"
 *)
locale vsg' =
  fixes l :: "('a, 'b, 'c) lifting"
  fixes S :: "'a \<Rightarrow> 'c set"
  fixes S' :: "'a \<Rightarrow> 'c set"

(*
(* TODO: finish these VSG defs, make sure they work. *)
locale lifting_valid_weak_vsg =
  lifting_valid_weak +
  vsg' +
  assumes S'_S : "\<And> x . S' x = S x"

sublocale lifting_valid_weak_vsg \<subseteq> lifting_valid_weak l S'
proof
  show "\<And>s a b. LUpd l s a b \<in> S' s"
    using S'_S put_S by auto
next
  show "\<And>s b a. LOut l s (LUpd l s a b) = a"
    using S'_S put_get by auto
next
  show "\<And>s b. b \<in> S' s \<Longrightarrow> b <[ LUpd l s (LOut l s b) b"
    using S'_S get_put_weak by auto
qed
*)

(*
  option_l_valid_weak + vsg' +
  assumes S'_S : "S' = option_l_S S"
*)

(* Some helpful lemmas for automation. *)
(* TODO: can we use lemma (in) instead?
 * or, can we create some kind of locale extending lifting_valid? *)
(*
lemma option_l_valid_weak_vsg :
  assumes H: "lifting_valid_weak"
*)

end