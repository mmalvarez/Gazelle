theory Lifter
  imports  "../Mergeable/Mergeable_Instances" "../Mergeable/Mono"
    "../Composition/Composition"
begin

(*
 * Here we define an abstraction that captures transforming
 * operations on a "smaller" structure (e.g., semantics of a
 * language component) to a larger (in the sense of 
 * having "more fields"), ordered structure
 *)

(* When we lift syntaxes we reverse the function arrow *)
type_synonym ('a, 'b) syn_lifting = "('b \<Rightarrow> 'a)"

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

locale lifting_sig =
  fixes l :: "('syn, 'a, 'b :: Pord_Weak) lifting"
  fixes S :: "('syn, 'b) valid_set"

locale lifting_putonly = lifting_sig +
  assumes put_S : "\<And> s a b . LUpd l s a b \<in> S s"

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

locale l_ortho_pres' = 
  fixes l1 :: "('a, 'b1, 'c :: Pordb) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c set"
  fixes l2 :: "('a, 'b2, 'c :: Pordb) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c set"

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

end