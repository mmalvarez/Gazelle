theory LiftUtils
 imports  "../Mergeable/MergeableInstances" "../Mergeable/MergeableAList" "../Mergeable/MergeableRAList"
begin

type_synonym ('a, 'b) syn_lifting = "('b \<Rightarrow> 'a)"

record ('syn, 'a, 'b) lifting =
  LUpd :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b :: Pord \<Rightarrow> 'b)"
  LOut :: "('syn \<Rightarrow> 'b \<Rightarrow> 'a)"
  LBase :: "'syn \<Rightarrow> 'b"

declare lifting.defs[simp]
declare lifting.cases [simp]

record ('syn, 'a, 'b) liftingv = "('syn, 'a, 'b :: Pord) lifting" +
  LOutS :: "'syn \<Rightarrow> 'b set"

definition LNew :: "('syn, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b"  where
"LNew l s a = LUpd l s a (LBase l s)"

type_synonym ('syn, 'b) valid_set =
"'syn \<Rightarrow> 'b set"

(* Validity of lifting *)

(* TODO: make sure the fourth clause here isn't too strong *)
definition lifting_valid_weak :: 
  "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_valid_weak l S =
  (\<forall> s a b . a = (LOut l s (LUpd l s a b)) \<and>
  (\<forall> s b . b \<in> S s \<longrightarrow> b <[ LUpd l s (LOut l s b) b) \<and>
  (\<forall> s a b . LUpd l s a b \<in> S s))"

lemma lifting_valid_weakI :
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s b. b \<in> S s \<Longrightarrow> b <[ LUpd l s (LOut l s b) b"
  assumes HP : "\<And> s a b . LUpd l s a b \<in> S s"
  shows "lifting_valid_weak l S" using assms
  by(auto simp add: lifting_valid_weak_def)

lemma lifting_valid_weakDO :
  assumes H : "lifting_valid_weak l S"
  shows "LOut l s (LUpd l s a b) = a" using assms
  by(auto simp add: lifting_valid_weak_def)

lemma lifting_valid_weakDO' :
  assumes H : "lifting_valid_weak l S"
  shows "LOut l s (LNew l s a) = a" using assms
  by(auto simp add: lifting_valid_weak_def LNew_def)

lemma lifting_valid_weakDI :
  assumes H : "lifting_valid_weak l S"
  assumes H' : "b \<in> S s"
  shows "b <[ LUpd l s (LOut l s b) b" using assms
  by(auto simp add:lifting_valid_weak_def)

lemma lifting_valid_weakDP :
  assumes H : "lifting_valid_weak l S" 
  shows "LUpd l s a b \<in> S s" using assms
  by(auto simp add: lifting_valid_weak_def)

(* Note that the second law is quite a strong condition -
   we require updates to _strictly increase_ the information content
   this implies the usage of something like priority *)
definition lifting_valid :: "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
                             ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_valid l S =
   ((\<forall> s a b . a = LOut l s (LUpd l s a b)) \<and>
    (\<forall> s a b . b \<in> S s \<longrightarrow> b <[ LUpd l s a b) \<and>
    (\<forall> s a b . LUpd l s a b \<in> S s))"

declare liftingv.defs [simp]
declare liftingv.cases [simp]

lemma lifting_validI :
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s a b. b \<in> S s \<Longrightarrow> b <[ LUpd l s a b"
  assumes HP : "\<And> s a b . LUpd l s a b \<in> S s"
  shows "lifting_valid l S" using assms
  by(auto simp add: lifting_valid_def)

lemma lifting_validDO :
  assumes H : "lifting_valid l S"
  shows "LOut l s (LUpd l s a b) = a" using assms
  by(auto simp add: lifting_valid_def)

lemma lifting_validDO' :
  assumes H : "lifting_valid l S"
  shows "LOut l s (LNew l s a) = a" using assms
  by(auto simp add: lifting_valid_def LNew_def)

lemma lifting_validDI :
  assumes H : "lifting_valid l S"
  assumes H' : "b \<in> S s"
  shows "b <[ LUpd l s a b" using assms
  by(auto simp add:lifting_valid_def)

lemma lifting_validDP :
  assumes H : "lifting_valid l S"
  shows "LUpd l s a b \<in> S s" using assms
  by(auto simp add:lifting_valid_def)

lemma lifting_valid_imp_weak :
  assumes H : "lifting_valid l S"
  shows "lifting_valid_weak l S" using assms
  by(auto simp add: lifting_valid_def lifting_valid_weak_def)

definition lifting_validb :: "('x, 'a, 'b :: Pordb, 'z) lifting_scheme \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validb l S =
  (lifting_valid l S \<and>
  (\<forall> s . LBase l s = \<bottom>))"

lemma lifting_validbI :
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s a b. b \<in> S s \<Longrightarrow> b <[ LUpd l s a b"
  assumes HP : "\<And> s a b . LUpd l s a b \<in> S s"
  assumes HB : "\<And> s . LBase l s = \<bottom>"
  shows "lifting_validb l S" using assms
  by(auto simp add: lifting_valid_def lifting_validb_def)

lemma lifting_validbI' :
  assumes H : "lifting_valid l S"
  assumes HB : "\<And> s . LBase l s = \<bottom>"
  shows "lifting_validb l S" using assms
  by(auto simp add: lifting_valid_def lifting_validb_def)

lemma lifting_validbDO :
  assumes H : "lifting_validb l S"
  shows "LOut l s (LUpd l s a b) = a" using assms
  by(auto simp add: lifting_valid_def lifting_validb_def)

lemma lifting_validbDO' :
  assumes H : "lifting_validb l S"
  shows "LOut l s (LNew l s a) = a" using assms
  by(auto simp add: lifting_valid_def lifting_validb_def LNew_def)

lemma lifting_validbDI :
  assumes H : "lifting_validb l S"
  assumes H' : "b \<in> S s"
  shows "b <[ LUpd l s a b" using assms
  by(auto simp add:lifting_valid_def lifting_validb_def)

lemma lifting_validbDB :
  assumes H : "lifting_validb l S"
  shows "LBase l s = \<bottom>" using assms
  by(auto simp add:lifting_valid_def lifting_validb_def)

lemma lifting_validbDP :
  assumes H : "lifting_validb l S"
  shows "LUpd l s a b \<in> S s" using assms
  by(auto simp add:lifting_validb_def lifting_valid_def)

lemma lifting_validbDV :
  assumes H : "lifting_validb l S"
  shows "lifting_valid l S"
  using assms 
  by(auto simp add:lifting_valid_def lifting_validb_def)

definition lifting_valid_weakb :: "('x, 'a, 'b :: Pordb, 'z) lifting_scheme \<Rightarrow>
                                   ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_valid_weakb l S =
  (lifting_valid_weak l S \<and>
  (\<forall> s . LBase l s = \<bottom>))"

lemma lifting_valid_weakbI :
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s b. b \<in> S s \<Longrightarrow> b <[ LUpd l s (LOut l s b) b"
  assumes HP : "\<And> s a b . LUpd l s a b \<in> S s"
  assumes HB : "\<And> s . LBase l s = \<bottom>"
  shows "lifting_valid_weakb l S" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbI' :
  assumes HV : "lifting_valid_weak l S"
  assumes HB : "\<And> s . LBase l s = \<bottom>"
  shows "lifting_valid_weakb l S" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDO :
  assumes H : "lifting_valid_weakb l S"
  shows "LOut l s (LUpd l s a b) = a" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDI :
  assumes H : "lifting_valid_weakb l S"
  assumes H' : "b \<in> S s"
  shows "b <[ LUpd l s (LOut l s b) b" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDP :
  assumes H : "lifting_valid_weakb l S"
  shows "LUpd l s a b \<in> S s" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDB :
  assumes H : "lifting_valid_weakb l S"
  shows "LBase l s = \<bottom>" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDV :
  assumes H : "lifting_valid_weakb l S"
  shows "lifting_valid_weak l S" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

abbreviation  lifting_valid' where
"lifting_valid' \<equiv> (\<lambda> l . lifting_valid l (\<lambda> _ . UNIV))"

abbreviation lifting_validb' where
"lifting_validb' \<equiv> (\<lambda> l . lifting_validb l (\<lambda> _ . UNIV))"

abbreviation lifting_valid_weak' where
"lifting_valid_weak' \<equiv> (\<lambda> l . lifting_valid_weak l (\<lambda> _ . UNIV))"

abbreviation lifting_valid_weakb' where
"lifting_valid_weakb' \<equiv> (\<lambda> l . lifting_valid_weakb l (\<lambda> _ . UNIV))"



(* TODO: refactor this so that everything is lifting_valid_cond,
lifting_valid is just defined in terms of it. *)

(*
  Mapping semantics through a lifting
*)

definition lift_map ::
  "('x, 'a , 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
    ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"lift_map l sem syn st =
  (LUpd l syn (sem syn (LOut l syn st)) st)"

declare lift_map_def [simp]

(* trailing s = "with syntax" *)
definition lift_map_s ::
    "('a1, 'b1) syn_lifting \<Rightarrow>
     ('a1, 'a2 , 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"lift_map_s l' l sem syn st =
  (LUpd l (l' syn) (sem (l' syn) (LOut l (l' syn) st)) st)"

declare lift_map_s_def [simp]

definition lower_map_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2) \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2)" where
"lower_map_s l' l sem syn st =
  (let syn' = (SOME x . l' x = syn) :: 'b1 in
  (LOut l syn (sem syn' (LNew l syn st))))"

declare lower_map_s_def [simp]

(* TODO (later): predicate lifting/lowering.
   This will be similar to LiftUtilsOrd. *)

(* Orthogonality of liftings
   Used to define valid merge-liftings. *)
(* could weaken this to require just that bases have a LUB
   this would complicate proofs though and might not even work. *)
(* we need to parameterize this by either
   - one set (union of two valid sets/bigger)
   - two sets (valid set of each lifting)
*)
definition l_ortho ::
  "('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b, 'z2) lifting_scheme \<Rightarrow>
   bool" where
"l_ortho l1 l2 =
  (
  (\<forall> s a1 a2 b .
    LUpd l1 s a1 (LUpd l2 s a2 b) = LUpd l2 s a2 (LUpd l1 s a1 b)) \<and>
  (\<forall> s . LBase l1 s = LBase l2 s))"

lemma l_orthoDI :
  fixes s :: 'x
  assumes H : "l_ortho (l1 :: ('x, 'a1, 'b ::Mergeable, 'z1) lifting_scheme)
                       (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme)"
  shows "LUpd l1 s a1 (LUpd l2 s a2 b) = LUpd l2 s a2 (LUpd l1 s a1 b)"
  using assms
  by(auto simp add: l_ortho_def; blast)

lemma l_orthoDB :
  fixes s :: 'x
  assumes H : "l_ortho (l1 :: ('x, 'a1, 'b ::Mergeable, 'z1) lifting_scheme)
                       (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme)"
  shows "LBase l1 s = LBase l2 s"
  using assms
  by(auto simp add: l_ortho_def; blast)

lemma l_orthoI [intro]:
  assumes HI :
    "\<And> s a1 a2 b . LUpd l1 s a1 (LUpd l2 s a2 b) = LUpd l2 s a2 (LUpd l1 s a1 b)"
  assumes HB :
    "\<And> s . LBase l1 s = LBase l2 s"
  shows "l_ortho l1 l2"
  using assms
  by(auto simp add: l_ortho_def)

lemma l_ortho_comm :
  assumes H :"l_ortho (l1 :: ('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme)
                      (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme)"
  shows "l_ortho l2 l1"
proof(rule l_orthoI)
  fix s a1 a2 b

  show "LUpd l2 s a1 (LUpd l1 s a2 b) = LUpd l1 s a2 (LUpd l2 s a1 b)"
    using l_orthoDI[OF H] by auto
next
  fix s
  show "LBase l2 s = LBase l1 s"
    using l_orthoDB[OF H] by auto
qed

end