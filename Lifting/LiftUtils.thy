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


(* Validity of lifting *)

(* we should stratify this into "lifting_valid_weak" and "lifting_valid"
weak is just the first law
that way we can express things like
"lifting a weakly valid lifting through a well-formed prio lifting
will be (strongly) valid"
*)

definition lifting_valid_weak :: "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> bool" where
"lifting_valid_weak l =
  (\<forall> s a b . a = (LOut l s (LUpd l s a b)) \<and>
  (\<forall> s b . b <[ LUpd l s (LOut l s b) b))"

lemma lifting_valid_weakI :
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s b. b <[ LUpd l s (LOut l s b) b"
  shows "lifting_valid_weak l" using assms
  by(auto simp add: lifting_valid_weak_def)

lemma lifting_valid_weakDO :
  assumes H : "lifting_valid_weak l"
  shows "LOut l s (LUpd l s a b) = a" using assms
  by(auto simp add: lifting_valid_weak_def)

lemma lifting_valid_weakDO' :
  assumes H : "lifting_valid_weak l"
  shows "LOut l s (LNew l s a) = a" using assms
  by(auto simp add: lifting_valid_weak_def LNew_def)

lemma lifting_valid_weakDI :
  assumes H : "lifting_valid_weak l"
  shows "b <[ LUpd l s (LOut l s b) b" using assms
  by(auto simp add:lifting_valid_weak_def)


(* Note that the second law is quite a strong condition -
   we require updates to _strictly increase_ the information content
   this implies the usage of something like priority *)
definition lifting_valid :: "('x, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> bool" where
"lifting_valid l =
   ((\<forall> s a b . a = LOut l s (LUpd l s a b)) \<and>
    (\<forall> s a b . b <[ LUpd l s a b))"

declare liftingv.defs [simp]
declare liftingv.cases [simp]

lemma lifting_validI :
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s a b. b <[ LUpd l s a b"
  shows "lifting_valid l" using assms
  by(auto simp add: lifting_valid_def)

lemma lifting_validDO :
  assumes H : "lifting_valid l"
  shows "LOut l s (LUpd l s a b) = a" using assms
  by(auto simp add: lifting_valid_def)

lemma lifting_validDO' :
  assumes H : "lifting_valid l"
  shows "a = LOut l s (LNew l s a)" using assms
  by(auto simp add: lifting_valid_def LNew_def)

lemma lifting_validDI :
  assumes H : "lifting_valid l"
  shows "b <[ LUpd l s a b" using assms
  by(auto simp add:lifting_valid_def)

lemma lifting_valid_imp_weak :
  assumes H : "lifting_valid l"
  shows "lifting_valid_weak l" using assms
  by(auto simp add: lifting_valid_def lifting_valid_weak_def)

(* could define a weak version of this, but likely not useful *)
definition lifting_validb :: "('x, 'a, 'b :: Pordb, 'z) lifting_scheme \<Rightarrow> bool" where
"lifting_validb l =
  (lifting_valid l \<and>
  (\<forall> s . LBase l s = \<bottom>))"

lemma lifting_validbI :
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s a b. b <[ LUpd l s a b"
  assumes HB : "\<And> s . LBase l s = \<bottom>"
  shows "lifting_validb l" using assms
  by(auto simp add: lifting_valid_def lifting_validb_def)

lemma lifting_validbI' :
  assumes H : "lifting_valid l"
  assumes HB : "\<And> s . LBase l s = \<bottom>"
  shows "lifting_validb l" using assms
  by(auto simp add: lifting_valid_def lifting_validb_def)

lemma lifting_validbDO :
  assumes H : "lifting_validb l"
  shows "LOut l s (LUpd l s a b) = a" using assms
  by(auto simp add: lifting_valid_def lifting_validb_def)

lemma lifting_validbDO' :
  assumes H : "lifting_validb l"
  shows "a = LOut l s (LNew l s a)" using assms
  by(auto simp add: lifting_valid_def lifting_validb_def LNew_def)

lemma lifting_validbDI :
  assumes H : "lifting_validb l"
  shows "b <[ LUpd l s a b" using assms
  by(auto simp add:lifting_valid_def lifting_validb_def)

lemma lifting_validbDB :
  assumes H : "lifting_validb l"
  shows "LBase l s = \<bottom>" using assms
  by(auto simp add:lifting_valid_def lifting_validb_def)

lemma lifting_validbDV :
  assumes H : "lifting_validb l"
  shows "lifting_valid l"
  using assms 
  by(auto simp add:lifting_valid_def lifting_validb_def)

definition lifting_valid_weakb :: "('x, 'a, 'b :: Pordb, 'z) lifting_scheme \<Rightarrow> bool" where
"lifting_valid_weakb l =
  (lifting_valid_weak l \<and>
  (\<forall> s . LBase l s = \<bottom>))"

lemma lifting_valid_weakbI :
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s b. b <[ LUpd l s (LOut l s b) b"
  assumes HB : "\<And> s . LBase l s = \<bottom>"
  shows "lifting_valid_weakb l" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbI' :
  assumes HV : "lifting_valid_weak l"
  assumes HB : "\<And> s . LBase l s = \<bottom>"
  shows "lifting_valid_weakb l" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDO :
  assumes H : "lifting_valid_weakb l"
  shows "LOut l s (LUpd l s a b) = a" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDI :
  assumes H : "lifting_valid_weakb l"
  shows "\<And> s b. b <[ LUpd l s (LOut l s b) b" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDB :
  assumes H : "lifting_valid_weakb l"
  shows "LBase l s = \<bottom>" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

lemma lifting_valid_weakbDV :
  assumes H : "lifting_valid_weakb l"
  shows "lifting_valid_weak l" using assms
  by(auto simp add: lifting_valid_weak_def lifting_valid_weakb_def)

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
     ('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"lift_map_s l' l sem syn st =
  (LUpd l (l' syn) (sem (l' syn) (LOut l (l' syn) st)) st)"

declare lift_map_s_def [simp]

definition lower_map_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
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
definition l_ortho ::
  "('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b, 'z2) lifting_scheme \<Rightarrow>
   bool" where
"l_ortho l1 l2 =
  (
    (\<forall> s . LBase l1 s = LBase l2 s) \<and>
    (\<forall> s a1 a2 b .
      \<exists> z . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z \<and>
        LOut l1 s z = a1 \<and> LOut l2 s z = a2
        ))" 


lemma l_orthoDB :
  fixes s :: 'x
  assumes H : "l_ortho (l1 :: ('x, 'a1, 'b ::Mergeable, 'z1) lifting_scheme)
                       (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme)"
  shows "LBase l1 s = LBase l2 s"
  using assms
  by(auto simp add: l_ortho_def; blast)
  
lemma l_orthoDI :
  fixes s :: 'x
  fixes a1 :: 'a1
  fixes a2 :: 'a2
  fixes b :: "('b :: Mergeable)"
  assumes H : "l_ortho (l1 :: ('x, 'a1, 'b, 'z1) lifting_scheme)
                       (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme)"
  obtains z where
    "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z"
    "LOut l1 s z = a1"
    "LOut l2 s z = a2"
  using assms
  by(auto simp add: l_ortho_def; blast)

lemma l_orthoI [intro]:
  assumes HB :
    "\<And> s . LBase l1 s = LBase l2 s"
  assumes HI :
    "\<And> s a1 a2 b . 
      (\<exists> z . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z \<and> 
             LOut l1 s z = a1 \<and> LOut l2 s z = a2)"
  shows "l_ortho l1 l2"
  using assms
  by(auto simp add: l_ortho_def)

lemma l_ortho_comm :
  assumes H :"l_ortho (l1 :: ('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme) 
                      (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme)"
  shows "l_ortho l2 l1"
proof(rule l_orthoI)
  fix s

  show "LBase l2 s = LBase l1 s"
    using l_orthoDB[OF H]
    by auto

next
  fix s :: "'x"
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  fix b :: "'b"

  obtain z where
    Zsup : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z" and
    Z1 : "LOut l1 s z = a1" and
    Z2 : "LOut l2 s z = a2"
    using l_orthoDI[OF H] by blast

  have "is_sup {LUpd l2 s a2 b, LUpd l1 s a1 b} z \<and> 
                LOut l2 s z = a2 \<and> LOut l1 s z = a1"
    using is_sup_comm2[OF Zsup] Z1 Z2
    by auto

  thus "\<exists>z. is_sup {LUpd l2 s a2 b, LUpd l1 s a1 b} z \<and> 
                    LOut l2 s z = a2 \<and> LOut l1 s z = a1"
    by auto
qed

end