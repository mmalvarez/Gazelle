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
definition lifting_valid :: "('x, 'a, 'b :: Pord, 'z) liftingv_scheme \<Rightarrow> bool" where
"lifting_valid l =
  ((\<forall> s a b . LUpd l s a b \<in> LOutS l s) \<and>
   (\<forall> s a b . a = LOut l s (LUpd l s a b)) \<and>
   (\<forall> s b . b \<in> LOutS l s \<longrightarrow> b <[ LUpd l s (LOut l s b) b))"

(* let's see if this is more ergonomic *)
declare liftingv.defs [simp]
declare liftingv.cases [simp]

lemma lifting_validI :
  assumes HSO : "\<And> s a b . LUpd l s a b \<in> LOutS l s"
  assumes HI : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes HO : "\<And> s b . b \<in> LOutS l s \<Longrightarrow>
                        b <[ LUpd l s (LOut l s b) b"
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
  assumes HO : "b \<in> LOutS l s"
  shows "b <[ LUpd l s (LOut l s b) b" using assms
  by(auto simp add:lifting_valid_def)

lemma lifting_validDSO :
  assumes H : "lifting_valid l"
  shows "LUpd l s a b \<in> LOutS l s" using assms
  by(auto simp add: lifting_valid_def)

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

definition l_ortho ::
  "('x, 'a1, 'b :: Mergeable, 'z1) liftingv_scheme \<Rightarrow>
   ('x, 'a2, 'b, 'z2) liftingv_scheme \<Rightarrow>
   bool" where
"l_ortho l1 l2 =
  (\<forall> s a1 a2 b .
    \<exists> z . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z \<and>
      z \<in> LOutS l1 s \<and> z \<in> LOutS l2 s \<and>
      LOut l1 s z = a1 \<and> LOut l2 s z = a2
      )" 

lemma l_orthoD [elim] :
  fixes s :: 'x
  fixes a1 :: 'a1
  fixes a2 :: 'a2
  fixes b :: "('b :: Mergeable)"
  assumes H : "l_ortho (l1 :: ('x, 'a1, 'b, 'z1) liftingv_scheme)
                       (l2 :: ('x, 'a2, 'b, 'z2) liftingv_scheme)"
  obtains z where
    "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z"
    "z \<in> LOutS l1 s"
    "z \<in> LOutS l2 s"
    "LOut l1 s z = a1"
    "LOut l2 s z = a2"
  using assms
  by(auto simp add: l_ortho_def; blast)

lemma l_orthoI [intro]:
  assumes H :
    "\<And> s a1 a2 b . 
      (\<exists> z . is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z \<and> 
             z \<in> LOutS l1 s \<and> z \<in> LOutS l2 s \<and>
             LOut l1 s z = a1 \<and> LOut l2 s z = a2)"
  shows "l_ortho l1 l2"
  using assms
  by(auto simp add: l_ortho_def)

lemma l_ortho_comm :
  assumes H :"l_ortho (l1 :: ('x, 'a1, 'b :: Mergeable, 'z1) liftingv_scheme) 
                      (l2 :: ('x, 'a2, 'b, 'z2) liftingv_scheme)"
  shows "l_ortho l2 l1"
proof(rule l_orthoI)
  fix s :: "'x"
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  fix b :: "'b"

  obtain z where
    Zsup : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} z" and
    ZS1 : "z \<in> LOutS l1 s" and
    ZS2 : "z \<in> LOutS l2 s" and
    Z1 : "LOut l1 s z = a1" and
    Z2 : "LOut l2 s z = a2"
    using l_orthoD[OF H] by blast

  have "is_sup {LUpd l2 s a2 b, LUpd l1 s a1 b} z \<and> z \<in> LOutS l2 s \<and>
         z \<in> LOutS l1 s \<and> LOut l2 s z = a2 \<and> LOut l1 s z = a1"
    using is_sup_comm2[OF Zsup] ZS1 ZS2 Z1 Z2
    by auto

  thus "\<exists>z. is_sup {LUpd l2 s a2 b, LUpd l1 s a1 b} z \<and> z \<in> LOutS l2 s \<and>
         z \<in> LOutS l1 s \<and> LOut l2 s z = a2 \<and> LOut l1 s z = a1"
    by auto
qed

end