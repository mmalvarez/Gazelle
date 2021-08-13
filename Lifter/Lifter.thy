theory Lifter
 imports  "../Mergeable/Mergeable_Instances" "../Mergeable/Mergeable_Oalist" "../Mergeable/Mergeable_Roalist" "../Mergeable/Mono"
begin

(* This file (which really should be called Lifting, but this conflicts with a file in Isabelle's
 * standard library) contains a definition of an interface for lifting functions from the
 * data types over which they are naturally defined 
 *
 * This infrastructure is what allows us to take (in an ideal case) a
 * semantic implementation from an existing development and use it with Gazelle - in particular,
 * getting it to work correctly with the wrapper types (see Mergeable.thy, Mergeable_Instances.thy)
 *
 * The concept here is inspired by that of _lenses_ (indeed, this development can be seen as an 
 * outgrowth of exploring the space of optics to try to capture the relationship between
 * semantic state types that is necessary to make Gazelle work seamlessly and
 * ultimately integrating them with partial orderings (see Mergeable.thy, Pord.thy)). It is also
 * (somewhat) inspired by Isabelle's built-in Lifting/Transfer utility.
 * While Lifting/Transfer offers excellent automation, it does not easily support 
 * reasoning about a corresponding lowering" operation, which is important for reasoning about
 * predicates.
*)

(* When we lift syntaxes we reverse the function arrow *)
type_synonym ('a, 'b) syn_lifting = "('b \<Rightarrow> 'a)"

(*
 * A _lifting_ is a record with 3 type parameters (a corresponding syntax 'syn,
 * a type 'a corresponding to the "small" type, and a type 'b corresponding to the "big"
 * type that 'a is being "injected into"
 *
 * Liftings contain implementations of 3 functions (think of them as being like a typeclass
 * dictionary).
 * - LUpd is a "lens-update": for a "small" element a and a "big" element b,
 *   LUpd a b returns a new "big" element that is b "updated to contain a"
 * - LOut "projects out" a "small" value a, "contained in" the given big value b
 * - LBase contains a "default" element of 'b. This is used to implement, for instance,
 *   creating a new 'b given only some 'a. (See LNew, below). Note that while we could
 *   use Isabelle's _undefined_ instead, giving an explicit definition of base helps
 *   us avoid annoying issues with the generated code that happen when execution reaches an
 *   undefined.
 *
 * This interface is geared towards supporting lifting semantics in a "small" language
 * ('syn \<Rightarrow> 'a \<Rightarrow> 'a) to a semantics in a "big" language ('syn \<Rightarrow> 'b \<Rightarrow> 'b); accordingly
 * these primitives also take the label on the syntax node being executed as an argument.
 *
 * All of these primitives have an extra 'syn parameter, so that their behavior can depend
 * on the label of the syntax node being execut
 *
 * In an ideal world, this construct might be a typeclass; however, because of some limitations of
 * Isabelle's built-in typeclass infrastructure (most significantly the lack of support for
 * typeclasses with more than one type parameter) this isn't possible.
 *
 * We are able to use typeclasses to provide a fair degree of automation on constructing
 * liftings based on a user specification; see Auto_Lift.thy for details.
 *)
record ('syn, 'a, 'b) lifting =
  LUpd :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b :: Pord \<Rightarrow> 'b)"
  LOut :: "('syn \<Rightarrow> 'b \<Rightarrow> 'a)"
  LBase :: "'syn \<Rightarrow> 'b"

declare lifting.defs[simp]
declare lifting.cases [simp]

(* As we'll see below, there is a traditional "lens law"
 * that we would very much like to hold generally, but that does not. This is the law that
 * says informally "if we project out of a 'b, then inject the projected value,
 * we get back the same object (or, in a weaker form, we get back an object that is at least
 * as informative; that is, ]> according to our information ordering)
 *
 * To see why this fails, take the sum type, and the "first component"/"inl" projection.
 * When projecting out of (Inr x :: ('a1 + 'a2) option),
 * we return a "bogus" value y of type 'a1; when we inject back in, we will get (Inl y)
 * According to our implementation of ordering for Sum, (Inl y) and (Inl x) must be
 * incomparable (see Meregeable_Instances.thy for a bit more on why).
 *
 * To get around this, we attach a "valid set" to our lifting to get a liftingv
 * ("lifting with Valid-set"). This valid set characterizes what subset of the type 'b
 * the above-mentioned law _does_hold for.
 *)
record ('syn, 'a, 'b) liftingv = "('syn, 'a, 'b :: Pord) lifting" +
  LOutS :: "'syn \<Rightarrow> 'b set"

definition LNew :: "('syn, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b"  where
"LNew l s a = LUpd l s a (LBase l s)"

type_synonym ('syn, 'b) valid_set =
"'syn \<Rightarrow> 'b set"

(*
 * Validity of lifting. This looks a lot like a standard definition of validity of a "weak lens"
 * (i.e., a lens without a "put-put law").
 * - Clause 1 is standard: "we get out what we put in"
 * - Clause 2 is almost standard; is says that "when we update b with projected data from b,
     we get back the same b (or something informationally larger)."
 * - Clause 3 says that after we update, we are always in the valid set (i.e.,
     we can always meaningfully project back out).
 * This validity is "weak" in that there is a stronger version of the second clause that is
 * sometimes useful; see lifting_valid below.
 *)

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

(* 
 * The stronger version of validity for lifting corresponds intuitively to the stronger definition
 * of lenses that includes a "put-put law", stating that successive updates erase all traces
 * of previous updates.
 *
 * The change from lifting_valid_weak is only in the second law - rather than saying that we get
 * back a result informationally greater than b if we update b with its own contents, we now
 * require that we get back an informationally greater result when updating b with _any_
 * contents.
 * 
 * This is quite a strong condition, and usually necessitates the usage of something like md_prio
 * (see Mergeable_Instances.thy).
*)
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

(* Finally, for liftings with a "least" (bottom) element, we want
 * LBase to conincide with that element.
*)
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


(*
 * The primary way we use these lifting instances is to make it easier to lift
 * functions from the "small" type to the "big" type, and to reason about them.
 * This sometimes includes lifting predicates from the "small" type to the "big" type.
 *
 * First, we define how we map semantics through a lifting.
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


(* syntax-translation of lifting *)
definition l_synt ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('b1, 'a2, 'b2) lifting" where
"l_synt l' l =
  \<lparr> LUpd = (LUpd l) o l'
  , LOut = (LOut l) o l'
  , LBase = (LBase l) o l'\<rparr>"

lemma l_synt_valid_weak :
  assumes H : "lifting_valid_weak l S"
  shows "lifting_valid_weak (l_synt l' l) (S o l')" using H
  unfolding lifting_valid_weak_def l_synt_def
  by(auto)

lemma l_synt_valid :
  assumes H : "lifting_valid l S"
  shows "lifting_valid (l_synt l' l) (S o l')" using H
  unfolding lifting_valid_def l_synt_def
  by(auto)

lemma l_synt_valid_weakb :
  assumes H : "lifting_valid_weakb l S"
  shows "lifting_valid_weakb (l_synt l' l) (S o l')" using H
  unfolding lifting_valid_weakb_def lifting_valid_weak_def l_synt_def
  by(auto)

lemma l_synt_validb :
  assumes H : "lifting_validb l S"
  shows "lifting_validb (l_synt l' l) (S o l')" using H
  unfolding lifting_validb_def lifting_valid_def l_synt_def
  by(auto)


(* Now we introduce a concept of "orthogonality" of liftings. This basically says that
 * we are allowed to change the order in which updates from two orthogonal liftings
 * happen, and that the bases of the two liftings are equal. This makes it much easier
 * to reason about a "merging" of these two liftings (see Lifter_Instances for exactly what that
 * means) since we don't have to worry about the two liftings "interfering" with each other
 * in ways that break commutativity.
 *
 * TODO: do we actually use this?
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

(* Theorems about lifting and monotonicity. *)
(* lemma: lifted functions are monotone (if lifted using a valid lifting) *)
lemma lift_monot :
  assumes Hv : "lifting_valid l S"
  shows "monot (S (l' syn)) (lift_map_s l' l f syn)"
proof(rule monotI)
  fix x
  assume Hx : "x \<in> S (l' syn)"

  show "x <[ lift_map_s l' l f syn x"
  unfolding monot_def lift_map_s_def
  using lifting_validDI[OF Hv Hx]
  by auto
qed

(* idea: similar to lifting_valid:
   - Out (upd) preserves
   - Upd (out) preserves
   - Set membership preserved

do we need "orthoB" or similar?
*)
definition l_ortho_alt ::
  "('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'b) valid_set \<Rightarrow>
   ('x, 'a2, 'b, 'z2) lifting_scheme \<Rightarrow>
   ('x, 'b) valid_set \<Rightarrow>
   bool" where
"l_ortho_alt l1 S1 l2 S2 =
  (
  (\<forall> s a b . b \<in> S1 s \<longrightarrow> LOut l1 s (LUpd l2 s a b) = LOut l1 s b) \<and>
  (\<forall> s a b . b \<in> S2 s \<longrightarrow> LOut l2 s (LUpd l1 s a b) = LOut l2 s b) \<and>
  (\<forall> s a b . b \<in> S1 s \<longrightarrow> LUpd l2 s a b \<in> S1 s) \<and>
  (\<forall> s a b . b \<in> S2 s \<longrightarrow> LUpd l1 s a b \<in> S2 s))
 "

lemma l_ortho_altDO1 :
  fixes s :: 'x
  assumes H : "l_ortho_alt (l1 :: ('x, 'a1, 'b ::Mergeable, 'z1) lifting_scheme) S1
                       (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme) S2"
  assumes Hin : "b \<in> S1 s"
  shows "LOut l1 s (LUpd l2 s a b) = LOut l1 s b"
  using assms
  by(auto simp add: l_ortho_alt_def; blast)

lemma l_ortho_altDO2 :
  fixes s :: 'x
  assumes H : "l_ortho_alt (l1 :: ('x, 'a1, 'b ::Mergeable, 'z1) lifting_scheme) S1
                       (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme) S2"
  assumes Hin : "b \<in> S2 s"
  shows "LOut l2 s (LUpd l1 s a b) = LOut l2 s b"
  using assms
  by(auto simp add: l_ortho_alt_def; blast)

lemma l_ortho_altDP1 :
  fixes s :: 'x
  assumes H : "l_ortho_alt (l1 :: ('x, 'a1, 'b ::Mergeable, 'z1) lifting_scheme) S1
                       (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme) S2"
  assumes Hin : "b \<in> S1 s"
  shows "LUpd l2 s a b \<in> S1 s"
  using assms
  by(auto simp add: l_ortho_alt_def; blast)

lemma l_ortho_altDP2 :
  fixes s :: 'x
  assumes H : "l_ortho_alt (l1 :: ('x, 'a1, 'b ::Mergeable, 'z1) lifting_scheme) S1
                       (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme) S2"
  assumes Hin : "b \<in> S2 s"
  shows "LUpd l1 s a b \<in> S2 s"
  using assms
  by(auto simp add: l_ortho_alt_def; blast)

lemma l_ortho_altI [intro]:
  assumes HI1 : "\<And> s a b . b \<in> S1 s \<Longrightarrow> LOut l1 s (LUpd l2 s a b) = LOut l1 s b"
  assumes HI2 : "\<And> s a b . b \<in> S2 s \<Longrightarrow> LOut l2 s (LUpd l1 s a b) = LOut l2 s b"
  assumes HP1 : "\<And> s a b . b \<in> S1 s \<Longrightarrow> LUpd l2 s a b \<in> S1 s"
  assumes HP2 : "\<And> s a b . b \<in> S2 s \<Longrightarrow> LUpd l1 s a b \<in> S2 s" 
  shows "l_ortho_alt l1 S1 l2 S2"
  using assms
  by(auto simp add: l_ortho_alt_def)

definition l_ortho_altb ::
  "('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'b) valid_set \<Rightarrow>
   ('x, 'a2, 'b, 'z2) lifting_scheme \<Rightarrow>
   ('x, 'b) valid_set \<Rightarrow>
   bool" where
"l_ortho_altb l1 S1 l2 S2 =
  (l_ortho_alt l1 S1 l2 S2 \<and>
  (\<forall> s . LBase l1 s = LBase l2 s))"

lemma l_ortho_altbDB :
  assumes "l_ortho_altb l1 S1 l2 S2"
  shows "LBase l1 s = LBase l2 s" using assms
  by(auto simp add: l_ortho_altb_def)

lemma l_ortho_altbDV :
  assumes "l_ortho_altb l1 S1 l2 S2"
  shows "l_ortho_alt l1 S1 l2 S2"
  using assms
  by(auto simp add: l_ortho_altb_def)

lemma l_ortho_altbI :
  assumes HV : "l_ortho_alt l1 S1 l2 S2"
  assumes HB : "\<And> s . LBase l1 s = LBase l2 s"
  shows "l_ortho_altb l1 S1 l2 S2"
  using assms
  by(auto simp add: l_ortho_altb_def)

lemma l_ortho_alt_comm :
  assumes H :"l_ortho_alt (l1 :: ('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme) S1
                      (l2 :: ('x, 'a2, 'b, 'z2) lifting_scheme) S2"
  shows "l_ortho_alt l2 S2 l1 S1"
proof(rule l_ortho_altI)
  show "\<And>s a b. b \<in> S2 s \<Longrightarrow> LOut l2 s (LUpd l1 s a b) = LOut l2 s b"
    using l_ortho_altDO2[OF H]
    by(auto)
next
  show "\<And>s a b. b \<in> S1 s \<Longrightarrow> LOut l1 s (LUpd l2 s a b) = LOut l1 s b"
    using l_ortho_altDO1[OF H]
    by auto
next
  show "\<And>s a b. b \<in> S2 s \<Longrightarrow> LUpd l1 s a b \<in> S2 s"
    using l_ortho_altDP2[OF H]
    by auto
next
  show "\<And>s a b. b \<in> S1 s \<Longrightarrow> LUpd l2 s a b \<in> S1 s"
    using l_ortho_altDP1[OF H]
    by auto
qed
end