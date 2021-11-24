theory Composition_Core imports "../Mergeable/Mergeable" "../Mergeable/Mergeable_Facts"
begin

(* TODO: do we actually need to import lifter?*)

(* Here we begin to develop some primitives for language composition,
 * based on the partial-ordering-based
 * framework developed in Mergeable. We take multiple semantics ('a \<Rightarrow> 'b \<Rightarrow> 'b) and calculate
 * a new one of the same type. The idea is "run all of them, and then take the bsup of the result".
 *
 * Lang_Comp completes the appropriate definitions for composition, in a very general setting.
 * See Lang_Comp_Simple for a less-powerful but possibly easier-to-understand alternative.
 *
 * Since we know that bsup calculates the true supremum
 * of any inputs which have a supremum, we just need to show that the necessary suprema exist.
 * We then can meaningfully talk about a semantics that represents the merger of several
 * others, with the information ordering naturally resolving any "conflicts" between
 * these semantics' behaviors.
 *)

(* TODO: we seem to have a few different primitives that capture different notions of
 * compatability of semantics: sups_pres, sup_l, orthogonal liftings
 * it would be nice to have a clear statement somewhere of the relationship between
 * all these.
 *)

(* We will be presented with a list of language semantics, but will prefer to work
 * with sets whenever possible. *)
type_synonym ('a, 'b) langcomps =
  "('a \<Rightarrow> 'b \<Rightarrow> 'b) list"

(* Pcomps ("Parallel CompositionS") will calculate the merged semantics using bsup -
 * but is only guaranteed to be well-behaved under certain conditions (corresponding
 * to the existence of some necessary suprema).
 *
 * The idea is that in such cases, the ordering of composition doesn't matter
 * (since our composition operator bsup will coincide with sup; thus will be commutative
 * and associative) so we can just fold along the list in the natural order. *)
fun pcomps :: "('a, 'b :: Mergeable) langcomps \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomps [] a b = b"
| "pcomps [lh] a b = lh a b"
| "pcomps (lh#lt) a b =
   [^ lh a b, pcomps lt a b ^]"

(* Map a set of functions over inputs drawn from another set *)
definition scross :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" where
"scross Fs Xs =
  { x . \<exists> f y . f \<in> Fs \<and> y \<in> Xs \<and> x = f y }"

lemma scross_inI :
  assumes Hf : "f \<in> Fs"
  assumes Hx : "x \<in> Xs"
  assumes Heq : "res = f x"
  shows "res \<in> scross Fs Xs" using assms
  unfolding scross_def
  by blast

lemma scross_inD  :
  assumes "res \<in> scross Fs Xs"
  shows "\<exists> f y . f \<in> Fs \<and> y \<in> Xs \<and> res = f y" using assms
  unfolding scross_def
  by blast


lemma pcomps_cons_same :
  shows "pcomps (x#x#t) = pcomps (x#t)"
proof(induction t arbitrary: x)
  case Nil
  then show ?case 
    by(auto simp add: bsup_idem)
next
  case (Cons a1 t1)
  then show ?case unfolding pcomps.simps bsup_base_eq
    by auto
qed


end