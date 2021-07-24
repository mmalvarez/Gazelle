theory Dominant imports Composition
begin

(*
 * One very common case that arises when working with merged semantics is a situation where
 * two or more semantics are trivially non-conflicting for certain relevant pieces of syntax.
 * 
 * This style of reasoning is used in general Hoare rules covering extensions of a language
 * (see the Hoare directory). We show that the rule corresponding to construct C
 * in language L holds for any extension of L, provided the semantics function for L
 * remains "dominant" over the others for the syntax corresponding to C
 * (that is, will not be overridden).
 *
 * (Concretely: if I know my IMP semantics is dominant for IF statements,
 * I do not need to worry about other languages being merged in disrupting the intended
 * behavior of IF.)
 *)

(* dominant: for the given syntax x, f "dominates" set S if for all state inputs b,
 * f x b is the least upper bound of
 * applying each f' in S to x and b.
 *)
definition dominant ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> 'a \<Rightarrow> bool"
("_ \<downharpoonleft> _ _" [250, 252, 254])
where
"(f \<downharpoonleft> S x) =
 (\<forall> b . is_sup ((\<lambda> g . g x b) ` S) (f x b))"

lemma dominantI [intro] :
  assumes "\<And> b . is_sup ((\<lambda> g . g x b) ` S) (f x b)"
  shows "(f \<downharpoonleft> S x)" using assms
  unfolding dominant_def by auto

lemma dominantE [elim] :
  assumes "(f \<downharpoonleft> S x)"
  shows "is_sup ((\<lambda> g . g x b) ` S) (f x b)" using assms
  unfolding dominant_def by auto

(* If sups_pres holds on a set
 * (I believe this hypothesis is needed to rule out badly-behaved sets that subvert the intuitive
 * meaning of dominant, though not 100% sure - TODO)
 * and f is dominant for some syntax x
 * then the result of running the merged semantics will exactly equal the result of f
 * on that syntax.
 *)

lemma dominant_pcomps :
  assumes Hpres : "sups_pres (set l)"
  assumes Hne : "z \<in> set l"
  assumes H : "(f \<downharpoonleft> (set l) x)"
  shows "pcomps l x b = f x b"
proof-

  have B : "is_sup {b} b"
    using sup_singleton by auto

  have Sup1 : "is_sup (scross ((\<lambda>f. f x) ` set l) {b}) (pcomps l x b)"
    using sups_pres_pcomps_gen[OF Hpres Hne, of "{b}" b b x] B
    by auto

  have Rewrite1 : "(\<lambda>f. f b) ` (\<lambda>f. f x) ` set l = (\<lambda> f . f x b) ` set l"
    by blast

  have Sup2 : "is_sup ((\<lambda>f. f x b) ` set l) (pcomps l x b)"
    using Sup1
    unfolding scross_singleton2 Rewrite1
    by auto

  have Sup2' : "is_sup ((\<lambda>f. f x b) ` set l) (f x b)"
    using dominantE[OF H, of b]
    by auto

  show ?thesis using is_sup_unique[OF Sup2 Sup2'] by auto
qed

lemma dominant_pcomps_set :
  assumes Hpres : "sups_pres S"
  assumes Hne : "z \<in> S"
  assumes H : "(f \<downharpoonleft> S x)"
  assumes L : "set l = S"
  shows "pcomps l x b = f x b"
  using dominant_pcomps assms unfolding sym[OF L] by auto

(* 
 * A more fine-grained version of dominant - capturing the idea of "quotiented" dominance.
 * Whereas "true" dominance says that f's result is equal to the sep, this one says that
 * some relation holds (?)
 *)

(* dominant: for the given syntax x, f "dominates" set S if for all state inputs b,
 * f x b is the least upper bound of
 * applying each f' in S to x and b.
 * how can we special-case this?
 *)
(*
definition dominantP ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> 'a \<Rightarrow> bool"
("_; _ \<downharpoonleft> _ _" [280, 282, 284, 286])
where
"(f; P \<downharpoonleft> S x) =
 (\<forall> b . is_sup ((\<lambda> g . g x b) ` S) (f x b))"

lemma dominantI [intro] :
  assumes "\<And> b . is_sup ((\<lambda> g . g x b) ` S) (f x b)"
  shows "(f \<downharpoonleft> S x)" using assms
  unfolding dominant_def by auto

lemma dominantE [elim] :
  assumes "(f \<downharpoonleft> S x)"
  shows "is_sup ((\<lambda> g . g x b) ` S) (f x b)" using assms
  unfolding dominant_def by auto
*)

end