theory Dominant imports Composition "../Lifter/Lifter"
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

(* binary notion of dominance (greater than or equal) for liftings *)
(* original notion had a valid-set parameter S, but i 
 * don't think we need it (new update should be equivalent to changing it to
   UNIV in all cases *)

locale dominant2_sig =
  fixes l1 :: "('a, 'b1, 'c :: Pord) lifting"
  fixes l2 :: "('a, 'b2, 'c :: Pord) lifting"
  fixes S :: "'a \<Rightarrow> 'c set"
  fixes X :: "'a set"

locale dominant2 = dominant2_sig +
  assumes dominant_leq :
    "\<And> a1 a2 b x . x \<in> X \<Longrightarrow> b \<in> S x \<Longrightarrow> LUpd l2 x a2 b <[ LUpd l1 x a1 b"

(*
locale dominant2_sig =
  fixes l1 :: "('a, 'b1, 'c :: Pord) lifting"
  fixes l2 :: "('a, 'b2, 'c :: Pord) lifting"
  fixes X :: "'a set"

locale dominant2 = dominant2_sig +
  assumes dominant_leq :
    "\<And> a1 a2 b x . x \<in> X \<Longrightarrow> LUpd l2 x a2 b <[ LUpd l1 x a1 b"
*)
(* dominant: for the given syntax x, f "dominates" set S if for all state inputs b,
 * f x b is the least upper bound of
 * applying each f' in S to x and b.
 *)
definition dominant ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> bool"
("_ \<downharpoonleft> _ _" [250, 252, 254])
where
"(f \<downharpoonleft> S X) =
 (\<forall> b x . x \<in> X \<longrightarrow> is_sup ((\<lambda> g . g x b) ` S) (f x b))"

(* TODO: might be a good idea to have a special version of dominant for lifters.
 * Similar e.g. to ortho.
 *)

lemma dominantI [intro] :
  assumes "\<And> b x . x \<in> X \<Longrightarrow> is_sup ((\<lambda> g . g x b) ` S) (f x b)"
  shows "(f \<downharpoonleft> S X)" using assms
  unfolding dominant_def by auto

lemma dominantE [elim] :
  assumes "(f \<downharpoonleft> S X)"
  assumes "x \<in> X"
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
  assumes Hpres : "sups_pres (set l) S"
  assumes Hne : "z \<in> set l"
  assumes H : "(f \<downharpoonleft> (set l) X)"
  assumes Xin : "x \<in> X"
  assumes Bin : "b \<in> S x"
  shows "pcomps l x b = f x b"
proof-

  have B : "is_sup {b} b"
    using sup_singleton by auto

  have Hne' : "l \<noteq> []"
    using Hne by auto


  have Sup1 : "is_sup (((\<lambda>f. f x b) ` set l)) (pcomps l x b)"
    using sups_pres_pcomps_sup'[OF Hpres Hne'] Bin B
    by auto

  have Rewrite1 : "(\<lambda>f. f b) ` (\<lambda>f. f x) ` set l = (\<lambda> f . f x b) ` set l"
    by blast

  have Sup2 : "is_sup ((\<lambda>f. f x b) ` set l) (pcomps l x b)"
    using Sup1
    unfolding scross_singleton2 Rewrite1
    by auto

  have Sup2' : "is_sup ((\<lambda>f. f x b) ` set l) (f x b)"
    using dominantE[OF H Xin, of b]
    by auto

  show ?thesis using is_sup_unique[OF Sup2 Sup2'] by auto
qed

lemma dominant_pcomps_set :
  assumes Hpres : "sups_pres Fs S"
  assumes Hne : "z \<in> Fs"
  assumes H : "(f \<downharpoonleft> Fs X)"
  assumes L : "set l = Fs"
  assumes Xin: "x \<in> X"
  assumes Bin : "b \<in> S x"
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

(* "pairwise" way of proving dominance using dominant2 *)
(* do we need UNIV here? *)
lemma dominant2_dominant: 
  fixes l1 :: "('a, 'b1, 'c :: Mergeable) lifting"
  assumes HDom : "dominant2 l1 l2 S X"
  shows "(LMap l1 f1) \<downharpoonleft> {LMap l1 f1, LMap l2 f2} X"
proof
  fix b :: 'c
  fix x :: 'a
  assume Xin : "x \<in> X"


end