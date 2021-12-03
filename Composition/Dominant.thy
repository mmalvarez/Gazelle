theory Dominant imports Composition "../Lifter/Lifter" "Composition_Lifter"
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


(*
locale dominant2_sig =
  fixes l1 :: "('a1, 'b1, 'c :: {Pord, Okay}) lifting"
  fixes t1 :: "'a \<Rightarrow> 'a1"
  fixes l2 :: "('a2, 'b2, 'c) lifting"
  fixes t2 :: "'a \<Rightarrow> 'a2"
  fixes X :: "'a set"

locale dominant2 = dominant2_sig +
  assumes dominant2_out :
    "\<And> a1 a2 b x . x \<in> X \<Longrightarrow> b \<in> ok_S \<Longrightarrow> 
    LOut l2 (t2 x) a2 b = LOut l1 (t1 x) a1 b"
*)
(* dominant: for the given syntax x, f "dominates" set S if for all state inputs b,
 * f x b is the least upper bound of
 * applying each f' in S to x and b.
 *)
(* NB:
 * An arguably more natural definition would be to require f to be a UB instead of a SUP.
 * However, the difference probably isn't a big deal, and changing this
 * would require some changes to other proofs.
 *)
definition dominant ::
  " ('a, 'b, 'c :: {Pord, Okay}) lifting \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'c) set \<Rightarrow> 'a set \<Rightarrow> bool"
("_ _ \<downharpoonleft> _ _" [250, 252, 254])
where
"(l f \<downharpoonleft> S X) =
 (\<forall> b x . x \<in> X \<longrightarrow> b \<in> ok_S \<longrightarrow> 
   (\<exists> supr . is_sup ((\<lambda> g . g x b) ` S) supr \<and>
    LOut l x (f x b) = LOut l x supr))"

(* TODO: might be a good idea to have a special version of dominant for lifters.
 * Similar e.g. to ortho.
 *)

lemma dominantI [intro] :
  assumes "\<And> b x . x \<in> X \<Longrightarrow> b \<in> ok_S \<Longrightarrow> 
    (\<exists> supr . is_sup ((\<lambda> g . g x b) ` S) supr \<and>
    LOut l x (f x b) = LOut l x supr)"
  shows "(l f \<downharpoonleft> S X)" using assms
  unfolding dominant_def by auto

lemma dominantE [elim] :
  assumes "(l f \<downharpoonleft> S X)"
  assumes "x \<in> X"
  assumes "b \<in> ok_S"
  shows "(\<exists> supr . is_sup ((\<lambda> g . g x b) ` S) supr \<and>
    LOut l x (f x b) = LOut l x supr)" using assms
  unfolding dominant_def by auto

(* If sups_pres holds on a set
 * (I believe this hypothesis is needed to rule out badly-behaved sets that subvert the intuitive
 * meaning of dominant, though not 100% sure - TODO)
 * and f is dominant for some syntax x
 * then the result of running the merged semantics will exactly equal the result of f
 * on that syntax.
 *)

lemma dominant_pcomps :
  assumes Hpres : "sups_pres (set fs) (\<lambda> _ . ok_S)"
  assumes Hne : "z \<in> set fs"
  assumes H : "(l f \<downharpoonleft> (set fs) X)"
  assumes Xin : "x \<in> X"
  assumes Bin : "b \<in> ok_S"
  shows "LOut l x (pcomps fs x b) = LOut l x (f x b)"
proof-

  have B : "is_sup {b} b"
    using sup_singleton by auto

  have Hne' : "fs \<noteq> []"
    using Hne by auto


  have Sup1 : "is_sup (((\<lambda>f. f x b) ` set fs)) (pcomps fs x b)"
    using sups_pres_pcomps_sup'[OF Hpres Hne'] Bin B
    by auto

  have Rewrite1 : "(\<lambda>f. f b) ` (\<lambda>f. f x) ` set fs = (\<lambda> f . f x b) ` set fs"
    by blast

  have Sup2 : "is_sup ((\<lambda>f. f x b) ` set fs) (pcomps fs x b)"
    using Sup1
    unfolding scross_singleton2 Rewrite1
    by auto

  obtain supr where
    Sup2' : "is_sup ((\<lambda> f .  f x b) ` set fs) supr" "LOut l x supr = LOut l x (f x b)"
    using dominantE[OF H Xin Bin]
    by auto

  show ?thesis using is_sup_unique[OF Sup2 Sup2'(1)] Sup2'(2) by auto
qed

lemma dominant_pcomps_set :
  assumes Hpres : "sups_pres Fs (\<lambda> _ . ok_S)"
  assumes Hne : "z \<in> Fs"
  assumes H : "(l f \<downharpoonleft> Fs X)"
  assumes L : "set fs = Fs"
  assumes Xin: "x \<in> X"
  assumes Bin : "b \<in> ok_S"
  shows "LOut l x (pcomps fs x b) = LOut l x (f x b)"
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
(*
lemma dominant2_dominant: 
  fixes l1 :: "('a1, 'b1, 'c :: {Mergeable, Okay}) lifting"
  fixes l2 :: "('a2, 'b2, 'c) lifting"
  assumes HDom : "dominant2 l1 t1 l2 t2 X"
  shows "l1 (lift_map_s t1 l1 f1) \<downharpoonleft> {lift_map_s t1 l1 f1, lift_map_s t2 l2 f2} X"
proof
  fix b :: 'c
  fix x :: 'a
  assume Xin : "x \<in> X"
  assume Bin : "b \<in> ok_S"

  interpret D : dominant2 l1 t1 l2 t2 X
    using HDom.

  show "is_sup
            ((\<lambda>g. g x b) `
             {lift_map_s t1 l1 f1,
              lift_map_s t2 l2 f2})
            (lift_map_s t1 l1 f1 x b)"
  proof(rule is_supI)
    fix z

    assume "z \<in> (\<lambda>g. g x b) ` {lift_map_s t1 l1 f1,
              lift_map_s t2 l2 f2}"
    then consider (1) "z = lift_map_s t1 l1 f1 x b" | (2) "z = lift_map_s t2 l2 f2 x b"
      by auto

    then show "z <[ lift_map_s t1 l1 f1 x b"
    proof cases
      case 1
      then show ?thesis
        by(auto simp add: leq_refl)
    next
      case 2
      then show ?thesis
        using D.dominant_leq[OF Xin Bin]
        by(auto simp add: lift_map_s_def)
    qed
  next
    fix w

    assume Ub : "is_ub ((\<lambda>g. g x b) ` {lift_map_s t1 l1 f1,
             lift_map_s t2 l2 f2}) w"

    have S_eq : "((\<lambda>g. g x b) ` {lift_map_s t1 l1 f1,
             lift_map_s t2 l2 f2}) = {lift_map_s t1 l1 f1 x b, lift_map_s t2 l2 f2 x b}"
      by auto

    show "lift_map_s t1 l1 f1 x b <[ w"
      using is_ubE[OF Ub[unfolded S_eq], of "lift_map_s t1 l1 f1 x b"]
      by auto
  qed
qed
*)
lemma dominant_singleton :
  fixes f :: "'a \<Rightarrow> ('b :: {Mergeable, Okay}) \<Rightarrow> 'b"
  shows "l f \<downharpoonleft> {f} X"
proof
  fix b :: 'b
  fix x :: 'a
  assume "x \<in> X"

  have Conc1 : "is_sup ((\<lambda>g. g x b) ` {f}) (f x b)"
    using sup_singleton[of "f x b"]
    by auto

  have Conc2 : "LOut l x (f x b) = LOut l x (f x b)"
    by simp

  show "\<exists>supr.
              is_sup ((\<lambda>g. g x b) ` {f}) supr \<and>
              LOut l x (f x b) = LOut l x supr"
    using Conc1 Conc2 by auto
qed

(* TODO: do we want to use dominant2 instead here (in the hypothesis)?
 * Probably doesn't matter.
 *)
(*
 * NB: with a weaker definition of dominant, we could relax the requirement
 * that f \<in> Fs,
 *)

(* need a new lifting correctness condition:
 * if the following hold on 2 pieces of data
  - has a least uppeer bound, which is valid
  - LOut of the two are equal

 * then LOut of the least upper bound is equal to that same value.
*)

lemma dominant_pairwise :
  fixes Fs :: "('a \<Rightarrow> ('b :: {Mergeable, Okay, Pordpsc}) \<Rightarrow> 'b) set"
  assumes Hfin : "finite Fs"
  assumes HFs_f : "f \<in> Fs"
  assumes Pres : "sups_pres Fs (\<lambda> s . ok_S )"
  assumes H: "\<And> f' . f' \<in> Fs \<Longrightarrow> l f \<downharpoonleft> {f', f} X"
  shows "l f \<downharpoonleft> Fs X"
proof
  fix b :: 'b
  fix x :: 'a

  assume Xin : "x \<in> X"
  assume Bin : "b \<in> ok_S"

  have Fin' : "finite ((\<lambda>g. g x b) ` Fs)"
    using Hfin
    by auto


  have Pairwise : "(\<And> w1 w2 . w1 \<in> (\<lambda>g. g x b) ` Fs \<Longrightarrow> w2 \<in> (\<lambda>g. g x b) ` Fs \<Longrightarrow> has_sup {w1, w2}) "
  proof-
    fix w1 w2 :: 'b
    assume Hw1 : "w1 \<in> (\<lambda>g. g x b) ` Fs"

    then obtain w1i f1 where F1 : "w1 = f1 x w1i" "f1 \<in> Fs"
      by auto

    assume Hw2 : "w2 \<in> (\<lambda>g. g x b) ` Fs"

    then obtain w2i f2 where F2 : "w2 = f2 x w2i" "f2 \<in> Fs"
      by auto

    obtain sup1 where Sup1 : "is_sup ((\<lambda>g. g x b) ` {f1, f}) sup1" "LOut l x (f x b) = LOut l x sup1"
      using dominantE[OF H[OF F1(2)] Xin Bin]
      by auto

    obtain sup2 where Sup1 : "is_sup ((\<lambda>g. g x b) ` {f2, f}) sup2" "LOut l x (f x b) = LOut l x sup2"
      using dominantE[OF H[OF F2(2)] Xin Bin]
      by auto

(* YOU ARE HERE
 * we need to figure out exactly what the issue is with this in terms of
 * what pairwise fact we need that we may not have
 * (or if the theorem just isn't true....)
*)
    show "has_sup {w1, w2}"
      using dominantE[OF H[OF F1(2)] Xin Bin]


  show "\<exists>supr.
              is_sup ((\<lambda>g. g x b) ` Fs) supr \<and>
              LOut l x (f x b) = LOut l x supr"
    using sup_finite_pairwise[OF Fin' imageI[OF HFs_f]]

  show
    "is_sup ((\<lambda>g. g x b) ` Fs) (f x b)"
  proof(rule is_supI)
    fix z

    assume Z: "z \<in> (\<lambda>g. g x b) ` Fs"

    then obtain zf where Zf : "zf \<in> Fs" "zf x b = z"
      by auto

    have Zf_dom : "f \<downharpoonleft> {zf} X"
      using H[OF Zf(1)]
      by auto

    have Zf_sup : "is_sup ((\<lambda>g. g x b) ` {zf}) (f x b)"
      using dominantE[OF Zf_dom Xin Bin]
      by auto
      
    then have Conc' :
      "zf x b <[ f x b"
      using is_supD1[OF Zf_sup, of "zf x b"]
      by auto

    then show "z <[ f x b"
      using Zf(2)
      by auto
  next
    fix w

    assume Ub : "is_ub ((\<lambda>g. g x b) ` Fs) w"


    have HFs_f' : "f x b \<in> (\<lambda>g. g x b) ` Fs"
      using imageI[OF HFs_f]
      by auto

    show "f x b <[ w"
      using is_ubE[OF Ub HFs_f']
      by auto
  qed
qed

end