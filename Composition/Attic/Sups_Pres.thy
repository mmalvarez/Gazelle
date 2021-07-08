theory Sups_Pres imports Lang_Comp
begin

(* TODO: relocate these definitions, to the extent that is even necessary. I don't think we
 * need this file anymore. *)

(* In sups_pres, we describe a notion of a set of functions "preserving suprema"
 * from their inputs to their outputs.
 * More concretely, "sups_pres Fs" states that for any nonempty, finite set of inputs Xs,
 * having a supremum s, then the following two suprema exist and are equal:
 * 1) the least upper bound of the set of outputs obtained by taking the "cross product":
      that is, the set containing f x for each f \<in> Fs, x \<in> Xs.
 * 2) the least upper bound of the set of outputs obtained by applying each f to the
      supremum of the inputs, s
 *
 * While this definition is a bit clunky, it has the key advantage that it enables us to work
 * over _sets_ of functions, avoiding tedious reasoning about repetition and permutation in
 * lists of functions. As can be seen in Lang_Comp, this definition implies a number of
 * rather nice and intuitive properties about the set Fs. Generally we will use sups_pres
 * as the specification of what it means for a set of functions to be able to be merged in
 * a well-defined way.
 *
 * I believe this may be related to the concept of continuity in traditional domain theory.
 *)


(* "Cross-product" between a set of functions (applied to) a set of inputs *)
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

(* The definition. See above for a gloss of what this means. *)
definition sups_pres :: 
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> bool" where
"sups_pres Fs =
  (\<forall> x syn s Xs .
    x \<in> Xs \<longrightarrow>
    finite Xs \<longrightarrow>
    is_sup Xs s \<longrightarrow>
    (\<exists> s' . is_sup ((\<lambda> f . f syn s) ` Fs) s' \<and>
       is_sup (scross ((\<lambda> f . f syn) ` Fs) Xs) s'))"


lemma sups_presI [intro] :
  assumes "\<And> x syn s Xs . x \<in> Xs \<Longrightarrow>
            finite Xs \<Longrightarrow>
            is_sup Xs s \<Longrightarrow>
            (\<exists> s' . is_sup ((\<lambda> f . f syn s) ` Fs) s' \<and> is_sup (scross ((\<lambda> f . f syn) ` Fs) Xs) s')"
  shows "sups_pres Fs"
  using assms unfolding sups_pres_def by blast

lemma sups_presD :
  assumes "sups_pres Fs"
  assumes "x \<in> Xs"
  assumes "finite Xs"
  assumes "is_sup Xs s"
  shows "(\<exists> s' . is_sup ((\<lambda> f . f syn s) ` Fs) s' \<and>
         is_sup (scross ((\<lambda> f . f syn) ` Fs) Xs) s')" using assms
  unfolding sups_pres_def 
  by blast

(* Some convenient properties about scross, in the spirit of relating it to
 * Isabelle's built-in notion of cross product of sets *)
lemma scross_subset :
  assumes HF : "Fs1 \<subseteq> Fs2"
  assumes HX : "Xs1 \<subseteq> Xs2"
  shows "scross Fs1 Xs1 \<subseteq> scross Fs2 Xs2"
proof
  fix res
  assume Hres : "res \<in> scross Fs1 Xs1"

  obtain f x where
    F : "f \<in> Fs1" and
    X : "x \<in> Xs1" and
    Res : "res = f x" using scross_inD[OF Hres] by blast

  show "res \<in> scross Fs2 Xs2"
  proof(rule scross_inI)
    show "f \<in> Fs2"
      using F HF by blast
    show "x \<in> Xs2"
      using X HX by blast
    show "res = f x" using Res by auto
  qed
qed

(* This alternate definition of scross makes it much easier to apply some of Isabelle's
 * built-in theorems about set finiteness and cardinality. *)
definition scross_alt :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" where
"scross_alt Fs Xs =
  (\<lambda> fx . (case fx of (f, x) \<Rightarrow> f x)) ` (Fs \<times> Xs)"

lemma scross_alt_eq :
  "scross_alt Fs Xs = scross Fs Xs"
  unfolding scross_def scross_alt_def
  by(auto)

lemma scross_finite :
  assumes HF : "finite Fs"
  assumes HX : "finite Xs"
  shows "finite (scross Fs Xs)" 
  unfolding sym[OF scross_alt_eq] scross_alt_def
  using finite_cartesian_product[OF HF HX]
  by blast

(* is this actually true? *)
lemma sups_pres_subset :
  fixes Fs :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set"
  assumes H : "sups_pres Fs"
  assumes Hfin : "finite Fs"
  assumes Hsub : "Fs' \<subseteq> Fs"
  assumes Hnemp : "f \<in> Fs'"
  shows "sups_pres Fs'"
proof(rule sups_presI)
  fix syn 
  fix Xs :: "'b set"
  fix el :: "'b"
  fix s :: "'b"

  assume H' : "is_sup Xs s"
  assume Hfin_Xs : "finite Xs"
  assume Hnemp_Xs : "el \<in> Xs"

  obtain Rest where Rest : "Fs' \<union> Rest = Fs" using Hsub by blast

  have Rfin : "finite Rest" using Rest Hfin by auto

  obtain s' where 
    S' : "is_sup ((\<lambda> f . f syn s) ` (Fs' \<union> Rest)) s'" and
    Conc' : "is_sup (scross ((\<lambda>f. f syn) ` (Fs' \<union> Rest)) Xs) s'" unfolding Rest
    using sups_presD[OF H Hnemp_Xs Hfin_Xs H', of syn]
    by blast

  have Subset' : "(\<lambda>f. f syn) ` Fs' \<subseteq> (\<lambda>f. f syn) ` Fs"
    unfolding sym[OF Rest] by blast

  have Subset_full : "(scross ((\<lambda>f. f syn) ` (Fs')) Xs)  \<subseteq> (scross ((\<lambda>f. f syn) ` (Fs' \<union> Rest)) Xs)"    
    using scross_subset[OF Subset', of Xs Xs]
    unfolding Rest
    by blast

  have Subset_s : "((\<lambda>f. f syn s) ` (Fs')) \<subseteq> ((\<lambda>f. f syn s) ` (Fs))"
    unfolding sym[OF Rest] by blast

  have Nemp_full : "(f syn el) \<in> scross ((\<lambda>f. f syn) ` Fs') Xs"
    using Hnemp Hnemp_Xs
    unfolding scross_def by auto

  have Nemp_s : "(f syn s) \<in> ((\<lambda>f. f syn s) ` (Fs'))"
    using Hnemp Hnemp_Xs
    unfolding scross_def by auto

  have Hfin' : "finite ((\<lambda>f. f syn) ` (Fs))"
    using Hfin by blast

  have Hfin'_s : "finite ((\<lambda> f . f syn s) ` Fs)"
    using Hfin by blast

  have Fin_full : "finite (scross ((\<lambda>f. f syn) ` (Fs)) Xs)"
    using scross_finite[OF Hfin' Hfin_Xs]
    by auto

  have Fin_s : "finite ((\<lambda>f. f syn s) ` (Fs))"
    using rev_finite_subset[OF Hfin'_s , of "((\<lambda>f. f syn s) ` Fs)"]
    unfolding sym[OF Rest]
    by(blast)

  have Sup_full' : "has_sup (scross ((\<lambda>f. f syn) ` Fs') Xs)" using
    has_sup_subset[OF _ _ Subset_full Nemp_full, of s'] Fin_full Conc' unfolding sym[OF Rest]
    by auto

  then obtain s'_full where S'_full : "is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) s'_full"
    unfolding has_sup_def by auto

  have Sup_s' : "has_sup ((\<lambda> f . f syn s) ` Fs')" using
    has_sup_subset[OF _ _ Subset_s Nemp_s, of s'] Fin_s S' unfolding sym[OF Rest]
    by auto

  then obtain s'_s where S'_s : "is_sup ((\<lambda> f . f syn s) ` Fs') s'_s"
    unfolding has_sup_def
    by auto

  have S_is_sup_extend : "is_sup (Xs \<union> {s}) s" sorry

  have Test : "is_sup (scross ((\<lambda>f. f syn) ` Fs') (Xs \<union> {s})) s'_full"
    sorry

  have Ub1 : "is_ub ((\<lambda> f . f syn s) ` Fs') s'_full"
  proof(rule is_ub_intro)
    fix z
    assume Z : "z \<in> (\<lambda>f. f syn s) ` Fs'"

    

    show "z <[ s'_full"
      using is_sup_unfold1[OF Test, of z]
      using Z
      unfolding scross_def
      by(auto)
  qed

  have Ub1_leq : "s'_s <[ s'_full"
    using is_sup_unfold2[OF S'_s Ub1] by auto

  have Ub2 : "is_ub (scross ((\<lambda>f. f syn) ` Fs') Xs) s'_s"
  proof(rule is_ub_intro)
    fix z

    assume Z : "z \<in> scross ((\<lambda>f. f syn) ` Fs') Xs"

    (* is this true?

       maybe we can try induction on the size of Rest? Or Xs?
       alternately, maybe we can obtain that Fs' and Rest each have LUB, and the LUB of the whole is equal
       to the LUB of the two LUBs.


ok, can we come up with a counterexample?

- suppose one of our functions in Rest overflows everything to Top
- so LUB of the entire thing is Top no matter what set of Xs we use
- however we could have a subset of arbitrary functions aside from this one
  - we don't actually know anything about this behavior. since arbitrary,
    they very well may not be sups_pres

    *)


(* so, we need a new abstraction for understanding when we can
merge multi-step things. 

(that is, make a statement about a sub-semantics execution compared to a full execution)
- one idea: sups_pres comparing part to whole?

*)

    show "z <[ s'_s"
      using is_sup_unfold1[OF S'_s]
      sorry
  qed

  have Ub2_leq : "s'_full <[ s'_s"
    using is_sup_unfold2[OF S'_full Ub2]
    by auto

  have Ub_eq : "s'_full = s'_s"
    using leq_antisym[OF Ub1_leq Ub2_leq]
    by auto

  have "is_sup ((\<lambda>f. f syn s) ` Fs') s'_s \<and>
        is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) s'_s"
    using Ub_eq S'_s S'_full
    by auto

  then show "\<exists>s'. is_sup ((\<lambda>f. f syn s) ` Fs') s' \<and>
             is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) s'"
    by blast
qed
(*
  show "has_sup (scross ((\<lambda>f. f syn) ` Fs') Xs)"
    using has_sup_subset[OF _ Supr Subset Nemp ] Fin unfolding Rest
    by auto
*)
qed

lemma sups_pres_pair :
  assumes Hf : "sups_pres {f1, f2}"
  assumes Hx : "has_sup {x1, x2}"
  shows "has_sup {f1 syn x1, f2 syn x2}"
proof-

  have "has_sup (scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2})"
    using sups_presD[OF Hf Hx, of x1 syn]
    by auto

  then obtain z where Z: "is_sup (scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2}) z"
    unfolding has_sup_def by auto

  have Scross_eq : 
    "(scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2}) =
      { f1 syn x1, f1 syn x2, f2 syn x1, f2 syn x2 }"
    unfolding scross_def by blast

  have Sub : "{f1 syn x1, f2 syn x2} \<subseteq> { f1 syn x1, f1 syn x2, f2 syn x1, f2 syn x2 }"
    by blast

  show "has_sup {f1 syn x1, f2 syn x2}"
    using has_sup_subset[OF _ Z, of "{f1 syn x1, f2 syn x2}" "f1 syn x1"]
    unfolding Scross_eq
    by blast
qed

lemma scross_singleton1 :
"scross {f} Xs = f ` Xs"
  unfolding scross_def
  by blast

lemma scross_singleton2 :
"scross Fs {x} = (\<lambda> f . f x) ` Fs"
  unfolding scross_def
  by blast


end