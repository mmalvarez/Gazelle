theory Dominant imports Composition "../Lifter/Lifter" "Composition_Lifter" "../Lifter/Toggle"
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
(*
(\<forall> b . is_sup ((\<lambda> g . g x b) ` S) (f x b))"
*)
definition dominant ::
  "('a \<Rightarrow> 'c \<Rightarrow> ('c :: Pord_Weak)) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'c) set \<Rightarrow> 'a set \<Rightarrow> bool"
("_ \<downharpoonleft> _ _" [250, 252, 254])
where
"(f \<downharpoonleft> S X) =
  (\<forall> x b . x \<in> X \<longrightarrow>
   (is_sup ((\<lambda> g . g x b) ` S) (f x b)))"

(* TODO: might be a good idea to have a special version of dominant for lifters.
 * Similar e.g. to ortho.
 *)

lemma dominantI [intro] :
  assumes "\<And> b x . x \<in> X \<Longrightarrow> 
    (is_sup ((\<lambda> g . g x b) ` S) (f x b))"
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
  assumes Hpres : "sups_pres (set fs) (\<lambda> _ . ok_S)"
  assumes Hne : "z \<in> set fs"
  assumes H : "(f \<downharpoonleft> (set fs) X)"
  assumes Xin : "x \<in> X"
  assumes Bin : "b \<in> ok_S"
  shows "(pcomps fs x b) = (f x b)"
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

  have Sup2' : "is_sup ((\<lambda> f .  f x b) ` set fs) (f x b)"
    using dominantE[OF H Xin]
    by auto

  show ?thesis using is_sup_unique[OF Sup2 Sup2'] Sup2' by auto
qed

lemma dominant_pcomps_set :
  assumes Hpres : "sups_pres Fs (\<lambda> _ . ok_S)"
  assumes Hne : "z \<in> Fs"
  assumes H : "(f \<downharpoonleft> Fs X)"
  assumes L : "set fs = Fs"
  assumes Xin: "x \<in> X"
  assumes Bin : "b \<in> ok_S"
  shows "(pcomps fs x b) = (f x b)"
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
  fixes f :: "'a \<Rightarrow> ('b :: {Mergeable}) \<Rightarrow> 'b"
  shows "f \<downharpoonleft> {f} X"
proof
  fix b :: 'b
  fix x :: 'a
  assume "x \<in> X"

  show "is_sup ((\<lambda>g. g x b) ` {f}) (f x b)"
    using sup_singleton[of "f x b"]
    by auto
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
  fixes Fs :: "('a \<Rightarrow> ('b :: {Pord}) \<Rightarrow> 'b) set"
  assumes Hfin : "finite Fs"
  assumes HFs_f : "f \<in> Fs"
  assumes H: "\<And> f' . f' \<in> Fs \<Longrightarrow> f \<downharpoonleft> {f', f} X"
  shows "f \<downharpoonleft> Fs X"
proof
  fix b :: 'b
  fix x :: 'a

  assume Xin : "x \<in> X"

  have Fin' : "finite ((\<lambda>g. g x b) ` Fs)"
    using Hfin
    by auto

  show "is_sup ((\<lambda>g. g x b) ` Fs)
            (f x b)"
  proof(rule is_supI)
    fix y
    assume Y: "y \<in> (\<lambda> g . g x b) ` Fs"

    then obtain f0 where F0 : "y = f0 x b" "f0 \<in> Fs"
      by auto

    have Dom: "f \<downharpoonleft> {f0, f} X"
      using H[OF F0(2)]
      by auto

    have Supr : "is_sup ((\<lambda>g. g x b) ` {f0, f}) (f x b)"
      using dominantE[OF Dom Xin]
      by auto

    show "y <[ f x b"
      using is_supD1[OF Supr, of "f0 x b"] F0
      by auto
  next
    fix ub
    assume Ub : "is_ub ((\<lambda>g. g x b) ` Fs) ub"

    show "f x b <[ ub"
      using is_ubE[OF Ub imageI[OF HFs_f]]
      by auto
  qed
qed

lemma dominant_toggle :
  assumes Valid : "lifting_valid l1 S1"
  assumes Toggle : "\<And> s . s \<in> X \<Longrightarrow> t1 s \<and> \<not> (t2 s)"
  shows  "(lift_map_t_s l'1 l1 t1 f1) \<downharpoonleft> {toggle t2 f2, (lift_map_t_s l'1 l1 t1 f1)} X"
proof
  fix b
  fix x :: 'd
  assume Xin : "x \<in> X"

  interpret V : lifting_valid l1 S1
    using Valid.

  have T1 : "t1 x" and T2 : "\<not> t2 x"
    using Toggle[OF Xin]
    by auto

  have Res1 : 
    "lift_map_t_s l'1 l1 t1 f1 x b = LUpd l1 (l'1 x) (f1 (l'1 x) (LOut l1 (l'1 x) b)) b"
    using T1
    by(auto simp add: lift_map_t_s_def lift_map_s_def)

  have Res2 : "toggle t2 f2 x b = b"
    using T2
    by(auto simp add: toggle_def)

  have Conc' : "toggle t2 f2 x b <[ lift_map_t_s l'1 l1 t1 f1 x b"
    using V.get_put
    unfolding Res1 Res2
    by auto

  show "is_sup
            ((\<lambda>g. g x b) `
             {toggle t2 f2, lift_map_t_s l'1 l1 t1 f1})
            (lift_map_t_s l'1 l1 t1 f1 x b)"
    using is_sup_pair[OF Conc']
    by auto
qed

lemma dominant_subset :
  assumes Dom : "f \<downharpoonleft> Fs X"
  assumes Fs' : "Fs' \<subseteq> Fs"
  assumes F_in : "f \<in> Fs'"
  shows "f \<downharpoonleft> Fs' X"
proof
  fix x b
  assume Xin : "x \<in> X"

  have Sup : "is_sup ((\<lambda>g. g x b) ` Fs) (f x b)"
    using dominantE[OF Dom Xin]
    by auto

  show "is_sup ((\<lambda>g. g x b) ` Fs') (f x b)"
  proof(rule is_supI)
    fix w

    assume W: "w \<in> (\<lambda>g. g x b) ` Fs'"

    then have W' : "w \<in> (\<lambda>g. g x b) ` Fs"
      using Fs'
      by auto

    show "w <[ f x b"
      using is_supD1[OF Sup W']
      by auto
  next
    fix ub

    assume Ub : "is_ub ((\<lambda>g. g x b) ` Fs') ub"

    show "f x b <[ ub"
      using is_ubE[OF Ub imageI[OF F_in]]
      by auto
  qed
qed

lemma dominant_toggles' :
  
  assumes Valid : "lifting_valid l1 S1"
  assumes Fs_fin : "finite (Fs :: (_ \<Rightarrow> (_ :: Mergeable) \<Rightarrow> _) set)"
  assumes Fs_sub : "Fs_sub \<subseteq> Fs"
  assumes Fs_f1 : "lift_map_t_s l'1 l1 t1 f1 \<in> Fs_sub"
  assumes Toggle1 : "\<And> s . s \<in> X \<Longrightarrow> t1 s"
  assumes Toggles : "\<And> f . f \<in> Fs \<Longrightarrow> f \<noteq> lift_map_t_s l'1 l1 t1 f1 \<Longrightarrow>
    (\<exists> tg g . f = toggle tg g \<and> (\<forall> s . s \<in> X \<longrightarrow> \<not> tg s))"
  shows  "(lift_map_t_s l'1 l1 t1 f1) \<downharpoonleft> Fs_sub X"
proof-

  interpret V : lifting_valid l1 S1
    using Valid.

  obtain c where C: "c = card Fs"
    by auto

(* TODO: this could just be a case-split instead of induction lol *)
  show "(lift_map_t_s l'1 l1 t1 f1) \<downharpoonleft> Fs_sub X"
    using Fs_fin Fs_f1 Toggle1 Toggles C Fs_sub
  proof(induction c arbitrary: Fs Fs_sub)
  case 0
    then show ?case by auto
  next
    case (Suc c')
    then show ?case
    proof(cases c')
      case Z' : 0

      then have "card Fs = Suc 0"
        using Suc.prems
        by auto

      then obtain f where F:
        "Fs = {f}"
        unfolding card_1_singleton_iff
        by auto
        
      then have "Fs = {lift_map_t_s l'1 l1 t1 f1}"
        using  Suc.prems  by auto

      then have "Fs_sub = {lift_map_t_s l'1 l1 t1 f1}"
        using Suc.prems by auto

      then show ?thesis using dominant_singleton[of "lift_map_t_s l'1 l1 t1 f1" X]
        by auto
    next
      case Suc' : (Suc c'')

      obtain Fs_nf where Fs_nf : "Fs_nf = Fs - {lift_map_t_s l'1 l1 t1 f1}"
        by auto

      then have Fs_nf_fin : "finite Fs_nf"
        using Suc.prems by auto

      have F1_in : "lift_map_t_s l'1 l1 t1 f1 \<in> Fs"
        using Suc.prems
        by auto

      have Fs_n'f_cd : "card Fs_nf = c'"
        using card_Diff_singleton[OF Suc.prems(1) F1_in] 
        Suc.prems(5) Suc'
        unfolding Fs_nf
        by(auto)

      then obtain f2 where F2 :
        "f2 \<in> Fs_nf"
        using Suc' card_gt_0_iff[of Fs_nf]
        by auto

      then have F2_neq : "f2 \<noteq> lift_map_t_s l'1 l1 t1 f1"
        using Fs_nf by auto

      have F2_in_Fs : "f2 \<in> Fs"
        using F2 Fs_nf by auto

      obtain Fs_tl where Fs_tl : "Fs_tl = Fs - {f2}"
        by auto

      have Fs_tl_cd : "card Fs_tl = c'"
        using card_Diff_singleton[OF Suc.prems(1) F2_in_Fs] 
        Suc.prems(5) Suc'
        unfolding Fs_tl
        by(auto)

      have F_fs_tl : "lift_map_t_s l'1 l1 t1 f1 \<in> Fs_tl"
        using F1_in F2_neq Fs_tl
        by auto

      show ?thesis
      proof(rule dominant_pairwise)
        show "finite Fs_sub"
          using finite_subset Suc.prems
          by auto
      next
        show "lift_map_t_s l'1 l1 t1 f1 \<in> Fs_sub"
          using Suc.prems
          by(auto)
      next
        fix f3
        assume F3 : "f3 \<in> Fs_sub"

        have F3_in' : "f3 \<in> Fs"
          using Suc.prems F3
          by auto

        show "lift_map_t_s l'1 l1 t1 f1 \<downharpoonleft> {f3, lift_map_t_s l'1 l1 t1 f1} X"
        proof(cases "f3 = lift_map_t_s l'1 l1 t1 f1")
          case True

          show ?thesis
            using dominant_singleton[of "lift_map_t_s l'1 l1 t1 f1"]
            unfolding True
            by auto
        next
          case False


          then obtain tg g where F3_toggle :
            "f3 = toggle tg g" "\<And> s . s \<in> X \<Longrightarrow> \<not> tg s"
            using Suc.prems(4)[OF F3_in']
            by auto
  
          have Toggles : "(\<And>s. s \<in> X \<Longrightarrow> t1 s \<and> \<not> tg s)"
            using F3_toggle Suc.prems(3)
            by auto
  
          show "lift_map_t_s l'1 l1 t1 f1 \<downharpoonleft> {f3, lift_map_t_s l'1 l1 t1 f1} X"
            using dominant_toggle[OF Valid Toggles, of X id]
            unfolding F3_toggle(1)
            by(auto)
        qed
      qed
    qed
  qed
qed

lemma dominant_toggles :
  assumes Valid : "lifting_valid l1 S1"
  assumes Fs_fin : "finite (Fs :: (_ \<Rightarrow> (_ :: Mergeable) \<Rightarrow> _) set)"
  assumes Fs_f1 : "lift_map_t_s l'1 l1 t1 f1 \<in> Fs"
  assumes Toggle1 : "\<And> s . s \<in> X \<Longrightarrow> t1 s"
  assumes Toggles: "\<And> f . f \<in> Fs \<Longrightarrow> f \<noteq> lift_map_t_s l'1 l1 t1 f1 \<Longrightarrow>
    (\<exists> tg g . f = toggle tg g \<and> (\<forall> s . s \<in> X \<longrightarrow> \<not> tg s))"
  shows  "(lift_map_t_s l'1 l1 t1 f1) \<downharpoonleft> Fs X"
proof-

  show "lift_map_t_s l'1 l1 t1 f1 \<downharpoonleft> Fs X"
    using dominant_toggles'[OF Valid Fs_fin _ Fs_f1 Toggle1 Toggles]
    by blast
qed

lemma dominant_toggles2 :
  assumes Valid : "lifting_valid l1 S1"
  assumes Fs_fin : "finite (Fs :: (_ \<Rightarrow> (_ :: Mergeable) \<Rightarrow> _) set)"
  assumes Fs_f1 : "lift_map_t_s l'1 l1 t1 f1 \<in> Fs"
  assumes Toggle1 : "\<And> s . s \<in> X \<Longrightarrow> t1 s"
  assumes Toggles: "\<And> f s z . f \<in> Fs \<Longrightarrow> f s z \<noteq> lift_map_t_s l'1 l1 t1 f1 s z \<Longrightarrow>
    (\<exists> tg g . f = toggle tg g \<and> (\<forall> s . s \<in> X \<longrightarrow> \<not> tg s))"
  shows  "(lift_map_t_s l'1 l1 t1 f1) \<downharpoonleft> Fs X"
proof-
  have Toggles' : "\<And> f . f \<in> Fs \<Longrightarrow> f  \<noteq> lift_map_t_s l'1 l1 t1 f1 \<Longrightarrow>
    (\<exists> tg g . f = toggle tg g \<and> (\<forall> s . s \<in> X \<longrightarrow> \<not> tg s))"
  proof-
    fix f
    assume Fin : "f \<in> Fs"
    assume Neq : "f \<noteq> lift_map_t_s l'1 l1 t1 f1"

    then obtain s  where Neq' : "f s  \<noteq> lift_map_t_s l'1 l1 t1 f1 s "
      by(auto)

    then obtain z where Neq'' : "f s z \<noteq> lift_map_t_s l'1 l1 t1 f1 s z"
      by auto

    then show "\<exists>tg g. f = toggle tg g \<and> (\<forall>s. s \<in> X \<longrightarrow> \<not> tg s)"
      using Toggles[OF Fin Neq'']
      by auto
  qed

  show "lift_map_t_s l'1 l1 t1 f1 \<downharpoonleft> Fs X"
    using dominant_toggles'[OF Valid Fs_fin _ Fs_f1 Toggle1 Toggles']
    by blast
qed


lemma dominant_toggle' :
  assumes Valid : "lifting_valid l1 S1"
  assumes Toggle : "\<And> s . s \<in> X \<Longrightarrow> t1 (l'1 s) \<and> \<not> (t2 (l'2 s))"
  shows  "(lift_map_st_s l'1 l1 t1 f1) \<downharpoonleft> {(lift_map_st_s l'2 l2 t2 f2), (lift_map_st_s l'1 l1 t1 f1)} X"
proof
  fix b
  fix x :: 'd
  assume Xin : "x \<in> X"

  interpret V : lifting_valid l1 S1
    using Valid.

  have T1 : "t1 (l'1 x)" and T2 : "\<not> t2 (l'2 x)"
    using Toggle[OF Xin]
    by auto

  have Res1 : 
    "lift_map_st_s l'1 l1 t1 f1 x b = LUpd l1 (l'1 x) (f1 (l'1 x) (LOut l1 (l'1 x) b)) b"
    using T1
    by(auto simp add: lift_map_st_s_def lift_map_s_def)

  have Res2 : "lift_map_st_s l'2 l2 t2 f2 x b = b"
    using T2
    by(auto simp add: lift_map_st_s_def)

  have Conc' : "lift_map_st_s l'2 l2 t2 f2 x b <[ lift_map_st_s l'1 l1 t1 f1 x b"
    using V.get_put
    unfolding Res1 Res2
    by auto

  show "is_sup
            ((\<lambda>g. g x b) `
             {lift_map_st_s l'2 l2 t2 f2, lift_map_st_s l'1 l1 t1 f1})
            (lift_map_st_s l'1 l1 t1 f1 x b)"
    using is_sup_pair[OF Conc']
    by auto
qed


end