theory LifterM
imports Lifter Lifter_Instances LifterX "../Mergeable/Mergeable_Facts"
begin

definition LMap ::
  "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"LMap l f s b =
  LUpd l s (f s (LOut l s b)) b"

declare LMap_def [simp]

(* idea: mapping preserves sups. first, we have the single-lifting case. *)
definition lifting_validm_weak ::
  "('x, 'a, 'b :: {Pord, Okay}) lifting \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validm_weak l S =
 ((lifting_validx_weak l S) \<and> 
  (\<forall> v V supr f s . v \<in> V \<longrightarrow> V \<subseteq> S s \<longrightarrow> is_sup V supr \<longrightarrow> supr \<in> S s \<longrightarrow> is_sup (LMap l f s ` V) (LMap l f s supr)))"

definition lifting_validm_weakb ::
  "('x, 'a, 'b :: {Pordb, Okay}) lifting \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validm_weakb l S =
 ((lifting_validx_weakb l S) \<and> 
  (\<forall> v V supr f s . v \<in> V \<longrightarrow> V \<subseteq> S s \<longrightarrow> is_sup V supr \<longrightarrow> supr \<in> S s \<longrightarrow> is_sup (LMap l f s ` V) (LMap l f s supr)) \<and>
  (\<forall> s . \<bottom> \<notin> S s))"


(* TODO: need membership in S? *)
lemma lifting_validm_weakI :
  assumes "lifting_validx_weak l S"
  assumes "\<And> v V supr f s . 
         v \<in> V \<Longrightarrow>
         V \<subseteq> S s \<Longrightarrow>
         is_sup V supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup (LMap l f s ` V) (LMap l f s supr)"
  shows "lifting_validm_weak l S"
  using assms 
  by(auto simp add: lifting_validm_weak_def)

lemma lifting_validm_weakDV :
  assumes "lifting_validm_weak l S" 
  shows "lifting_validx_weak l S"
  using assms by (auto simp add: lifting_validm_weak_def)

lemma lifting_validm_weakDM :
  assumes "lifting_validm_weak l S" 
  assumes "v \<in> V"
  assumes "V \<subseteq> S s" 
  assumes "supr \<in> S s"
  assumes "is_sup V supr"
  shows "is_sup (LMap l f s ` V) (LMap l f s supr)"
  using assms by (auto simp add: lifting_validm_weak_def)

lemma lifting_validm_weakbI :
  assumes "lifting_validx_weakb l S"
  assumes "\<And> v V supr f s . 
         v \<in> V \<Longrightarrow>
         V \<subseteq> S s \<Longrightarrow>
         is_sup V supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup (LMap l f s ` V) (LMap l f s supr)"
  assumes "\<And> s . \<bottom> \<notin> S s"
  shows "lifting_validm_weakb l S"
  using assms 
  by(auto simp add: lifting_validm_weakb_def)

lemma lifting_validm_weakbDV :
  assumes "lifting_validm_weakb l S" 
  shows "lifting_validx_weakb l S"
  using assms by (auto simp add: lifting_validm_weakb_def)

lemma lifting_validm_weakbDM :
  assumes "lifting_validm_weakb l S" 
  assumes "v \<in> V"
  assumes "V \<subseteq> S s" 
  assumes "supr \<in> S s"
  assumes "is_sup V supr"
  shows "is_sup (LMap l f s ` V) (LMap l f s supr)"
  using assms by (auto simp add: lifting_validm_weakb_def)

lemma lifting_validm_weakbDB :
  assumes "lifting_validm_weakb l S" 
  shows "\<bottom> \<notin> S s"
  using assms
  by(auto simp add: lifting_validm_weakb_def)

(* TODO: do we only need the finite case? if so we could just prove this for pairs
 and then induct on set size... *)

(* TODO *)
(*
lemma lifting_validm_weakDM' :
  assumes H : "lifting_validm_weak l S"
  assumes H1 : "x1 \<in> S s" 
  assumes H2 : "x2 \<in> S s"
  assumes Hsup_in : "supr \<in> S s"
  assumes Hfin : "finite (S s)"
  assumes Hsup : "is_sup Xs supr"
  shows "is_sup (LMap l f s ` Xs) (LMap l f s supr)"
  sorry  
*)
(* TODO: fix the others. *)
(* old version, says something different that we probably don't want *)
(*
definition lifting_validm_weak ::
  "('x, 'a, 'b :: {Pord, Okay}) lifting \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validm_weak l S =
 ((lifting_validx_weak l S) \<and>
  (\<forall> s b1 b2 f . b1 \<in> S s \<longrightarrow> b2 \<in> S s \<longrightarrow>
     b1 <[ b2 \<longrightarrow> 
     LUpd l s (f s (LOut l s b1)) b1 <[ LUpd l s (f s (LOut l s b2)) b2 ))"

lemma lifting_validm_weakI :
  assumes "lifting_validx_weak l S"
  assumes "\<And> s b1 b2 f . b1 \<in> S s \<Longrightarrow> b2 \<in> S s \<Longrightarrow>
     b1 <[ b2  \<Longrightarrow>
     LUpd l s (f (LOut l s b1)) b1 <[ LUpd l s (f (LOut l s b2)) b2 "
  shows "lifting_validm_weak l S"
  using assms 
  by(auto simp add: lifting_validm_weak_def)

lemma lifting_validm_weakDV :
  assumes "lifting_validm_weak l S" 
  shows "lifting_validx_weak l S"
  using assms by (auto simp add: lifting_validm_weak_def)

lemma lifting_validm_weakDM :
  assumes "lifting_validm_weak l S" 
  assumes "b1 \<in> S s" 
  assumes "b2 \<in> S s"
  assumes "b1 <[ b2"
  shows "LUpd l s (f s (LOut l s b1)) b1 <[ LUpd l s (f s (LOut l s b2)) b2"
  using assms by (auto simp add: lifting_validm_weak_def)
*)
definition lifting_validm ::
  "('x, 'a, 'b :: {Pord, Okay}) lifting \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validm l S =
 ((lifting_validx l S) \<and> 
  (\<forall> x1 x2 supr f s . x1 \<in> S s \<longrightarrow> x2 \<in> S s \<longrightarrow> is_sup {x1, x2} supr \<longrightarrow> supr \<in> S s \<longrightarrow> is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)))"

(* TODO: need membership in S? *)
lemma lifting_validmI :
  assumes "lifting_validx l S"
  assumes "\<And> x1 x2 supr f s . 
         x1 \<in> S s \<Longrightarrow> x2 \<in> S s \<Longrightarrow>
         is_sup {x1, x2} supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)"
  shows "lifting_validm l S"
  using assms 
  by(auto simp add: lifting_validm_def)

lemma lifting_validmDV :
  assumes "lifting_validm l S" 
  shows "lifting_validx l S"
  using assms by (auto simp add: lifting_validm_def)

lemma lifting_validmDM :
  assumes "lifting_validm l S" 
  assumes "x1 \<in> S s" 
  assumes "x2 \<in> S s"
  assumes "is_sup {x1, x2} supr"
  assumes "supr \<in> S s"
  shows "is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)"
  using assms by (auto simp add: lifting_validm_def)

lemma lifting_validmDM' :
  assumes H : "lifting_validm l S"
  assumes H1 : "x1 \<in> S s" 
  assumes H2 : "x2 \<in> S s"
  assumes Hfin : "finite (S s)"
  assumes Hsup : "is_sup Xs supr"
  assumes "supr \<in> S s"
  shows "is_sup (LMap l f s ` Xs) (LMap l f s supr)"
  sorry  

(* TODO *)

(*
definition lifting_validm_weakb ::
  "('x, 'a, 'b :: {Pordb, Okay}) lifting \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validm_weakb l S =
 ((lifting_validx_weakb l S) \<and> 
  (\<forall> x1 x2 supr f s . x1 \<in> S s \<longrightarrow> x2 \<in> S s \<longrightarrow> is_sup {x1, x2} supr \<longrightarrow> supr \<in> S s \<longrightarrow> is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)))"
*)
(* TODO: need membership in S? *)
(*
lemma lifting_validm_weakbI :
  assumes "lifting_validx_weakb l S"
  assumes "\<And> x1 x2 supr f s . 
         x1 \<in> S s \<Longrightarrow> x2 \<in> S s \<Longrightarrow>
         is_sup {x1, x2} supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)"
  shows "lifting_validm_weakb l S"
  using assms 
  by(auto simp add: lifting_validm_weakb_def)

lemma lifting_validm_weakbDV :
  assumes "lifting_validm_weakb l S" 
  shows "lifting_validx_weakb l S"
  using assms by (auto simp add: lifting_validm_weakb_def)

lemma lifting_validm_weakbDM :
  assumes "lifting_validm_weakb l S" 
  assumes "x1 \<in> S s" 
  assumes "x2 \<in> S s"
  assumes "is_sup {x1, x2} supr"
  assumes "supr \<in> S s"
  shows "is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)"
  using assms by (auto simp add: lifting_validm_weakb_def)

(* TODO *)
lemma lifting_validm_weakbDM' :
  assumes H : "lifting_validm_weakb l S"
  assumes H1 : "x1 \<in> S s" 
  assumes H2 : "x2 \<in> S s"
  assumes Hfin : "finite (S s)"
  assumes Hsup : "is_sup Xs supr"
  assumes "supr \<in> S s"
  shows "is_sup (LMap l f s ` Xs) (LMap l f s supr)"
  sorry  
*)
definition lifting_validmb ::
  "('x, 'a, 'b :: {Pordb, Okay}) lifting \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validmb l S =
 ((lifting_validxb l S) \<and> 
  (\<forall> x1 x2 supr f s . x1 \<in> S s \<longrightarrow> x2 \<in> S s \<longrightarrow> is_sup {x1, x2} supr \<longrightarrow> supr \<in> S s \<longrightarrow> is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)))"

(* TODO: need membership in S? *)
lemma lifting_validmbI :
  assumes "lifting_validxb l S"
  assumes "\<And> x1 x2 supr f s . 
         x1 \<in> S s \<Longrightarrow> x2 \<in> S s \<Longrightarrow>
         is_sup {x1, x2} supr \<Longrightarrow> supr \<in> S s \<Longrightarrow> is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)"
  shows "lifting_validmb l S"
  using assms 
  by(auto simp add: lifting_validmb_def)

lemma lifting_validmbDV :
  assumes "lifting_validmb l S" 
  shows "lifting_validxb l S"
  using assms by (auto simp add: lifting_validmb_def)

lemma lifting_validmbDM :
  assumes "lifting_validmb l S" 
  assumes "x1 \<in> S s" 
  assumes "x2 \<in> S s"
  assumes "is_sup {x1, x2} supr"
  assumes "supr \<in> S s"
  shows "is_sup {LMap l f s x1, LMap l f s x2} (LMap l f s supr)"
  using assms by (auto simp add: lifting_validmb_def)

(* TODO *)
lemma lifting_validmbDM' :
  assumes H : "lifting_validmb l S"
  assumes H1 : "x1 \<in> S s" 
  assumes H2 : "x2 \<in> S s"
  assumes Hfin : "finite (S s)"
  assumes Hsup : "is_sup Xs supr"
  assumes Hsup_in : "supr \<in> S s"
  shows "is_sup (LMap l f s ` Xs) (LMap l f s supr)"
  sorry  

(* TODO: show the rest of these for the liftings we care about. *)

(* TODO: need a separate notion for triv_l *)
lemma triv_l_validm_weak :
  shows "lifting_validm_weak (triv_l) (\<lambda> _ . UNIV)"
proof(rule lifting_validm_weakI)
  show "lifting_validx_weak triv_l (\<lambda>_. UNIV)" sorry
next
  fix v :: "'b md_triv"
  fix V 
  fix supr :: "'b md_triv"
  fix s 
  fix f

  assume Nemp : "v \<in> V"
  assume H : "is_sup V supr"

  show "is_sup (LMap triv_l f s ` V) (LMap triv_l f s supr)"
  proof(rule is_supI)
    fix x

    assume "x \<in> LMap triv_l f s ` V"

    then obtain x0 where X0 : "x0 \<in> V" "LMap triv_l f s x0 = x"
      by(auto)

    obtain x0' where X0' : "x0 = mdt x0'"
      by(cases x0; auto)

    obtain supr' where Supr' : "supr = mdt supr'"
      by(cases supr; auto)

    have Eq : "x0' = supr'"
      using is_supD1[OF H X0(1)] X0' Supr'
      by(auto simp add: triv_pleq)

    show "x <[ LMap triv_l f s supr"
      using X0' X0 Eq Supr'
      by(auto simp add: triv_pleq)
  next
    fix y
    assume Ub : "is_ub (LMap triv_l f s ` V) y"

    obtain y' where Y' : "y = mdt y'" by(cases y; auto)

    obtain v' where V' : "v = mdt v'" by(cases v; auto)

    have Eq1 : "y = LMap triv_l f s v"
      using is_ubE[OF Ub, of "LMap triv_l f s v"] Nemp
      by(auto simp add: triv_pleq)

    have  "supr = v"
      using is_supD1[OF H Nemp] by(auto simp add: triv_pleq)

    hence Eq2 : "LMap triv_l f s supr = LMap triv_l f s v" by simp

    show "LMap triv_l f s supr <[ y"
      using Eq1 Eq2
      by(simp add: triv_pleq)
  qed
qed

lemma is_sup_pair :
  assumes "a <[ b"
  shows "is_sup {a, b} b" using assms
  by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

(* TODO: do we actually need set restrictions? *)
lemma option_l_validm_weakb :
  fixes l :: "('a, 'b, ('c :: {Okay, Pord})) lifting"
  assumes H : "lifting_validm_weak l S"
  shows "lifting_validm_weakb (option_l l) (option_l_S S)"
proof(rule lifting_validm_weakbI)
  show "lifting_validx_weakb (option_l l) (option_l_S S)" sorry
next
  fix V
  fix s 
  fix v supr :: "'c option"
  fix f

  assume Nemp : "v \<in> V"
  assume V_valid : "V \<subseteq> option_l_S S s"

  assume Hsup : "is_sup V supr"
  assume Hsup_in : "supr \<in> option_l_S S s"

  obtain supr' where Supr' : "supr = Some supr'" "supr' \<in> S s"
    using V_valid Hsup_in by(auto simp add: option_l_S_def)

  show "is_sup (LMap (option_l l) f s ` V) (LMap (option_l l) f s supr)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap (option_l l) f s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (option_l l) f s xo = x"
      by auto

    have "xo <[ supr" using is_supD1[OF Hsup Xo(1)] by simp

    have "x \<in> option_l_S S s"
      using lifting_valid_weakDP[OF lifting_validx_weakDV[OF lifting_validm_weakDV[OF H]]] Xo
      by(cases l; auto simp add: option_l_S_def option_l_def split: option.splits)

    then obtain x' where X' : "x = Some x'" "x' \<in> S s"
      by(auto simp add: option_l_S_def)

    obtain xo' where Xo' : "xo = Some xo'" "xo' \<in> S s" using V_valid Xo
      by(auto simp add: option_l_S_def)

    have "xo' <[ supr'" using Xo' Supr' `xo <[ supr`
      by(simp add: option_pleq)

    hence "is_sup {xo', supr'} supr'"
      using is_sup_pair by auto

    hence Conc' : "is_sup (LMap l f s ` {xo', supr'}) (LMap l f s supr')"
      using Xo' Supr' lifting_validm_weakDM[OF H, of xo' "{xo', supr'}" s supr' f] 
      by auto

    thus "x <[ LMap (option_l l) f s supr"
      using is_supD1[OF Conc', of x'] X' Xo Xo' Supr'
      by(cases l; auto simp add: option_l_def option_pleq)
  next

    fix z

    assume Ub : "is_ub (LMap (option_l l) f s ` V) z" 

    obtain V' where SV' : "V = Some ` V'" "V' \<subseteq> S s"
      using V_valid
      by(auto simp add: option_l_S_def; blast)

    obtain v' where V' : "v = Some v'" "v' \<in> V'"
      using Nemp SV'
      by auto

    have Supr'_sup : "is_sup V' supr'"
    proof(rule is_supI)
      fix x'

      assume "x' \<in> V'"

      then show "x' <[ supr'"
        using is_supD1[OF Hsup, of "Some x'"] Supr' SV' V'
        by(auto simp add: option_pleq)
    next

      fix z'

      assume "is_ub V' z'"

      then have "is_ub V (Some z')"
        using V' SV'
        by(auto simp add: option_pleq is_ub_def)

      then show "supr' <[ z'"
        using is_supD2[OF Hsup, of "Some z'"] Supr'
        by(auto simp add: option_pleq)
    qed

    have Supr'_sup : "is_sup (LMap l f s ` V') (LMap l f s supr')"
      using lifting_validm_weakDM[OF H V'(2) SV'(2) _ Supr'_sup, of f] Supr'(2)
      by auto

    obtain vr' where Vr' : "LMap (option_l l) f s v = Some vr'"
      using lifting_valid_weakDP[OF lifting_validx_weakDV[OF lifting_validm_weakDV[OF H]]]  V'
      by(cases l; auto simp add: option_l_def)

    have "LMap (option_l l) f s v <[ z"
      using is_ubE[OF Ub, of "LMap (option_l l) f s v"] Nemp
      by(auto)

    then obtain z' where Z' : "z = Some z'" using Vr'
      by(cases z; auto simp add: option_pleq)

    hence "is_ub (LMap l f s ` V') z'"
      using Ub SV'
      by(cases l; auto simp add: option_l_def is_ub_def option_pleq)

    hence "LMap l f s supr' <[ z'"
      using is_supD2[OF Supr'_sup] by auto

    then show "LMap (option_l l) f s supr <[ z" using V' Z' Supr'
      by(cases l; auto simp add: option_l_def is_ub_def option_pleq)
  qed
next
  show "\<And> s . \<bottom> \<notin> option_l_S S s"
    by(auto simp add: option_l_S_def option_bot)
qed

(* TODO: should we instead force i to be some increment function? *)
(* TODO: i think the real issue here might be that we need the converse: if outputs have a sup,
 * then so did inputs. is this something we can assume? i dont think so - it would force functions
to be one-to-one (see for instance the md_triv case)

another approach: require that valid elements not be bottom. then the fact that
supr must be valid will imply that we have a true supremum.

problem: with products, we can have one field be bottom without the whole tuple being bottom
 *)
lemma prio_l_validm_weak :
  fixes l :: "('a, 'b, ('c :: {Okay, Pordbc})) lifting"
  assumes H : "lifting_validm_weakb l S"
  assumes Hstr1 : "\<And> s p1 p2 . p1 \<le> p2 \<Longrightarrow> i s p1 \<le> i s p2"
  assumes Hstr2 : "\<And> s p1 p2 . p1 < p2 \<Longrightarrow> i s p1 < i s p2"
  shows "lifting_validm_weakb (prio_l b i l) (prio_l_S S)"
proof(rule lifting_validm_weakbI)
  show "lifting_validx_weakb (prio_l b i l) (prio_l_S S)" sorry
next
  fix V
  fix s 
  fix v supr :: "'c md_prio"
  fix f

  assume Nemp : "v \<in> V"
  assume V_valid : "V \<subseteq> prio_l_S S s"

  assume Hsup : "is_sup V supr"
  assume Hsup_in : "supr \<in> prio_l_S S s"

  obtain supr' psupr' where Supr' : "supr = mdp psupr' supr'" "supr' \<in> S s"
    using V_valid Hsup_in
    by(auto simp add: prio_l_S_def split:md_prio.splits)

  have Vsubs : "V \<subseteq> ({ xp . (case xp of mdp p x \<Rightarrow> x \<in> S s)})"
    using V_valid
    by(auto simp add: prio_l_S_def)

  then obtain V' where SV' : "(\<lambda> x . case x of (mdp p m) \<Rightarrow> m) ` V = V'"
    by(blast)

  then have SV'_subs : "V' \<subseteq> S s"
    using V_valid
    by(auto simp add: prio_l_S_def split: md_prio.splits)

  obtain v' pv' where V' : "v = mdp pv' v'" "v' \<in> V'"
    using SV' imageI[OF Nemp, of "(\<lambda>x. case x of mdp p m \<Rightarrow> m)"]
    by(cases v; auto)

  obtain supr' psupr' where Supr' : "supr = mdp psupr' supr'" "supr' \<in> S s"
    using V_valid Hsup_in
    by(auto simp add: prio_l_S_def split: md_prio.splits)

  obtain supr_res' psupr_res' where Result : "LMap (prio_l b i l) f s supr = mdp psupr_res' supr_res'"
    by(cases "LMap (prio_l b i l) f s supr"; auto)

  show "is_sup (LMap (prio_l b i l) f s ` V) (LMap (prio_l b i l) f s supr)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap (prio_l b i l) f s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (prio_l b i l) f s xo = x"
      by auto

    have "xo <[ supr" using is_supD1[OF Hsup Xo(1)] by simp

    have "x \<in> prio_l_S S s" 
      using lifting_valid_weakbDP[OF lifting_validx_weakbDV[OF lifting_validm_weakbDV[OF H]]] Xo
      by(cases l; auto simp add: prio_l_S_def prio_l_def split: md_prio.splits)

    then obtain x' px' where X' : "x = mdp px' x'" "x' \<in> S s"
      by(auto simp add: prio_l_S_def split: md_prio.splits)

    obtain xo' pxo' where Xo' : "xo = mdp pxo' xo'" "xo' \<in> S s" using Xo Vsubs
      by(cases xo; auto simp add: prio_l_S_def split: md_prio.splits)

    show "x <[ LMap (prio_l b i l) f s supr"
    proof(cases "pxo' = psupr'")
      case True

      then have "xo' <[ supr'" using Xo' Supr' `xo <[ supr`
        by(simp add: prio_pleq)

      hence "is_sup {xo', supr'} supr'"
        using is_sup_pair by auto
  
      hence Conc' : "is_sup (LMap l f s ` {xo', supr'}) (LMap l f s supr')"
        using Xo' Supr' lifting_validm_weakbDM[OF H, of xo' "{xo', supr'}" s supr' f] 
        by auto

      then show ?thesis
        using is_supD1[OF Conc', of x'] X' Xo Xo' Supr' Hstr1[of pxo' psupr'] True
        by(cases l; auto simp add: prio_l_def prio_pleq split: md_prio.splits)
    next
      case False

      then have "pxo' < psupr'"
        using `xo <[ supr` Xo' Supr'
        by(auto simp add: prio_pleq split: if_split_asm)

      have "px' < psupr_res'" using Hstr2[OF `pxo' < psupr'`, of s]
          Result X' Xo Xo' Supr'
        by(cases l; auto simp add: prio_l_def)

      then show ?thesis using X' Xo Xo' Supr' X' Result
        by(auto simp add:prio_pleq split: md_prio.splits)
    qed
  next

    fix zo

    assume Ub : "is_ub (LMap (prio_l b i l) f s ` V) zo" 

    obtain zo' pzo' where Z' : "zo = mdp pzo' zo'"
      by(cases zo; auto)

    have Psupr_res'_eq :
      "psupr_res' = i s psupr'"
      using Supr' Result
      by(cases l; auto simp add: prio_l_def prio_pleq split: md_prio.splits if_splits)

    obtain Vmax where VSmax : "Vmax = {w . w \<in> V \<and> 
      (\<exists> w' pw' . w = mdp pw' w' \<and>
       (\<forall> y y' py' . y \<in> V \<longrightarrow> y = mdp py' y' \<longrightarrow> py' \<le> pw'))}"
      by auto

    have VSmax_eq : "\<And> w y pw' w' py' y' .
      w \<in> Vmax \<Longrightarrow> y \<in> Vmax \<Longrightarrow>
      w = mdp pw' w' \<Longrightarrow>
      y = mdp py' y' \<Longrightarrow>
      pw' = py'"
    proof-
      fix w y pw' w' py' y'
      assume Hw1 : "w \<in> Vmax"
      assume Hy1 : "y \<in> Vmax"
      assume Hwp1 : "w = mdp pw' w'"
      assume Hyp1 : "y = mdp py' y'"

      have Hw1_v : "w \<in> V" using VSmax Hw1 by blast
      have Hy1_v : "y \<in> V" using VSmax Hy1 by blast


      have "py' \<le> pw'"
        using Set.subsetD[OF Set.equalityD1[OF VSmax] Hw1] Hy1_v Hyp1 Hwp1
        by auto

      have "pw' \<le> py'"
        using Set.subsetD[OF Set.equalityD1[OF VSmax] Hy1] Hw1_v Hyp1 Hwp1
        by auto

      show "pw' = py'"
        using `py' \<le> pw'` `pw' \<le> py'`
        by auto
    qed

    have Vmax_fact2 : "\<And> n . Vmax = {} \<Longrightarrow>
      (\<exists> w pw' w' . w \<in> V \<and> w = mdp pw' w' \<and> pw' > n)"
    proof-
      fix n
      assume Contr : "Vmax = {}"
      then show "(\<exists> w pw' w' . w \<in> V \<and> w = mdp pw' w' \<and> pw' > n)"
      proof(induction n)
        case 0
        then show ?case unfolding VSmax using V' Nemp apply(auto)
          apply(drule_tac x = v in spec)
          apply(auto)
          done
      next
        case (Suc n)

        obtain w pw' w' where W: "w \<in> V" "w = mdp pw' w'" "n < pw'"
          using Suc.IH[OF Suc.prems] by auto

        show ?case using W Suc.prems
          unfolding VSmax using V' Nemp apply(auto)
          apply(drule_tac x = w in spec)
          apply(auto)
          done
      qed
    qed

    have Psupr'_max : "\<And> w pw' w' . w \<in> V \<Longrightarrow> w = mdp pw' w' \<Longrightarrow> pw' \<le> psupr'"
    proof-
      fix w pw' w'
      assume H1 :"w \<in> V"
      assume H2 : "w = mdp pw' w'"

      show "pw' \<le> psupr'"
        using is_supD1[OF Hsup H1] H2 Supr'
        by(auto simp add: prio_pleq split:if_splits)
    qed

    have VSmax_nemp : "Vmax = {} \<Longrightarrow> False"
    proof-

      assume Contr : "Vmax = {}"

      obtain w pw' w' where W: "w \<in> V" "w = mdp pw' w'" "psupr' < pw'"
        using Vmax_fact2[OF Contr, of psupr']
        by auto

      show False using Psupr'_max[OF W(1) W(2)] W(3)
        by(auto)
    qed

    hence "Vmax \<noteq> {}" by auto

    then obtain m where M : "m \<in> Vmax"
      unfolding sym[OF ex_in_conv]
      by(auto)

    obtain pm' m' where M' : "m = mdp pm' m'"
      by(cases m; auto)

    have "m \<in> V"
      using VSmax M by auto

    obtain Vmaxp where VSmaxp : "Vmaxp = (\<lambda> x . (case x of (mdp px' x') \<Rightarrow> px')) ` Vmax"
      by simp

    obtain Vmaxv where VSmaxv : "Vmaxv = (\<lambda> x . (case x of (mdp px' x') \<Rightarrow> x')) ` Vmax"
      by simp

    have In_Vmax  :
      "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
        y \<in> V \<Longrightarrow> y = mdp py' y'\<Longrightarrow> py'\<le> pw'"
      unfolding VSmax
      by blast

    have In_Vmax_Conv :       
      "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
        y \<in> V \<Longrightarrow> y = mdp pw' y'\<Longrightarrow> y \<in> Vmax"
      unfolding VSmax
      by(auto)

    have Notin_Vmax : 
      "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
        y \<in> V \<Longrightarrow> y \<notin> Vmax \<Longrightarrow> y = mdp py' y'\<Longrightarrow> py' < pw'"
    proof-
      fix w pw' w' y y' py'
      assume Win : "w \<in> Vmax"
      assume W' : "w = mdp pw' w'"
      assume Yin : "y \<in> V"
      assume Ynotin : "y \<notin> Vmax"
      assume Y' : "y = mdp py' y'"

      have "py' \<le> pw'" using In_Vmax[OF Win W' Yin Y'] by simp

      show "py' < pw'"
      proof(cases "py' = pw'")
        case False
        then show ?thesis using `py' \<le> pw'` by simp
      next
        case True

        then have "y \<in> Vmax" using In_Vmax_Conv[OF Win W' Yin] Y'
          by auto

        then have False using Ynotin by simp

        thus ?thesis by simp
      qed
    qed

    (* do we need this? *)
    have "is_sup Vmax supr"
    proof(rule is_supI)
      fix x
      assume "x \<in> Vmax"
      then have Hx : "x \<in> V" unfolding VSmax by auto


      show "x <[ supr" using is_supD1[OF Hsup Hx] by simp
    next
      fix w
      assume Ub : "is_ub Vmax w"

      have Ub' : "is_ub V w"
      proof(rule is_ubI)
        fix x
        assume X : "x \<in> V"

        obtain x' px' where X' : "x = mdp px' x'" by(cases x; auto)

        have "px' \<le> pm'"
          using In_Vmax[OF M M' X X'] by simp

        obtain w' pw' where W' : "w = mdp pw' w'" by(cases w; auto)

        have "m <[ w" using is_ubE[OF Ub M] by simp

        then show "x <[ w"
        proof(cases "x \<in> Vmax")
          case True
          then show ?thesis using is_ubE[OF Ub, of x] by simp
        next
          case False

          then have "px' < pm'"
            using Notin_Vmax[OF M M' X False X'] by simp

          then show ?thesis using X' W' M' `m <[ w`
            by(auto simp add: prio_pleq split: if_splits)
        qed
      qed
      show "supr <[ w"
        using is_supD2[OF Hsup Ub'] by simp
    qed

    (* idea: either pm' is equal to supr, or is one less. *)
    show "LMap (prio_l b i l) f s supr <[ zo"
    proof(cases "has_sup Vmaxv")
      case False

      consider (L) "psupr' < 1 + pm'"
        | (E) "psupr' = 1 + pm'"
        | (G) "psupr' > 1 + pm'"
        using less_linear by auto

      then have Psupr_Inc : "psupr' = 1 + pm'"
      proof cases
        case L

        then have Eq : "psupr' = pm'" using Psupr'_max[OF `m \<in> V` M'] by simp

        have "is_sup Vmaxv supr'"
        proof(rule is_supI)
          fix w'
          assume W': "w' \<in> Vmaxv"

          obtain pw' where W: "(mdp pw' w') \<in> Vmax" using W'
            unfolding VSmaxv
            by(auto split: md_prio.splits)

          have Pw' : "pw' = pm'"
            using VSmax_eq[OF M W M']
            by auto

          have "mdp pw' w' <[ supr" using is_supD1[OF `is_sup Vmax supr` W]
            by simp

          then show "w' <[ supr'"
            using Eq Pw' Supr'
            by(auto simp add: prio_pleq)
        next
          fix z'

          assume Z' : "is_ub Vmaxv z'"

          have Zmax : "is_ub Vmax (mdp pm' z')"
          proof(rule is_ubI)
            fix w
            assume W : "w \<in> Vmax"

            obtain pw' w' where W' : "w = mdp pw' w'" by(cases w; auto)

            have Pw' : "pw' = pm'"
              using VSmax_eq[OF M W M' W'] by simp

            have "w' \<in> Vmaxv" using W W'
              unfolding VSmaxv using imageI[OF W, of "case_md_prio (\<lambda>px' x'. x')"]
              by auto

            then have "w' <[ z'"
              using is_ubE[OF Z'] by auto

            then show "w <[ mdp pm' z'" using Pw' W'
              by(auto simp add: prio_pleq split:if_splits)
          qed
          
          show "supr' <[ z'" using is_supD2[OF `is_sup Vmax supr` Zmax] Eq Supr'
            by(auto simp add: prio_pleq split:if_splits)
        qed

        then have False using False by(auto simp add: has_sup_def)

        then show "psupr' = 1 + pm'" by simp
      next
        case E
        then show ?thesis by simp
      next
        case G

        have Supr_Ub : "is_ub V (mdp (1 + pm') supr')"
        proof(rule is_ubI)
          fix w

          assume W : "w \<in> V"

          obtain pw' w' where W' : "w = mdp pw' w'" by(cases w; auto)

          have "pw' \<le> pm'" using In_Vmax[OF M M' W W'] by simp

          then show "w <[ mdp (1 + pm') supr'"
            using W'
            by(auto simp add: prio_pleq)
        qed

        then have "mdp psupr' supr' <[ mdp (1 + pm') supr'"
          using is_supD2[OF `is_sup V supr` Supr_Ub] Supr'
          by auto

        then have False using G
          by(auto simp add: prio_pleq split:if_splits)

        then show ?thesis by simp
      qed

      have "is_ub Vmax (mdp (1 + pm') \<bottom>)"
      proof(rule is_ubI)
        fix w

        assume W: "w \<in> Vmax"

        obtain pw' w' where W' : "w = mdp pw' w'" by(cases w; auto)

        have "pw' = pm'" using VSmax_eq[OF W M W' M'] by simp

        then show "w <[ mdp (1 + pm') \<bottom>"
          using W'
          by(auto simp add: prio_pleq)
      qed

      hence "supr <[ (mdp (1 + pm') \<bottom>)"
        using is_supD2[OF `is_sup Vmax supr`] by auto

      hence "supr = (mdp (1 + pm') \<bottom>)"
        using Supr' Psupr_Inc leq_antisym[OF bot_spec[of supr']]
        by(auto simp add: prio_pleq bot_spec)

      hence False using lifting_validm_weakbDB[OF H] Supr'
        by auto

      thus ?thesis by auto
    next
      case True

      then obtain vsup where Vsup : "is_sup Vmaxv vsup"
        by(auto simp add: has_sup_def)

      have "is_ub V (mdp pm' vsup)"
      proof(rule is_ubI)
        fix z
        assume Z: "z \<in> V"
        obtain pz' z' where Z' : "z = mdp pz' z'"
          by(cases z; auto)

        show "z <[ mdp pm' vsup"
        proof(cases "z \<in> Vmax")
          case True

          have "z' \<in> Vmaxv"
            using imageI[OF True, of "case_md_prio (\<lambda>px' x'. x')"] Z'
            unfolding VSmaxv
            by auto

          have "pz' = pm'"
            using VSmax_eq[OF True M Z' M'] by simp

          have "z' <[ vsup"
            using is_supD1[OF Vsup `z' \<in> Vmaxv`] by simp

          then show ?thesis using `pz' = pm'` Z'
            by(auto simp add: prio_pleq)
        next
          case False
          have "pz' < pm'"
            using Notin_Vmax[OF M M' Z False Z'] by simp

          then show ?thesis using Z'
            by(auto simp add: prio_pleq)
        qed
      qed

      have Supr_Vmax : "is_sup Vmaxv supr'"
      proof(rule is_supI)
        fix w'

        assume W': "w' \<in> Vmaxv"

        obtain pw' where W: "(mdp pw' w') \<in> Vmax" using W'
          unfolding VSmaxv
          by(auto split: md_prio.splits)

        have Pw' : "pw' = pm'"
          using VSmax_eq[OF M W M']
          by auto

        have "mdp pw' w' <[ supr" using is_supD1[OF `is_sup Vmax supr` W]
          by simp


        have "pw' = psupr'"
          using is_supD2[OF Hsup `is_ub V (mdp pm' vsup)`]
            Pw' Supr' `mdp pw' w' <[ supr`
          by(auto simp add: prio_pleq split: if_splits)

        then show "w' <[ supr'"
          using Pw' Supr' `mdp pw' w' <[ supr`
          by(auto simp add: prio_pleq)
      next

        fix w'

        assume W' : "is_ub Vmaxv w'"

        have "is_ub V (mdp pm' w')"
        proof(rule is_ubI)
          fix z
          assume Z: "z \<in> V"
          obtain pz' z' where Z' : "z = mdp pz' z'"
            by(cases z; auto)

          show "z <[ mdp pm' w'"
          proof(cases "z \<in> Vmax")
            case True

            then have "z' \<in> Vmaxv" 
              using imageI[OF True, of "case_md_prio (\<lambda>px' x'. x')"] Z'
              unfolding VSmaxv
              by auto
              
            have "z' <[ w'" using is_ubE[OF W' `z' \<in> Vmaxv`] by simp

            have "pz' = pm'" using VSmax_eq[OF True M Z' M'] by simp

            then show ?thesis using `z' <[ w'` Z'
              by(auto simp add: prio_pleq split: md_prio.splits)
          next
            case False

            have "pz' < pm'"
              using Notin_Vmax[OF M M' Z False Z'] by simp

            then show ?thesis using Z'
              by(auto simp add: prio_pleq)
          qed
        qed

        have "m' \<in> Vmaxv" using M' M
          unfolding VSmaxv
          using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"]
          by(auto)

        have "m' <[ w'"
          using is_ubE[OF W' `m' \<in> Vmaxv`] by simp

        have "supr <[ (mdp pm' w')"
          using is_supD2[OF Hsup `is_ub V (mdp pm' w')`]
          by simp

        have "m \<in> V" using M unfolding VSmax by auto

        have "pm' \<le> psupr'"
          using Psupr'_max[OF `m \<in> V` M'] by simp

        hence "pm' = psupr'"
          using `supr <[ (mdp pm' w')` Supr'
          by(auto simp add: prio_pleq split: if_splits)

        then show "supr' <[ w'"
          using Supr' `supr <[ mdp pm' w'`
          by(auto simp add: prio_pleq split: if_splits)
      qed

      have "m' \<in> Vmaxv" using M' M
        unfolding VSmaxv
        using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"]
        by(auto)

      have "Vmaxv \<subseteq> S s"
        using Vsubs
        unfolding VSmax VSmaxv
        by auto

      have Supr'_sup_vmax : "is_sup (LMap l f s ` Vmaxv) (LMap l f s supr')"
        using lifting_validm_weakbDM[OF H `m' \<in> Vmaxv` `Vmaxv \<subseteq> S s` Supr'(2)
            `is_sup Vmaxv supr'`]
        by simp

(* pm' is supr of vmaxv
*)

      consider (L) "pm' < psupr'"
        | (E) "pm' = psupr'"
        | (G) "pm' > psupr'"
        using less_linear by auto
      then have "pm' = psupr'"
      proof cases
        case L

        have "is_ub V (mdp pm' supr')"
        proof(rule is_ubI)
          fix w
          assume W : "w \<in> V"

          obtain pw' w' where W' : "w = mdp pw' w'"
            by(cases w; auto)

          show "w <[ mdp pm' supr'"
          proof(cases "w \<in> Vmax")
            case True

            have "pw' = pm'" using VSmax_eq[OF True M W' M'] by simp

            have "w' \<in> Vmaxv"
              using imageI[OF True, of "case_md_prio (\<lambda>px' x'. x')"] W'
              unfolding VSmaxv by auto

            then have "w' <[ supr'"
              using is_supD1[OF `is_sup Vmaxv supr'`] by auto

            then show "w <[ mdp pm' supr'"
              using `pw' = pm'` W'
              by(auto simp add: prio_pleq split: if_splits)
          next
            case False

            have "pw' < pm'" using Notin_Vmax[OF M M' W False W'] by simp

            then show "w <[ mdp pm' supr'"
              using W'
              by(auto simp add: prio_pleq split: if_splits)
          qed
        qed

        have "mdp psupr' supr' <[ mdp pm' supr'"
          using is_supD2[OF Hsup `is_ub V (mdp pm' supr')`] Supr'
          by auto

        then have False using L
          by(auto simp add: prio_pleq split: if_splits)

        then show ?thesis by simp
      next
        case E
        then show ?thesis by simp
      next
        case G

        have "m \<in> V" using M
          unfolding VSmax by auto

        have "mdp pm' m' <[ mdp psupr' supr'"
          using is_supD1[OF Hsup `m \<in> V`] M' Supr'
          by auto

        hence False using G
          by(auto simp add: prio_pleq split: if_splits)

        then show ?thesis by simp
      qed

      consider (L) "pzo' < i s pm'"
        | (E) "pzo' = i s pm'"
        | (G) "pzo' > i s pm'"
        using less_linear by auto
      then show "LMap (prio_l b i l) f s supr <[ zo"
      proof cases
        case L

        have "m \<in> V"
          using M VSmax by auto
        
        have Bad : "LMap (prio_l b i l) f s m \<in> LMap (prio_l b i l) f s ` V"
          using imageI[OF `m \<in> V`, of "LMap (prio_l b i l) f s"]
          by auto

        have False using is_ubE[OF Ub Bad] L M' Z'
          by(cases l; auto simp add: prio_l_def prio_pleq)

        then show ?thesis by simp
      next
        case E

        have Ub_max : "is_ub (LMap l f s ` Vmaxv) zo'"
        proof(rule is_ubI)
          fix wo'
          assume Wo' : "wo' \<in>  LMap l f s ` Vmaxv "

          obtain w pw' w' where W: "w = mdp pw' w'" "w \<in> Vmax" "LMap l f s w' = wo'" using Wo'
            unfolding VSmaxv
            by(auto split: md_prio.splits)

          have "pw' = pm'"
            using VSmax_eq[OF M `w \<in> Vmax` M' `w = mdp pw' w'`]
            by simp

          have "w \<in> V" using `w \<in> Vmax`
            unfolding VSmax by auto

          have Wmap : "LMap (prio_l b i l) f s w \<in> (LMap (prio_l b i l) f s ` V)"
            using imageI[OF `w \<in> V`] by auto

          have "LMap (prio_l b i l) f s w <[ zo"
            using is_ubE[OF Ub Wmap]  by simp

          then show "wo' <[ zo'"
            using Z' `pw' = pm'` E W
            by(cases l; auto simp add: prio_l_def prio_pleq)
        qed

        then show ?thesis using is_supD2[OF Supr'_sup_vmax Ub_max] E `pm' = psupr'` Z' Supr' Result
          by(cases l; auto simp add: prio_l_def prio_pleq)
      next
        case G
        have "m' \<in> Vmaxv" using M' M
          unfolding VSmaxv
          using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"]
          by(auto)

        have "m \<in> V" using M unfolding VSmax by auto

        have "m' \<in> Vmaxv" using M' M
          unfolding VSmaxv
          using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"]
          by(auto)

(* this should be true, but i've lost track of why. *)

        then show ?thesis using Supr' Z' G `pm' = psupr'`
          by(cases l; auto simp add: prio_l_def prio_pleq)
      qed
    qed
  qed
next
  show "\<And>s. \<bottom> \<notin> prio_l_S S s" using lifting_validm_weakbDB[OF H]
    by(auto simp add: prio_bot prio_l_S_def)
qed


lemma fst_l_validm_weak :
  fixes l :: "('a, 'b, ('c :: {Okay, Pord})) lifting"
  assumes H : "lifting_validm_weak l S"
  shows "lifting_validm_weak (fst_l l) (fst_l_S S)"
proof(rule lifting_validm_weakI)
  show "lifting_validx_weak (fst_l l) (fst_l_S S)" sorry
next
  fix s a1 a2 
  fix b1 b2 :: "('c * 'd)"
  fix f
  assume HB1 : "b1 \<in> fst_l_S S s"
  assume HB2 : "b2 \<in> fst_l_S S s"
  assume Lt :"b1 <[ b2"

  obtain b1' b1'r where B1 : "b1 = (b1', b1'r)" "b1' \<in> S s"
    using HB1 by(cases b1; auto simp add: fst_l_S_def)

  obtain b2' b2'r where B2 : "b2 = (b2', b2'r)" "b2' \<in> S s"
    using HB2 by(cases b2; auto simp add: fst_l_S_def)

  have Leq : "b1' <[ b2'"
    using Lt B1 B2 by (auto simp add: prod_pleq)

  have Leqr : "b1'r <[ b2'r"
    using Lt B1 B2 by (auto simp add: prod_pleq)

  show "LUpd (fst_l l) s
        (f (LOut (fst_l l) s b1)) b1 <[
       LUpd (fst_l l) s
        (f (LOut (fst_l l) s b2)) b2"
  proof(cases "b1' = b2'")
    case True
    then show ?thesis
      using B1 B2 lifting_validm_weakDM[OF H B1(2) B2(2) Leq] Leqr
      by(cases l; auto simp add: fst_l_def prod_pleq)
  next
    case False
    then show ?thesis 
      using B1 B2 lifting_validm_weakDM[OF H B1(2) B2(2) Leq] Leqr
      by(cases l; auto simp add: fst_l_def prod_pleq)
  qed
qed

(* Lifters that preserve least upper bounds when projecting (?) *)
(* is this an overly restrictive constraint? *)
(* LUpd l1 (l1' syn) (f1 (l1' syn) (LOut l1 (l1' syn) x)) x <[
    LUpd l1 (l1' syn) (f1 (l1' syn) (LOut l1 (l1' syn) sup1)) sup1 *)

(* b1 b2 \<in> S s \<Longrightarrow> b1 <[ b2 \<Longrightarrow> LUpd l s a b1 <[ LUpd l s a b2 *)
(* add not equal constraint? *)
(* b1 b2 \<in> S s \<Longrightarrow> b1 <[ b2 \<Longrightarrow> LUpd l s a1 b1 <[ LUpd l s a2 b2 *)

end