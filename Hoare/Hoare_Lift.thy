theory Hoare_Lift imports Hoare_Indexed Hoare_Indexed_Sound Hoare_Direct
  "../Lifter/Lifter" "../Composition/Composition" "../Composition/Dominant"
begin

(* TODO rename this file to Hoare_Direct_Lift (or Hoare_Step_Lift...) *)
(* TODO: do we still need this? *)

(*
 * This file contains some abstractions for lifting Hoare rules expressed on a single language
 * into Hoare rules expressed on merged languages.
 *
 * Note that this isn't particularly suitable for languages that deal with control -
 * see Language_Components/Imp_Ctl and Language_Components/Seq to see how we deal with
 * those cases.
 *
 * For languages without control, this is a more general approach (as we show here,
 * the "dominant" style of reasoning used in Imp_Ctl and Seq is a special case of this.)
 *)

(* This version does not take a valid set. It is usually not what we want. *)
text_raw \<open>%Snippet gazelle__hoare__hoare_lift__lift_pred_noS_s\<close>
definition lift_pred_noS_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord) lifting \<Rightarrow>
   'b1 \<Rightarrow>
   ('a2 \<Rightarrow> bool) \<Rightarrow>
   ('b2 \<Rightarrow> bool)"
  where
"lift_pred_noS_s l' l syn P st =
 P (LOut l (l' syn) st)"
text_raw \<open>%EndSnippet\<close>

definition lift_pred_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'b2 set) \<Rightarrow>
   'b1 \<Rightarrow>
   ('a2 \<Rightarrow> bool) \<Rightarrow>
   ('b2 \<Rightarrow> bool)"
  where
"lift_pred_s l' l S syn P st =
  (lift_pred_noS_s l' l syn P st \<and> st \<in> S (l' syn))"

(* When we lift a function on which a certain Hoare triple holds,
 * we know that an analogous Hoare triple holds on the lifted function and
 * lifted predicates.
 *)
text_raw \<open>%Snippet gazelle__hoare__hoare_lift__Vlift\<close>
lemma Vlift :
  assumes Valid : "lifting_valid_weak l S" 
  assumes V: "(sem) % {{P}} x {{Q}}"
  assumes Syn : "l' x' = x"
  shows "(lift_map_s l' l sem) % {{lift_pred_noS_s l' l x' P}} x' {{lift_pred_noS_s l' l x' Q}}"
text_raw \<open>%EndSnippet\<close>
proof-

  interpret Valid : lifting_valid_weak l S
    using Valid.

  show " lift_map_s l' l
     sem % {{lift_pred_noS_s l' l x'
              P}} x' {{lift_pred_noS_s l' l x' Q}}"
 using V Syn
  unfolding HTS_def HT_def lift_pred_noS_s_def lift_map_s_def 
  by(auto simp add: Valid.put_get)
qed

(* not especially useful - better to separate out the valid-set *)
lemma Vlift_valid :
  assumes Valid : "lifting_valid_weak l S" 
  assumes V: "(sem) % {{P}} x {{Q}}"
  assumes Syn : "l' x' = x"
  shows "(lift_map_s l' l sem) % {{lift_pred_s l' l S x' P}} x' {{lift_pred_s l' l S x' Q}}"
proof-
  interpret Valid : lifting_valid_weak l S
    using Valid.

  show " lift_map_s l' l
     sem % {{lift_pred_s l' l S x'
              P}} x' {{lift_pred_s l' l S x' Q}}"
 using V Syn
  unfolding HTS_def HT_def lift_pred_s_def lift_map_s_def lift_pred_noS_s_def
  using Valid.put_S
  by(auto simp add: Valid.put_get)
qed

(* Now, some stuff from Hoare_Lift. *)
definition lift_pred_valid_ok_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: {Pord, Okay}) lifting \<Rightarrow>
   'b1 \<Rightarrow>
   ('a2 \<Rightarrow> bool) \<Rightarrow>
   ('b2 \<Rightarrow> bool)"
  where
"lift_pred_valid_ok_s l' l syn P st =
  (lift_pred_noS_s l' l syn P st \<and> st \<in> ok_S)" 

lemma Vlift_valid_ok :
  assumes Valid : "lifting_valid_weak_ok l S" 
  assumes V: "(sem) % {{P}} x {{Q}}"
  assumes Syn : "l' x' = x"
  shows "(lift_map_s l' l sem) % {{lift_pred_valid_ok_s l' l x' P}} x' {{lift_pred_valid_ok_s l' l  x' Q}}"
proof-

  interpret Valid : lifting_valid_weak_ok l S
    using Valid.

  show ?thesis

 using V Syn
  unfolding HTS_def HT_def lift_pred_s_def lift_map_s_def lift_pred_s_def lift_pred_valid_ok_s_def
    lift_pred_noS_s_def
  using Valid.put_S Valid.ok_S_put
  by(auto simp add: Valid.put_get)
qed


(*
 * Intuitively, the only way for a Hoare triple that is valid on a language component
 * in isolation to fail to hold after being merged with another language is if
 * another language "overrides" that construct for some piece(s) of syntax.
 * This is why we have to weaken the conclusion, requiring only that there exists
 * a lesser (in the information-ordering sense) state on which the triple does hold.
 *)
text_raw \<open>%Snippet gazelle__hoare__hoare_lift__Vmerge\<close>
lemma Vmerge :
  assumes Pres : "sups_pres (set l) S"
  assumes Sem : "f \<in> set l"
  assumes P_S : "\<And> st . P st \<Longrightarrow> st \<in> S x"
  assumes V : "(f) % {{P}} x {{Q}}"
  shows "(pcomps l) % 
         {{P}}
         x
         {{(\<lambda> st . \<exists> st_sub . Q st_sub \<and> st_sub <[ st)}}"
text_raw \<open>%EndSnippet\<close>
proof(rule HTSI)
  fix a 
  assume HP : "P a"

  have Conc_f : "Q (f x a)"
    using HTSE[OF V HP]
    by auto

  have Elem : "f x a \<in> (\<lambda>f. f x a) ` set l"
    using Sem by auto

  have Nemp : "l \<noteq> []" using Sem by (cases l; auto)

  have Conc' : "f x a <[ pcomps l x a"
    using is_supD1[OF sups_pres_pcomps_sup'[OF Pres Nemp] Elem] P_S[OF HP]
    by auto

  show "\<exists>st_sub. Q st_sub \<and> st_sub <[ pcomps l x a"
    using Conc_f Conc'
    by auto
qed
    
(* Another way of looking a vmerge: if we know the conclusion is monotonic,
 * then we know that a triple with that conclusion still holds after a merge *)
text_raw \<open>%Snippet gazelle__hoare__hoare_lift__Vmerge_mono\<close>
lemma Vmerge_mono :
  assumes Pres : "sups_pres (set l) S"
  assumes Sem : "f \<in> set l"
  assumes Mono : "Pord.is_monop1 Q"
  assumes P_S : "\<And> st . P st \<Longrightarrow> st \<in> S x"
  assumes V : "(f) % {{P}} x {{Q}}"
  shows "(pcomps l) % 
         {{P}}
         x
         {{Q}}"
text_raw \<open>%EndSnippet\<close>
proof(-)
  have PC : "(pcomps l) % {{P}} x {{(\<lambda>st. \<exists>st_sub. Q st_sub \<and> st_sub <[ st)}}"
    using Vmerge[OF Pres Sem P_S V]
    by auto

  show "(pcomps l) % {{P}} x {{Q}}"
  proof(rule HTS_Conseq[OF PC])
    show "\<And> x . P x \<Longrightarrow> P x" by auto
  next
    fix x
    show "\<exists>st_sub. Q st_sub \<and> st_sub <[ x \<Longrightarrow> Q x"
    proof(clarify)
      fix x st_sub
      assume Hi1 : "Q st_sub"
      assume Hi2 : "st_sub <[ x"
      show "Q x" using Hi1 Hi2 Mono unfolding is_monop1_def
        by(auto)
    qed
  qed
qed


(* a (almost) weaker version of l_ortho, that
   talks about when liftings are orthogonal in the sense
   that arbitrary lifted functions preserve sups at runtime *)
(* this and the following definitions may not be particularly useful anymore
 * (TODO - decide if they are worth keeping *)
(*
definition l_ortho_run ::
  "('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b, 'z2) lifting_scheme \<Rightarrow>
   bool" where
"l_ortho_run l1 l2 = 
  (\<forall> x1 x2 . sups_pres {(\<lambda>syn . LUpd l1 syn x1), (\<lambda> syn . LUpd l2 syn x2)})"

lemma leq_sup :
  assumes H : "x1 <[ x2"
  shows "is_sup {x1, x2} x2"
proof(rule is_supI)
  fix x
  assume "x \<in> {x1, x2}"
  then show "x <[ x2" using H leq_refl by auto
next
  fix x'
  assume "is_ub {x1, x2} x'"
  then show "x2 <[ x'"
    by(auto simp add: is_ub_def)
qed
*)

(* 
 * When dealing with single-step languages, we have an important special case - that is,
 * the case where the single-step language is _dominant_ (see Composition/Dominant.thy)
 * for one or more pieces of syntax. In such cases we can show that the
 * lifted version of the rule holds without side conditions.
 *)

(* However, we might be able to avoid reasoning about liftings at all in such cases (?)
 * by playing the same parametricity trick as with the control languages?
 *)


(*
(* TODO: why is 'b being forced to be Mergeableb? *)
lemma prio_ortho_run :
  fixes tf :: "('x, 'a1, 'b :: Mergeableb) lifting"
  fixes tg :: "('x, 'a2, 'b ) lifting"
  assumes H0 : "\<And> s p . f1 s p \<noteq> g1 s p"
  shows "l_ortho_run (prio_l f0 f1 tf) (prio_l g0 g1 tg)"
  unfolding l_ortho_run_def sups_pres_def
proof(clarify)
  fix x1 x2 syn
  fix st :: "'b md_prio"

  obtain p st' where St : "st = mdp p st'" by(cases st; auto)

  have Conc' : "has_sup {(LUpd (prio_l f0 f1 tf) syn x1 st),
                         (LUpd (prio_l g0 g1 tg) syn x2 st)}"
  proof(cases "f1 syn p \<le> g1 syn p")
    case True
    then have True' : "f1 syn p < g1 syn p" using H0[of syn p] by auto
    then have Gt : "(LUpd (prio_l f0 f1 tf) syn x1 st) <[ (LUpd (prio_l g0 g1 tg) syn x2 st)"
      using St
      by(auto simp add: prio_l_def prio_pleq)

    show ?thesis using leq_sup[OF Gt] by (auto simp add: has_sup_def)
  next
    case False
    then have False' : "g1 syn p < f1 syn p" using H0[of syn p] by auto
    then have Gt : "(LUpd (prio_l g0 g1 tg) syn x2 st) <[ (LUpd (prio_l f0 f1 tf) syn x1 st)"
      using St
      by(auto simp add: prio_l_def prio_pleq)
    show ?thesis using is_sup_comm2[OF leq_sup[OF Gt]] by (auto simp add: has_sup_def)
  qed

  thus "has_sup
        ((\<lambda>f. f syn st) ` 
         {\<lambda>syn. LUpd (prio_l f0 f1 tf) syn x1, \<lambda>syn. LUpd (prio_l g0 g1 tg) syn x2})"
    by(auto)
qed
*)
(*
lemma l_ortho_imp_weak :

  fixes tf :: "('x, 'a1, 'b :: Mergeable) lifting"
  fixes tg :: "('x, 'a2, 'b ) lifting"
(* TODO: make sure these really need to be the same valid-set
   i don't intuitively understand why this should be *)

  assumes Hvf :  "lifting_valid tf Sf"
  assumes Hvg :  "lifting_valid tg Sg"
  assumes Hs : "Sf = Sg"
  assumes H: "l_ortho tf tg"
  shows "l_ortho_run tf tg"
  unfolding l_ortho_run_def sups_pres_def
proof(clarify)
  fix x1 x2 syn st

  have Orth : "LUpd tf syn x1 (LUpd tg syn x2 st) = LUpd tg syn x2 (LUpd tf syn x1 st)"
    using l_orthoDI[OF H, of syn x1 x2 st] by auto

  have Ub : "is_ub {LUpd tf syn x1 st, LUpd tg syn x2 st} (LUpd tf syn x1 (LUpd tg syn x2 st))"
  proof(rule is_ubI)
    fix x
    assume Hx : "x \<in> {LUpd tf syn x1 st, LUpd tg syn x2 st}"

    then consider (1) "x = LUpd tf syn x1 st" |
                  (2) "x = LUpd tg syn x2 st" by auto

    then show "x <[ LUpd tf syn x1 (LUpd tg syn x2 st)"
    proof cases
      case 1

      have Sg : "x \<in> Sg syn"
        using lifting_validDP[OF Hvf] unfolding 1 Orth Hs by auto

      then show ?thesis
        using lifting_validDI[OF Hvg Sg]
        unfolding 1 Orth by auto
    next
      case 2
      have Sf : "x \<in> Sf syn"
        using lifting_validDP[OF Hvg] unfolding 2 Orth Hs by auto

      then show ?thesis
        using lifting_validDI[OF Hvf Sf]
        unfolding 2 sym[OF Orth] by auto
    qed
  qed

  hence Ub' : "has_ub {LUpd tf syn x1 st, LUpd tg syn x2 st}"
    by(auto simp add: has_ub_def)

  have Sup : "has_sup {LUpd tf syn x1 st, LUpd tg syn x2 st}" 
    using complete2[OF Ub'] by auto

  thus "has_sup ((\<lambda>f. f syn st) ` {\<lambda>syn. LUpd tf syn x1, \<lambda>syn. LUpd tg syn x2})"
    by auto
qed
*)

end