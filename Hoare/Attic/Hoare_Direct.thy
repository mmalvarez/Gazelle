theory Hoare_Direct imports "../Lifting/LiftUtils" "../Lifting/LiftInstances" "../Lifting/LangCompSimple"
begin

(* A direct-style implementation of Hoare logic (distinct from the CPS-flavored version
 * found in Hoare.thy.
 * The CPS version proved more flexible and convenient, so this was abandoned.
 *)

abbreviation C where
"C x \<equiv> (\<lambda> _ . x)"

definition predimp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ *-> _" 63)
  where
"predimp P1 P2 =
  (\<forall> x . P1 x \<longrightarrow> P2 x)"

definition VT :: 
  "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  ("{{_}} _ {{_}}" [0,0,0] 61) where
"VT pre x post =
  (\<forall> a b . pre a \<longrightarrow> x a b \<longrightarrow> post b)"

lemma VTI :
  assumes H1 : 
    "\<And> a b . pre a \<Longrightarrow> x a b \<Longrightarrow> post b"
  shows "VT pre x post" using assms
  unfolding VT_def by auto

lemma VTE :
  assumes H : "VT pre x post"
  assumes Ha : "pre a"
  assumes Hb : "x a b"
  shows "post b" using assms
  unfolding VT_def by auto

lemma Vtop :
  shows "{{P}} X {{C True}}"
  by(simp add:VT_def)

lemma Vbot :
  shows "{{C False}} X {{P}}"
  by(simp add:VT_def)

lemma Vconseq_pre :
  assumes H1 : "{{P}} X {{Q}}"
  assumes H2 : "P' *-> P"
  shows "{{P'}} X {{Q}}" using assms
  by(auto simp add: VT_def predimp_def)

lemma Vconseq_post :
  assumes H1 : "{{P}} X {{Q}}"
  assumes H2 : "Q *-> Q'"
  shows "{{P}} X {{Q'}}" using assms
  by(auto simp add: VT_def predimp_def)

lemma VandI :
  assumes H1 : "{{P1}} X {{Q1}}"
  assumes H2 : "{{P2}} X {{Q2}}"
  shows "{{(\<lambda> x . (P1 x \<and> P2 x))}} X {{(\<lambda> x . (Q1 x \<and> Q2 x))}}"
    using assms
    by(auto simp add: VT_def)


type_synonym ('x, 'a) syn_triple =
  "('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool)"

(* we could use ad-hoc polymorphism here, in leiu of an actual typeclass,
for syn_triple (keyed on syntax). but maybe this wouldn't be a good idea.
*)

(* "valid triple, syntax." *)
(*
definition VTS ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_: {{_}} _ {{_}}" [0,0,0,0] 62)
  where
"VTS sem pre x post =
  VT pre (sem x) post"
*)

(* hmm. how to deal with syntax transformation when lifting predicates? *)
(*
definition VTS :: 
  "('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('x \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_: {{_}} _ {{_}}" [0,0,0,0] 62)
  where
"VTS sem pre x post =
  VT (pre x) (sem x) (post x)"
*)

abbreviation VTS :: 
  "('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ % {{_}} _ {{_}}" [0,0,0,0] 63)
  where
"VTS sem pre x post \<equiv>
  VT (pre) (sem x) (post)"

(* executable VTS. probably less useful than relational one. *)
definition VTS' ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where
"VTS' sem pre x post =
  VT pre (\<lambda> a b . sem x a = b) post"

definition lift_pred_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   'b1 \<Rightarrow>
   ('a2 \<Rightarrow> bool) \<Rightarrow>
   ('b2 \<Rightarrow> bool)" where
"lift_pred_s l' l syn P st =
 P (LOut l (l' syn) st)"

(* TODO: figure out why there is this ambiguity *)
definition semprop2 ::
  "('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3) \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3 \<Rightarrow> bool)"
  ("! _" [3] 61)
  where
"semprop2 f a1 a2 a3 \<equiv>
  (f a1 a2 = a3)"

lemma semprop2I :
  "(!f) a1 a2 (f a1 a2)"
  by(auto simp add: semprop2_def)

lemma semprop2E :
  assumes H : "(!f) a1 a2 a3"
  shows "a3 = f a1 a2" using assms
  by(auto simp add: semprop2_def)

(* need to consider liftings. *)
lemma Vlift :
  assumes Valid : "lifting_valid l v" 
  assumes V: "(!sem) % {{P}} x {{Q}}"
  assumes Syn : "l' x' = x"
  shows "(! lift_map_s l' l sem) % {{lift_pred_s l' l x' P}} x' {{lift_pred_s l' l x' Q}}"
 using V Syn
  unfolding VT_def lift_pred_s_def lift_map_s_def semprop2_def
  by(auto simp add: lifting_validDO[OF Valid])

(* need to fix up LangComp.thy.
   ok, i think we can actually avoid talking about lifting here. just merging (?) *)
(* maybe we actually do want to integrate these... *)


(* do we need explicit P0 ... Pn ?*)
lemma Vmerge :
  assumes Pres : "sups_pres (set l)"
  assumes Sem : "f \<in> set l"
  assumes V : "(!f) % {{P}} x {{Q}}"
  shows "(! pcomps' l) % 
         {{P}}
         x
         {{(\<lambda> st . \<exists> st_sub . Q st_sub \<and> st_sub <[ st)}}"
proof(rule VTI)
  fix a b
  assume HP : "P a"
  assume HS : "(! pcomps' l) x a b"

  have Conc_f : "Q (f x a)"
    using VTE[OF V HP]
    unfolding semprop2_def by auto

  have Elem : "f x a \<in> (\<lambda>f. f x a) ` set l"
    using Sem by auto

  have Nemp : "l \<noteq> []" using Sem by (cases l; auto)

  have Conc' : "f x a <[ pcomps' l x a"
    using is_sup_unfold1[OF sups_pres_pcomps_sup[OF Pres Nemp] Elem]
    by auto

  have Pc_l_b : "pcomps' l x a = b" using HS unfolding semprop2_def
    by auto

  show "\<exists>st_sub. Q st_sub \<and> st_sub <[ b"
    using Conc_f Conc' unfolding Pc_l_b
    by auto
qed
    

lemma Vmerge_mono :
  assumes Pres : "sups_pres (set l)"
  assumes Sem : "f \<in> set l"
  assumes Mono : "Pord.is_monop1 Q"
  assumes V : "(!f) % {{P}} x {{Q}}"
  shows "(! pcomps' l) % 
         {{P}}
         x
         {{Q}}"
proof(-)
  have PC : "(! pcomps' l) % {{P}} x {{\<lambda>st. \<exists>st_sub. Q st_sub \<and> st_sub <[ st}}"
    using Vmerge[OF Pres Sem V]
    unfolding semprop2_def
    by auto

  show "(! pcomps' l) % {{P}} x {{Q}}"
  proof(rule Vconseq_post[OF PC])
    show "(\<lambda>st. \<exists>st_sub. Q st_sub \<and> st_sub <[ st) *-> Q"
      unfolding predimp_def
    proof(clarify)
      fix x st_sub
      assume Hi1 : "Q st_sub"
      assume Hi2 : "st_sub <[ x"
      show "Q x" using Hi1 Hi2 Mono unfolding is_monop1_def
        by(auto)
    qed
  qed
qed

(* ok, should have a way of proving sups_pres holds on some lifted stuff
   idea: for every input (?) lifted outputs have sup
   this will look kind of similar to orthogonality

   do we need the more general version of sups_pres for this though?

   goal is to show that sups_pres {lift_map_s l1 f1, lift_map_s l2 f2} for all f1, f2

   this means that:
    {lift_map_s l1 f1 syn st, lift_map_s l2 f2 syn st} have a sup

   this means that:
    {LUpd ln syn (fn syn (LOut ln syn st)) st} have a sup

   one common(?) case: LUpd ln syn x1 , LUpd ln syn x2 always have a sup

   - does l_ortho imply this?

 *)

(* a (almost) weaker version of l_ortho, that
   talks about when liftings are orthogonal in the sense
   that arbitrary lifted functions preserve sups at runtime *)
definition l_ortho_run ::
  "('x, 'a1, 'b :: Mergeable, 'z1) lifting_scheme \<Rightarrow>
   ('x, 'a2, 'b, 'z2) lifting_scheme \<Rightarrow>
   bool" where
"l_ortho_run l1 l2 = 
  (\<forall> x1 x2 . sups_pres {(\<lambda>syn . LUpd l1 syn x1), (\<lambda> syn . LUpd l2 syn x2)})"

lemma leq_sup :
  assumes H : "x1 <[ x2"
  shows "is_sup {x1, x2} x2"
proof(rule is_sup_intro)
  fix x
  assume "x \<in> {x1, x2}"
  then show "x <[ x2" using H leq_refl by auto
next
  fix x'
  assume "is_ub {x1, x2} x'"
  then show "x2 <[ x'"
    by(auto simp add: is_ub_def)
qed

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
  proof(rule is_ub_intro)
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

   

end