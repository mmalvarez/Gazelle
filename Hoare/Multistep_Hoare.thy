theory Multistep_Hoare imports Hoare "../Semantics/Gensyn_Sem_Small"
"../Gensyn_Descend_Facts"
begin

(* Idea here:
  - _partial_ correctness
  - so we need some kind of way to talk about case where we run out of gas (or don't terminate, etc)
 *)

(*
 * should we be explicit about how we pull out the gensyn_skel? 
 * this would (e.g. if it is a lifting) enable explicitly updating
 * however, we can probably handle this at the predicate level
*)

(*
definition semprop_gsx ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool)"
  ("|? _ ?|")  
  where
"semprop_gsx gs x m m' =
  (\<exists> n flag . gensyn_sem_small_exec_many gs x n m = (m', flag))"

*)

(* will concrete childpaths be sufficient here? *)
definition GVT ::
  "('x, 'mstate) g_sem \<Rightarrow>
  childpath \<Rightarrow>
   (('mstate) \<Rightarrow> bool) \<Rightarrow> 
   'x gensyn \<Rightarrow> 
   gensyn_small_result \<Rightarrow>
   (('mstate) \<Rightarrow> bool) \<Rightarrow>
   bool"
  ("|? _ ?| % {? _, _ ?} _ {? _, _ ?}")
  where
"GVT gs cp1 P prog res Q =
  (\<forall> st .
    P (st) \<longrightarrow>
    (\<exists> n st' . gensyn_sem_small_exec_many gs cp1 prog n st = (st', res) \<and>
       Q (st')))"

lemma GVTI [intro] :
  assumes "(\<And> st . P st  \<Longrightarrow> 
              (\<exists> n st' . gensyn_sem_small_exec_many gs cp prog n st = (st', res) \<and> Q (st')))"
  shows "|? gs ?| % {?cp, P?} prog {?res, Q?}" using assms
  unfolding GVT_def 
  by(auto)

lemma GVTE [elim]:
  assumes "|? gs ?| % {?cp, P?} prog {?res, Q?}"
  assumes "P (st)"
  obtains n st' where 
    "gensyn_sem_small_exec_many gs cp prog n st = (st', res)"
    "Q (st')"
  using assms
  unfolding GVT_def 
  by blast

(* lifting Hoare rules from single step into VTSM *)
(* TODO: make this more general now that childpaths aren't concrete. *)
lemma vtsm_lift_step_cont :
  assumes H0 : "gs_sem f' = f"
  assumes Hend : "\<And> st . Q st \<Longrightarrow> childpath_update cp (gs_getpath f' st) = Some cp'"
  assumes Hpath : "gensyn_get prog cp = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  shows "|? f' ?| % {?cp,P?} prog {? Ok cp',Q?}"
proof
  fix st
  assume HP : "P st"
  
  have Hf : "(!f) s st (f s st)" by(rule semprop2I)

  have Qf : "Q (f s st)" using VTE[OF H HP Hf] by auto

  have End : "childpath_update cp (gs_getpath f' (f s st)) = Some cp'"
    using Hend[OF Qf] by auto

  have Conc' :  "gensyn_sem_small_exec_many f' cp prog 1 st = (f s st, Ok cp')"
    using H0 Hpath End by auto

  show "\<exists>n st'. gensyn_sem_small_exec_many f' cp prog n st = (st', Ok cp') \<and> Q st'"  
    using Conc' Qf by blast
qed

lemma vtsm_step_halt :
  assumes H0 : "gs_sem f' = f"
  assumes Hend : "\<And> st . Q st \<Longrightarrow> childpath_update cp (gs_getpath f' st) = None"
  assumes Hpath : "gensyn_get prog cp = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  shows "|? f' ?| % {?cp,P?} prog {? Halted,Q?}"
proof
  fix st
  assume HP : "P st"
  
  have Hf : "(!f) s st (f s st)" by(rule semprop2I)

  have Qf : "Q (f s st)" using VTE[OF H HP Hf] by auto

  have End : "childpath_update cp (gs_getpath f' (f s st)) = None"
    using Hend[OF Qf] by auto

  have Conc' :  "gensyn_sem_small_exec_many f' cp prog 1 st = (f s st, Halted)"
    using H0 Hpath End by auto

  show "\<exists>n st'. gensyn_sem_small_exec_many f' cp prog n st = (st', Halted) \<and> Q st'"  
    using Conc' Qf by blast
qed

lemma vtsm_lift_cont :
  assumes H0 : "gs_sem f' = f"
  assumes Hstart : "\<And> st . Q st \<Longrightarrow> childpath_update p1 (gs_getpath f' st) = Some p2" 
  assumes Hp1 : "gensyn_get prog p1 = Some (G s l)"
(*  assumes Hstart' : "\<And> st . Q st \<Longrightarrow> gs_pathD (gs_getpath f' st) p2 = Some p3" *)
  assumes H : "(!f) % {{P}} s {{Q}}"
  assumes H' : "|? f' ?| % {?p2,Q?} prog {?res,Q'?}"
  shows "|? f' ?| % {?p1,P?} prog {?res,Q'?}"
proof(rule GVTI)

  fix st
  assume HP : "P st"

  have Hf : "(!f) s st (f s st)" by(rule semprop2I)

  have Qf : "Q (f s st)" using VTE[OF H HP Hf] by auto

  have Start : "childpath_update p1 (gs_getpath f' (f s st)) = Some p2"
    using Hstart[OF Qf] by auto

  obtain st' n where
    Exc : "gensyn_sem_small_exec_many f' p2 prog n (f s st) = (st', res)" and
    Q' : "Q' st'"
    using GVTE[OF H' Qf] by auto

  have Conc' : "gensyn_sem_small_exec_many f' p1 prog (n+1) st = (st', res)"
    using Exc Start H0 Hp1
    by(auto)

  show "\<exists>n st'.
           gensyn_sem_small_exec_many f' p1 prog n st = (st', res) \<and> Q' st'"
    using Conc' Q' by blast
qed

lemma gsxm_steps_steps :
  assumes H1 : "gensyn_sem_small_exec_many f' cp1 prog n1 st1 = (st2, Ok cp2)"
  assumes H2 : "gensyn_sem_small_exec_many f' cp2 prog n2 st2 = (st3, res)"
  shows "gensyn_sem_small_exec_many f' cp1 prog (n1 + n2) st1 = (st3, res)" using assms
proof(induction n1 arbitrary: st1 st2 cp1 cp2 n2 res)
  case 0
  then show ?case by(auto)
next
  case (Suc n1)
  show ?case 
  proof(cases "gensyn_get prog cp1")
    case None
    then show ?thesis using Suc by(auto)
  next
    case (Some x1)

    obtain x1l x1t where X1 : "x1 = G x1l x1t" by(cases x1; auto)

    show ?thesis 
    proof(cases "childpath_update cp1 (gs_getpath f' (gs_sem f' x1l st1))")
      case None' : None
      then show ?thesis using Suc Some X1 by auto
    next
      case Some' : (Some cp2')

      have Cp2 : "cp2' = cp2'"
        using Suc Some Some' X1 by auto

      then show ?thesis using Suc Some X1 Some' by(auto)
    qed
  qed
qed

lemma vtsm_seq :
  assumes H1 : "|? f' ?| % {?cp1,P1?} prog {?Ok cp2,P2?}"
  assumes H2 : "|? f' ?| % {?cp2,P2?} prog {?res,P3?}"
  shows "|? f' ?| % {?cp1,P1?} prog {?res,P3?}"
proof(rule GVTI)
  fix st1
  assume HP : "P1 st1"

  obtain n1 st2 where
    Ex1 : "gensyn_sem_small_exec_many f' cp1 prog n1 st1 = (st2, Ok cp2)" and
    Q1 : "P2 st2"
    using GVTE[OF H1 HP] by auto

  obtain n2 st3 where
    Ex2 : "gensyn_sem_small_exec_many f' cp2 prog n2 st2 = (st3, res)" and
    Q'2 : "P3 st3" using GVTE[OF H2 Q1] by auto

  have Conc' : "gensyn_sem_small_exec_many f' cp1 prog (n1 + n2) st1 = (st3, res)"
    using gsxm_steps_steps[OF Ex1 Ex2] by auto

  show "\<exists>n st'. gensyn_sem_small_exec_many f' cp1 prog n st1 = (st', res) \<and> P3 st'"
    using Q'2 Conc' by blast
qed

lemma childpath_rev_update_suffix :
  assumes "childpath_rev_update cp upd = Some cp'"
  shows "childpath_rev_update (cp@suf) upd = Some (cp'@suf)"
  using assms
proof(induction cp arbitrary: suf)
  case Nil
  then show ?case by(cases upd; auto)
next
  case (Cons ch ct)
  show ?case 
  proof(cases upd)
    case Parent
    then show ?thesis
      using Cons by(auto)
  next
    case (Desc x2)
    then show ?thesis
      using Cons by(auto)
  qed
qed

lemma childpath_rev_update_None :
  assumes H: "childpath_rev_update cp upd = None"
  shows "upd = Parent" "cp = []"
proof(cases cp)
  case Nil
  {
    show "upd = Parent" using Nil H by(cases upd; auto)
  }
next
  case (Cons a list)
  {
    have "False" using Cons H by(cases upd; auto)
    thus "upd = Parent" by auto
  }
next
  show "cp = []" using H by(cases cp; cases upd; auto)
qed

lemma childpath_rev_update_suffix_None :
  assumes H: "childpath_rev_update cp upd = None"
  shows "childpath_rev_update (cp@(sufh#suft)) upd = Some suft" using assms
proof(cases cp)
  case Nil
  then show ?thesis using H
    by(cases upd; auto)
next
  case (Cons a list)
  then show ?thesis using H
    by(cases upd; auto)
qed

lemma childpath_update_prefix :
  assumes H: "childpath_update cp upd = Some cp'"
  shows "childpath_update (pref@cp) upd = Some (pref@cp')"
proof-

  show "childpath_update (pref @ cp) upd = Some (pref @ cp')"
    using H childpath_rev_update_suffix 
  unfolding childpath_update_def
  by(auto split:option.splits)
qed

lemma childpath_update_None :
  assumes H: "childpath_update cp upd = None"
  shows "upd = Parent" "cp = []"
proof-
  have H' : "childpath_rev_update (rev cp) upd = None"
    using H
    unfolding childpath_update_def
    by(auto split:option.split_asm)

  show "upd = Parent"
    using childpath_rev_update_None[OF H'] by auto

  show "cp = []"
    using childpath_rev_update_None[OF H'] by auto
qed


lemma childpath_update_prefix_None :
  assumes H: "childpath_update cp upd = None"
  shows "childpath_update ((prefb@[preft])@cp) upd = Some prefb" 
proof-
  obtain sufh suft where Suf :
    "rev((prefb@[preft])) = sufh#suft"
    by(cases "rev(prefb@[preft])"; auto)

  have H' : "childpath_rev_update (rev cp) upd = None"
    using H unfolding childpath_update_def
    by(auto split:option.splits)

  have Upd' : "childpath_rev_update ((rev cp)@(sufh#suft)) upd = Some suft"
    using childpath_rev_update_suffix_None[OF H'] by auto

  have Rev : "(rev ((prefb@[preft]) @ cp)) = (rev cp @ rev (prefb@[preft]))"
    by auto

  show "childpath_update ((prefb@[preft]) @ cp) upd = Some prefb" using Upd'
    unfolding childpath_update_def Rev using Suf
    by(auto)
qed

lemma droplast'_snoc :
  "droplast' (l @ [x]) = l"
proof(induction l arbitrary: x)
case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by(cases l; auto)
qed

lemma droplast_snoc :
  "droplast (l @ [x]) = Some l"
proof(induction l arbitrary: x)
case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by(cases l; auto)
qed

lemma droplast_snoc_conv :
  assumes H : "droplast l = Some l'"
  shows "\<exists> x . l = (l' @ [x])" using assms
proof(induction l arbitrary: l')
case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by(cases l; auto split:option.splits)
qed

lemma cons_snoc :
  "\<exists> xb xx . xh # xt = (xb @ [xx])"
proof(induction xt arbitrary: xh)
  case Nil
  then show ?case by auto
next
  case (Cons a xt)

  obtain xb1 xx where Xb : "a#xt = xb1 @ [xx]"
    using Cons[of a] by auto

  have Conc' : "xh # a # xt = xh#xb1 @ [xx]" using Xb
    by(auto)

  thus ?case by auto
qed


lemma gsxm_sub_steps :
  assumes Hp : "gensyn_get prog1 ppre = Some prog2"
  assumes H: "gensyn_sem_small_exec_many f' cp1 prog2 n st1 = (st2, Ok cp2)"
  shows "gensyn_sem_small_exec_many f' (ppre@cp1) prog1 n st1 = (st2, Ok (ppre@cp2))"
  using assms
proof(induction n arbitrary: cp1 st1 cp2 st2)
  case 0
  then show ?case
    by(auto)
next
  case (Suc n)

  then obtain xl xd where X : "gensyn_get prog2 cp1 = Some (G xl xd)"
    by(cases "gensyn_get prog2 cp1"; auto)

  have Comp : "gensyn_get prog1 (ppre @ cp1) = Some (G xl xd)"
    using gensyn_get_comp[OF X Hp] by auto

  obtain cp_next where Cnext :
    "childpath_update cp1 (gs_getpath f' (gs_sem f' xl st1)) = Some cp_next"
    using Suc.prems X 
    by(cases "childpath_update cp1 (gs_getpath f' (gs_sem f' xl st1))"; auto simp add: Let_def)

  have Next :
    "gensyn_sem_small_exec_many f' cp_next prog2 n (gs_sem f' xl st1) = (st2, Ok cp2)"
    using Suc.prems X Cnext
    by(auto simp add: Let_def)

  have Cp2_pre :
    "childpath_update (ppre @ cp1) (gs_getpath f' (gs_sem f' xl st1)) = Some (ppre @ cp_next)"
    using childpath_update_prefix[OF Cnext] by auto

  show ?case using Suc.IH[OF Hp Next] Comp Cp2_pre
    by(auto simp add: Let_def)
qed

lemma vtsm_sub_steps :
  assumes Hp : "gensyn_get prog1 ppre = Some prog2"
  assumes H : "|? f' ?| % {?cp1,P1?} prog2 {?Ok cp2,P2?}"
  shows "|? f' ?| % {?(ppre@cp1),P1?} prog1 {?Ok (ppre@cp2),P2?}"
proof
  fix st
  assume Hin : "P1 st"

  obtain n st' where Exec : "gensyn_sem_small_exec_many f' cp1 prog2 n st = (st', Ok cp2)" and P2 : "P2 st'"
    using GVTE[OF H Hin] by auto

  show "\<exists>n st'.
             gensyn_sem_small_exec_many f' (ppre @ cp1) prog1 n st =
             (st', Ok (ppre @ cp2)) \<and>
             P2 st'"
    using gsxm_sub_steps[OF Hp Exec] P2 by auto
qed

(* this lemma is "precise", but I'm not sure if it's as useful as the next one *)
lemma gsxm_sub_halt_step :
  assumes Hp : "gensyn_get prog1 ppre = Some prog2"
  assumes Hdrop : "droplast ppre = Some ppre'"
  assumes Hlast: "gensyn_sem_small_exec_many f' cp1 prog2 n st1 = (st2, Ok cp2)"
  assumes Hhalt: "gensyn_sem_small_exec f' cp2 prog2 st2 = (st3, Halted)"
  shows "gensyn_sem_small_exec_many f' (ppre@cp1) prog1 (Suc n) st1 = (st3, Ok ppre')"
  using assms
proof(induction n arbitrary: cp1 cp2 st1 st2 st3 ppre ppre' prog1 prog2)
  case 0

  then obtain xl xd where X : "gensyn_get prog2 cp1 = Some (G xl xd)"
    by(cases "gensyn_get prog2 cp1"; auto)

  have Comp : "gensyn_get prog1 (ppre @ cp1) = Some (G xl xd)"
    using gensyn_get_comp[OF X] 0 by auto

  have X' : "gensyn_get prog1 (ppre @ cp1) = Some (G xl xd)"
    using 0 Comp X
    by(cases "gensyn_get prog1 (ppre @ cp1)"; auto)

  have Sub_None: "childpath_update cp2 (gs_getpath f' (gs_sem f' xl st2)) = None"
    using 0 X Comp X'
    by(auto split:option.splits simp add: Let_def)

  obtain ppreh ppret where Ppre_cons : "ppre = ppreh#ppret"
    using "0.prems" by(cases ppre; auto)

  obtain ppreb pprex where Ppre :
    "ppre = ppreb @ [pprex]" using Ppre_cons cons_snoc[of ppreh ppret] by auto

  have Ppre' : "ppreb = ppre'"
    using 0 droplast_snoc[of ppreb pprex] Ppre by auto
    
  have Upd : "childpath_update (ppre@cp2) (gs_getpath f' (gs_sem f' xl st2)) = Some ppreb" 
    using childpath_update_prefix_None[OF Sub_None, of ppreb pprex] Ppre
    by(auto)

  show ?case using 0 X Comp X' Upd Ppre'
    by(auto split:option.splits simp add: Let_def)
next
  case (Suc n)

  then obtain xl xd where X : "gensyn_get prog2 cp1 = Some (G xl xd)"
    by(cases "gensyn_get prog2 cp1"; auto)

  have Comp : "gensyn_get prog1 (ppre @ cp1) = Some (G xl xd)"
    using gensyn_get_comp[OF X] Suc by auto

  have X' : "gensyn_get prog1 (ppre @ cp1) = Some (G xl xd)"
    using Suc Comp X
    by(cases "gensyn_get prog1 (ppre @ cp1)"; auto)

  obtain ppreh ppret where Ppre_cons : "ppre = ppreh#ppret"
    using "Suc.prems" by(cases ppre; auto)

  obtain ppreb pprex where Ppre :
    "ppre = ppreb @ [pprex]" using Ppre_cons cons_snoc[of ppreh ppret] by auto

  have Ppre' : "ppreb = ppre'"
    using Suc droplast_snoc[of ppreb pprex] Ppre by auto

  show ?case
  proof(cases "childpath_update cp1 (gs_getpath f' (gs_sem f' xl st1))")
    case None
    then show ?thesis 
    proof(cases ppre)
      case Nil
      then show ?thesis
        using Suc X Comp X' None
        by(auto)
    next
      case (Cons ppreh ppret)
      then show ?thesis
        using Suc X Comp X' None
        by(auto)
    qed
  next
    case (Some cp1a)

    show ?thesis
    proof(cases "gensyn_get prog2 cp1a")
      case None' : None
      then show ?thesis 
        using Some Suc.prems X Comp X' by(cases n; auto)
    next
      case Some' : (Some desc1a)

      have Upd : "childpath_update (ppre@cp1) (gs_getpath f' (gs_sem f' xl st1)) = Some (ppre@cp1a)" 
        using childpath_update_prefix[OF Some, of ppre] Ppre Ppre'
        by(auto)

      then show ?thesis using Some Suc  X Comp X'
        by(auto split:option.splits simp add: Let_def)
    qed
  qed
qed

lemma vtsm_sub_halt_step :
  assumes Hp : "gensyn_get prog1 ppre = Some prog2"
  assumes Hdrop : "droplast ppre = Some ppre'"
  assumes Hlast : "|? f' ?| % {?cp1, P1?} prog2 {?Ok cp2, P2?}"
  assumes Hhalt: "\<And> st2 . P2 st2 \<Longrightarrow> 
    \<exists> st3 . gensyn_sem_small_exec f' cp2 prog2 st2 = (st3, Halted) \<and> P3 st3"
  shows "|? f' ?| % {? (ppre @ cp1), P1?} prog1 {? Ok ppre', P3?}"
proof
  fix st1
  assume Hin : "P1 st1"

  obtain n1 st2 where Exec1 : "gensyn_sem_small_exec_many f' cp1 prog2 n1 st1 =
    (st2, Ok cp2)" and P2 : "P2 st2"
    using GVTE[OF Hlast Hin] by auto

  obtain st3 where Exec2 : "gensyn_sem_small_exec f' cp2 prog2 st2 = (st3, Halted)"
    and P3 : "P3 st3"
    using Hhalt[OF P2] by auto

  have Conc' : "gensyn_sem_small_exec_many f' (ppre @ cp1) prog1 (Suc n1) st1 =
                   (st3, Ok ppre') \<and> P3 st3"
    using gsxm_sub_halt_step[OF Hp Hdrop Exec1 Exec2] P3
    by auto

  then show "\<exists>n st'.
               gensyn_sem_small_exec_many f' (ppre @ cp1) prog1 n st1 =
               (st', Ok ppre') \<and>
               P3 st'"
    by blast
qed

lemma gsxm_sub_halt :
  assumes Hp : "gensyn_get prog1 ppre = Some prog2"
  assumes Hdrop : "droplast ppre = Some ppre'"
  assumes H: "gensyn_sem_small_exec_many f' cp1 prog2 n st1 = (st2, Halted)"
  shows "(\<exists> n' . n' \<le> n \<and>
            gensyn_sem_small_exec_many f' (ppre@cp1) prog1 n' st1 = (st2, Ok ppre'))"
  using assms
proof(induction n arbitrary: cp1 st1 st2 ppre ppre' prog1 prog2)
  case 0
  then show ?case
    by(auto)
next
  case (Suc n)

  then obtain xl xd where X : "gensyn_get prog2 cp1 = Some (G xl xd)"
    by(cases "gensyn_get prog2 cp1"; auto)

  have Comp : "gensyn_get prog1 (ppre @ cp1) = Some (G xl xd)"
    using gensyn_get_comp[OF X] Suc by auto

  have X' : "gensyn_get prog1 (ppre @ cp1) = Some (G xl xd)"
    using Suc Comp X
    by(cases "gensyn_get prog1 (ppre @ cp1)"; auto)

  show ?case using Suc
  proof(cases "childpath_update cp1 (gs_getpath f' (gs_sem f' xl st1))")
    case None

    show ?thesis
    proof(cases ppre)
      case Nil
      then show ?thesis
        using Suc X Comp X' None
        by(auto)
    next
      case (Cons ppreh ppret)

      obtain ppreb pprex where Ppre :
        "ppre = ppreb @ [pprex]" using Cons cons_snoc[of ppreh ppret] by auto

      have Ppre' : "ppreb = ppre'"
        using Suc.prems(2) droplast_snoc[of ppreb pprex] Ppre by auto
        
      have Upd : "childpath_update (ppre@cp1) (gs_getpath f' (gs_sem f' xl st1)) = Some ppreb" 
        using childpath_update_prefix_None[OF None, of ppreb pprex] Ppre
        by(auto)

      have CpNil : "cp1 = []" and Par : "(gs_getpath f' (gs_sem f' xl st1)) = Parent"
        using childpath_update_None[OF None] by auto

      (* in this case we halt immediately. *)
      have Conc'1 : "gensyn_sem_small_exec_many f' (ppre @ cp1)
        prog1 1 st1 =
       (st2, Ok ppre')"
        using Upd Cons None Comp X X' Ppre Suc.prems CpNil Par Ppre'
        by(auto)

      have Conc'2 : "1 \<le> Suc n" by auto

      show ?thesis using Conc'1 Conc'2 by auto
    qed
  next
    case(Some cp1a)
    show ?thesis
    proof(cases "gensyn_get prog2 cp1a")
      case None' : None
      then show ?thesis 
        using Some Suc.prems X Comp X' by(cases n; auto)
    next
      case Some' : (Some desc1a)

      have Exec : "gensyn_sem_small_exec_many f' cp1a prog2 n (gs_sem f' xl st1) = (st2, Halted)"
        using Some Suc.prems  X Comp X' 
        by(auto split:option.splits simp add: Let_def)

      have Upd : "childpath_update cp1 (gs_getpath f' (gs_sem f' xl st1)) = Some cp1a"
        using Some Suc.prems  X Comp X' Some'
        by(auto)

      show ?thesis using Some Suc.prems  X Comp X' Suc.IH[OF Suc.prems(1) Suc.prems(2) Exec] Some'
          childpath_update_prefix[OF Upd,of ppre]
        by(auto)
    qed
  qed
qed

lemma vtsm_sub_halt :
  assumes Hp : "gensyn_get prog1 ppre = Some prog2"
  assumes Hdrop : "droplast ppre = Some ppre'"
  assumes H : "|? f' ?| % {?cp1, P1?} prog2 {?Halted, P2?}"
  shows "|? f' ?| % {?(ppre @ cp1), P1?} prog1 {?Ok ppre', P2?}"
proof
  fix st
  assume Hin : "P1 st"

  obtain n st' where Exec : "gensyn_sem_small_exec_many f' cp1 prog2 n st = (st', Halted)"
    and P2 : "P2 st'"
    using GVTE[OF H Hin] by auto

  obtain n' where Exec' :
    "gensyn_sem_small_exec_many f' (ppre @ cp1) prog1 n' st = (st', Ok ppre')"
    using gsxm_sub_halt[OF Hp Hdrop Exec] by auto

  show "\<exists>n st'.
             gensyn_sem_small_exec_many f' (ppre @ cp1) prog1 n st =
             (st', Ok ppre') \<and>
             P2 st'"
    using Exec' P2 by blast
qed


(* necessary theorems (sketch):
1. for a single instruction Hoare rule (assuming already lifted):
in
*)


end