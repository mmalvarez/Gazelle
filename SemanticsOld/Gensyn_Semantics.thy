theory Gensyn_Semantics
  imports "../Gensyn" "../Gensyn_Descend"
begin

(* Exploring splitting this up into base and recursive gensyn sem *)

(* TODO:
break this file up into code and spec? *)

datatype ('x) gs_result =
  GRUnhandled
  | GRPath childpath
  | GRCrash
  | GRDone
  | GRFuel
  | GROther 'x

inductive nosem_x_sem::
  " 'x \<Rightarrow>
    'mstate \<Rightarrow> 
    'mstate \<Rightarrow> 
      childpath \<Rightarrow>
      ('x option) gensyn \<Rightarrow>  
      ('rx) gs_result \<Rightarrow>
      bool"
  where  "nosem_x_sem _ _ _ _ _ GRUnhandled"



locale Gensyn_Semantics_Sig =
  fixes  Gensyn_Semantics_parms  :: "'x \<Rightarrow>
                      'mstate \<Rightarrow> 
                      'mstate \<Rightarrow> 
                      childpath \<Rightarrow>
                      ('x option) gensyn \<Rightarrow>  
                      ('xr) gs_result \<Rightarrow>
                      bool" 
begin

definition x_sem :: _ where
"x_sem = Gensyn_Semantics_parms"

end


locale Gensyn_Semantics =
Gensyn_Semantics_Sig 

begin

print_context
(* NB this is a big step semantics. sufficient for Ethereum, but perhaps not enough
   for other platforms
   *)


inductive gensyn_sem ::
  "('a) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'b \<Rightarrow>
   'b \<Rightarrow>
   bool
  "
  where
  "\<And> t cp x l m m' .
    gensyn_get t cp = Some (G x l) \<Longrightarrow>
    x_sem x m m' cp (gs_map Some t) GRDone \<Longrightarrow>
    gensyn_sem t cp m m'"

| "\<And> t cp x l m cp' m' m'' .
    gensyn_get t cp = Some (G x l) \<Longrightarrow>
    x_sem x m m' cp (gs_map Some t) (GRPath cp') \<Longrightarrow>
    gensyn_sem t cp' m' m'' \<Longrightarrow>
    gensyn_sem t cp m m''"
end

print_locale Gensyn_Semantics

(* we can probably get away with just an exec version of this one *)
interpretation Gensyn_Semantics_Nosem : Gensyn_Semantics 
  nosem_x_sem
  done


(* test - numnodes predicate *)
fun gensyn_numnodes_l :: "('x) gensyn list \<Rightarrow> nat" where
"gensyn_numnodes_l [] = 1"
| "gensyn_numnodes_l ((G x l)#t) = gensyn_numnodes_l l + gensyn_numnodes_l t"

lemma gensyn_numnodes_l_nz : "gensyn_numnodes_l l > (0 :: nat)"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(case_tac a, auto)
    done
qed


(* in order to characterize when this works, though, we are going to
   need a way to characterize what the predicate is actually looking at *)

(* should the returned states be undefined? it shouldn't really matter. *)
fun nosem_x_sem_exec :: "'x \<Rightarrow> 'mstate \<Rightarrow>
  childpath \<Rightarrow> ('x) gensyn \<Rightarrow> ('xr gs_result * 'mstate)" where
"nosem_x_sem_exec _ m _ _ = (GRUnhandled, m)"

(* TODO: this still needs to be fixed up probably *)
(*
locale Gensyn_Semantics_Exec =
  fixes x_sem_exec :: "
                      'x \<Rightarrow> 
                      'mstate \<Rightarrow>
                      childpath \<Rightarrow> 
                      ('x) gensyn \<Rightarrow> 
                      ('xr gs_result *
                      'mstate)"

begin

(* TODO: deal with the rest of the exec stuff later *)

(* fueled interpreter for semantics *)
(* TODO: count down only for backwards jumps? *)
fun gensyn_sem_exec ::
  "('b, 'r, 'g) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
    nat \<Rightarrow>
   'mstate option" 
  where
  "gensyn_sem_exec t cp m 0 = None"

| "gensyn_sem_exec t cp m (Suc n) =
    (case gensyn_get t cp of
     None \<Rightarrow> None
     | Some (GBase g b) \<Rightarrow>
       (case base_sem_exec g b m cp t of

              (GRDone, m') \<Rightarrow> Some m'
             | (GRPath cp', m') \<Rightarrow> gensyn_sem_exec t cp' m' n
             | (_, _) \<Rightarrow> None)
     | Some (GRec g r l) \<Rightarrow>
        (case rec_sem_exec g r m cp t of
             (GRDone, m') \<Rightarrow> Some m'
             | (GRPath cp', m') \<Rightarrow> gensyn_sem_exec t cp' m' n
             | (_, _) \<Rightarrow> None))"

lemma gensyn_sem_exec_morefuel :
  assumes H: "gensyn_sem_exec t cp m n = Some m'"
  (*assumes Hn' : "n' > n"*)
  shows "gensyn_sem_exec t cp m (Suc n) = Some m'" using H
proof(induction n arbitrary: t cp m m')
  case 0
  then show ?case by auto
next
  case (Suc nx)
  thus ?case
  proof(cases "gensyn_get t cp")
    case None
    then show ?thesis using Suc by auto
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (GBase x11 x12)
      then show ?thesis using Suc Some
      proof(cases "base_sem_exec x11 x12 m cp t")
          case (Pair st' m'')
          then show ?thesis using Pair GBase Some Suc
            apply(case_tac st', auto)
            done
        qed
    next
      case (GRec x21 x22 x23)
      then show ?thesis
      proof(cases "rec_sem_exec x21 x22 m cp t")
          case (Pair st' m'')
          then show ?thesis using Pair GRec Some Suc
            apply(case_tac st', auto)
            done
        qed
      qed
    qed
  qed

fun gsx_base_sem :: " 'g \<Rightarrow> 
                      'b \<Rightarrow> 
                      'mstate \<Rightarrow>
                      'mstate \<Rightarrow>
                      childpath \<Rightarrow> 
                      ('b, 'r, 'g) gensyn \<Rightarrow>
                      ('xr) gs_result \<Rightarrow>
                      bool"
  where
"gsx_base_sem g b m m' cp t res = 
    (base_sem_exec g b m cp t = (res, m'))"


fun gsx_rec_sem :: "'g \<Rightarrow>
                    'r \<Rightarrow>
                    'mstate \<Rightarrow>
                    'mstate \<Rightarrow>
                    childpath \<Rightarrow>
                    ('b, 'r, 'g) gensyn \<Rightarrow>
                    ('xr) gs_result \<Rightarrow>
                    bool"
  where
"gsx_rec_sem g r m m' cp t res =
  (rec_sem_exec g r m cp t = (res, m'))"

fun gsx_gensyn_sem ::
"('b, 'r, 'g) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
   'mstate \<Rightarrow>
   bool
  "
where
"gsx_gensyn_sem t cp m m' =  (\<exists> fuel . gensyn_sem_exec t cp m fuel = Some m')"

end

(* standard version of the semantics *)
sublocale Gensyn_Semantics_Exec \<subseteq> Gensyn_Semantics
 where base_sem = gsx_base_sem and rec_sem = gsx_rec_sem
  done

context Gensyn_Semantics_Exec
begin



lemma gensyn_exec_eq_l2r :
  fixes t cp m m'
  shows  "gensyn_sem t cp m m' \<Longrightarrow> gsx_gensyn_sem t cp m m'"
  proof(induction rule: gensyn_sem.induct)
case (1 t cp g b m m')
  then show ?case
    apply(simp)
    apply(rule_tac x = 1 in exI) apply(auto)
    done
next
case (2 t cp g b m cp' m' m'')
  then show ?case
    apply(simp)
    apply(auto)
    apply(rule_tac x = "Suc fuel" in exI) apply(auto)
    done
next
  case (3 t cp g r l m m')
  then show ?case
    apply(simp)
    apply(rule_tac x = 1 in exI) apply(auto)
    done
next
  case (4 t cp g r l m cp' m' m'')
  then show ?case
    apply(simp)
    apply(auto)
    apply(rule_tac x = "Suc fuel" in exI) apply(auto)
    done
qed

lemma gensyn_exec_eq_r2l :
  fixes fuel
  shows "\<And> t cp m m'. gensyn_sem_exec t cp m (fuel) = Some m' \<Longrightarrow> gensyn_sem t cp m m'"
  proof(induction fuel)
    case 0
    then show ?case by auto
  next
    case (Suc fuel)
    then show ?case 
    proof(cases "gensyn_get t cp")
      case None
      then show ?thesis using Suc by auto
    next
      case (Some a)
      then show ?thesis using Suc
      proof(cases a)
        case (GBase x11 x12) then show ?thesis using Some Suc
        proof(cases "base_sem_exec x11 x12 m cp t")
            case (Pair a'' b)
            then show ?thesis using GBase Some Suc
              apply(simp)
              apply(case_tac a'', auto simp add: Gensyn_Semantics.gensyn_sem.intros)
              done
          qed
      next
        case (GRec x21 x22 x23)
        then show ?thesis using Some Suc
          proof(cases "rec_sem_exec x21 x22 m cp t")
            case (Pair a'' b)
            then show ?thesis using GRec Some Suc
              apply(simp)
              apply(case_tac a'', auto simp add: Gensyn_Semantics.gensyn_sem.intros)
              done
        qed
      qed
    qed
  qed

lemma gensyn_exec_agree :
  "gensyn_sem = gsx_gensyn_sem"
proof -
  have Goal : "\<And> t cp m m' . gensyn_sem t cp m m' = gsx_gensyn_sem t cp m m'" 
  proof -
  
  fix t cp m m'
    show "gensyn_sem t cp m m' = gsx_gensyn_sem t cp m m'"
      using gensyn_exec_eq_l2r gensyn_exec_eq_r2l  by auto
  qed

    thus "gensyn_sem = gsx_gensyn_sem" by blast
qed

(*
interpretation Gensyn_Exec_Semantics_Fuel : Gensyn_Semantics
 gsx_base_sem gsx_rec_sem
 rewrites Crew : "Gensyn_Exec_Semantics.gensyn_sem = gsx_gensyn_sem"
proof(unfold_locales)
  have Goal : "\<And> t cp m m' . Gensyn_Exec_Semantics.gensyn_sem t cp m m' = gsx_gensyn_sem t cp m m'" 
  proof - 
    fix t cp m m'
    show "Gensyn_Exec_Semantics.gensyn_sem t cp m m' = gsx_gensyn_sem t cp m m'"
      using gensyn_exec_eq_l2r gensyn_exec_eq_r2l  by auto
  qed

    thus "Gensyn_Exec_Semantics.gensyn_sem = gsx_gensyn_sem" by blast
  qed
*)
end

global_interpretation Gensyn_Exec_Semantics_Nosem : Gensyn_Semantics_Exec 
  "nosem_base_sem_exec :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> unit gs_result * _"
  "nosem_rec_sem_exec :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> unit gs_result * _"
  defines Gensyn_Exec_Semantics_Nosem_gensyn_sem_exec = Gensyn_Exec_Semantics_Nosem.gensyn_sem_exec
  and     Gensyn_Exec_Semantics_Nosem_gsx_base_sem = Gensyn_Exec_Semantics_Nosem.gsx_base_sem
  and     Gensyn_Exec_Semantics_Nosem_gsx_rec_sem = Gensyn_Exec_Semantics_Nosem.gsx_rec_sem
  done


lemmas [code_unfold] = Gensyn_Exec_Semantics_Nosem.gensyn_sem_exec.simps
lemmas [code_unfold] = Gensyn_Exec_Semantics_Nosem.gsx_base_sem.simps
lemmas [code_unfold] = Gensyn_Exec_Semantics_Nosem.gsx_rec_sem.simps

(* the lesson here is that we need to concretize before we export code *)

value "Gensyn_Exec_Semantics_Nosem.gensyn_sem_exec (GBase () ()) [] () (0 :: nat)"
*)
end