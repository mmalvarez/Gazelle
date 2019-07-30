theory Gensym_Semantics
  imports "../Gensym" "../Gensym_Descend"
begin

(* TODO:
break this file up into code and spec? *)

locale Gensym_Semantics =
  (* fixes/assumes go here *)
  (* NB: these are "small steps" in that they return a new childpath and don't do a full
         execution *)
  (* TODO: make these parametric in gensym parameters so that
           they can't do weird computations over tree other than
           calculating new childpath? *)
  fixes base_sem :: "('b, 'r, 'g) gensym \<Rightarrow>
                      'g \<Rightarrow> 
                      'b \<Rightarrow> 
                      childpath \<Rightarrow> 
                      'mstate \<Rightarrow> 
                      childpath option \<Rightarrow>
                      'mstate \<Rightarrow> 
                      bool"
  (* TODO: should rec_sem take the list component of GRec?
     probably not *)
  fixes rec_sem :: "('b, 'r, 'g) gensym \<Rightarrow>
                    'g \<Rightarrow>
                    'r \<Rightarrow>
                    childpath \<Rightarrow>
                    'mstate \<Rightarrow>
                    childpath option \<Rightarrow>
                    'mstate \<Rightarrow>
                    bool"
begin

(* NB this is a big step semantics. sufficient for Ethereum, but perhaps not enough
   for other platforms
   *)
inductive gensym_sem ::
  "('b, 'r, 'g) gensym \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
   'mstate \<Rightarrow>
   bool
  "
  where
  "\<And> t cp g b m m' .
    gensym_get t cp = Some (GBase g b) \<Longrightarrow>
    base_sem t g b cp m None m' \<Longrightarrow>
    gensym_sem t cp m m'"

| "\<And> t cp g b m cp' m' m'' .
    gensym_get t cp = Some (GBase g b) \<Longrightarrow>
    base_sem t g b cp m (Some cp') m' \<Longrightarrow>
    gensym_sem t cp' m' m'' \<Longrightarrow>
    gensym_sem t cp m m''"

| "\<And> t cp g r l m m' .
   gensym_get t cp = Some (GRec g r l) \<Longrightarrow>
   rec_sem t g r cp m None m' \<Longrightarrow>
   gensym_sem t cp m m'"

| "\<And> t cp g r l m cp' m' m'' .
   gensym_get t cp = Some (GRec g r l) \<Longrightarrow>
   rec_sem t g r cp m (Some cp') m' \<Longrightarrow>
   gensym_sem t cp' m' m'' \<Longrightarrow>
   gensym_sem t cp m m''"

end

locale Gensym_Semantics_Exec =
  fixes base_sem_exec :: "('b, 'r, 'g) gensym \<Rightarrow>
                      'g \<Rightarrow> 
                      'b \<Rightarrow> 
                      childpath \<Rightarrow> 
                      'mstate \<Rightarrow> 
                      (childpath option *
                      'mstate) option"

  fixes rec_sem_exec :: "('b, 'r, 'g) gensym \<Rightarrow>
                      'g \<Rightarrow>
                      'r \<Rightarrow>
                      childpath \<Rightarrow>
                      'mstate \<Rightarrow>
                      (childpath option *
                      'mstate) option"

begin

(* fueled interpreter for semantics *)
(* TODO: count down only for backwards jumps? *)
fun gensym_sem_exec ::
  "('b, 'r, 'g) gensym \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
    nat \<Rightarrow>
   'mstate option" 
  where
  "gensym_sem_exec t cp m 0 = None"

| "gensym_sem_exec t cp m (Suc n) =
    (case gensym_get t cp of
     None \<Rightarrow> None
     | Some (GBase g b) \<Rightarrow>
       (case base_sem_exec t g b cp m of
             None \<Rightarrow> None
             | Some (None, m') \<Rightarrow> Some m'
             | Some (Some cp', m') \<Rightarrow> gensym_sem_exec t cp' m' n)
     | Some (GRec g r l) \<Rightarrow>
        (case rec_sem_exec t g r cp m of
             None \<Rightarrow> None
             | Some (None, m') \<Rightarrow> Some m'
             | Some (Some cp', m') \<Rightarrow> gensym_sem_exec t cp' m' n))"

lemma gensym_sem_exec_morefuel :
  assumes H: "gensym_sem_exec t cp m n = Some m'"
  (*assumes Hn' : "n' > n"*)
  shows "gensym_sem_exec t cp m (Suc n) = Some m'" using H
proof(induction n arbitrary: t cp m m')
  case 0
  then show ?case by auto
next
  case (Suc nx)
  thus ?case
  proof(cases "gensym_get t cp")
    case None
    then show ?thesis using Suc by auto
  next
    case (Some a)
    then show ?thesis 
    proof(cases a)
      case (GBase x11 x12)
      then show ?thesis using Suc Some
      proof(cases "base_sem_exec t x11 x12 cp m")
        assume None': "base_sem_exec t x11 x12 cp m = None"
        then show ?thesis using Suc Some GBase by auto
      next
        fix stm'
        assume Some': "base_sem_exec t x11 x12 cp m = Some stm'"
        then show ?thesis
        proof(cases stm')
          case (Pair st' m'')
          then show ?thesis
          proof(cases st')
            assume None'' : "st' = None"
            thus ?thesis using Pair Some' GBase Some Suc by auto
          next
            fix st's
            assume Some'' : "st' = Some st's"
            thus ?thesis using Pair Some' GBase Some Suc by auto
          qed
        qed
      qed
    next
      case (GRec x21 x22 x23)
      then show ?thesis
      proof(cases "rec_sem_exec t x21 x22 cp m")
        assume None' :"rec_sem_exec t x21 x22 cp m = None"
        then show ?thesis using Suc Some GRec by auto
      next
        fix stm'
        assume Some': "rec_sem_exec t x21 x22 cp m = Some stm'"
        then show ?thesis
        proof(cases stm')
          case (Pair st' m'')
          then show ?thesis
          proof(cases st')
            assume None'' : "st' = None"
            thus ?thesis using Pair Some' GRec Some Suc by auto
          next
            fix st's
            assume Some'' : "st' = Some st's"
            thus ?thesis using Pair Some' GRec Some Suc by auto
          qed
        qed
      qed
    qed
  qed
qed

definition gsx_base_sem :: "('b, 'r, 'g) gensym \<Rightarrow>
                      'g \<Rightarrow> 
                      'b \<Rightarrow> 
                      childpath \<Rightarrow> 
                      'mstate \<Rightarrow> 
                      childpath option \<Rightarrow>
                      'mstate \<Rightarrow> 
                      bool"
  where
"gsx_base_sem  =
  (\<lambda> t g b cp m cp' m' . base_sem_exec t g b cp m = Some (cp', m'))"

definition gsx_rec_sem :: "('b, 'r, 'g) gensym \<Rightarrow>
                    'g \<Rightarrow>
                    'r \<Rightarrow>
                    childpath \<Rightarrow>
                    'mstate \<Rightarrow>
                    childpath option \<Rightarrow>
                    'mstate \<Rightarrow>
                    bool"
  where
"gsx_rec_sem  =
  (\<lambda>  t g r cp m cp' m' . rec_sem_exec t g r cp m = Some (cp', m'))"

definition gsx_gensym_sem ::
"('b, 'r, 'g) gensym \<Rightarrow>
   childpath \<Rightarrow>
   'mstate \<Rightarrow>
   'mstate \<Rightarrow>
   bool
  "
where
"gsx_gensym_sem  =
  (\<lambda> t cp m m' . \<exists> fuel . gensym_sem_exec t cp m fuel = Some m')"

(* standard version of the semantics *)
interpretation Gensym_Exec_Semantics : Gensym_Semantics
 gsx_base_sem gsx_rec_sem
  done

lemma gensym_exec_eq_l2r :
  fixes t cp m m'
  shows  "Gensym_Exec_Semantics.gensym_sem t cp m m' \<Longrightarrow> gsx_gensym_sem t cp m m'"
  proof(induction rule: Gensym_Exec_Semantics.gensym_sem.induct)
case (1 t cp g b m m')
  then show ?case
    apply(simp add: gsx_gensym_sem_def gsx_base_sem_def)
    apply(rule_tac x = 1 in exI) apply(auto)
    done
next
case (2 t cp g b m cp' m' m'')
  then show ?case
    apply(simp add: gsx_gensym_sem_def gsx_base_sem_def)
    apply(auto)
    apply(rule_tac x = "Suc fuel" in exI) apply(auto)
    done
next
  case (3 t cp g r l m m')
  then show ?case
    apply(simp add: gsx_gensym_sem_def gsx_rec_sem_def)
    apply(rule_tac x = 1 in exI) apply(auto)
    done
next
  case (4 t cp g r l m cp' m' m'')
  then show ?case
    apply(simp add: gsx_gensym_sem_def gsx_rec_sem_def)
    apply(auto)
    apply(rule_tac x = "Suc fuel" in exI) apply(auto)
    done
qed

lemma gensym_exec_eq_r2l :
  fixes fuel
  shows "\<And> t cp m m'. gensym_sem_exec t cp m (fuel) = Some m' \<Longrightarrow> Gensym_Exec_Semantics.gensym_sem t cp m m'"
  proof(induction fuel)
    case 0
    then show ?case by auto
  next
    case (Suc fuel)
    then show ?case 
    proof(cases "gensym_get t cp")
      case None
      then show ?thesis using Suc by auto
    next
      case (Some a)
      then show ?thesis using Suc
      proof(cases a)
        case (GBase x11 x12) then show ?thesis using Some Suc
        proof(cases "base_sem_exec t x11 x12 cp m")
          assume None' : "base_sem_exec t x11 x12 cp m = None"
          thus ?thesis using GBase Some Suc by auto
        next
          fix a'
          assume Some' : "base_sem_exec t x11 x12 cp m = Some a'"
          thus ?thesis using GBase Some Suc
          proof(cases a')
            case (Pair a'' b)
            then show ?thesis using Some' GBase Some Suc
            proof(cases a'')
              assume None'' : "a'' = None"
              then show ?thesis using Pair Some' GBase Some Suc Gensym_Semantics.gensym_sem.intros
                by (auto simp add:gsx_base_sem_def)
            next
              fix a'''
              assume Some'' : "a'' = Some a'''"
              then show ?thesis using Pair Some' GBase Some Suc 
                    Gensym_Semantics.gensym_sem.intros(2)[of t cp x11 x12 gsx_base_sem]
                by (auto simp add:gsx_base_sem_def)
            qed
          qed
        qed
      next

  case (GRec x21 x22 x23)
  then show ?thesis using Some Suc
  proof(cases "rec_sem_exec t x21 x22 cp m")
    assume None' : "rec_sem_exec t x21 x22 cp m = None"
    thus ?thesis using GRec Some Suc by auto
  next

    fix a'
    assume Some' : "rec_sem_exec t x21 x22 cp m = Some a'"
    thus ?thesis using GRec Some Suc
    proof(cases a')
      case (Pair a'' b)
      then show ?thesis
      proof(cases a'')
        assume None'' : "a'' = None"
        thus ?thesis using GRec Some Suc Some' Pair
              Gensym_Semantics.gensym_sem.intros gsx_rec_sem_def
          by auto

      next

        fix a'''
        assume Some'' : "a'' = Some a'''"
        thus ?thesis using GRec Some Suc Some' Pair
              Gensym_Semantics.gensym_sem.intros(4)[of t cp x21 x22 x23 gsx_rec_sem] gsx_rec_sem_def
          by auto
      qed
    qed
  qed
qed
qed
qed

(* version of the semantics that just wraps the fueled interpreter *)
(* OK, we need some kind of lemma that will let us turn (f = g) into (forall x, f x = g x) *)
interpretation Gensym_Exec_Semantics_Fuel : Gensym_Semantics
 gsx_base_sem gsx_rec_sem
 rewrites Crew : "Gensym_Exec_Semantics.gensym_sem = gsx_gensym_sem"
proof(unfold_locales)
  have Goal : "\<And> t cp m m' . Gensym_Exec_Semantics.gensym_sem t cp m m' = gsx_gensym_sem t cp m m'" 
  proof - 
    fix t cp m m'
    show "Gensym_Exec_Semantics.gensym_sem t cp m m' = gsx_gensym_sem t cp m m'"
      using gensym_exec_eq_l2r
                             gensym_exec_eq_r2l gsx_gensym_sem_def by auto
  qed

    thus "Gensym_Exec_Semantics.gensym_sem = gsx_gensym_sem" by blast
  qed

end

end