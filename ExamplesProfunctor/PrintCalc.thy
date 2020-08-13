theory PrintCalc imports
 "../MergeableTc/Mergeable" "../MergeableTc/MergeableInstances" 
  "../Lifting/LiftInstancesProfunctor"
begin


datatype calc =
  Cadd int
  | Csub int
  | Cmul int
  | Cdiv int
  | Creset int
  | Cskip

(*
datatype calc_st = CSi int
*)
definition calc_sem :: "calc \<Rightarrow> int \<Rightarrow> int" where
"calc_sem syn st = 
  (case syn of
     (Cadd i) \<Rightarrow> st + i
    |(Csub i) \<Rightarrow> st - i
    |(Cmul i) \<Rightarrow> st * i
    |(Cdiv i) \<Rightarrow> divide_int_inst.divide_int st i
    |(Creset i) \<Rightarrow> i
    | Cskip \<Rightarrow> st)"



(* need "liftable" typeclass"? *)

datatype print =
  Pprint
  | Preset
  | Pskip


type_synonym state = "int md_triv option md_prio * int list md_triv option"

datatype syn =
  Sadd int
  | Ssub int
  | Smul int
  | Sdiv int
  | Sreset int
  | Sskip

definition print_trans :: "syn \<Rightarrow> print" where
"print_trans c = 
  (case c of
    Sreset _ \<Rightarrow> Preset
    | Sskip \<Rightarrow> Pskip
    | _ \<Rightarrow> Pprint)"

definition calc_trans :: "syn \<Rightarrow> calc" where
"calc_trans c =
  (case c of
    Sadd i \<Rightarrow> (Cadd i)
    | Ssub i \<Rightarrow> (Csub i)
    | Smul i \<Rightarrow> (Cmul i)
    | Sdiv i \<Rightarrow> (Cdiv i)
    | Sreset i \<Rightarrow> (Creset i)
    | Sskip \<Rightarrow> Cskip)"
    

type_synonym print_st = "(int * int list)"
definition print_sem :: "print \<Rightarrow> print_st \<Rightarrow> print_st" where
"print_sem syn st =
  (case st of
    (sti, stl) \<Rightarrow>
      (case syn of
         Pprint \<Rightarrow> (sti, stl @ [sti])
         | Preset \<Rightarrow> (sti, [])
         | Pskip \<Rightarrow> (sti, stl)))"

definition print_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
  "print_sem_l = 
    lift
            (prod_l1 ((prio_l_zero (option_l (triv_l (id_l print_trans)))))
                    ((option_l (triv_l (id_l print_trans))))) print_sem"

definition calc_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"calc_sem_l =
  lift
    (fst_l (prio_l_inc (option_l (triv_l (id_l calc_trans))))) calc_sem"

definition print_calc_lc :: "(syn, state) langcomp" where
"print_calc_lc =
  \<lparr> Sem1 = calc_sem_l
  , Sem2 = print_sem_l \<rparr>"

value "pcomp print_calc_lc (Smul 9) (mdp 0 (Some (mdt 2)), Some (mdt []))"
value "pcomp' print_calc_lc (Smul 9) (mdp 0 (Some (mdt 2)), Some (mdt []))"

(* still not quite right. we need some kind of way to relate the syntaxes... *)
lemma ex_lc_valid :
  "lc_valid print_calc_lc" 
  apply(rule lc_valid_lift)
   apply(simp add: print_calc_lc_def calc_sem_l_def print_sem_l_def)
  apply(rule sup_l_comm)
  apply(rule sup_l1_prod_fst) 
   apply(simp add: prio_l_def option_l_def triv_l_def id_l_def prio_l_inc_def prio_l_zero_def prio_l_const_def sync_def)
     apply(simp only: prio_l_inc_def prio_l_zero_def prio_l_const_def )
  apply(rule sup_l_prio)
  done
  


end