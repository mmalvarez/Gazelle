theory Intro_Example_Gazelle
  imports 
    "../Lifter/Auto_Lifter"
    Main 
    "./Intro_Example"
    "../Language_Components/Seq/Seq"
    "../Hoare/Hoare_Step"
begin

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__syntax\<close>
datatype composed =
  Calc calc
  | Mem mem
  | Sq
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__translation\<close>
fun calc_trans :: "composed \<Rightarrow> calc" where
"calc_trans (Calc x ) = x"
| "calc_trans _ = Skip_Calc"

fun mem_trans :: "composed \<Rightarrow> mem" where
"mem_trans (Mem m) = m"
| "mem_trans _ = Skip_Mem"

fun seq_trans :: "composed \<Rightarrow> Seq.syn" where
"seq_trans Sq = Seq.Sseq"
| "seq_trans _ = Seq.Sskip"

fun count_trans :: "composed \<Rightarrow> count" where
"count_trans Sq = Skip_Count"
| "count_trans _ = Op"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__priorities\<close>
fun calc_prio :: "(calc \<Rightarrow> nat)" where
"calc_prio Skip_Calc = 1"
| "calc_prio _ = 2"

fun mem_prio :: "mem \<Rightarrow> nat" where
"mem_prio (Skip_Mem) = 1"
| "mem_prio _ = 2"

fun count_prio :: "count \<Rightarrow> nat" where
"count_prio (Skip_Count) = 1"
| "count_prio Op = 2"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__toggle\<close>
fun calc_toggle :: "composed \<Rightarrow> bool" where
"calc_toggle (Calc _) = True"
| "calc_toggle _ = False"

fun mem_toggle :: "composed \<Rightarrow> bool" where
"mem_toggle (Mem _) = True"
| "mem_toggle _ = False"

text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__state\<close>
type_synonym 'x swr =
  "'x md_triv option md_prio"

definition Swr :: "'x \<Rightarrow> 'x swr" where
"Swr x = (mdp 0 (Some (mdt x)))"

type_synonym ('x) composed_state' =
  "(int swr * int swr * int swr * 
   (String.literal, int) oalist swr * int swr * 'x)"

type_synonym ('s, 'x) composed_state =
  "('s, 'x composed_state') control"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__lift\<close>
definition calc_lift' ::
  "(calc, calc_state, _ composed_state') lifting" where
"calc_lift' = 
  schem_lift (SP NA (SP NB NC))
             (SP (SPRC calc_prio (SO NA)) 
                  (SP (SPRC calc_prio (SO NB))
                  (SP (SPRC calc_prio (SO NC)) NX)))"

definition calc_lift ::
  "(calc, calc_state, (composed, _) composed_state) lifting" where
"calc_lift = no_control_lifting calc_lift'"

definition mem_lift' ::
  "(mem, mem_state, _ composed_state') lifting"
  where
"mem_lift' = 
  schem_lift
    (SP NA (SP NB (SP NC ND)))
    (SP (SPRC mem_prio (SO NA)) 
        (SP (SPRC mem_prio (SO NB)) 
        (SP (SPRC mem_prio (SO NC))
        (SP (SPRC mem_prio (SO ND)) NX))))"

definition mem_lift ::
  "(mem, mem_state, (composed, _) composed_state) lifting" where
"mem_lift = no_control_lifting mem_lift'"

definition count_lift' ::
  "(count, count_state, _ composed_state') lifting" where
"count_lift' =
  schem_lift NA
    (SP NX (SP NX (SP NX (SP NX (SP (SPRI (SO NA)) NX)))))"

definition count_lift ::
  "(count, count_state, (composed, _) composed_state) lifting" where
"count_lift = no_control_lifting count_lift'"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__composition\<close>
definition composed_sem :: 
  "composed \<Rightarrow> 
  (composed, _) composed_state \<Rightarrow>
  (composed, _) composed_state" where
"composed_sem =
  pcomps
    [ lift_map_t_s calc_trans calc_lift calc_toggle calc_sem
    , lift_map_t_s mem_trans mem_lift mem_toggle mem_sem
    , lift_map_s count_trans count_lift count_sem
    , seq_sem_l_gen seq_trans]"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__composition_run\<close>

definition example_prog :: "composed gensyn" where
"example_prog =
  \<diamond> Sq
  [ \<dagger> Calc (Const 1)
  , \<dagger> Mem (Write (STR ''x'') Reg_c)
  , \<dagger> Calc (Const 2)
  , \<dagger> Mem (Write (STR ''y'') Reg_c)
  , \<dagger> Mem (Read (STR ''x'') Reg_a)
  , \<dagger> Mem (Read (STR ''y'') Reg_b)
  , \<dagger> Calc Add
  , \<dagger> Mem (Write (STR ''result'') Reg_c)
  ]"

definition init_state :: "(composed, unit) composed_state" where
"init_state =
  (Swr [example_prog], Swr None, Swr 0, 
   Swr 0, Swr 0, Swr empty, Swr 0, ())"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example_gazelle__composition_run_value\<close>

value "sem_run composed_sem 99 init_state"
\<comment> \<open>Result:\<close>
text \<open>@{value "sem_run composed_sem 99 init_state"}\<close>

text_raw \<open>%EndSnippet\<close>

end