theory Intro_Example
  imports Main "../Lib/Oalist/Oalist" "../Syntax/Gensyn"
begin

text_raw \<open>%Snippet paper_examples__intro_example__calc\<close>
datatype calc =
  Add
  | Sub
  | Mul
  | Div
  | Const int
  | Skip_Calc

type_synonym calc_state = "(int * int * int)"

fun calc_sem :: "calc \<Rightarrow> calc_state \<Rightarrow> calc_state" where
"calc_sem Add (x, y, z) = (x, y, x + y)"
| "calc_sem Sub (x, y, z) = (x, y, x - y)"
| "calc_sem Mul (x, y, z) = (x, y, x * y)"
| "calc_sem Div (x, y, z) =
  (x, y, divide_int_inst.divide_int x y)"
| "calc_sem (Const i) (x, y, z) = (x, y, i)"
| "calc_sem (Skip_Calc) t = t"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example__mem\<close>

datatype reg_id =
  Reg_a
  | Reg_b
  | Reg_c

datatype mem =
  Read "String.literal" "reg_id"
  | Write "String.literal" "reg_id"
  | Skip_Mem

type_synonym mem_state = "(int * int * int * (String.literal, int) oalist)"

fun mem_sem :: "mem \<Rightarrow> mem_state \<Rightarrow> mem_state" where
"mem_sem (Read s r) (ra, rb, rc, mem) =
  (case get mem s of
    Some v \<Rightarrow>
    (case r of
      Reg_a \<Rightarrow> (v, rb, rc, mem)
      | Reg_b \<Rightarrow> (ra, v, rc, mem)
      | Reg_c \<Rightarrow> (ra, rb, v, mem))
    | None \<Rightarrow> (ra, rb, rc, mem))"
| "mem_sem (Write s r) (ra, rb, rc, mem) =
   (case r of
    Reg_a \<Rightarrow> (ra, rb, rc, update s ra mem)
    | Reg_b \<Rightarrow> (ra, rb, rc, update s rb mem)
    | Reg_c \<Rightarrow> (ra, rb, rc, update s rc mem))"
| "mem_sem (Skip_Mem) t = t"

text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example__seq\<close>

datatype seq =
  Seq
  | Skip_Seq

text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example__count\<close>

datatype count =
  Op
  | Skip_Count

type_synonym count_state = "int" 

fun count_sem :: "count \<Rightarrow> count_state \<Rightarrow> count_state" where
"count_sem Op x = (x + 1)"
| "count_sem _ x = x"

text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example__handwritten_composition\<close>

type_synonym composed_state =
  "(int * int * int * (String.literal, int) oalist * int)"

datatype composed =
  Calc calc
  | Mem mem
  | Sq "composed list"

fun composed_sem ::
  "composed \<Rightarrow> composed_state \<Rightarrow> composed_state" where
"composed_sem (Calc i) (ra, rb, rc, mem, ct) =
  (case calc_sem i (ra, rb, rc) of
    (ra', rb', rc') \<Rightarrow> (ra', rb', rc', mem, count_sem Op ct))"
| "composed_sem (Mem i) (ra, rb, rc, mem, ct) =
  (case mem_sem i (ra, rb, rc, mem) of
    (ra', rb', rc', mem') \<Rightarrow>
      (ra', rb', rc', mem', count_sem Op ct))"
| "composed_sem (Sq []) st = st"
| "composed_sem (Sq (h#t)) st =
   composed_sem (Sq t) (composed_sem h st)"

text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example__handwritten_composition_run\<close>
definition example_prog :: "composed" where
"example_prog =
  Sq
  [ Calc (Const 1)
  , Mem (Write (STR ''x'') Reg_c)
  , Calc (Const 2)
  , Mem (Write (STR ''y'') Reg_c)
  , Mem (Read (STR ''x'') Reg_a)
  , Mem (Read (STR ''y'') Reg_b)
  , Calc Add
  , Mem (Write (STR ''result'') Reg_c)
  ]"

definition init_state :: "composed_state" where
"init_state =
  (0, 0, 0, empty, 0)"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__intro_example__handwritten_composition_run_value\<close>
value "composed_sem example_prog init_state"
\<comment> \<open>Result:\<close>
text \<open>@{value "composed_sem example_prog init_state"}\<close>
text_raw \<open>%EndSnippet\<close>

end