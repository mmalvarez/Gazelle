theory SynComposeExamples imports Compose "../MergeableTc/MergeableInstances" HOL.Lifting
begin

datatype calc =
  Cadd int
  | Csub int
  | Cmul int
  | Cdiv int
  | Creset int

datatype print =
  Pprint
  | Preset

definition calc_sem :: "calc \<Rightarrow> int \<Rightarrow> int" where
"calc_sem c r =
  (case c of
    Cadd i \<Rightarrow> r + i
    | Csub i \<Rightarrow> r - i
    | Cmul i \<Rightarrow> r * i
    | Cdiv i \<Rightarrow> r div i
    | Creset r' \<Rightarrow> r')"

definition print_sem :: "print \<Rightarrow> (int * int list) \<Rightarrow> (int * int list)" where
"print_sem p r =
  (case p of
    Pprint \<Rightarrow> (case r of
                (i, l) \<Rightarrow> (i, l@[i]))
    | Preset \<Rightarrow> (case r of
                (i, l) \<Rightarrow> (i, [])))"

type_synonym cs_syno = "(int md_triv option md_prio * int list md_triv option)"

typedef cs = "UNIV :: cs_syno set"
  by auto




end