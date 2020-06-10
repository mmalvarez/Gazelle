theory ComposeExamples imports Compose "../Mergeable/MergeableInstances"

begin

(* state for calc language: 
   int (current accumulator value)  
*)
global_interpretation MGT_int : Mg_Trivial "TYPE(int)"
  defines MGT_int_bsup = MGT_int.bsup
  and     MGT_int_pleq = MGT_int.pleq
  done

global_interpretation PBO_int : Pbord_Option "MGT_int_pleq"
  defines PBO_int_bot = PBO_int.bot
  and     PBO_int_pleq = PBO_int.pleq
  done

global_interpretation MGO_int : Mg_Option "MGT_int_pleq" "MGT_int_bsup"
  defines MGO_int_bsup = MGO_int.bsup
  done

global_interpretation MGOP_int : Mg_Priority "PBO_int_pleq" PBO_int_bot "MGO_int_bsup"
  defines MGOP_int_bsup = MGOP_int.bsup
  and     MGOP_int_bot  = MGOP_int.bot
  and     MGOP_int_pleq = MGOP_int.pleq
  done

global_interpretation MGT_intl : Mg_Trivial "TYPE(int list)"
  defines MGT_intl_pleq = MGT_intl.pleq
  and     MGT_intl_bsup = MGT_intl.bsup
  done

global_interpretation PBO_intl : Pbord_Option "MGT_intl_pleq"
  defines PBO_intl_bot = PBO_intl.bot
  and     PBO_intl_pleq = PBO_intl.pleq
  done

global_interpretation MGO_intl : Mg_Option "MGT_intl_pleq" "MGT_intl_bsup"
  defines MGO_intl_bsup = MGO_intl.bsup
  done

global_interpretation MG_r : Mg_Pair MGOP_int_pleq PBO_intl_pleq MGOP_int_bot PBO_intl_bot MGOP_int_bsup MGO_intl_bsup
  defines MG_r_pleq = MG_r.pleq
  and     MG_r_bsup = MG_r.bsup
  done

type_synonym pri = nat

definition seml :: "int \<Rightarrow> int" where
  "seml x = (1 + x)"

definition seml' :: "nat * int option \<Rightarrow> (nat * int option)" where
"seml' xo = 
  (case xo of
    (n, Some i) \<Rightarrow> (n + 1, Some (i + 1))
    | (n, None) \<Rightarrow> (n, None))"

definition semr :: "(int * int list) \<Rightarrow> (int * int list)" where
"semr x =
(case x of
  (i, ints) \<Rightarrow> (i, ints @ [i]))"

(* n, None or 0, None ? *)
definition semr' :: "((nat * int option) * int list option) \<Rightarrow> ((nat * int option) * int list option)" where
"semr' x =
(case x of
  ((n, Some i), Some ints) \<Rightarrow> ((n, Some i), Some (ints @ [i]))
  | ((n, None), None) \<Rightarrow> ((n, None), None))"

definition injl :: "nat * int option \<Rightarrow> ((nat * int option) * int list option)" where
"injl x = (x, None)"

definition prjl :: "((nat * int option) * int list option) \<Rightarrow> nat * int option" where
"prjl = fst"

definition injr :: "((nat * int option) * int list option) \<Rightarrow> ((nat * int option) * int list option)" where
"injr = id"

definition prjr :: "((nat * int option) * int list option) \<Rightarrow> ((nat * int option) * int list option)" where
"prjr = id"


global_interpretation C_pa: SemComp
  _ _ _
  MG_r_pleq MG_r_bsup injl prjl injr prjr seml' semr'
  defines C_pa_pcomp = C_pa.pcomp
  and     C_pa_pcomp' = C_pa.pcomp'
  and     C_pa_seml_l = C_pa.seml_l
  and     C_pa_liftl1 = C_pa.liftl1
  and     C_pa_semr_l = C_pa.semr_l
  and     C_pa_liftr1 = C_pa.liftr1
  done

global_interpretation C_pas : SemComp_Spec
  _ _ _
  MG_r_pleq MG_r_bsup injl prjl injr prjr seml' semr'


value  "C_pa_pcomp ((0, Some 2), Some [1, 2, 3])
= C_pa_pcomp' ((0, Some 2), Some [1, 2, 3])"

end