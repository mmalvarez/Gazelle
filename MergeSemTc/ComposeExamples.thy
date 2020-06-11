theory ComposeExamples imports Compose "../MergeableTc/MergeableInstances" HOL.Lifting

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

type_synonym ex_syn = "(int md_triv option md_prio * int list md_triv option)"

typedef example = "UNIV :: ex_syn set"
  by auto

setup_lifting type_definition_example

definition exi :: "(int md_triv option md_prio * int list md_triv option) \<Rightarrow> example"
  where "exi = Abs_example"

definition seml' :: "int md_triv option md_prio \<Rightarrow> int md_triv option md_prio" where
"seml' xo = 
  (case xo of
    mdp n (Some (mdt i)) \<Rightarrow> mdp (n + 1) (Some (mdt (i + 1)))
    | mdp n None \<Rightarrow> mdp n None)"

definition seml'' :
  "seml'' x = 
  (case x of (x', y') \<Rightarrow> (seml' x', y'))"

lift_definition seml_e :: "example \<Rightarrow> example" is seml'' .

definition semr :: "(int * int list) \<Rightarrow> (int * int list)" where
"semr x =
(case x of
  (i, ints) \<Rightarrow> (i, ints @ [i]))"

(* n, None or 0, None ? *)
definition semr' :: "(int md_triv option md_prio * int list md_triv option) \<Rightarrow> (int md_triv option md_prio * int list md_triv option)" where
"semr' x =
(case x of
  (mdp n (Some (mdt i)), Some (mdt ints)) \<Rightarrow> (mdp n (Some (mdt i)), Some (mdt (ints @ [i])))
  | ((mdp n None), None) \<Rightarrow> (mdp n None, None))"

lift_definition semr_e :: "example \<Rightarrow> example" is semr' .

definition injl :: "nat * int option \<Rightarrow> ((nat * int option) * int list option)" where
"injl x = (x, None)"

definition prjl :: "((nat * int option) * int list option) \<Rightarrow> nat * int option" where
"prjl = fst"

definition injr :: "((nat * int option) * int list option) \<Rightarrow> ((nat * int option) * int list option)" where
"injr = id"

definition prjr :: "((nat * int option) * int list option) \<Rightarrow> ((nat * int option) * int list option)" where
"prjr = id"

definition dom1' :: "(int md_triv option md_prio * int list md_triv option) set" where
"dom1' = {x . \<exists> n x' . x = (mdp n x', None)}"

lift_definition dom1_e :: "example set" is "{x . \<exists> n x' . x = (mdp n x', None)}" .

definition dom2' :: "(int md_triv option md_prio * int list md_triv option) set"
  where "dom2' = {x . True}"

lift_definition dom2_e :: "example set" is "{x . True}" .

definition bot' :: "(int md_triv option md_prio * int list md_triv option)" where
"bot' = (bot, bot)"

lift_definition bot_e :: "example" is bot .

definition pleq' :: "ex_syn \<Rightarrow> ex_syn \<Rightarrow> bool" where
"pleq' = pleq"

lift_definition pleq_e :: "example \<Rightarrow> example \<Rightarrow> bool" is pleq done

definition bsup' :: "ex_syn \<Rightarrow> ex_syn \<Rightarrow> ex_syn" where
"bsup' = bsup"

lift_definition bsup_e :: "example \<Rightarrow> example \<Rightarrow> example" is bsup' .

declare dom1'_def and dom1_e_def and dom2'_def and dom2_e_def and
        seml'_def and seml_e_def and semr'_def and semr_e_def and
        bot'_def and bot_e_def and bsup'_def and bsup_e_def and pleq'_def and pleq_e_def [simp]

declare pleq'_def [simp]

lift_definition is_sup_e :: "example set \<Rightarrow> example \<Rightarrow> bool"
  is is_sup.

lift_definition has_sup_e :: "example set \<Rightarrow> bool"
  is has_sup.

lift_definition is_ub_e :: "example set \<Rightarrow> example \<Rightarrow> bool"
  is is_sup.

lift_definition has_ub_e :: "example set \<Rightarrow> bool"
is has_ub .

(* Goal: make it so we don't have to reprove everything here *)
instantiation example :: Pord_Weak begin
definition example_pleq :
  "pleq = pleq_e"
instance proof
  fix a :: example
  show "a <[ a" unfolding example_pleq
    by(transfer; rule leq_refl)
next
  show 
"\<And>(a::example) (b::example) c::example.
       a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c" unfolding example_pleq
    by(transfer; rule leq_trans)
qed
end

instantiation example :: "Pord" begin
instance proof
  show
"\<And>(a::example) b::example.
       a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b" unfolding example_pleq
    by(transfer;  rule leq_antisym; auto)
qed
end


instantiation example :: Pordc
begin
instance proof
  show "\<And>(a::example) b::example.
       has_ub {a, b} \<Longrightarrow> has_sup {a, b}"
    apply(transfer)


instantiation example :: Comp begin
definition example_dom1 :
  "dom1 = dom1_e"
definition example_dom2 :
  "dom2 = dom2_e"
definition example_sem1 :
  "sem1 = seml_e"
definition example_sem2 :
  "sem2 = semr_e"
definition example_bot :
  "bot = bot_e"
definition example_bsup :
  "bsup = bsup_e"
definition example_pleq :
  "pleq = pleq_e"

instance proof
  show
"\<And>(a::example) b::example.
       a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b" unfolding example_pleq
    by(transfer; unfold pleq'_def; rule leq_antisym; auto)
next 
  show "\<And>(a::example) b::example.
       has_ub {a, b} \<Longrightarrow> has_sup {a, b}"
    apply(simp add:has_ub has_sup)

(*
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
*)

value  "C_pa_pcomp ((0, Some 2), Some [1, 2, 3])
= C_pa_pcomp' ((0, Some 2), Some [1, 2, 3])"

end