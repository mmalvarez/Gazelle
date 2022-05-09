theory Need_Toggle
  imports "../Composition/Composition" "../Lifter/Auto_Lifter" "../Lifter/Toggle" "../Composition/Dominant"
begin

(*
fun sem1 :: "(int md_triv option md_prio * ('a :: Pordc)) \<Rightarrow>
             (int md_triv option md_prio * 'a)" where
"sem1 (mdp p1 (Some (mdt v1)), x2) =
  (mdp (2 + p1) (Some (mdt 0)), x2)"
| "sem1 x = x"

fun sem2 :: "(int md_triv option md_prio * int md_triv option md_prio) \<Rightarrow>
  (int md_triv option md_prio * int md_triv option md_prio)" where
"sem2 (mdp p1 (Some (mdt v1)), mdp p2 (Some (mdt v2))) =
  (mdp (2 + p1) (Some (mdt 0)), mdp (1 + p2) (Some (mdt v2)))"
| "sem2 x = x"
*)

text_raw \<open>%Snippet paper_examples__need_toggle__langs\<close>
datatype syn =
  Op1
  | Op2

fun sem1 :: "syn \<Rightarrow> int \<Rightarrow> int" where
"sem1 Op1 x = (1 + x)"
| "sem1 _ x = x"

fun sem1_p :: "syn \<Rightarrow> nat" where
"sem1_p Op1 = 2"
| "sem1_p _ = 1"

fun sem2 :: "syn \<Rightarrow> (int * int) \<Rightarrow> (int * int)" where
"sem2 Op2 (x1, x2) = (x1, (2 + x2))"
| "sem2 _ x = x"

fun sem2_p :: "syn \<Rightarrow> nat" where
"sem2_p Op2 = 2"
| "sem2_p _ = 1"

type_synonym state =
  "int md_triv option md_prio *
   int md_triv option md_prio"

definition sem1_lift ::
  "(syn, int,
    int md_triv option md_prio *
    ('a :: Mergeableb)) lifting" where
"sem1_lift = schem_lift NA (SP (SPRC sem1_p (SO NA)) NX)"

definition sem2_lift :: "(syn, (int * int), state) lifting" where
"sem2_lift =
  schem_lift (SP NA NB)
    (SP (SPRI (SO NA)) (SPRC sem2_p (SO NB)))"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__need_toggle__toggles\<close>
fun sem1_toggle :: "syn \<Rightarrow> bool" where
"sem1_toggle Op1 = True"
| "sem1_toggle Op2 = False"

fun sem2_toggle :: "syn \<Rightarrow> bool" where
"sem2_toggle Op1 = False"
| "sem2_toggle Op2 = True"

definition sems :: "(syn \<Rightarrow> state \<Rightarrow> state) set" where
"sems = {lift_map_t_s id sem1_lift sem1_toggle sem1
        ,lift_map_t_s id sem2_lift sem2_toggle sem2}"

lemma sem1_dominant :
  "(lift_map_t_s id sem1_lift sem1_toggle sem1) \<down> sems ({Op1})"
proof(rule dominant_toggles)
text_raw \<open>%EndSnippet\<close>
  show "lift_map_t_s id sem1_lift
     sem1_toggle sem1
    \<in> sems"
    by(auto simp add: sems_def)
next
  fix s
  show "s \<in> {Op1} \<Longrightarrow> sem1_toggle s"
    by(cases s; auto)
next
  fix f
assume H1 : "f \<in> sems"
  assume H2 :"f \<noteq>
         lift_map_t_s id sem1_lift
          sem1_toggle sem1"
  have Fact : "f = lift_map_t_s id sem2_lift sem2_toggle sem2"
    using H1 H2
    by(auto simp add: sems_def)
  show "
         \<exists>tg g.
            f = toggle tg g \<and>
            (\<forall>s. s \<in> {Op1} \<longrightarrow> \<not> tg s)"
    apply(auto)
    apply(rule_tac x = sem2_toggle in exI)
    apply(auto simp add: Fact lift_map_t_s_def toggle_def lift_map_t_s_toggle)
    done
next
  oops
end