theory Gensyn imports Main
begin

datatype ('x) gensyn =
  G "'x" "(('x) gensyn) list"

type_synonym gensyn_skel = "(unit) gensyn"

type_synonym param_gensyn = "(_) gensyn"


declare gensyn.splits [split]

fun gs_map :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x gensyn \<Rightarrow> 'y gensyn" where
"gs_map f (G x l) = G (f x) (map (gs_map f) l)"

fun gs_map_opt :: "('x \<Rightarrow> 'y option) \<Rightarrow> 'x gensyn \<Rightarrow> 'y gensyn option" where
"gs_map_opt f (G x l) = 
  (case (f x) of
    None \<Rightarrow> None
    | Some fx \<Rightarrow>
    (case List.those (List.map (gs_map_opt f) l) of
      None \<Rightarrow> None
      | Some fl \<Rightarrow> Some (G fx fl)))"

definition gs_sk :: "'a gensyn \<Rightarrow> gensyn_skel" where
"gs_sk t = gs_map (\<lambda> _ . ()) t"

type_synonym childpath = "nat list"

datatype ('x) gs_result =
  GRPath childpath
  | GRCrash
  | GRDone
  | GRUnhandled
  | GRSync "'x gs_result"
  | GROther 'x

lemma gensyn_induct':
  assumes Lr : "(\<And> (x :: 'x) (l :: ('x) gensyn list) . P2 l \<Longrightarrow> P2 [(G x l)])"
  and Lrn : "P2 []"
  and Lrc : "\<And>t l . P2 [(t :: 'x gensyn)] \<Longrightarrow>
                         P2 l \<Longrightarrow>
                         P2 (t # l)"
  shows "P2 (l)"
proof-
  {   fix t
      have "P2 [t] \<and> (! x l . t = G x l \<longrightarrow> P2 l)"
      proof(induction t)
        case (G x l)
        then show ?case
          apply(induct l) using Lr Lrn Lrc
           apply(clarsimp)
          apply(clarsimp)
          apply(auto)
           apply(rule_tac Lr)
           apply(rule_tac Lrc) apply(auto)
          apply(rule_tac Lrc) apply(auto)
          done
 qed
     }
  thus ?thesis by auto
qed



lemma gensyn_induct:
  assumes Lr : "(\<And> (x :: 'x) (l :: ('x) gensyn list) . P2 l \<Longrightarrow> P1 (G x l))"
  and Lrn : "P2 []"
  and Lrc : "\<And>t l . P1 (t :: 'x gensyn) \<Longrightarrow>
                         P2 l \<Longrightarrow>
                         P2 (t # l)"
shows "P1 (t)"
proof-
  {   fix l
      have "P2 l \<and> (! h t . l = h#t \<longrightarrow> P1 h \<and> P2 t )" (*using Lr Lrn Lrc*)
proof(induction l rule:gensyn_induct')
  case (1 x l2)
  then show ?case apply(auto intro:Lr Lrn Lrc) done
next
  case 2
  then show ?case by (auto intro: Lr Lrn Lrc)
next
  case (3 t l)
  then show ?case
    apply(clarsimp)
    apply(rule_tac Lrc) apply(auto)
    done
qed }

  thus ?thesis apply(simp)
    done
qed

end
