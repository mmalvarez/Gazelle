theory Gensyn imports Main
begin

datatype ('x) gensyn =
  G "'x" "(('x) gensyn) list"

declare gensyn.splits [split]

fun gs_map :: "('x \<Rightarrow> 'y) \<Rightarrow> 'x gensyn \<Rightarrow> 'y gensyn" where
"gs_map f (G x l) = G (f x) (map (gs_map f) l)"

(* for consistency with other syntax declarations *)
(*
definition LSeq :: "'g \<Rightarrow> 'r \<Rightarrow> (('b, 'r, 'g) gensyn list) \<Rightarrow> ('b, 'r, 'g) gensyn" where
"LSeq g r l = GRec g r l"
*)

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
