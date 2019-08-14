theory Gensyn imports Main
begin

datatype ('b, 'r, 'g) gensyn = 
  GBase "'g" "'b"
  | GRec "'g" "'r" "(('b, 'r, 'g) gensyn) list"

(* for consistency with other syntax declarations *)
(*
definition LSeq :: "'g \<Rightarrow> 'r \<Rightarrow> (('b, 'r, 'g) gensyn list) \<Rightarrow> ('b, 'r, 'g) gensyn" where
"LSeq g r l = GRec g r l"
*)

lemma gensyn_induct':
  assumes Lb: "(\<And> (g :: 'g) (b :: 'b) . P1 (GBase g b))"
  and Lr : "(\<And> (g :: 'g) (r :: 'r) (l :: ('b, 'r, 'g) gensyn list) . P2 l \<Longrightarrow> P1 (GRec g r l))"
  and Lrn : "P2 []"
  and Lrc : "\<And>t l . P1 t \<Longrightarrow>
                         P2 l \<Longrightarrow> 
                         P2 (t # l)"
  shows "P1 t \<and> P2 l"
proof-
  {fix t
    have "P1 t \<and> (\<forall> g r l . t = GRec g r l \<longrightarrow> P2 l)"
    proof (induction)
    case (GBase g b) thus ?case using Lb by auto next
    case (GRec g r l) thus ?case
    apply (induct l) using Lr Lrn Lrc
    apply(auto) apply(force) apply(force)
    done
    qed}
  
  thus ?thesis by auto
  qed

lemma gensyn_induct:
  assumes Lb: "(\<And> (g :: 'g) (b :: 'b) . P1 (GBase g b))"
  and Lr : "(\<And> (g :: 'g) (r :: 'r) (l :: ('b, 'r, 'g) gensyn list) . P2 l \<Longrightarrow> P1 (GRec g r l))"
  and Lrn : "P2 []"
  and Lrc : "\<And>t l . P1 t \<Longrightarrow>
                         P2 l \<Longrightarrow> 
                         P2 (t # l)"
shows C1: "P1 (t :: ('b, 'r, 'g) gensyn)"
  and C2 : "P2 (l :: ('b, 'r, 'g) gensyn list)" using gensyn_induct'[OF Lb Lr Lrn Lrc]
proof(auto)
qed

end