theory Gensym imports Main
begin

datatype ('b, 'r, 'g) gensym = 
  GBase "'g" "'b"
  | GRec "'g" "'r" "(('b, 'r, 'g) gensym) list"


lemma gensym_induct':
  assumes Lb: "(\<And> (g :: 'g) (b :: 'b) . P1 (GBase g b))"
  and Lr : "(\<And> (g :: 'g) (r :: 'r) (l :: ('b, 'r, 'g) gensym list) . P2 l \<Longrightarrow> P1 (GRec g r l))"
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

lemma gensym_induct:
  assumes Lb: "(\<And> (g :: 'g) (b :: 'b) . P1 (GBase g b))"
  and Lr : "(\<And> (g :: 'g) (r :: 'r) (l :: ('b, 'r, 'g) gensym list) . P2 l \<Longrightarrow> P1 (GRec g r l))"
  and Lrn : "P2 []"
  and Lrc : "\<And>t l . P1 t \<Longrightarrow>
                         P2 l \<Longrightarrow> 
                         P2 (t # l)"
shows C1: "P1 (t :: ('b, 'r, 'g) gensym)"
  and C2 : "P2 (l :: ('b, 'r, 'g) gensym list)" using gensym_induct'[OF Lb Lr Lrn Lrc]
proof(auto)
qed

end