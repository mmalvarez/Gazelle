theory AList_bnf
imports "AList/AList" "AList/Linorder_Insts"
begin

type_synonym 'a balist = "((String.literal list) * 'a) list"

typedef (overloaded) ('value) oalist =
  "{xs :: 'value balist .
       strict_order (map fst xs)}"
  morphisms impl_of oalist
proof
  show "[] \<in> {xs :: 'value balist . strict_order (map fst xs)}"
    by(auto simp add:strict_order_def)
qed

setup_lifting type_definition_oalist

lift_bnf 'value oalist [wits: "[]  :: 'value balist"]
proof
    fix f :: "('value => 'value2)"
    fix l :: "'value balist"
    assume H : "l \<in> {x. strict_order (map fst x)}"
    show  "strict_order (map fst (map  (map_prod id f) l))" using H
        by(simp add: strict_order_def)
next
    fix z :: "('v1 * 'v2) balist"
    assume H1 : "map (map_prod id fst) z \<in> {x. strict_order (map fst x)}"
    assume H2 : "map (map_prod id snd) z \<in> {x. strict_order (map fst x)}"
    show "\<exists>z'\<in>{x. strict_order (map fst x)}.
           \<Union> (Basic_BNFs.snds ` set z') \<subseteq> \<Union> (Basic_BNFs.snds ` set z) \<and>
           map (map_prod id fst) z' = map (map_prod id fst) z \<and> 
           map (map_prod id snd) z' = map (map_prod id snd) z" using H1 H2
        by(auto simp add: strict_order_def)
next
    show "[] \<in> {x. strict_order (map fst x)}"
    by(auto simp add: strict_order_def)
next
    show "\<And>a. a \<in> \<Union> (Basic_BNFs.snds ` set []) \<Longrightarrow> False"
    by auto
qed

datatype letstry =
    LNil
    | LCons "letstry oalist"

typedef (overloaded) ('value) nexty =
    "{ x :: 'value oalist . length (impl_of x) = 0}"
    apply(transfer)
    apply(rule_tac x = "[]"  in bexI)
    apply(auto simp add: strict_order_def)
    done
end