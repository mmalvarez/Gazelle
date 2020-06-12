theory ComposeExamples imports Compose "../MergeableTc/MergeableInstances" HOL.Lifting HOL.Lifting_Set

begin

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
  "seml'' (x :: ex_syn) = 
  (case x of (x', y') \<Rightarrow> ((seml' x', None) :: ex_syn))"

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
  | ((mdp n x'1), x'2) \<Rightarrow> (mdp n x'1, x'2))"

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
  where "dom2' = {x . \<exists> l r' . x = (l, Some r')}"

lift_definition dom2_e :: "example set" is "UNIV" .

definition bot' :: "(int md_triv option md_prio * int list md_triv option)" where
"bot' = (bot, bot)"

lift_definition bot_e :: "example" is bot .

definition pleq' :: "ex_syn \<Rightarrow> ex_syn \<Rightarrow> bool" where
"pleq' = pleq"

lift_definition pleq_e :: "example \<Rightarrow> example \<Rightarrow> bool" is pleq done

definition bsup' :: "ex_syn \<Rightarrow> ex_syn \<Rightarrow> ex_syn" where
"bsup' = bsup"

lift_definition bsup_e :: "example \<Rightarrow> example \<Rightarrow> example" is bsup .

declare dom1'_def and dom1_e_def and dom2'_def and dom2_e_def and
        seml'_def and seml_e_def and semr'_def and semr_e_def and
        bot'_def and bot_e_def and bsup'_def and bsup_e_def and pleq'_def and pleq_e_def [simp]

declare pleq'_def [simp]

lift_definition is_least_e :: "(example \<Rightarrow> bool) \<Rightarrow> example \<Rightarrow> bool"
is is_least .

lift_definition is_ub_e :: "example set \<Rightarrow> example \<Rightarrow> bool"
  is is_ub.

lift_definition has_ub_e :: "example set \<Rightarrow> bool"
is has_ub .

lift_definition is_sup_e :: "example set \<Rightarrow> example \<Rightarrow> bool"
  is is_sup .

lift_definition has_sup_e :: "example set \<Rightarrow> bool"
  is has_sup.

lift_definition is_bsup_e :: "example \<Rightarrow> example \<Rightarrow> example \<Rightarrow> bool"
  is is_bsup.


(* Goal: make it so we don't have to reprove everything here *)
instantiation example :: Pord_Weak begin
definition example_pleq :
  "pleq = pleq_e"
instance proof
  fix a :: example
  show "a <[ a" unfolding example_pleq
(* apply(transfer_start)  *)
    by(transfer; rule leq_refl)
next
  show 
"\<And>(a::example) (b::example) c::example.
       a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c" unfolding example_pleq
    by(transfer; rule leq_trans)
qed
end


context includes lifting_syntax
begin


end

(* lift in the other direction? *)

instantiation example :: "Pord" begin
instance proof
  show
"\<And>(a::example) b::example.
       a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b" unfolding example_pleq

    by(transfer;  rule leq_antisym; auto)
qed
end

lemma thing' :
  fixes S 
  shows "(has_ub :: example set \<Rightarrow> bool) S = has_ub_e S" unfolding has_ub_e.rep_eq has_ub_def is_ub_def example_pleq pleq_e.rep_eq
  apply(transfer)
  apply(auto)
  done


instantiation example :: "Pordc" begin
instance proof
  fix a b :: example
  assume H : "has_ub {a, b}"
  show "has_sup {a, b}" using H 
    unfolding has_ub_def is_ub_def has_sup_def is_sup_def is_least_def example_pleq
      
    apply(transfer)
    apply(fold is_ub_def; fold has_ub_def; 
          fold is_least_def; fold is_sup_def; fold has_sup_def)
    apply(rule_tac complete2; auto)
    done
qed

end

instantiation example :: Pordb begin

definition example_bot :
  "bot = bot_e"
instance proof
  fix a :: example
  show "\<bottom> <[ a" unfolding example_pleq example_bot
    apply(transfer)
    apply(rule bot_spec)
    done
qed
end

declare is_ub_e.transfer [Transfer.transferred, transfer_rule]

instantiation example :: Mergeable begin
definition example_bsup :
  "bsup = bsup_e"
instance proof
  show
"\<And>(a::example) b::example. is_bsup a b [^ a, b ^]" 
    unfolding is_bsup_def is_sup_def is_least_def is_bub_def is_ub_def example_pleq example_bsup
    
    apply(transfer)
    apply(fold is_ub_def; fold is_least_def; fold is_sup_def; fold is_bub_def)
    apply(fold is_least_def) apply(fold is_bsup_def) apply(rule bsup_spec)
    done
qed
end

instantiation example :: Mergeableb begin
instance proof qed
end

instantiation example :: Comp begin
definition example_dom1 :
  "dom1 = dom1_e"
definition example_dom2 :
  "dom2 = dom2_e"
definition example_sem1 :
  "sem1 = seml_e"
definition example_sem2 :
  "sem2 = semr_e"

instance proof
  show "(\<bottom> :: example) \<in> dom1"
    unfolding example_dom1 example_bot
    apply(transfer)
    apply(simp add:prio_bot prod_bot option_bot)
    done
next
  show "(\<bottom> :: example) \<in> dom2"
    unfolding example_dom2 example_bot
    apply(transfer)
    apply(simp add:prio_bot prod_bot option_bot)
    done
next
  fix x :: example
  assume H1 : "x \<in> dom1"
  show "sem1 x \<in> dom1" using H1
    apply(simp add:example_sem1 example_dom1)
    apply(transfer)
    apply(simp add:seml'' seml'_def split:prod.splits option.splits md_triv.splits md_prio.splits)
    done
next
  fix x :: example
  assume H1 : "x \<in> dom2"
  show "sem2 x \<in> dom2" using H1
    apply(simp add:example_sem2 example_dom2)
    apply(transfer)
    apply(simp add:seml'' seml'_def split:prod.splits option.splits md_triv.splits md_prio.splits)
    done
next

  fix x1 x2 :: example
  assume H1 : "x1 \<in> dom1"
  assume H2 : "x2 \<in> dom2"
  assume Hsup : "has_sup {x1, x2}"

  have "has_ub {x1, x2}" using Hsup by(auto simp add:has_sup_def is_least_def has_ub_def is_sup_def)
  then obtain ub  where Hub :  "is_ub {x1, x2} ub" by (auto simp add:has_ub_def)

  have "has_ub {sem1 x1, sem2 x2}" using H1 H2 Hub
     unfolding has_sup_def has_ub_def is_sup_def is_least_def is_ub_def example_sem1 example_sem2 example_dom1 example_dom2 example_pleq
   proof(transfer)
     fix x1 x2 ub :: ex_syn
     assume H1t : "x1 \<in> {x. \<exists>n x'. x = (mdp n x', None)}"
     assume H2t : "x2 \<in> UNIV"
     assume "\<forall>x\<in>{x1, x2}. x <[ ub"
     hence  Hubt : "is_ub {x1, x2} ub" by(auto simp add:is_ub_def)

     obtain x1l and x1r where "x1 = (x1l, x1r)" by (cases x1; auto)
     then obtain x1p and x1' where Hx1 : "x1 = (mdp x1p x1', x1r)" by (cases x1l; auto)
     obtain x2l and x2r where "x2 = (x2l, x2r)" by (cases x2; auto)
     then obtain x2p and x2' where Hx2 : "x2 = (mdp x2p x2', x2r)" by (cases x2l; auto)
     obtain ubl and ubr where "ub = (ubl, ubr)" by (cases ub; auto)
     then obtain ubp and ub' where Hub' : "ub = (mdp ubp ub', ubr)" by (cases ubl; auto)

     obtain x1'l and x1'r where "seml'' x1 = (x1'l, x1'r)" by(cases "seml'' x1"; auto) 
     then obtain x1'p and x1'' where Hx1' : "seml'' x1 = (mdp x1'p x1'', x1'r)" by (cases x1'l; auto)

     obtain x2'l and x2'r where "semr' x2 = (x2'l, x2'r)" by (cases "semr' x2"; auto)
     then obtain x2'p and x2'' where Hx2' : "semr' x2 = (mdp x2'p x2'', x2'r)" by (cases x2'l; auto)

     have 0 : "ubp \<ge> x1p" using Hx1 Hubt Hub'
       by(auto simp add:is_ub_def prod_pleq prio_pleq triv_pleq split:md_prio.splits if_splits)

     have 1 : "ubp \<ge> x2p" using Hx2 Hubt Hub'
       by(auto simp add:is_ub_def prod_pleq prio_pleq triv_pleq split:md_prio.splits if_splits)

     have Conc'1 : "seml'' x1 <[ (mdp (2 + ubp) None, x2'r)" using Hx1 Hx2 Hx1' Hx2' Hubt Hub' H1t 0
       apply(auto simp add:seml'' semr'_def seml'_def prod_pleq prio_pleq triv_pleq leq_refl option_pleq option_bot is_ub_def split:option.splits md_triv.splits)
       done

     have Conc'2 : "semr' x2 <[ (mdp (2 + ubp) None, x2'r)" using Hx1 Hx2 Hx1' Hx2' Hubt Hub' H1t 1
       by(auto simp add:seml'' semr'_def seml'_def prod_pleq prio_pleq triv_pleq leq_refl option_pleq option_bot split:option.splits md_triv.splits)

     show "\<exists>a. \<forall>x\<in>{seml'' x1, semr' x2}. x <[ a" using Conc'1 Conc'2 by auto
   qed

   thus "has_sup {sem1 x1, sem2 x2}" using complete2 by auto

 qed
end


value [simp] "pcomp (exi (mdp (0 :: nat) (Some (mdt (5 :: int))), Some (mdt [])))"

end