theory ComposeExamples imports  "../MergeableTc/Mergeable" "../MergeableTc/MergeableInstances" "../MergeableTc/SplittableInstances" HOL.Lifting HOL.Lifting_Set LiftUtils

begin

(* new approach
   - define syntax, semantics as normal
   - define a combined representation using Mergeable+Splittable
   - ** use "lifting" to translate semantics into the projected version
*)



term "(prod_lm ((fst_l (prio_l_zero (option_l (triv_l (id_l))))))
                     ((snd_l (option_l (triv_l (id_l))))))"
term "(prod_l ((prio_l_zero (option_l (triv_l (id_l)))))
                     ((option_l (triv_l (id_l)))))"
term "(fst_l (prio_l_zero (option_l (triv_l (id_l)))))"
term "(snd_l (option_l (triv_l (id_l))))"

value "print_sem_l (Sreset 0)
               (mdp 1 (Some (mdt 1)), Some (mdt []))"


value "calc_sem_l (Sreset 0)
(mdp 1 (Some (mdt 1)), Some (mdt []))"






(*
setup_lifting type_definition_synsem_t

lift_definition print_sem_l_t :: "synsem_t \<Rightarrow> synsem_t \<Rightarrow> synsem_t" is print_sem_l
  done

instantiation synsem_t :: Pord_Weak begin
lift_definition synsem_t_pleq' :: "synsem_t \<Rightarrow> synsem_t \<Rightarrow> bool" 
is "pleq :: synsem \<Rightarrow> synsem \<Rightarrow> bool" done

definition synsem_t_pleq :
"pleq = synsem_t_pleq'"

instance proof
  fix a :: synsem_t
  show "a <[ a" 
    apply(simp add:synsem_t_pleq) apply(transfer) apply(auto intro:leq_refl)
    done
next
  fix a b c :: synsem_t
  show "a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c"
    apply(simp add:synsem_t_pleq) apply(transfer) apply(auto elim:leq_trans)
    done
qed
end

instantiation synsem_t :: Pord begin
instance proof
  fix a b :: synsem_t
  show "a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b" using leq_antisym[of "Rep_synsem_t a" ]
    apply(simp add:synsem_t_pleq; transfer)
    apply(auto)
    done
qed
end

instantiation synsem_t :: Pordc begin
instance proof
  fix a b :: synsem_t
  show " has_ub {a, b} \<Longrightarrow> has_sup {a, b}"
    using complete2[of"Rep_synsem_t a" ]
    apply(simp only:has_ub_def has_sup_def is_sup_def is_ub_def
          is_least_def synsem_t_pleq)
    apply(transfer)
    apply(auto)
    done
qed end

instantiation synsem_t :: Pordb begin
lift_definition synsem_t_bot' :: "synsem_t" 
is "bot :: synsem" done

definition synsem_t_bot :
"bot = synsem_t_bot'"

instance proof
  fix a :: synsem_t
  show "\<bottom> <[ a"
    using bot_spec[of"Rep_synsem_t a" ]
    apply(simp only:synsem_t_pleq synsem_t_bot)
    apply(transfer)
    apply(auto)
    done
qed end

instantiation synsem_t :: Mergeable begin
lift_definition synsem_t_bsup' :: "synsem_t \<Rightarrow> synsem_t \<Rightarrow> synsem_t"
is "bsup :: synsem \<Rightarrow> synsem \<Rightarrow> synsem"
  done
definition synsem_t_bsup :
"bsup = synsem_t_bsup'"

instance proof
  fix a b :: synsem_t
  show "is_bsup a b [^ a, b ^]" 
    using bsup_spec[of "Rep_synsem_t a"]
    unfolding  synsem_t_pleq synsem_t_bot synsem_t_bsup
      is_bsup_def is_sup_def is_ub_def is_least_def is_bub_def
    by(transfer;auto)
qed
end

(* new idea
   we need some kind of way to talk about injecting combined syntax in
   we also need to talk about the domains
   for now we don't need Splittable I think. could be useful later
*)

instantiation synsem_t :: Mergeableb begin
instance proof qed
end



instantiation synsem_t :: Splittableb begin
lift_definition synsem_t_projs' :: "synsem_t projs_t"
is "projs" done

definition synsem_t_projs :
"projs = synsem_t_projs'"

instance proof
  fix s::"char list"
  fix d::"synsem_t set"
  fix f::"synsem_t \<Rightarrow> synsem_t"
  fix x :: "synsem_t"
  assume "(s, d, f) \<in> set projs"
  thus "is_project x d (f x)"
    using projs_spec[of s "Rep_synsem_t ` d" _ "Rep_synsem_t x"]
    unfolding synsem_t_pleq synsem_t_projs is_project_def is_greatest_def
      synsem_t_pleq
    apply(transfer)
    apply(auto)
    done
next
  show "distinct (map fst (projs :: synsem_t projs_t))"
    using projs_distinct'[of "projs :: synsem projs_t"]
    unfolding synsem_t_projs
    apply(transfer) apply(auto)
    done
qed
end
*)

(*
definition sem_lift_triv_prod1 :: "(('a * 'b) \<Rightarrow> ('a * 'b)) \<Rightarrow>
                                   (('a triv * 'b) \<Rightarrow> ('a triv * 'b))" where
"sem_lift_triv_prod1 =
  "
*)

(*
definition print_sem' :: "print md_triv option \<Rightarrow> (int md_triv option md_prio * int list md_triv option)" where
"print_sem'
*)

(* Here the user has to specify the combined state explicitly. I wonder if
  there is a way to avoid even this. *)
(*
   I also wonder if there is a nicer way to specify the overlap.
*)
(* define subtype, 
*)
(*
type_synonym ex_st_t = "(int md_triv option md_prio * int list md_triv option)"
type_synonym ex_syn_t = "(calc md_triv option)"
type_synonym ex_t = "(ex_syn_t * ex_st_t)"
*)

end


(*

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
*)