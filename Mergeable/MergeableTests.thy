theory MergeableTests imports Mergeable
begin

(* goal: make these proofs more manageable by generalizing
*)

(* define some partial orders:
   trivial: leq means a = b
   option : None < Some
   pairs: (a, b) < (c, d) means (a < c \<and>b < d)
   lexicographical
      (a, b) < (c, d) means (a < c) and (c < a \<longrightarrow> b < d)
 *)

(* define some Mergeables:
  trivial (bsup takes first one)
  option (see test0)
  pairs (see test?)
  lexicographical (do this one later) 

*)

locale Pordc_Trivial =
  fixes t :: "'a itself"
begin
definition pleq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"pleq a b = (a = b)"

end

locale Pordc_Trivial_Spec = Pordc_Trivial

sublocale Pordc_Trivial_Spec \<subseteq> Pordc_Spec "pleq"
proof(unfold_locales)
  show "\<And>a. pleq a a" by (simp add:pleq_def)

  show "\<And>a b c. pleq a b \<Longrightarrow> pleq b c \<Longrightarrow> pleq a c"
    by (simp add:pleq_def)

  show "\<And>a b. pleq a b \<Longrightarrow> pleq b a \<Longrightarrow> a = b"
    by (simp add:pleq_def)

  show "\<And>a b. Pord.has_ub pleq {a, b} \<Longrightarrow> Pord.has_sup pleq {a, b}"
by(auto simp add:
pleq_def
Pord.has_ub_def Pord.is_ub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def)
qed

locale Mg_Trivial = Pordc_Trivial
begin
definition bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"bsup a b = a"

end

locale Mg_Trivial_Spec =
  Mg_Trivial + Pordc_Trivial_Spec

declare [[show_types]]
sublocale Mg_Trivial_Spec \<subseteq> Mergeable_Spec pleq bsup
proof(auto simp only:Mergeable_Spec_def)
  show "Pordc_Spec pleq" by (rule local.Pordc_Spec_axioms)

  show "Mergeable_Spec_axioms pleq bsup"
  proof(unfold_locales)
    show "\<And> (a :: 'a) b. is_bsup a b (bsup a b)"
apply( simp only:
pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def)
      apply(fast)
      done
   qed
qed

locale Pordc_Option' =
  fixes pleq' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
definition pleq :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
"pleq x y =
  (case x of
      None \<Rightarrow> True
      | Some x' \<Rightarrow>
        (case y of
          None \<Rightarrow> False
          | Some y' \<Rightarrow> (pleq' x' y')))"
end

locale Pordc_Option = Pordc_Option' +
  O : Pord pleq' 

locale Pordc_Option_Spec = Pordc_Option +
  OS : Pordc_Spec pleq'

sublocale Pordc_Option_Spec \<subseteq> Pordc_Spec "pleq"
proof(unfold_locales)
  show "\<And> a . pleq a a"
  proof(-)
    fix a
    show "pleq a a"
      by(cases a; auto simp add:pleq_def OS.leq_refl)
  qed

  show "\<And>a b c. pleq a b \<Longrightarrow> pleq b c \<Longrightarrow> pleq a c"
  proof(-)
    fix a b c
    assume H1 : "pleq a b"
    assume H2 : "pleq b c"
    show "pleq a c" using OS.leq_trans H1 H2
      by(auto simp add:pleq_def split:option.splits)
  qed

  show "\<And>a b. pleq a b \<Longrightarrow> pleq b a \<Longrightarrow> a = b"
  proof(-)
    fix a b
    assume H1 : "pleq a b"
    assume H2 : "pleq b a"
    show "a = b" using H1 H2 OS.leq_antisym
      by(auto simp add:pleq_def split:option.splits)
  qed

  show "\<And>a b. Pord.has_ub pleq {a, b} \<Longrightarrow> Pord.has_sup pleq {a, b}"
  proof(-)
    fix a b
    assume H : "Pord.has_ub pleq {a, b}"
    show "Pord.has_sup pleq {a, b}" 
    proof(cases a)
      case None
      then show ?thesis
      proof(cases b) 
        show "a = None \<Longrightarrow> b = None \<Longrightarrow> Pord.has_sup pleq {a, b}"      
          by(auto simp add:
                pleq_def
                Pord.has_ub_def  Pord.is_ub_def
                Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def split:option.splits)
        show " \<And>aa::'a. a = None \<Longrightarrow> b = Some aa \<Longrightarrow> Pord.has_sup pleq {a, b}" using H OS.leq_refl
          by(auto simp add:
                pleq_def
                Pord.has_ub_def  Pord.is_ub_def
                Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def split:option.splits) 
        qed
      next
      case (Some a')
      then show ?thesis
      proof(cases b)
        show "a = Some a' \<Longrightarrow> b = None \<Longrightarrow> Pord.has_sup pleq {a, b}" using H OS.leq_refl
        by(auto simp add:
                pleq_def
                Pord.has_ub_def  Pord.is_ub_def
                Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def split:option.splits) 

        show "\<And>aa::'a. a = Some a' \<Longrightarrow> b = Some aa \<Longrightarrow> Pord.has_sup pleq {a, b}"
          proof(-)
          fix aa
          assume Hi1 : "a = Some a'"
          assume Hi2 : "b = Some aa"
          
          have OUb : "O.has_ub {a', aa}"  using H Hi1 Hi2
            by(auto simp add:pleq_def Pord.is_ub_def Pord.has_ub_def split:option.splits)
          obtain x where OSup : "O.is_sup {a', aa} x" using OS.complete2[OF OUb]
            by(auto simp add:pleq_def Pord.has_sup_def)
  
          have "Pord.is_sup pleq {a, b} (Some x)" using OSup Hi1 Hi2
          apply(auto simp add:
                  pleq_def
                  Pord.has_ub_def  Pord.is_ub_def
                  Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def split:option.splits) 
            apply(rule_tac ext) apply(clarsimp) 
            apply(rule_tac ext) apply(clarsimp)
            (* TODO: make this nicer *)
            apply(rename_tac xsup)
            apply(drule_tac x = xsup in fun_cong) apply(auto)
            done
  
          thus "Pord.has_sup pleq {a, b}" by (auto simp add:Pord.has_sup_def)
        qed
      qed
    qed
  qed
qed

locale Mg_Option' = Pordc_Option +
  fixes bsup' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

definition bsup :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
"bsup x y =
  (case x of
    None \<Rightarrow> y
    | Some x' \<Rightarrow> (case y of
                       None \<Rightarrow> Some x'
                       | Some y' \<Rightarrow> Some (bsup' x' y')))"
end

locale Mg_Option = Mg_Option' +
  OM : Mergeable pleq' bsup'

locale Mg_Option_Spec = Mg_Option +
  Pordc_Option_Spec +
  OMS : Mergeable_Spec pleq' bsup'

sublocale Mg_Option_Spec \<subseteq> Mergeable_Spec pleq bsup
proof(auto simp only:Mergeable_Spec_def)
  show "Pordc_Spec pleq" by (rule local.Pordc_Spec_axioms)

  show "Mergeable_Spec_axioms pleq bsup"
  proof(unfold_locales)
    fix a b
    show "is_bsup a b (bsup a b)"
    proof(cases a)
      case None
      then show ?thesis
      proof(cases b)
        show "a = None \<Longrightarrow> b = None \<Longrightarrow> is_bsup a b (bsup a b)"
          by(auto simp add: pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def)

        fix aa
        show "a = None \<Longrightarrow> b = Some aa \<Longrightarrow> is_bsup a b (bsup a b)"
          apply(simp add: pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def split:option.splits)
          apply(clarsimp)
          apply(rule_tac conjI) apply(clarsimp)
           apply(rule_tac x = "Some aa" in exI) apply(clarsimp) apply(simp add:OS.leq_refl)
           apply(rule_tac x = "Some aa" in exI) apply(clarsimp)  apply(simp add:OS.leq_refl)
          apply(clarsimp)
          apply(drule_tac x = aa in spec) apply(simp add:OS.leq_refl)
          done
      qed next

      case(Some a')
      then show ?thesis
      proof(cases b)
        show "a = Some a' \<Longrightarrow> b = None \<Longrightarrow> is_bsup a b (bsup a b)"
          apply(simp add: pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def split:option.splits)
          apply(simp add: OS.leq_refl)
          done

        show "\<And> aa. a = Some a' \<Longrightarrow> b = Some aa \<Longrightarrow> is_bsup a b (bsup a b)"
        proof(-)
          fix aa
          assume Hi1 : "a = Some a'"
          assume Hi2 : "b = Some aa"

          show "is_bsup a b (bsup a b)" using Hi1 Hi2 OMS.bsup_spec[of a' aa]
            apply(simp add: pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def)
            apply(rule_tac conjI)
             apply(simp add: O.is_bsup_def O.is_least_def O.is_bub_def)

            apply(rule_tac conjI)
             apply(clarsimp)
             apply(simp split:option.splits)


             apply(rule_tac conjI)
             apply(clarsimp)

    next
      case (Some a)
      then show ?thesis sorry
    qed
apply( simp only:
pleq_def bsup_def is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def)
      apply(fast)
      done
   qed
qed

definition test0_bsup :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
"test0_bsup x y =
  (case x of
    None \<Rightarrow> y
    | Some x' \<Rightarrow> Some x')"
  

value "test0_bsup None (Some 2 :: nat option)"
value "test0_bsup (Some 2) (None :: nat option)"

interpretation Test0 : Mergeable_Spec test0_lleq test0_bsup
proof(unfold_locales)

  show "\<And> a . test0_lleq a a"
  proof(-)
    fix a
    show "test0_lleq a a"
      by(cases a; auto simp add:test0_lleq_def)
  qed

  show "\<And>a b c. test0_lleq a b \<Longrightarrow> test0_lleq b c \<Longrightarrow> test0_lleq a c"
  proof(-)
    fix a b c
    assume H1 : "test0_lleq a b"
    assume H2 : "test0_lleq b c"
    show "test0_lleq a c" using H1 H2
      by(auto simp add:test0_lleq_def split:option.splits)
  qed

  show "\<And>a b. test0_lleq a b \<Longrightarrow> test0_lleq b a \<Longrightarrow> a = b"
  proof(-)
    fix a b
    assume H1 : "test0_lleq a b"
    assume H2 : "test0_lleq b a"
    show "a = b" using H1 H2
      by(auto simp add:test0_lleq_def split:option.splits)
  qed

  show "\<And>a b. Pord.has_ub test0_lleq {a, b} \<Longrightarrow> Pord.has_sup test0_lleq {a, b}"
  proof(-)
    fix a b
    assume H : "Pord.has_ub test0_lleq {a, b}"
    show "Pord.has_sup test0_lleq {a, b}" using H
(* completeness *)
      by(auto simp add:
test0_lleq_def
Pord.has_ub_def Pord.is_ub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def All_def; 
      auto  split:option.splits)
  qed

  show "\<And>a b. Pord.is_bsup test0_lleq a b (test0_bsup a b)"
  proof(-)
    fix a b
    show "Pord.is_bsup test0_lleq a b (test0_bsup a b)"
          apply(auto simp add:
test0_lleq_def test0_bsup_def
Pord.has_ub_def Pord.is_ub_def Pord.is_bsup_def Pord.is_bub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def) 
        apply(auto split:option.splits)
      apply(case_tac sd; clarsimp)
      apply(auto)
      done
  qed
qed

(*
type_synonym t1 = "nat option * nat"
*)
type_synonym ('a, 'b) t1 = "'a option * 'b option"

(*
definition test_lleq :: "t1 \<Rightarrow> t1 \<Rightarrow> bool" where 
"test_lleq l r =    (case (l, r) of
         ((None, l2), (None, r2)) \<Rightarrow> l2 = r2
       | ((None, l2), (Some r1, r2)) \<Rightarrow> l2 = r2
       | ((Some _, _), (None, _)) \<Rightarrow> False
       | ((Some l1, l2 ), (Some r1, r2)) \<Rightarrow> l1 = r1 \<and> l2 = r2)"
*)

(*
definition test_lleq :: "('a, 'b) t1 \<Rightarrow> ('a, 'b) t1 \<Rightarrow> bool" where 
"test_lleq l r = 
   (case (l, r) of
         ((None, None), (_, _)) \<Rightarrow> True
         | ((None, Some x2), (_, Some y2)) \<Rightarrow> x2 = y2
         | ((Some x1, None), (Some y1, _)) \<Rightarrow> x1 = y1
         | ((Some x1, Some x2), (Some y1, Some y2)) \<Rightarrow> x1 = y1 \<and> x2 = y2
         | (_, _) \<Rightarrow> False)"
*)
definition test_lleq :: "('a, 'b) t1 \<Rightarrow> ('a, 'b) t1 \<Rightarrow> bool" where 
"test_lleq l r = 
   (case l of
   (ll, lr) \<Rightarrow>
   (case r of
   (rl, rr) \<Rightarrow>
                 
         ((None, None), (_, _)) \<Rightarrow> True
         | ((None, Some x2), (_, Some y2)) \<Rightarrow> x2 = y2
         | ((Some x1, None), (Some y1, _)) \<Rightarrow> x1 = y1
         | ((Some x1, Some x2), (Some y1, Some y2)) \<Rightarrow> x1 = y1 \<and> x2 = y2
         | (_, _) \<Rightarrow> False)"

definition test_bsup :: "('a, 'b) t1 \<Rightarrow> ('a, 'b) t1 \<Rightarrow> ('a, 'b) t1" where
"test_bsup l r = 
    (case (l, r) of
            ((None, l2), (None, r2)) \<Rightarrow> (None, l2)
            |((None, l2), (Some r1, r2)) \<Rightarrow> (Some r1, l2)
            |((Some l1, l2), (None, r2)) \<Rightarrow> (Some l1, l2)
            |((Some l1, l2), (Some r1, r2)) \<Rightarrow> (Some l1, l2))"

(*
definition test_aug :: "t1 \<Rightarrow> t1a" where
"test_aug t =
  (case t of
    (x1, x2) \<Rightarrow> (x1, Some x2))"

definition test_deaug :: "t1a \<Rightarrow> t1 option" where
"test_deaug ta =
  (case ta of
    (x1, Some x2) \<Rightarrow> Some (x1, x2)
    | _ \<Rightarrow> None)"
*)

interpretation Test : Mergeable_Spec test_lleq test_bsup
proof(unfold_locales)

  show "\<And> a . test_lleq a a"
    by(simp add: test_lleq_def split:prod.splits option.splits)

  show "\<And>a b c . test_lleq a b \<Longrightarrow> test_lleq b c \<Longrightarrow> test_lleq a c"
    by(simp add: test_lleq_def split:prod.splits option.splits)

  show "\<And> a b . test_lleq a b \<Longrightarrow> test_lleq b a \<Longrightarrow> a = b"
    by (simp add: test_lleq_def split:prod.splits option.splits)

(* completeness *)

  show "\<And>a b. Pord.has_ub test_lleq {a, b} \<Longrightarrow> Pord.has_sup test_lleq {a, b}"

        apply(simp add:Pord.has_ub_def Pord.is_ub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def)
        apply(clarsimp)
        apply(simp add:test_lleq_def)
    apply(simp split:option.splits; (clarsimp; force))
    done

(* end completeness *)

  show "\<And>a b. Pord.is_bsup test_lleq a b (test_bsup a b)"

  apply(simp add: Pord.is_bsup_def Pord.is_bub_def Pord.is_least_def Pord.is_sup_def Pord.is_ub_def)
    apply(simp add: test_lleq_def test_bsup_def)
    apply(simp split:prod.splits) apply(auto)
      apply(simp split:option.splits)
apply(simp split:option.split) apply(auto)

  apply(case_tac a; clarsimp)
  apply(case_tac aaa; clarsimp)
   apply(case_tac aa; clarsimp)
  apply(case_tac a; clarsimp)
    apply(case_tac b; clarsimp)
      apply(case_tac bb; clarsimp)
      apply(case_tac ab; clarsimp) 
       apply(drule_tac x = None in spec) apply(drule_tac x = "Some a" in spec)
        apply(clarsimp)

  apply(case_tac bb; clarsimp)
       apply(case_tac ab; clarsimp) 

       apply(drule_tac x = None in spec) apply(drule_tac x = "Some a" in spec)
        apply(clarsimp)

  apply(case_tac bb; clarsimp)
       apply(case_tac ab; clarsimp) 
    apply(case_tac b; clarsimp)

   apply(rule_tac conjI)

  apply(clarsimp)
    apply(case_tac ab; clarsimp)
    apply(case_tac aa; clarsimp)

    apply(case_tac b; clarsimp)
       apply(case_tac bb; clarsimp)
      apply(case_tac bb; clarsimp)
     apply(case_tac bb; clarsimp)
    apply(case_tac aa; clarsimp)
     apply(case_tac bb; clarsimp)
    apply(case_tac b; clarsimp)

       apply(drule_tac x = "None"  in spec) apply(drule_tac x = "Some aa" in spec)
        apply(clarsimp)
  
       apply(drule_tac x = "None"  in spec) apply(drule_tac x = "Some aa" in spec)
       apply(clarsimp)

      apply(case_tac b; clarsimp)
     apply(case_tac bb; clarsimp)
    apply(case_tac bb; clarsimp)

  apply(clarsimp)
  apply(simp cong:option.case_cong)
  apply(case_tac aa; clarsimp)
  apply(simp cong:option.case_cong)

       apply(drule_tac x = "Some a" in spec) apply(clarsimp)
       apply(drule_tac x = "None" in spec)
       apply(clarsimp)

       apply(drule_tac x = "Some a" in spec) apply(drule_tac x = "Some baa" in spec)
      apply(clarsimp)
    apply(case_tac b; clarsimp) apply(case_tac a; clarsimp)
     apply(case_tac aa; clarsimp)
apply(case_tac aa; clarsimp)

       apply(drule_tac x = "Some a" in spec) apply(clarsimp)
       apply(drule_tac x = "None" in spec)
   apply(clarsimp)

  apply(simp split:option.splits) apply(clarsimp)


  apply(case_tac aa; clarsimp)
   apply(case_tac ab; clarsimp)
   apply(case_tac b; clarsimp)
   apply(case_tac ac; clarsimp)
     apply(simp  split:option.splits)

   apply(case_tac ac; clarsimp)
    apply(simp  split:option.splits)


   apply(case_tac ac; clarsimp)
   apply(simp  split:option.splits)

   apply(case_tac b; clarsimp)
   apply(case_tac ac; clarsimp)
apply(case_tac ad; clarsimp)
    apply(simp  split:option.splits)
apply(case_tac ad; clarsimp)
  apply(simp  split:option.splits)

   apply(case_tac ac; clarsimp)
apply(case_tac ad; clarsimp)
    apply(simp  split:option.splits)
apply(case_tac ad; clarsimp)
  apply(simp  split:option.splits)

  done
(* ok, so this seems to work - but is rather ugly. *)
*)

end