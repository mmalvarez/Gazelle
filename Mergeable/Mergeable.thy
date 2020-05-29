theory Mergeable imports Pord Aug_Pord

begin

(*
(* preliminary definitions for use in characterizing bsup *)
context Aug_Pord
begin


(* ... *)


  assumes bsup_is_bsup:
    "\<And> a b . is_bsup a b (bsup a b)"      

*)

(* mergeable is a type with an ordering, as well as a way to
  "naturally" (-ish) merge elements that may not have a LUB *)
locale Mergeable =
  Pord +
  fixes bsup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"


(* TODO: do we need to change specification of bsup so that
    it does not use the lifted order when talking about is_sup ?*)
locale Mergeable_Spec =
  Mergeable +

assumes bsup_leq : "\<And> a b . pleq a (bsup a b)"


assumes bsup_mono2 : 
  "\<And> b b' a .
      pleq b b' \<Longrightarrow>
      pleq (bsup a b) (bsup a b')"


(* the following are things I would have liked to have.
But they are not true in general. *)
(*
assumes bsup_idem1 :
  "\<And> a b .
    bsup a (bsup a b) = bsup a b"


assumes bsup_idem2 :
  "\<And> a b . bsup (bsup a b) b = bsup a b"

assumes bsup_assoc :
  "\<And> a b c .
    bsup a (bsup b c) = bsup (bsup a b) c"
*)
(* TODO: this specification is likely incomplete - we can probably say
         more about the cases where a, b have no "real" sup *)

(* if two elements have a supremum, bsup will equal it *)
(* this one is probably not provable from the other
   axioms, but perhaps we should check *)
assumes bsup_sup :
  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
(*
begin

lemma bsup_sup_test
:  "\<And> a b . has_sup {a, b} \<Longrightarrow> is_sup {a, b} (bsup a b)"
  apply(simp add:has_sup_def is_sup_def is_least_def is_ub_def)
  apply(auto)
    apply(simp add:bsup_leq)

(* if there is a proof here, it will involve (bsup a s) and (bsup b s)
but i doubt it. *)
end
*)

(* next up: we need to show that
   any Aug_Pord has enough information
   to give us bsup according to the spec above. *)

locale Aug_Mergeable =
  Aug_Pord +
  fixes bsup :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"

locale Aug_Mergeable_Spec =
  Aug_Mergeable +
  Aug_Pordc_Spec +

assumes bsup_spec :
  "\<And> a b . is_bsup a b (bsup a b)"

begin

lemma aug_merge_bsup_leq : 
"\<And> a b . l_pleq a (bsup a b)"
  apply(cut_tac a = a and b = b in bsup_spec)
  apply(simp add:is_sup_def l_pleq_def is_bsup_def is_bub_def Pord.is_least_def)
  done

(*
lemma aug_merge_bsup_mono1 :
  "\<And> a a' b .
      l_pleq a a' \<Longrightarrow>
      l_pleq (bsup a b) (bsup a' b)"

      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)
  apply(cut_tac a = a and b = b in bsup_spec)
        apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)
*)

lemma aug_merge_bsup_mono2 :
  "\<And> b b' a .
      l_pleq b b' \<Longrightarrow>
      l_pleq (bsup a b) (bsup a b')"
     apply(subgoal_tac "is_bub a b (bsup a b')")
  apply(cut_tac a = a and b = b in bsup_spec)
      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)

      apply(simp add:l_pleq_def is_bsup_def is_bub_def is_sup_def )
      apply(safe)


      apply(cut_tac a = a and b = b' in bsup_spec)
      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)

      apply(cut_tac a = a and b = b in bsup_spec)
      apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)
      apply(auto)

      apply(cut_tac a = a and b = b' in bsup_spec)
        apply(simp add:is_least_def l_pleq_def is_bsup_def is_bub_def is_sup_def Pord.is_least_def is_ub_def)
      apply(clarsimp)

  apply(thin_tac
" \<forall>a'. pleq (aug a) (aug a') \<and> (\<forall>bd. pleq bd (aug b') \<longrightarrow> (\<forall>sd. pleq (aug a) sd \<and> pleq bd sd \<and> (\<forall>a'. pleq (aug a) a' \<and> pleq bd a' \<longrightarrow> pleq sd a') \<longrightarrow> pleq sd (aug a'))) \<longrightarrow> pleq (aug (bsup a b')) (aug a')"
)
  apply(thin_tac
" \<forall>a'. pleq (aug a) (aug a') \<and> (\<forall>bd. pleq bd (aug b) \<longrightarrow> (\<forall>sd. pleq (aug a) sd \<and> pleq bd sd \<and> (\<forall>a'. pleq (aug a) a' \<and> pleq bd a' \<longrightarrow> pleq sd a') \<longrightarrow> pleq sd (aug a'))) \<longrightarrow> pleq (aug (bsup a b)) (aug a')"
)
      apply(rotate_tac -1)
  apply(drule_tac x = bd in spec) apply(auto)

      apply(drule_tac a = bd and b = "aug b" and c = "aug b'" in leq_trans)
   apply(simp) apply(simp)
  done

lemma aug_merge_bsup_sup :
  "\<And> a b . LLl.has_sup {a, b} \<Longrightarrow> LLl.is_sup {a, b} (bsup a b)"
    apply(cut_tac a = a and b = b in bsup_spec)
  apply(simp add: LLl.has_sup_def LLl.is_sup_def is_bsup_def is_bub_def LLl.is_ub_def LLl.is_least_def
is_sup_def is_ub_def is_least_def
) apply(auto)

   apply(drule_tac x = s in spec) apply(auto)
    apply(drule_tac x = bd in spec) apply(auto)
    apply(drule_tac x = "aug s" in spec) apply(auto)

     apply(drule_tac a = a and a' = s in "leq_aug_leq")  apply(auto)
  apply(drule_tac a = bd and b = "aug b" and c = "aug s"
        in leq_trans)
     apply(rule_tac leq_aug_leq) apply(auto)

   apply(drule_tac x = "aug b" in spec) apply(auto)
    apply(simp add: leq_refl)

  apply(drule_tac x = "aug s" in spec) apply(auto)
     apply(rule_tac leq_aug_leq) apply(auto)
     apply(rule_tac leq_aug_leq) apply(auto)

    apply(cut_tac a = a in aug_deaug)
    apply(drule_tac aug_leq_leq1) apply(simp) apply(clarsimp)

    apply(cut_tac a = b in aug_deaug)
    apply(drule_tac aug_leq_leq1) apply(simp) apply(clarsimp)
    apply(drule_tac x = a'a in spec) apply(auto)
    apply(drule_tac b = a' in deaug_aug) apply(clarsimp)
    apply(rule_tac leq_aug_leq, auto)

  apply(cut_tac a = s in aug_deaug)
   apply(drule_tac aug_leq_leq1) apply(simp) apply(clarsimp)
   apply(simp add:aug_deaug) apply(clarsimp)
   apply(drule_tac a = b and b = s and c = "bsup a b" in LLl.leq_trans) apply(auto)

  apply(drule_tac x = s in spec) apply(auto)
  apply(rotate_tac -1)
  apply(drule_tac x = "aug s" in spec) apply(auto)
    apply(simp add:leq_aug_leq)
   apply(drule_tac a = b and a' = s in leq_aug_leq) 
  apply(drule_tac a = bd and b = "aug b" and c = "aug s" in
    leq_trans) apply(auto)

  apply(drule_tac x = a' in spec) apply(auto)
  apply(drule_tac a = "bsup a b" and b = "s" and c = a' in LLl.leq_trans) apply(auto)
  done


(* lemmas to help establish bsup_sup_assoc *)
lemma bsup_comm :
  assumes H : "LLl.has_sup {a, b}"
  shows "bsup a b = bsup b a"
proof -
  have 0 : "\<exists> x . LLl.is_sup { a, b} x" using H
    by (auto simp add:LLl.is_sup_def LLl.has_sup_def)
  have 1 : "LLl.is_sup {a, b} (bsup a b)" using H
    by(auto elim: aug_merge_bsup_sup)
  from 0 obtain x where 2: "LLl.is_sup {a, b} x" .. 
  hence 3 : "bsup a b = x " using 1
    by(auto simp add:LLl.is_sup_def LLl.is_least_unique)
  from H have 4: "LLl.has_sup {b, a}"
    by(auto simp add: LLl.has_sup_def elim:LLl.is_sup_comm2)
  hence 5: "LLl.is_sup {b, a} x" using 2
    by(auto simp add: LLl.has_sup_def LLl.is_sup_unique elim:LLl.is_sup_comm2[of a b x])
  have 6 : "LLl.is_sup {b, a} (bsup b a)" using 4
    by(auto elim: aug_merge_bsup_sup)
  have 7 : "bsup b a = x" using 5 and 6
    by(auto simp add:LLl.is_sup_unique)
  show ?thesis using 7 and 3 by auto
qed

(*
lemma sup_contr :
  assumes Hnolub : "\<not> (LLl.has_sup {a, b})"
  assumes Hub : "LLl.has_ub {a, b}"
  shows "(\<exists> ub1 ub2 . 
            (\<not> l_pleq ub1 ub2 \<and>
             \<not> l_pleq ub2 ub1 \<and>
             LLl.is_ub {a, b} ub1 \<and>
             LLl.is_ub {a, b} ub2))"
proof(-)
  obtain ub1 where Is_Ub1 : "LLl.is_ub {a, b} ub1" using Hub
    by(auto simp add:LLl.has_ub_def)
*)  
  

lemma sup_extend :
  assumes Hleq : "pleq a x"
  assumes Hlub1 : "is_sup {a, c} u1"
  assumes Hlub2 : "is_sup {x, c} u2"
  shows "pleq u1 u2"
proof(-)
  have 0 :  "pleq x u2" using Hlub2 by (auto simp add:is_sup_def is_ub_def is_least_def)
  have 1 :  "pleq a u2" using leq_trans[OF Hleq 0] by auto
  hence "is_ub {a, c} u2" using Hlub2
    by (auto simp add:is_sup_def is_ub_def is_least_def)

  thus ?thesis using Hlub1
    by (auto simp add:is_sup_def is_ub_def is_least_def)
qed
(* need 2 directions.
1 where a is lesser than a'
1 where a is greater than a'
? *)

(* assumes Hleqa : "l_pleq a (bsup a' b')" *)

(* TODO: I think this may be insufficiently general *)
lemma bsup_compare1:
(*  assumes Hleq1 : " *)
 assumes Hleqa : "l_pleq a a'"
  assumes Hleqa' : "l_pleq a' (bsup a b)"
(*  assumes Hleqb : "l_pleq b b'" *)
  assumes Hdesc : "\<And> bd sd . pleq bd (aug b) \<Longrightarrow> is_sup {aug a, bd} sd \<Longrightarrow> 
                        (pleq bd (aug b'))" (* can we get away with has_ub here? *)
(* also used to have:  \<and> pleq bd (aug (bsup a' b')) *)
  shows "l_pleq (bsup a b) (bsup a' b')"
proof(-)
  have Bub : "is_bub a b (bsup a' b')"
  proof(-)
(*    fix d s
    assume d_leq : "l_pleq d b"
    assume d_sup : "LLl.is_sup {a, d} s"
    have 0: "l_pleq d b'" using Hdesc[OF d_leq d_sup] ..
    have 1: "l_pleq d (bsup a' b')" using Hdesc [OF d_leq d_sup] .. *)
    
    have 0: "is_bsup a' b' (bsup a' b')" using bsup_spec 
      by (auto simp add:is_bsup_def)
    have Hbub : "\<And> bd sd . pleq bd (aug b) \<Longrightarrow> is_sup {aug a, bd} sd \<Longrightarrow> pleq sd (aug (bsup a b))"
      using bsup_spec[of a b] by(auto simp add:bsup_spec is_bsup_def is_bub_def LLl.is_least_def l_pleq_def) 
    
    have Hbub' : "\<And> bd sd . pleq bd (aug b') \<Longrightarrow> is_sup {aug a', bd} sd \<Longrightarrow> pleq sd (aug (bsup a' b'))"
      using bsup_spec[of a' b'] by(auto simp add:bsup_spec is_bsup_def is_bub_def LLl.is_least_def l_pleq_def) 
    
    have 1: "is_bsup a b (bsup a b)" using bsup_spec
      by (auto simp add:is_bsup_def)

    have Conc1 : "l_pleq a (bsup a' b')" using Hleqa
    proof(-)
      have in0 : "l_pleq a' (bsup a' b')" using  aug_merge_bsup_leq by auto
      thus ?thesis using LLl.leq_trans[OF Hleqa in0] by auto
    qed

    have Conc2 : "\<And> bd sd . pleq bd (aug b) \<Longrightarrow> is_sup {aug a, bd} sd \<Longrightarrow> pleq sd (aug (bsup a' b'))"
    proof(-)
      fix bd sd
      assume Hbd : "pleq bd (aug b)"
      assume Hsup : "is_sup {aug a, bd} sd"

      have 0 : "pleq bd (aug b')" using Hdesc[OF Hbd Hsup] by auto
(*      have 1 : "pleq bd (aug (bsup a' b'))" using Hdesc[OF Hbd Hsup] *)

      have 1 : "pleq bd sd" using Hsup 
        by(auto simp add: is_sup_def is_ub_def is_least_def)

      have 2 : "pleq sd (aug (bsup a b))" using Hbub[OF Hbd Hsup] by auto

      have 3 : "pleq bd (aug (bsup a b))" using leq_trans[OF 1 2] by auto 

      (* problem - need to show existence of least upper bound
         but we do not have (and, i think, do not want) a standard notion of completeness *)

      hence 3 : "is_ub {(aug a'), bd} (aug (bsup a b))" using Hleqa'
        by(auto simp add:is_ub_def leq_refl l_pleq_def) 

      hence 4 : "has_ub {(aug a'), bd}"
        by (auto simp add:has_ub_def)

      hence 5 : "has_sup {(aug a'), bd}"
        by (auto simp add:complete2)

      then obtain sd' where Hsd' : "is_sup {aug a', bd} sd'" by (auto simp add:has_sup_def)

      have 6: "pleq sd' (aug (bsup a' b'))" using Hbub'[OF 0 Hsd'] by auto

      have 7 : "pleq (aug a) (aug a')" using Hleqa by (simp add:l_pleq_def)
      have 8 : "pleq sd sd'" using sup_extend[OF 7 Hsup Hsd'] by auto
      
      show "pleq sd (aug (bsup a' b'))" using leq_trans[OF 8 6] by auto
    qed

    then show ?thesis using Conc1 Conc2 by(simp add:is_bub_def) 
  qed
  thus ?thesis using bsup_spec [of a b]
    by(auto simp add:is_bsup_def LLl.is_least_def)
qed

(* do we really need to prove this again?
or can we do something more general? *)
lemma bsup_compare2:
 assumes Hleqa' : "l_pleq a' a"
 assumes Hleqa : "l_pleq a (bsup a' b')" 
(*  assumes Hleqb : "l_pleq b b'" *)
  assumes Hdesc : "\<And> bd sd . pleq bd (aug b) \<Longrightarrow> is_sup {aug a, bd} sd \<Longrightarrow> 
                        (pleq bd (aug b'))" (* can we get away with has_ub here? *)
(* also used to have:  \<and> pleq bd (aug (bsup a' b')) *)
  shows "l_pleq (bsup a b) (bsup a' b')"
proof(-)
  have Bub : "is_bub a b (bsup a' b')"
  proof(-)
(*    fix d s
    assume d_leq : "l_pleq d b"
    assume d_sup : "LLl.is_sup {a, d} s"
    have 0: "l_pleq d b'" using Hdesc[OF d_leq d_sup] ..
    have 1: "l_pleq d (bsup a' b')" using Hdesc [OF d_leq d_sup] .. *)
    
    have 0: "is_bsup a' b' (bsup a' b')" using bsup_spec 
      by (auto simp add:is_bsup_def)
    have Hbub : "\<And> bd sd . pleq bd (aug b) \<Longrightarrow> is_sup {aug a, bd} sd \<Longrightarrow> pleq sd (aug (bsup a b))"
      using bsup_spec[of a b] by(auto simp add:bsup_spec is_bsup_def is_bub_def LLl.is_least_def l_pleq_def) 
    
    have Hbub' : "\<And> bd sd . pleq bd (aug b') \<Longrightarrow> is_sup {aug a', bd} sd \<Longrightarrow> pleq sd (aug (bsup a' b'))"
      using bsup_spec[of a' b'] by(auto simp add:bsup_spec is_bsup_def is_bub_def LLl.is_least_def l_pleq_def) 
    
    have 1: "is_bsup a b (bsup a b)" using bsup_spec
      by (auto simp add:is_bsup_def)

    have Conc1 : "l_pleq a (bsup a' b')" using Hleqa by auto

    have Conc2 : "\<And> bd sd . pleq bd (aug b) \<Longrightarrow> is_sup {aug a, bd} sd \<Longrightarrow> pleq sd (aug (bsup a' b'))"
    proof(-)
      fix bd sd
      assume Hbd : "pleq bd (aug b)"
      assume Hsup : "is_sup {aug a, bd} sd"

      have 0 : "pleq bd (aug b')" using Hdesc[OF Hbd Hsup] by auto

      have 1 : "pleq bd sd" using Hsup 
        by(auto simp add: is_sup_def is_ub_def is_least_def)

      have 2 : "pleq sd (aug (bsup a b))" using Hbub[OF Hbd Hsup] by auto


      have 3 : "pleq bd (aug (bsup a b))" using leq_trans[OF 1 2] by auto 

      (* problem - need to show existence of least upper bound
         but we do not have (and, i think, do not want) a standard notion of completeness *)

      have 4 : "l_pleq a' (bsup a b)" using LLl.leq_trans[OF Hleqa' aug_merge_bsup_leq[of a b]] 
        by auto

      hence 5 : "is_ub {(aug a'), bd} (aug (bsup a b))" using 3
        by(auto simp add:is_ub_def leq_refl l_pleq_def)

      hence 6 : "has_ub {(aug a'), bd}" by (auto simp add:has_ub_def)

      have 7: "has_sup {aug a', bd}" using complete2[OF 6] by auto

      have 8 : "pleq bd (aug b')" using Hdesc[OF Hbd Hsup] by auto

      obtain sd' where Hsd' : "is_sup {aug a', bd} sd'" using 7 by (auto simp add:has_sup_def)

      have 9 : "pleq sd' (aug (bsup a' b'))" using Hbub'[OF 8 Hsd'] by auto

      have 10 : "pleq bd sd'" using Hsd' by (auto simp add:is_sup_def is_least_def is_ub_def)

      have 11 : "pleq bd (aug (bsup a' b'))" using leq_trans[OF 10 9] by auto

      have 12 : "is_ub {(aug a), bd} (aug (bsup a' b'))" using Hleqa 11
        by(auto simp add:is_ub_def l_pleq_def)

      show "pleq sd (aug (bsup a' b'))" using 12 Hsup
        by(auto simp add:is_ub_def is_sup_def is_least_def)
    qed

    then show ?thesis using Conc1 Conc2 by(simp add:is_bub_def) 
  qed
  thus ?thesis using bsup_spec [of a b]
    by(auto simp add:is_bsup_def LLl.is_least_def)
  qed


lemma assoc_fact1 :
  "bsup a (bsup b c) = (bsup (bsup a b) (bsup b c))"
proof(-)
  have 0:  "l_pleq a (bsup a b)" using bsup_spec 
    by(simp add:aug_merge_bsup_leq)
  have 1:  "l_pleq b (bsup b c)" using bsup_spec 
    by(simp add:aug_merge_bsup_leq)
  have 2 : "l_pleq (bsup a b) (bsup a (bsup b c))"
    using aug_merge_bsup_mono2[OF 1] by auto

(*
  have 3 : "\<And> bd sd. pleq bd (aug (bsup b c)) \<Longrightarrow> is_sup {aug a, bd} sd \<Longrightarrow> pleq bd (aug (bsup b c))"
    by auto
*)
  have LtoR : "l_pleq (bsup a (bsup b c)) (bsup (bsup a b) (bsup b c))"
    using bsup_compare1[OF 0 2] by auto

  have RtoL : "l_pleq (bsup (bsup a b) (bsup b c)) (bsup a (bsup b c))"
    using bsup_compare2[OF 0 2] by auto

  thus ?thesis using LLl.leq_antisym[OF LtoR RtoL] by auto
qed

lemma leq_completion :
  assumes Hleq : "pleq a a'"
  assumes Hsup : "is_sup {a', b} x"

shows "has_sup {a, b}"
proof(-)
  have 0 :  "pleq a' x" using Hsup by (simp add:is_sup_def is_least_def is_ub_def)
  have 1 : "pleq a x" using leq_trans[OF Hleq 0] by auto
  hence 2 : "is_ub {a, b} x" using Hsup by (simp add:is_sup_def is_least_def is_ub_def)
  hence 3 : "has_ub {a, b}" by (auto simp add:has_ub_def)
  thus ?thesis by (auto elim: complete2)
qed

(* i think we need to prove this directly. not from the other one
also we should see if we can actually prove the real associativity using
a slightly more general bsup_compare talking about descendents (probably not...) *)

lemma assoc_fact2 :
  "l_pleq (bsup (bsup a b) c) (bsup (bsup a b) (bsup a c))"
proof(-)
  have 0 : "l_pleq (bsup a b) (bsup a b)" using LLl.leq_refl by auto

  have 1 : "l_pleq (bsup a b) (bsup (bsup a b) c)" using aug_merge_bsup_leq by auto

  have 2 : "l_pleq (bsup a b) (bsup (bsup a b) (bsup a c))" using aug_merge_bsup_leq by auto

  have 3 : "(\<And>bd sd. pleq bd (aug c) \<Longrightarrow> is_sup {aug (bsup a b), bd} sd \<Longrightarrow> pleq bd (aug (bsup a c)))"
  proof(-)
    fix bd sd
    assume Hpleq : "pleq bd (aug c)"
    assume Hsup : "is_sup {aug (bsup a b), bd} sd"

    have in1 : "has_sup {aug (bsup a b), bd}" using Hsup by (auto simp add:has_sup_def)
    have in2 : "pleq (aug a) (aug (bsup a b))" using aug_merge_bsup_leq by (auto simp add:l_pleq_def)
    have in3 : "has_sup {aug a, bd}" using leq_completion[OF in2 Hsup] by auto
    then obtain sd' where Hsd : "is_sup {aug a, bd} sd'"
      by (auto simp add:has_sup_def)

    have in4 : "pleq sd' (aug (bsup a c))" using Hsd Hpleq bsup_spec[of a c]
      by(auto simp add: is_bsup_def LLl.is_least_def is_bub_def)

    have in5 : "pleq bd sd'" using Hsd by (simp add:is_sup_def is_ub_def is_least_def)

    show "pleq bd (aug (bsup a c))" using leq_trans[OF in5 in4] by auto
  qed

  thus ?thesis using bsup_compare1[OF 0 1 3] by auto
qed


(* remaining facts we want:
has_sup a b \<Longrightarrow> (bsup a (bsup b c)) = (bsup b (bsup a c))
has_sup a b \<Longrightarrow> (bsup (bsup a b)) c \<le> bsup a (bsup b c)

*)

lemma sup_assoc_fact1 :
  fixes a b c
  assumes Hsup : "LLl.has_sup {a, b}"
  shows "l_pleq (bsup (bsup a b) c) (bsup a (bsup b c))"
proof(-)
  have 0 : "bsup (bsup a b) c = bsup (bsup b a) c"
    using bsup_comm[OF Hsup]  by auto

  have 1 : "l_pleq (bsup (bsup b a) c) (bsup (bsup b a) (bsup b c))"
    using assoc_fact2 by auto

  have 3 : "bsup (bsup b a) (bsup b c) = bsup (bsup a b) (bsup b c)"
    using bsup_comm[OF Hsup] by auto

  have 4 : "bsup (bsup a b) (bsup b c) = bsup a (bsup b c)"
    using assoc_fact1 by auto

  show ?thesis using 0 1 3 4 by auto
qed

lemma sup_assoc_fact2 :
  fixes a b c
  assumes Hsup : "LLl.has_sup {a, b}"
  shows "bsup (bsup a b) c = bsup (bsup b a) c"
  using bsup_comm[OF Hsup] by auto

lemma sup_assoc_fact3 :
  fixes a b c
  assumes Hsup : "LLl.has_sup {a, b}"
  shows "l_pleq (bsup (bsup a b) c) (bsup b (bsup a c))"
proof(-)

(*  have "bsup (bsup a b) c = bsup (bsup b a) c" using sup_assoc_fact2[OF Hsup] by auto *)

  have 1 : "l_pleq (bsup (bsup a b) c) (bsup (bsup a b) (bsup a c))"
    using assoc_fact2 by auto

  have 2 : "bsup (bsup a b) (bsup a c) = bsup (bsup b a) (bsup a c)"
    using bsup_comm[OF Hsup] by auto

  have 3 : "bsup (bsup b a) (bsup a c) = bsup b (bsup a c)" 
    using assoc_fact1 by auto

  show ?thesis using 1 2 3 by auto

qed

(*

lemma assoc_fact3 :
  "\<And> a b c . bsup (bsup a b) c = (bsup (bsup a b) (bsup a c))"
proof(-)
  fix a b c
  have LtoR : "l_pleq (bsup (bsup a b) c) (bsup (bsup a b) (bsup a c))" using assoc_fact2 by auto

  have RtoL : "l_pleq (bsup (bsup a b) (bsup a c)) (bsup (bsup a b) c)"
  proof(-)
    have 0 : "l_pleq (bsup (bsup a b) (bsup a c)) (bsup (bsup (bsup a b) a) (bsup (bsup a b) c))"
      using assoc_fact2[of a b "bsup a c"]

(*
  have 4 : "(\<And>bd sd. pleq bd (aug (bsup a c)) \<Longrightarrow> is_sup {aug (bsup a b), bd} sd \<Longrightarrow> pleq bd (aug c))"
  proof(-)
    fix bd sd
    assume Hpleq : "pleq bd (aug (bsup a c))"
    assume Hsup : "is_sup {aug (bsup a b), bd} sd"
*)
  
  
(*
lemma assoc :
(*  "bsup a (bsup b c) = bsup (bsup a b) c" *)
"l_pleq (bsup (bsup a b) c) (bsup a (bsup b c))"
proof(-)

  have 0:  "l_pleq a (bsup a b)" using bsup_spec 
    by(simp add:aug_merge_bsup_leq)

  have 1 : "l_pleq (bsup a b) (bsup a b)" 
    using LLl.leq_refl by auto

  have 2 :
"(\<And>cd sd. pleq cd (aug c) \<Longrightarrow> is_sup {aug (bsup a b), cd} sd \<Longrightarrow> pleq cd (aug (bsup b c)))"
*)

end

sublocale Aug_Mergeable_Spec \<subseteq> PM : Mergeable_Spec l_pleq bsup
  apply(unfold_locales)

  (* bsup_leq *)
  apply(rule_tac aug_merge_bsup_leq)

(* bsup_mono2 *)
(* perhaps this one isn't true either? *)
  apply(rule_tac aug_merge_bsup_mono2; simp)

(* bsup_sup *)
  apply(rule_tac aug_merge_bsup_sup; simp)

  done

fun test0_lleq :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"test0_lleq None _ = True"
| "test0_lleq x y = (x = y)"

fun test0_aug_lleq :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"test0_aug_lleq None _ = True"
| "test0_aug_lleq x y = (x = y)"

fun test0_bsup :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
"test0_bsup None r = r"
| "test0_bsup l r = l"
  

value "test0_bsup None (Some 2)"
value "test0_bsup (Some 2) (None)"
term "Mergeable_Spec"

print_locale Aug_Mergeable_Spec

interpretation Test0 : Aug_Mergeable_Spec test0_lleq  id Some test0_bsup
  apply(unfold_locales)
     apply(case_tac a; clarsimp) 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)
              apply(case_tac b; clarsimp)

(* completeness *)

        apply(simp add:Pord.has_ub_def Pord.is_ub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def)

     apply(case_tac a; clarsimp) 
    apply(case_tac b; clarsimp)
        apply(rule_tac x = None in exI)
        apply(simp add:All_def)
  apply(rule_tac ext; auto)


(* end completeness *)

     apply(case_tac a; clarsimp) 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)
  apply(auto)

apply(simp add:Aug_Pord.l_pleq_def)
  apply(simp add:Aug_Pord.l_pleq_def)

  apply(simp add: Aug_Pord.is_bsup_def Aug_Pord.is_bub_def Pord.is_least_def Pord.is_sup_def Pord.is_ub_def)
  
  apply(auto)
apply(simp add:Aug_Pord.l_pleq_def)
    apply(case_tac a; clarsimp)

   apply(case_tac a; clarsimp) 

   apply(case_tac a; clarsimp) 

  apply(case_tac b; clarsimp)
  apply(drule_tac x = "Some a" in spec) apply(auto)
apply(simp add:Aug_Pord.l_pleq_def)
  done


type_synonym t1 = "nat option * nat"

type_synonym t1a = "nat option * nat option"

(*
definition test_lleq :: "t1 \<Rightarrow> t1 \<Rightarrow> bool" where 
"test_lleq l r =    (case (l, r) of
         ((None, l2), (None, r2)) \<Rightarrow> l2 = r2
       | ((None, l2), (Some r1, r2)) \<Rightarrow> l2 = r2
       | ((Some _, _), (None, _)) \<Rightarrow> False
       | ((Some l1, l2 ), (Some r1, r2)) \<Rightarrow> l1 = r1 \<and> l2 = r2)"
*)

definition test_lleq :: "t1a \<Rightarrow> t1a \<Rightarrow> bool" where 
"test_lleq l r = 
   (case (l, r) of
         ((None, None), (_, _)) \<Rightarrow> True
         | ((None, Some x2), (_, Some y2)) \<Rightarrow> x2 = y2
         | ((Some x1, None), (Some y1, _)) \<Rightarrow> x1 = y1
         | ((Some x1, Some x2), (Some y1, Some y2)) \<Rightarrow> x1 = y1 \<and> x2 = y2
         | (_, _) \<Rightarrow> False)"

definition test_bsup :: "t1 \<Rightarrow> t1 \<Rightarrow> t1" where
"test_bsup = (\<lambda> l r .
    (case (l, r) of
            ((None, l2), (None, r2)) \<Rightarrow> (None, l2)
            |((None, l2), (Some r1, r2)) \<Rightarrow> (Some r1, l2)
            |((Some l1, l2), (None, r2)) \<Rightarrow> (Some l1, l2)
            |((Some l1, l2), (Some r1, r2)) \<Rightarrow> (Some l1, l2)))"

definition test_aug :: "t1 \<Rightarrow> t1a" where
"test_aug t =
  (case t of
    (x1, x2) \<Rightarrow> (x1, Some x2))"

definition test_deaug :: "t1a \<Rightarrow> t1 option" where
"test_deaug ta =
  (case ta of
    (x1, Some x2) \<Rightarrow> Some (x1, x2)
    | _ \<Rightarrow> None)"

(*
print_locale Aug_Mergeable_Spec
interpretation Test : Aug_Mergeable_Spec test_lleq test_aug test_deaug test_bsup

  apply(unfold_locales)
              apply(simp add: test_lleq_def split:prod.splits option.splits)
  apply(simp add: test_lleq_def split:prod.splits option.splits)
         apply(simp add: test_lleq_def split:prod.splits option.splits)

(* completeness *)

        apply(simp add:Pord.has_ub_def Pord.is_ub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def)

        apply(clarsimp)
        apply(simp add:test_lleq_def)
        apply(simp split:option.splits; (clarsimp; force))

(* end completeness *)

       apply(simp add: test_deaug_def test_aug_def test_lleq_def split:prod.splits option.splits)
      apply(simp add: test_deaug_def test_aug_def test_lleq_def split:prod.splits option.splits)
       apply(clarsimp)

      apply(simp add: Aug_Pord.l_pleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)
      apply(simp add: Aug_Pord.l_pleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)
     apply(clarsimp) apply(fastforce)
      apply(simp add: Aug_Pord.l_pleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)

  apply(simp add: Aug_Pord.l_pleq_def Aug_Pord.is_bsup_def Aug_Pord.is_bub_def Pord.is_least_def Pord.is_sup_def Pord.is_ub_def)
  apply(simp add: test_deaug_def test_aug_def test_lleq_def test_bsup_def)


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
*)
end