theory Syn_Merge imports "Syntax" "../Prism/Sum_Merge"

begin

(* reify/denote are just a prism!
syn1 :: ('s1, 'r) prism
syn2 :: ('s2, 'r) prism
merge :: ('s1, 's2, 'c) sum_merge
and we get a ('c, 'r) prism (?)
put differently a syntax is just a prism with extra C and Case
*)
record ('s1, 's2, 'c, 'r) syn_merge_parms =
  syn1 :: "('s1, 'r) syn_parms"
  syn2 :: "('s2, 'r) syn_parms"
  merge :: "('s1, 's2, 'c) sum_merge_parms"

declare syn_merge_parms.defs [simp]

locale Syn_Merge'' = fixes Syn_Merge_parms :: "('s1, 's2, 'c, 'r) syn_merge_parms"

locale Syn_Merge' = Syn_Merge'' + 
  S1 : Syn_Spec "syn1 Syn_Merge_parms" +
  S2 : Syn_Spec "syn2 Syn_Merge_parms" +
  SM : Sum_Merge_Spec "merge Syn_Merge_parms"

begin

(* footprint. intuition is that this is disjoint union...
   however, what do we do if there is overlap? i guess we can rule this out in spec.
   the whole point of having labels is that we want to be able to distinguish provenance
   of different syntactic forms.
*)

function mreify :: "'c \<Rightarrow> 'd" where
"mreify x =
  (case SM.cases1 x of 
    Inl s1 \<Rightarrow> S1.reify s1
    | _ \<Rightarrow> (case SM.cases2 x of
              Inl s2 \<Rightarrow> S2.reify s2
              | _ \<Rightarrow> mreify x))"
   apply(pat_completeness)
  apply(auto)
  done
termination
  apply(relation "measure (\<lambda> _ . 0)")
   apply(auto)
  apply(drule_tac SM.Coh2) apply(clarify)
  apply(simp add:SM.SP1.CaseInj)
  done

(* also we may run into problems when we have the same types. *)
fun mdenote :: "'d \<Rightarrow> 'c option" where
"mdenote r =
  (case S1.denote r of
    Some x \<Rightarrow> Some (SM.inj1 x)
  | _ \<Rightarrow> (case S2.denote r of
          Some x \<Rightarrow> Some (SM.inj2 x)
           | _ \<Rightarrow> None))
      "

abbreviation mfootprint :: "char list set" where
"mfootprint \<equiv> S1.footprint \<union> S2.footprint"

print_context

(* TODO: abbrevs or defs here? *)
(*
fun mC :: "char list \<Rightarrow> 'd \<Rightarrow> 'c option" where
"mC s r =
  (case S1.C s r of
    Some x1 \<Rightarrow> Some (SM.inj1 x1)
    | _ \<Rightarrow> 
  (case S2.C s r of
    Some x2 \<Rightarrow> Some (SM.inj2 x2)
    | _ \<Rightarrow> None))"
*)
(* we are relying on footprint disjointness to make this reasonable.
   note also that we are doing extra calculation up front *)

(* I think we actually need all 4 cases here, to rule out
weird situations where there is misalignment between the two
footprints
*)
(*
fun mCase :: "char list \<Rightarrow> 'c \<Rightarrow> 'd option" where
"mCase s x =
  (case
      (case SM.cases1 x of
        (Inl s1) \<Rightarrow>
         (case S1.Case s s1 of
           Some r \<Rightarrow> Some r
          | None \<Rightarrow> None)
        | _ \<Rightarrow> None)
   of  Some r \<Rightarrow> Some r
     | None \<Rightarrow> 
       (case SM.cases2 x of
         (Inl s2) \<Rightarrow> S2.Case s s2
         | _ \<Rightarrow> None))"
*)

abbreviation msyn_parms :: "('c, 'd) syn_parms" where
  "msyn_parms \<equiv> \<lparr> reify = mreify
                , denote = mdenote
                , footprint = mfootprint \<rparr>"

end

(* TODO do we need the duals of these? denote then reify? *)
locale Syn_Merge = Syn_Merge' +
  assumes drCoh1 : "\<And> x2 x1 . S1.denote (S2.reify x2) = Some x1 \<Longrightarrow>
                        SM.inj1 x1 = SM.inj2 x2"
  assumes drCoh2 : "\<And> x1 x2 . S2.denote (S1.reify x1) = Some x2 \<Longrightarrow>
                        SM.inj2 x2 = SM.inj1 x1"
  assumes rCoh : "\<And> x1 x2 . SM.inj1 x1 = SM.inj2 x2 \<Longrightarrow>
                              S1.reify x1 = S2.reify x2"
                        

(*
 S1.denote (S2.reify c2) = Some x2a \<Longrightarrow>
       SM.cases2 (SM.inj2 c2) = Inl c2 \<Longrightarrow> SM.inj1 x2a = SM.inj2 c
*)
sublocale Syn_Merge \<subseteq> Syn_Spec "msyn_parms"
  apply(unfold_locales)
     apply(simp)

   apply(auto  split:option.splits)
       apply(split sum.split) apply(clarsimp) apply(auto)
        apply(rule_tac x = x1 in exI)

        apply(simp add: S1.rdvalid)

       apply(split sum.split) apply(safe)
        apply(split sum.split_asm) apply(clarsimp)
        apply(simp add: S2.rdvalid)
        apply(simp only:) apply(clarify)
        apply(split sum.split_asm) apply(clarsimp)
       apply(frule_tac SM.SP1.CaseInr)
apply(frule_tac SM.SP2.CaseInr) apply(clarify)
       apply(drule_tac SM.Coh1)
  apply(simp only:)
       apply(clarify)

      apply(split sum.split_asm) apply(clarsimp)
       apply(simp add:S1.rdvalid)
       apply(simp add:SM.SP1.CaseInl)
          apply(split sum.split_asm) apply(clarsimp)
        apply(split sum.split_asm) apply(clarsimp)
       apply(simp add:S2.rdvalid)
       apply(frule_tac SM.SP1.CaseInr)
  apply(frule_tac SM.SP2.CaseInr) apply(clarify)
       apply(drule_tac SM.Coh1)
  apply(simp only:)
       apply(clarify)

            apply(split sum.split_asm) apply(clarsimp)
       apply(simp add:S1.rdvalid)
            apply(split sum.split_asm) apply(clarsimp)
     apply(split sum.split_asm) apply(clarsimp)
       apply(simp add:S2.rdvalid)
       apply(simp add:SM.SP2.CaseInl)
         apply(frule_tac SM.SP1.CaseInr)
  apply(frule_tac SM.SP2.CaseInr) apply(clarify)
       apply(drule_tac SM.Coh1)
  apply(simp only:)
       apply(clarify)

      apply(split sum.split_asm) apply(clarsimp)
       apply(simp add:S1.rdvalid)
     apply(simp add:SM.SP1.CaseInl)
          apply(split sum.split_asm) apply(clarsimp)
        apply(split sum.split_asm) apply(clarsimp)
       apply(simp add:S2.rdvalid) apply(clarify)
       apply(frule_tac SM.SP1.CaseInr)
     apply(clarify)
  apply(frule_tac SM.SP2.CaseInl) apply(clarify)
       apply(drule_tac SM.Coh1)
  apply(simp only:)
       apply(clarify)
     apply(simp add:drCoh1)
      apply(split sum.split_asm) apply(clarsimp)
      apply(frule_tac SM.SP2.CaseInr) apply(clarify)
      apply(frule_tac SM.SP1.CaseInr) apply(clarify)
       apply(drule_tac SM.Coh1)
  apply(simp only:)
       apply(clarify)

   apply(split sum.split) apply(clarsimp) apply(safe)
    apply(frule_tac SM.SP1.CaseInl)
    apply(simp add:rCoh)
    apply(simp add: S2.drvalid)
   apply(split sum.split) apply(safe)
    apply(simp add:SM.SP2.CaseInj)  
    apply(simp add: S2.drvalid)
    apply(simp add:SM.SP2.CaseInj)  

     apply(split sum.split) apply(clarsimp) apply(safe)
    apply(simp add:SM.SP1.CaseInj)  
    apply(simp add: S1.drvalid)
     apply(split sum.split) apply(safe)
   apply(simp add:SM.SP1.CaseInj)  
    apply(simp add:SM.SP1.CaseInj)  
  done
end