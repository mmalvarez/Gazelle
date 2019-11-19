theory Sum_Merge imports "Prism"

begin

record ('s1, 's2, 'c) sum_merge_parms =
  prism1 :: "('s1, 'c) prism_parms"
  prism2 :: "('s2, 'c) prism_parms"

declare sum_merge_parms.defs [simp]
locale Sum_Merge' =
  fixes Sum_Merge_parms :: 
      "('a, 'b, 'c) sum_merge_parms"

locale Sum_Merge = Sum_Merge' +
  P1 : Prism "prism1 Sum_Merge_parms" +
  P2 : Prism "prism2 Sum_Merge_parms"

begin

abbreviation cases1 :: "('c \<Rightarrow> 'a + 'c)" where
"cases1 \<equiv> P1.cases"

abbreviation cases2 :: "('c \<Rightarrow> 'b + 'c)" where
"cases2 \<equiv> P2.cases"

abbreviation inj1 :: "('a \<Rightarrow> 'c)" where
"inj1 \<equiv> P1.inj "

abbreviation inj2 :: "('b \<Rightarrow> 'c)" where
"inj2 \<equiv> P2.inj"

definition overlap :: "('a * 'b) set" where
  "overlap = {(a, b) . inj1 a = inj2 b}"
(*
definition covered :: "('c) set" where
  "covered = {c . (\<exists> a . inj1 a = c) \<or> (\<exists> b . inj2 b = c)}"

lemma CoveredE :
  "c \<in> covered \<Longrightarrow>
    (\<exists> a . inj1 a = c) \<or> (\<exists> b . inj2 b = c)"
  apply(auto simp add:covered_def)
  done

lemma CoveredI1 :
  "(inj1 a) \<in> covered"
  apply(auto simp add:covered_def)
  done

lemma CoveredI2 :
  "(inj2 b) \<in> covered"
  apply(auto simp add:covered_def)
  done
*)
lemma OverlapE :
  "(a, b) \<in> overlap \<Longrightarrow> inj1 a = inj2 b"
  apply(auto simp add:overlap_def)
  done

lemma OverlapI :
  "inj1 a = inj2 b \<Longrightarrow> (a, b) \<in> overlap"
  apply(auto simp add:overlap_def)
  done

(* for prism instance *)
(* note that we are "biasing" toward the left side here
the idea is that we want to see if we can possibly project out
as a left side element, and if so, return that. *)
(* this didn't help - should change these back and
figure out how to proceed. *)
(*
definition mcases :: "'c \<Rightarrow> ('a + 'b) + 'c" where
"mcases c =
  (case (cases1 c) of
    Inl a \<Rightarrow> Inl (Inl a)
    | Inr _ \<Rightarrow> (case (cases2 c) of
        Inl b \<Rightarrow> (case (cases1 (inj2 b)) of
          Inl a' \<Rightarrow> Inl (Inl a')
          | _ \<Rightarrow> Inl (Inr b))
        | Inr _ \<Rightarrow> Inr ( c)))"

definition minj :: "'a + 'b \<Rightarrow> 'c" where
"minj x =
  (case x of
    Inl a \<Rightarrow> inj1 a
    | Inr b \<Rightarrow> 
        (case (cases1 (inj2 b)) of
                 Inl a' \<Rightarrow> inj1 a'
                | Inr c \<Rightarrow> inj2 b))"
*)


(*declare case1_def case2_def inj1_def inj2_def [simp]*)
(*
definition lift1s :: "('a \<Rightarrow> 's1) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lift1s f x =
  inj1 (f x)"

definition lift2s :: "('a \<Rightarrow> 's2) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lift2s f x =
  inj2 (f x)"

definition lower1s :: "('c \<Rightarrow> 'a) \<Rightarrow> ('s1 \<Rightarrow> 'a)" where
"lower1s f x =
  f (inj1 x)"

definition lower2s :: "('c \<Rightarrow> 'a) \<Rightarrow> ('s2 \<Rightarrow> 'a)" where
"lower2s f x =
  f (inj2 x)"
(* warning: these are not fully concrete *)
(* question: are these "more restricted" than the dual
   ones for products? if so, why? do we need separate ones
   to deal with booleans? *)
(* optionize these? *)
definition lift1p :: "('s1 \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"lift1p f x =
  f (SOME x' . case1 x = Inl x')"

definition lift2p :: "('s2 \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'a)" where
"lift2p f x =
  f (SOME x' . case2 x = Inl x')"

definition lower1p :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 's1)" where
"lower1p f x =
  (SOME x' . case1 (f x) = Inl x')"

definition lower2p :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 's2)" where
"lower2p f x =
  (SOME x' . case2 (f x) = Inl x')"
*)
end

(* TODO: prove some sanity-check lemmas here *)
locale Sum_Merge_Spec = Sum_Merge +
  SP1 : Prism_Spec "prism1 Sum_Merge_parms" +
  SP2 : Prism_Spec "prism2 Sum_Merge_parms" 

(* TODO: have a version of this that is even more obviously dual to the Coh for Prod_Merge? *)
(*
assumes Coh' :
    "\<And> c .
          smap2 (sfan2, Inl) (deassoc_sum (smap3 (inj1, inj2, id) (smap2 (id, cases2) (cases1 c)))) =
          smap2 (sfan2, Inr) (deassoc_sum (smap3 (inj2, inj1, id) (smap2 (id, cases1) (cases2 c))))"
*)

(*
assumes Coh12 : 
    "\<And> c . 
      sfan3 (smap3 (inj1, inj2, id) (smap2 (id, cases2) (cases1 c))) = c"

assumes Coh21 : 
    "\<And> c . 
      sfan3 (smap3 (inj2, inj1, id) (smap2 (id, cases1) (cases2 c))) = c"
*)
begin

lemma Coh12 :
"\<And> c . 
      sfan3 (smap3 (inj1, inj2, id) (smap2 (id, cases2) (cases1 c))) = c"
  apply(case_tac "cases1 c", clarsimp)
   apply(simp add: SP1.CaseInl)

  apply(frule_tac SP1.CaseInr)
  apply(clarsimp)
  apply(case_tac "cases2 b", clarsimp)
   apply(simp add: SP2.CaseInl)
  apply(clarsimp)
  apply(frule_tac SP2.CaseInr)
  apply(clarsimp)
  done

lemma Coh21 :
    "\<And> c . 
      sfan3 (smap3 (inj2, inj1, id) (smap2 (id, cases1) (cases2 c))) = c"
  apply(case_tac "cases2 c", clarsimp)
   apply(simp add: SP2.CaseInl)

  apply(frule_tac SP2.CaseInr)
  apply(clarsimp)
  apply(case_tac "cases1 b", clarsimp)
   apply(simp add: SP1.CaseInl)
  apply(clarsimp)
  apply(frule_tac SP1.CaseInr)
  apply(clarsimp)
  done

lemma Coh12' :
  "cases1 (inj2 x) = Inl x' \<Longrightarrow> inj1 x' = inj2 x"
  apply(insert Coh12[of "inj2 x"])
  apply(clarsimp)
  done

lemma Coh21' :
  "cases2 (inj1 x) = Inl x' \<Longrightarrow> inj1 x = inj2 x'"
  apply(insert Coh21[of "inj1 x"])
  apply(clarsimp)
  done

end


(* idea: if we have a pair of coherent prisms that merge,
   we can extend this to a lens to any other target that has prisms from
   both sources, as long as those lenses do not overlap (?) *)

locale Sum_Merge_Total_Spec = Sum_Merge_Spec +
  assumes TCoh12 :
    "\<And> c c' . 
      sfan3 (smap3 (inj1, inj2, const c') (smap2 (id, cases2) (cases1 c))) = c"

assumes TCoh21 : 
    "\<And> c c' . 
      sfan3 (smap3 (inj2, inj1, const c') (smap2 (id, cases1) (cases2 c))) = c"

begin

lemma Total1 :
  fixes c c'
  shows "cases1 c = Inr c' \<Longrightarrow>
   (\<exists> c2 . cases2 c' = Inl c2 \<and> inj2 c2 = c)"
  apply(insert TCoh12[of _ c]) apply(simp)
  apply(insert TCoh21[of _ c']) 


  apply(case_tac "cases2 c'") apply(simp)
  apply(case_tac "cases2 c") apply(simp)
   apply(drule_tac  allI) apply(drule_tac x = c' in spec) apply(clarsimp)

  apply(auto)
  apply(case_tac "cases1 b", auto)
  apply(drule_tac  allI) apply(drule_tac x = b in spec) apply(clarsimp)
  apply(drule_tac allI)
  apply(drule_tac x = "inj1 undefined" in spec)
  apply(insert SP1.CaseInj[of _])
  apply(fastforce)
  done
  
lemma Total2 :
  "cases2 c = Inr c' \<Longrightarrow>
   (\<exists> c1 . cases1 c' = Inl c1 \<and> inj1 c1 = c)"
  apply(insert TCoh21[of _ c]) apply(simp)
  apply(insert TCoh12[of _ c']) 


  apply(case_tac "cases1 c'") apply(simp)
  apply(case_tac "cases1 c") apply(simp)
   apply(drule_tac  allI) apply(drule_tac x = c' in spec) apply(clarsimp)

  apply(auto)
  apply(case_tac "cases2 b", auto)
  apply(drule_tac  allI) apply(drule_tac x = b in spec) apply(clarsimp)
  apply(drule_tac allI)
  apply(drule_tac x = "inj1 undefined" in spec)
  apply(insert SP1.CaseInj[of _])
  apply(fastforce)
  done

(*
lemma CaseInjCoh1 : 
  fixes s2 s1
  shows "cases1 (inj2
*)
end

(* building a par of lenses guaranteed to have no overlap *)
locale Sum_Merge_Extend' = Sum_Merge_Total_Spec +
  fixes Sum_Merge_Extend_parms :: "('a, 'b, 'd) sum_merge_parms"

(*
(* idea: we force the two lenses to have an overlap given
   by the overlap of the final result 
NOTE: you can only do this in one direction (the direction of the larger overlap)
so, i'm not sure if this is worth doing. *)
locale Sum_Merge_Extend_Adapt = Sum_Merge_Extend' +
    SMS : Sum_Merge_Spec "Sum_Merge_Extend_parms" 
begin
print_context
abbreviation overlap' :: "('a * 'b) set" where
"overlap' \<equiv> SMS.overlap"

definition macases1 :: "'c \<Rightarrow> 'c + 'a" where
"mcases d =
  (case cases1' d of
   (Inl a) \<Rightarrow> Inl (inj1 a)
   | Inr d' \<Rightarrow> (case cases2' d of
      (Inl b) \<Rightarrow> Inl (inj2 b)
      | (Inr d'') \<Rightarrow> Inr d''))"

(* TODO: prove totality? *)
definition mainj1 :: "'a \<Rightarrow> 'c" where
"minj c =
  (case cases1 c of
    Inl a \<Rightarrow> inj1' a
    | Inr (_) \<Rightarrow> (case cases2 c of
      Inl b \<Rightarrow>  inj2' b))"


abbreviation maparms1 :: "('a, 'c) prism_parms" where
"maparms1 \<equiv> \<lparr> cases = macases1, inj = mainj1 \<rparr>"

abbreviation maparms2 :: "('b, 'c) prism_parms" where
"maparms2 \<equiv> \<lparr> cases = macases2, inj = mainj2 \<rparr>"

end
*)


locale Sum_Merge_Extend = Sum_Merge_Extend' +
  SMS : Sum_Merge_Spec "Sum_Merge_Extend_parms" (*+
  assumes OLCompat :
  "SMS.overlap = overlap" *)

begin
abbreviation cases1' :: "('d \<Rightarrow> 'a + 'd)" where
"cases1' \<equiv> SMS.P1.cases"

abbreviation cases2' :: "('d \<Rightarrow> 'b + 'd)" where
"cases2' \<equiv> SMS.P2.cases"

abbreviation inj1' :: "('a \<Rightarrow> 'd)" where
"inj1' \<equiv> SMS.P1.inj "

abbreviation inj2' :: "('b \<Rightarrow> 'd)" where
"inj2' \<equiv> SMS.P2.inj"


(* TODO: prove totality? *)
(* idea: cases1' should have picked it up if cases1 (inj2b) = Inl *)
definition mcases :: "'d \<Rightarrow> 'c + 'd" where
"mcases d =
  (case cases1' d of
   (Inl a) \<Rightarrow> Inl (inj1 a)
   | Inr d' \<Rightarrow> 
      (case cases2' d of
      (Inl b) \<Rightarrow> 
        (case cases1 (inj2 b) of
          Inl _ \<Rightarrow> Inr d 
         | Inr _ \<Rightarrow> Inl (inj2 b))
      | (Inr d'') \<Rightarrow> Inr d''))"

(* TODO: prove totality? *)
definition minj :: "'c \<Rightarrow> 'd" where
"minj c =
  (case cases1 c of
    Inl a \<Rightarrow> inj1' a
    | Inr (_) \<Rightarrow> (case cases2 c of
      Inl b \<Rightarrow>  inj2' b))"

abbreviation prism_parms :: "('c, 'd) prism_parms" where
"prism_parms \<equiv> \<lparr> cases = mcases, inj = minj \<rparr>"
end

locale Sum_Merge_Extend_Spec = Sum_Merge_Extend  +
  assumes OCompat : "SMS.overlap \<subseteq> overlap" 

sublocale Sum_Merge_Extend_Spec \<subseteq> Prism_Spec "prism_parms"
  apply(unfold_locales) apply(simp)

(* law 1 *)
    apply(simp add:mcases_def minj_def)

    apply(split sum.split) apply(safe)
     apply(split sum.split_asm)
      apply(simp add: SMS.SP1.CaseInj) apply(clarify)
  apply(simp add: SP1.CaseInl)

     apply(split sum.split_asm)
      apply(frule_tac SP2.CaseInl) apply(clarify)
  apply(frule_tac SP1.CaseInr) apply(clarsimp)
      apply(frule_tac SMS.SP1.CaseInl) 
      apply(drule_tac SMS.OverlapI) apply(rule_tac OverlapE)
      apply(auto simp add: Set.subsetD[OF OCompat])

     apply(drule_tac Total1) apply(clarsimp)
     apply(simp add: SP2.CaseInj)


    apply(auto   simp add:  SP1.CaseInj SP2.CaseInj Coh12'
              SMS.SP1.CaseInl SMS.SP2.CaseInl 
              SMS.SP1.CaseInj SMS.SP2.CaseInj
              split:sum.splits)  
        apply(frule_tac SP2.CaseInl) apply(clarify) apply(clarsimp)
       apply(frule_tac SP2.CaseInl) apply(clarify)
  apply(drule_tac Total1) apply(clarsimp)
     apply(simp add: SP2.CaseInj)
  apply(drule_tac Total1) apply(clarsimp)
     apply(simp add: SP2.CaseInj)
  apply(frule_tac SP1.CaseInr)
    apply(drule_tac Total1) apply(clarsimp)


(* law 2/3 *)

   apply(auto simp add:mcases_def minj_def 
              SP1.CaseInj SP2.CaseInj Coh12'
              SMS.SP1.CaseInl SMS.SP2.CaseInl 
split:sum.splits)

       apply(frule_tac SMS.SP1.CaseInr) apply(clarsimp)
  apply(frule_tac SMS.SP2.CaseInr) apply(clarsimp)

           apply(frule_tac Coh12') apply(frule_tac SMS.SP2.CaseInl)
      apply(clarsimp)
      apply(frule_tac SMS.SP2.CaseInr) apply(clarsimp)
      apply(frule_tac SMS.SP2.CaseInr) apply(clarsimp)
      apply(frule_tac SMS.SP2.CaseInr) apply(clarsimp)
      apply(drule_tac SMS.SP2.CaseInr) apply(clarsimp)
      apply(frule_tac SMS.SP1.CaseInr) apply(clarsimp)
      apply(frule_tac SMS.SP2.CaseInr) apply(clarsimp)
  
      apply(frule_tac SMS.SP1.CaseInr) apply(clarsimp)
  apply(frule_tac SMS.SP2.CaseInr) apply(clarsimp)

  done

end