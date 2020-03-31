theory Aug_Pord imports Pord

begin

(*
defining an ordering on one type from
another one, which is "supposed to" have
bottom elements for all its "components" (e.g.
fields of a tuple/record) even if the original
datatype lacks them
*)

locale Aug_Pord =
  Pord +
  fixes aug :: "'b \<Rightarrow> 'a"
  (* partial because 'b isn't guaratneed to have
     "componentwise bottom elements" *)
  fixes deaug :: "'a \<Rightarrow> 'b option"

begin

(* "l" is short for "lowered", the idea is that in
'b we no longer have the bottom element *)
definition l_pleq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
"l_pleq a b =
  pleq (aug a) (aug b)"


definition is_bub :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
"is_bub a b s =
  (l_pleq a s \<and>
    ((\<forall> bd sd . pleq bd (aug b) \<longrightarrow>
                Pord.is_sup pleq {aug a, bd} sd \<longrightarrow>
                pleq sd (aug s))))"

definition is_bsup :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
"is_bsup a b s =
  Pord.is_least l_pleq (is_bub a b) s"

end

locale Aug_Pord_Spec =
  Aug_Pord +
  Pord_Spec pleq +
  assumes aug_deaug :
  "\<And> a . deaug (aug a) = Some a"

assumes deaug_aug :
  "\<And> b a . deaug b = Some a \<Longrightarrow> aug a = b"

assumes leq_aug_leq :
  "\<And> a a'. l_pleq a a' \<Longrightarrow>  pleq (aug a) (aug a')"

assumes aug_leq_leq1 :
  "\<And> b b' a . l_peq b b' \<Longrightarrow>
              deaug b = Some a \<Longrightarrow> 
              (\<exists> a' . deaug b' = Some a' \<and> l_pleq a a')"

assumes aug_leq_leq2 :
  "\<And> b b' . pleq b b' \<Longrightarrow>
              deaug b' = None \<Longrightarrow> 
              deaug b = None"

(* proving that the partial order we just defined
   meets the partial order laws from Pord *)
sublocale Aug_Pord_Spec \<subseteq> LLl : Pord_Spec "l_pleq"
  apply(unfold_locales)
    apply(simp add:l_pleq_def)
    apply(simp add:leq_refl) 


    apply(simp add:l_pleq_def)
   apply(drule_tac a = "aug a" and b = "aug b" and c = "aug c" in leq_trans)
    apply(simp) apply(simp)

    apply(simp add:l_pleq_def)
  apply(cut_tac a = "aug a" and b = "aug b" in leq_antisym)
    apply(simp)
   apply(simp)

  apply(clarsimp)
  apply(cut_tac a = a in aug_deaug)
  apply(clarsimp)
  apply(cut_tac a = b in aug_deaug)

(* i'm not sure why the simplifier chokes
here. trace output is unhelpful
("??.Unknown" is the rule it says it keeps applying) *)
  apply(simp (asm_lr))
  done

end