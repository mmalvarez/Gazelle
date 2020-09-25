theory View_Overlap imports View
begin

locale View_Overlap = 
  fixes cross2 :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" 

assumes idem2 : "\<And> b a c . cross2 b a = c \<Longrightarrow> cross2 c a = c"
(* this implies that all a' contain the same amount of information *)
assumes idem2' : "\<And> b a a' . cross2 (cross2 b a) a' = cross2 b a'"

begin

(* we are going to create a view from a into a + b + (a * b) *)

fun inj' :: "('a * ('a + 'b + ('a * 'b))) \<Rightarrow> ('a + 'b + ('a * 'b))" where
"inj' (a, Inl a') = Inl a"
| "inj' (a, Inr (Inl b)) = Inr (Inr (a, cross2 b a))"
| "inj' (a, Inr (Inr (a', b'))) = 
    (if (cross2 b' a' = b') then
        Inr (Inr (a, cross2 b' a))
     else Inr (Inr (a', b')))"

fun prj' :: "('a + 'b + ('a * 'b)) \<Rightarrow> ('a + ('a + 'b + ('a * 'b)))" where
"prj' (Inl a) = Inl a"
| "prj' (Inr (Inl b)) = Inr (Inr (Inl b))"
| "prj' (Inr (Inr (a, b))) =
    (if (cross2 b a = b) then Inl a
      else Inr (Inr (Inr (a, b))))"

abbreviation vp :: "('a,  ('a + 'b + ('a * 'b))) view_parms" where
"vp \<equiv> \<lparr> inj = inj', prj = prj' \<rparr>"

end

sublocale View_Overlap \<subseteq> View_Spec vp
  apply(unfold_locales)
      apply(clarsimp)
      apply(case_tac r) apply(clarsimp) apply(clarsimp)
      apply(case_tac b) apply(clarsimp) apply(clarsimp)

      apply(case_tac r) apply(clarsimp) apply(clarsimp)
      apply(case_tac b) apply(clarsimp) apply(clarsimp)
     apply(simp split:if_splits)

    apply(clarsimp) apply(case_tac r) apply(simp) apply(clarsimp)
    apply(case_tac b) apply(clarsimp) 
     apply(simp split:if_splits)
    apply(clarsimp)      apply(simp split:if_splits)

   apply(simp) apply(case_tac r) apply(clarsimp) apply(clarsimp)
   apply(case_tac b) apply(clarsimp)
    apply(simp split:if_splits) apply(simp add:idem2)
  apply(clarsimp) apply(simp split:if_splits)
   apply(simp add:idem2)

  apply(simp) apply(case_tac c) apply(clarsimp)
  apply(case_tac ba) apply(clarsimp)
   apply(simp add: idem2 idem2')
  apply(clarsimp)
  apply(simp add: idem2 idem2')
  done

end