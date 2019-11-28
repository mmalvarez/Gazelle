theory View_Fun imports View
begin

(* Experiment in looking at non idempotent functions as views,
so that we can talk about semantics as part of larger view compositions
*)

locale View_Fun =
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
begin

fun inj' :: "'a * ('a * 'b * 'b) \<Rightarrow> ('a * 'b * 'b)" where
"inj' (a, a', b, b') =
  (a, b, (f a b))"

fun prj' :: "('a * 'b * 'b) \<Rightarrow> ('a + ('a * 'b * 'b))" where
"prj' (a, b, b') =
  (if f a b = b' then Inl a
   else Inr (a, b, b'))"

abbreviation vp :: "('a, ('a * 'b * 'b)) view_parms" where
"vp \<equiv> \<lparr> inj = inj', prj = prj' \<rparr>"

end

sublocale View_Fun \<subseteq> View_Spec "vp"
  apply(unfold_locales)
      apply(auto split:if_splits)
  done

end