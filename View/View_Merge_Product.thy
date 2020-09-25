theory View_Merge_Product
  imports View_Merge
begin

(* if we have two coherent views injecting a1/a2 into b,
   we can create a view from a1 + a2 into b *)
   
locale View_Merge_Sum = View_Merge_Spec
begin
print_context
fun inj' :: "(('a + 'b) * 'c) \<Rightarrow> 'c" where
"inj' (Inl a, c) = V1.inj (a, c)"
| "inj' (Inr b, c) = V2.inj (b, c)"

fun prj' :: "'c \<Rightarrow> (('a + 'b) + 'c)" where
"prj' c =
  (case V1.prj c of
    Inl a \<Rightarrow> Inl (Inl a)
    | Inr _ \<Rightarrow>
  (case V2.prj c of
    Inl b \<Rightarrow> Inl (Inr b)
    | Inr _ \<Rightarrow> Inr c))"
  
end

(* if we have two coherent views injecting a1/a2 into b,
   we can create a view from a1 + a2 into b *)
(* which of these will actually be useful for us?
*)
(*
locale View_Merge_Product = View_Merge_Spec
begin
print_context
fun inj' :: "(('a + 'b) * 'c) \<Rightarrow> 'c" where
"inj' (Inl a, c) = V1.inj (a, c)"
| "inj' (Inr b, c) = V2.inj (b, c)"

fun prj' :: "'c \<Rightarrow> (('a + 'b) + 'c)" where
"prj' c =
  (case V1.prj c of
    Inl a \<Rightarrow> Inl (Inl a)
    | Inr _ \<Rightarrow>
  (case V2.prj c of
    Inl b \<Rightarrow> Inl (Inr b)
    | Inr _ \<Rightarrow> Inr c))"
  
end
*)


end