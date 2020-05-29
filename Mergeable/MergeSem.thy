theory MergeSem imports Mergeable

begin

print_locale Aug_Mergeable
print_locale Aug_Pord

(* other ingredients we need:



*)
locale MergeSem =
  Aug_Mergeable "pleq :: 'a \<Rightarrow> 'a \<Rightarrow> bool" "aug :: 'b \<Rightarrow> 'a"  deaug bsup +
  T1 : Aug_Pord "pleq1 :: 'a1 \<Rightarrow> 'a1 \<Rightarrow> bool" "aug1 :: 'b1 \<Rightarrow> 'a1"  deaug1  +
  T2 : Aug_Pord "pleq2 :: 'a2 \<Rightarrow> 'a2 \<Rightarrow> bool" "aug2 :: 'b2 \<Rightarrow> 'a2" deaug2 
  for  pleq aug deaug bsup
       pleq1 aug1 deaug1
       pleq2 aug2 deaug2 +
     fixes inj1 :: "'a1 \<Rightarrow> 'a"
     fixes prj1 :: "'a \<Rightarrow> 'a1"
     fixes inj2 :: "'a2 \<Rightarrow> 'a"
     fixes prj2 :: "'a \<Rightarrow> 'a2"
     fixes sem1 ::
       "'b1 \<Rightarrow> 'b1" 
     fixes sem2 ::
       "'b2 \<Rightarrow> 'b2"
begin

(* spec will imply this is total *)
(* issue: bsup operates on lowered states.
but we will be supplying augmented states...
*)
definition sem12 :: "'b \<Rightarrow> 'b" where
"sem12 = (\<lambda> st .
  (let st1a = prj1 (aug st) in
   let st1 = (case (deaug st1a) of Some x1 \<Rightarrow> x1) in
   let st2 = prj2 (aug st) in
   let st1 = (case (deaug st2a) of Some x1 \<Rightarrow> x1) in
   
   bsup st1 (bsup st2 b)))"

end

print_locale MergeSem

end