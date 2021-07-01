theory MergeableFunStrong
imports Mono "../Mergeable/Mergeable"
begin

(* hmm. we need monotonicity... *)
instantiation "fun" :: (Pord_Weak, Pord_Weak) Pord_Weak
begin

definition fun_pleq :
"((f1 :: (('a :: Pord_Weak) \<Rightarrow> ('b :: Pord_Weak))) <[ f2) \<equiv>
 (\<forall> x1 x2 . x1 <[ x2 \<longrightarrow> f1 x1 <[ f2 x2)"

instance proof
  fix f1 :: "('a \<Rightarrow> 'b)"

  show "f1 <[ f1" unfolding fun_pleq

end