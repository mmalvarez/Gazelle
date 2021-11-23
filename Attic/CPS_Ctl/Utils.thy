theory Utils
  imports 
"../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable" "../Mergeable/MergeableInstances"
          "../Lifting/LiftUtils" "../Lifting/LiftInstances"
          "../Lifting/AutoLift"
begin
(* Some miscellaneous (especially "adapter" code)
   for use with the examples that didn't have a clear place elsewhere
*)

instantiation gensyn :: (Bogus) Bogus begin
definition gensyn_bogus :
"bogus = G bogus []"
instance proof qed
end
end