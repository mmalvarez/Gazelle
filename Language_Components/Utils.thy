theory Utils
  imports 
  "../Syntax/Gensyn" "../Syntax/Gensyn_Descend" "../Mergeable/Mergeable" 
  "../Mergeable/Mergeable_Instances"
  "../Lifter/Lifter" "../Lifter/Lifter_Instances"
begin

(* Some miscellaneous code for use in developing language components
   that didn't have a clear place elsewhere
*)

instantiation gensyn :: (Bogus) Bogus begin
definition gensyn_bogus :
"bogus = G bogus []"
instance proof qed
end
end