(* Kaleidoscope - a version of the "ViewRef" optic for use with Mergeables. *)

theory Kalei imports "../Mergeable/Mergeable"
begin

(* idea - kaleidoscope is 2 mergeables, plus
- injection functions for each (total but not guaratneed to be valid)
- projection functions for each

laws:
inj (prj x) \<le> x
prj (inj x) \<ge> x
orderings on types compatible
bsups compatible?
  
*)        

end