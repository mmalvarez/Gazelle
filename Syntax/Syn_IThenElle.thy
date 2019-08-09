theory Syn_IThenElle imports Syn_I Syn_Elle
begin

(* can we have a plugin for filling in type parameters
in sequential order? this would be nice *)

(*

we need to establish a convention for what order to list the
extension-point parameters in.

i think the innermost things should have their extension
points listed first

however, we might also want to follow the convention that
outermost xb and xa come last...

new convention: number extension points
in the order in which they appear (left to right).

i think this convention would actually be confusing though.

*)

(* this is the "flattened" version, so is to be preferred *)
type_synonym ('lix, 'llx, 'ljx, 'ljix, 'x0, 'x1, 'x2)
  syn_i_of_elle =
  "('lix, 'x0, ('llx, 'ljx, 'ljix, 'x1, 'x2) syn_elle) syn_i"

type_synonym ('lix, 'llx, 'ljx, 'ljix, 'x0, 'x1, 'x2)
  syn_elle_of_i =
  "('llx, 'ljx, 'ljix, ('lix, 'x0, 'x1) syn_i, 'x2) syn_elle"  

fun syn_i_elle_flatten ::
"('lix, 'llx, 'ljx, 'ljix, 'x0, 'x1, 'x2)
    syn_elle_of_i \<Rightarrow>
   ('lix, 'llx, 'ljx, 'ljix, 'x0, 'x1, 'x2)
    syn_i_of_elle"
where
"syn_i_elle_flatten x = 
  reassoc3_sum x"

fun syn_i_elle_deflatten ::
  "('lix, 'llx, 'ljx, 'ljix, 'x0, 'x1, 'x2)
    syn_i_of_elle \<Rightarrow>
   ('lix, 'llx, 'ljx, 'ljix, 'x0, 'x1, 'x2)
    syn_elle_of_i" where
"syn_i_elle_deflatten x =
  deassoc3_sum x
   "

(* note: in general smap may be needed here,
for more complex representations. in this case, in the
deflattened version, the nested representation shows up
in the first slot, so this is not needed*)

(* next up: experiment with writing functions over these representations *)

end