theory CPS_Experiment
  imports Main

begin

(* So, a straightforward CPS doesn't quite work because we don't know exactly how we are supposed to
   relate the sub-languages' incomplete pictures of syntax tree contents to the real tree

one approach: reify so all sub-languages can see real tree

another approach: find some kind of "sliding" representation over real tree (?)
  - that is, changed root
  - however, we do need to make sure we can still have arbitrary continuations
*)

end