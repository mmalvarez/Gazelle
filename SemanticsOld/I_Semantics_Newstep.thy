theory I_Semantics_Newstep imports "Gensyn_Semantics_Newstep" "../Syntax/Syn_I"
begin

(* Do we interpret or extend?
sublocale? 
use rewrites to change base_sem and rec_sem?
should this have trivial control flow, or allow insts
to do weird control flow things?
*)
(* Do we want both a regular and exec? i think so *)

(* options

(idea: is generic gensym_sem the "top" or "bottom"
element of our "lattice" of semantics?)

1. take just i_sem. do semantics for gensyms extending
instruction sym, but return None on unknown ones
- rely on being "downcalled" from higher levels

2. take a gensym semantics and override it in the
case of instructions
- "upcall" in the case of unknown instructions
- what if higher levels impose restrictions on
instructions?
  - could use explicit subtyping...
eed

*)

(* want "a gensyn that includes at least a sym_i" *)

(* this doesn't work, need gensyn tree *)

locale I_Semantics = 
  fixes i_sem :: "'i \<Rightarrow> 'mstate => 'mstate \<Rightarrow> bool"

begin

(* 2 approaches.
   approach 1: i_semantics builds a gensym semantics "from nothing"
   if instruction execution fails, we halt.

   approach 2: i_semantics takes an existing gensym semantics
   and "adds in" instructions.

   approach 1 is better because it allows the _user_ to later define
   approach 2 style semantics (mixins)
*)

(* question: dealing with interactions between global parameters
   and other things?
  sized insts?
*)

(* we can probably generalize this, by using unknown type parameters
  for everything, but this may not be necessary *)

(* we can also probably generalize over result/error types if we really
   want *)
(* TODO make sure this is a general enough type  in terms of
where quantifiers are*)

(* we need some way of selecting the next instruction
this depends on the kind of parent node we have
do we need another extension point to allow for this?. *)

inductive i_base_sem :: "(('i, 'xb, 'xa) syn_i, 'r, 'g) gensyn \<Rightarrow>
                   'g \<Rightarrow> ('i, 'xb, 'xa) syn_i \<Rightarrow> childpath \<Rightarrow> 'mstate \<Rightarrow>
                   childpath option \<Rightarrow> 'mstate \<Rightarrow> bool" where
"i_sem i m m' \<Longrightarrow> i_base_sem s g (LInst i) cp m (Some cp) m'"

(* key thing here: we are not actually descending into recursive nodes
as this would require a recursive semantics; we use nosem *)
interpretation I_Semantics : Gensym_Semantics
  i_base_sem nosem_rec_sem
  done

end

(*******************

This is _almost_ what we want.
However, the problem now is that we don't have an extension point to
allow for later syntactic/semantic extensions to change how next
nodes are calculated.

********************)

end