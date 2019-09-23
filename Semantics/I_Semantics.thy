theory I_Semantics imports "Gensyn_Semantics" "../Syntax/Syn_I"
begin

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

consts Length :: "'a \<Rightarrow> nat"

overloading
  Length0 \<equiv> "Length :: unit \<Rightarrow> nat"
begin

fun Length0 :: "unit \<Rightarrow> nat" where
  "Length0 () = 0"

end

value [nbe] "Length () :: nat"



(*consts LInst :: "'full itself \<Rightarrow> 'i \<Rightarrow> 'xp \<Rightarrow> ('i, 'xp, 'a) mpack"*)
(*
consts LInst :: "('w, 'x, 'y) mpack itself \<Rightarrow> 'i \<Rightarrow> 'xp \<Rightarrow> ('w, 'x, 'y) mpack"

overloading
  LInst0 \<equiv> "LInst :: ('i, 'xp, 'a) mpack itself \<Rightarrow> 'i \<Rightarrow> 'xp \<Rightarrow> ('i, 'xp, 'a) mpack"
begin

fun LInst0 :: "('i, 'xp, 'a) mpack itself \<Rightarrow> 'i \<Rightarrow> 'xp \<Rightarrow> ('i, 'xp, 'a) mpack" where
  "LInst0 tf i xp = (Inl i, xp) "
end 



lemmas [code] = LInst0.simps


value "LInst () () :: (unit, unit, unit) syn_i"

*)

(*
declare [[coercion_enabled]]

fun natid :: "nat \<Rightarrow> nat" where
"natid x = x"

fun swap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a + 'b) \<Rightarrow> ('b + 'a)"
  where
"swap f g (Inl x) = Inr x"
| "swap f g (Inr x) = Inl x"

declare [[coercion_map swap]]
*)

value \<open>STR''abc'' :: string\<close>


consts GetLen :: "'a \<Rightarrow> nat"
overloading
  GetLen0 \<equiv> "GetLen :: unit \<Rightarrow> nat"
begin

fun GetLen0 :: "unit \<Rightarrow> nat" where
  "GetLen0 () = 0"

end

declare GetLen0.simps [simp]

value [nbe] "GetLen () :: nat"

consts GetNat :: "'a \<Rightarrow> nat"
overloading
  Get0 \<equiv> "GetNat :: nat \<Rightarrow> nat"
begin

fun Get0 :: "nat \<Rightarrow> nat" where
  "Get0 n = n"

end

lemma testt : "GetNat (1 :: nat) = 1"
  apply(simp)
  done

value [nbe] "case (GetNat (0 :: nat) :: nat) of 0 \<Rightarrow> False | _ \<Rightarrow> True"

(*

value "(\<lambda> (x, y) . x) (2 :: nat, undefined :: nat)"

value "fst ((3, undefined) :: nat * nat)"
*)
locale I_Semantics_Sig =
  fixes xr :: "'rs itself"
  fixes ms :: "'mstate itself"
  fixes i_sem :: "'i \<Rightarrow> 'mstate => 'mstate \<Rightarrow> bool"


locale I_Semantics = I_Semantics_Sig 
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

print_context

inductive x_sem_i :: "  ('c, 'xp, 'xs) syn_i \<Rightarrow> 
                         'b \<Rightarrow>
                         'b \<Rightarrow>
                          childpath \<Rightarrow> ('c, 'xp, 'xs) syn_i gensyn \<Rightarrow> 
                          ('a) gs_result \<Rightarrow> bool" where
"i_sem i m m' \<Longrightarrow> x_sem_i (LInst i xp) m m' cp t GRUnhandled"

(* We still need a way to handle different kinds of gs results *)

(* key thing here: we are not actually descending into recursive nodes
as this would require a recursive semantics; we use nosem *)


end


locale Gensyn_Semantics_I = I_Semantics 

(* this seems like a bad idea unless we can make things work out
   when we combine together multiple locales *)
(*
sublocale Gensyn_Semantics_I \<subseteq> Gensyn_Semantics_Base_Sig
  where base_sem = i_base_sem
  done
*)


(* testing out sublocales *)
(* i think the problem with this is that we cannot further
sub-locale-ize I_Semantics *)

(* test - small programming language for arithmetic *)
datatype calc =
  AccAdd nat
  | AccSub nat
  | AccReset

fun calc_sem :: "calc \<Rightarrow> nat \<Rightarrow> nat" where
"calc_sem (AccAdd x) n = x + n"
| "calc_sem (AccSub x) n = x - n"
| "calc_sem (AccReset) _ = 42"

inductive calc_semb :: "calc \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"\<And> c n n' . calc_sem c n = n' \<Longrightarrow> calc_semb c n n'"

interpretation I_Semantics_Calc :
  I_Semantics "TYPE(unit)" _ calc_semb
  done


interpretation Gensyn_Semantics_Calc :
  Gensyn_Semantics "TYPE(unit)" _ I_Semantics_Calc.x_sem_i
  done


locale Gensyn_Base_Oneshot =
  fixes ms :: "'mstate itself"
  fixes x_sem :: "'x \<Rightarrow>
                           'mstate \<Rightarrow>
                           'mstate \<Rightarrow>
                           childpath \<Rightarrow> ('x) gensyn \<Rightarrow> 
                           ('xrs) gs_result \<Rightarrow> bool"
begin

inductive x_sem_oneshot :: "'x \<Rightarrow> 
                           'mstate \<Rightarrow>
                           'mstate \<Rightarrow>
                           childpath \<Rightarrow> ('x) gensyn \<Rightarrow> 
                           ('xrs) gs_result \<Rightarrow> bool"
  where
"x_sem x m m' cp t GRUnhandled \<Longrightarrow>
 x_sem_oneshot x m m' cp t GRDone"

| "x_sem x m m' cp t res \<Longrightarrow>
  x_sem_oneshot x m m' cp t res"

end

locale I_Semantics_Oneshot = I_Semantics


sublocale I_Semantics_Oneshot \<subseteq> Gensyn_Base_Oneshot
  where x_sem = x_sem_i
  done
  

sublocale I_Semantics_Oneshot \<subseteq> Gensyn_Semantics
  where x_sem = x_sem_oneshot
  done

interpretation Gensyn_Semantics_Calc_Oneshot :
  I_Semantics_Oneshot "TYPE(unit)" _ calc_semb
  done

term Gensyn_Semantics_Calc.gensyn_sem

lemma testout1 : "Gensyn_Semantics_Calc_Oneshot.gensyn_sem (G (LInst AccReset ()) []) [] 0 42"
  apply(rule Gensyn_Semantics_Calc_Oneshot.gensyn_sem.intros) apply(auto)
  apply(rule Gensyn_Base_Oneshot.x_sem_oneshot.intros)
  apply(rule I_Semantics.x_sem_i.intros)
  apply(rule calc_semb.intros)
  apply(auto)
  done

end