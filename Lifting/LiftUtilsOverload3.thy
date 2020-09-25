theory LiftUtilsOverload2
  imports "LiftUtils" "LiftInstances" "HOL-Library.Adhoc_Overloading"
begin

datatype 'a wrap1 = 
  W1 'a

datatype 'a wrap2 = 
  W2 'a

datatype 'a wrap3 =
  W3 'a

consts default_lifting1 :: 
"'a itself \<Rightarrow> 'c itself \<Rightarrow> ('a, 'b, 'c) lifting wrap1"

consts default_lifting2 :: 
"'a itself \<Rightarrow> 'c itself \<Rightarrow> ('a, 'b, 'c) lifting wrap2"

consts default_lifting3 :: 
"'a itself \<Rightarrow> 'c itself \<Rightarrow> ('a, 'b, 'c) lifting wrap3"

consts default_lifting :: 
"('a, 'b, 'c) lifting"


adhoc_overloading default_lifting1 "\<lambda> a b . W1 id_l"


adhoc_overloading default_lifting2
"\<lambda> a c . W2 id_l"
"\<lambda> (a :: 'a itself) (c :: 'b md_triv itself) .
   W2 (case_wrap1 triv_l (default_lifting1 a (TYPE('b))))"
"\<lambda> (a :: 'a itself) (c :: 'b option itself) .
   W2 (case_wrap1 option_l (default_lifting1 a (TYPE('b))))"

adhoc_overloading default_lifting3
"\<lambda> a c . W3 id_l"
"\<lambda> (a :: 'a itself) (c :: 'b md_triv itself) .
   W3 (case_wrap2 triv_l (default_lifting2 a (TYPE('b))))"
"\<lambda> (a :: 'a itself) (c :: 'b option itself) .
   W3 (case_wrap2 option_l (default_lifting2 a (TYPE('b))))"

definition xl ::
"('a itself \<Rightarrow> 'c itself \<Rightarrow> ('a, 'b, 'c) lifting wrap3) \<Rightarrow>
('a, 'b, 'c) lifting" where
"xl f =
  case_wrap3 id (f (TYPE('a)) (TYPE('c)))"

(* ok - so this seems to be less smart about figuring out how to thread through constructors
than typeclasses are. 
one approach would be to stratify but this only gets us so far
*)
declare [[show_variants]]

term "(\<lambda> (a :: 'a itself) (c :: 'b option itself) .
   W3 (case_wrap2 option_l (default_lifting2 a (TYPE('b))))) (TYPE(unit)) (TYPE(nat option md_triv))"

term "default_lifting3 (TYPE(unit)) (TYPE(nat option md_triv))::
(unit, nat, nat option md_triv) lifting wrap3"

end