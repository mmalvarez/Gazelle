theory Auto_Lifter_Datatypes imports Lifter

(*
 * Datatypes used in Auto_Lifter - essentially these are a way
 * to reify lifting structures into schema
 *)

begin

(* Define several types representing different kinds of schema structure and lifting. *)
datatype ('a, 'b) sprod = 
  SP "'a" "'b"

(* x is syntax (needed for priority functions) *)
datatype ('x, 'a) sprio =
  SPR "('x \<Rightarrow> nat)" "('x \<Rightarrow> nat \<Rightarrow> nat)" "'a"

(* x is syntax, k is key *)
datatype 'a soption =
  SO "'a"

datatype ('x, 'k, 'a) soalist =
  SL "'x \<Rightarrow> ('k :: linorder)" "'a"

datatype ('x, 'k, 'a) sroalist =
  SRL "'x \<Rightarrow> ('k :: linorder) option" "'a"

datatype ('x, 'da, 'c, 'a) sfan =
  SFAN "'x \<Rightarrow> 'da \<Rightarrow> 'c" "'a"

(* In schemas supplied as input to the auto-lifter, a "raw" name (e.g. NA)
 * is assumed to be the trivial lifting, and to be "terminal" (that is, this name represents
 * some piece of trivially lifted data and no further lifting should happen here.)
 *
 * However, sometimes this will actually correspond to an existing lifting that needs
 * to be included as part of the larger lifting. In this case we wrap with SID *)
datatype 'a sid =
  SID "'a"

(* convenience function for injecting existing liftings *)
datatype ('x, 'da, 'db, 'f, 'a) sinject =
  SINJ "('x, 'da, 'db, 'f) lifting" "'a"

(* dealing with the situation where we need to merge multiple (LHS) fields
   into one (RHS) field. this is very important in making the automation convenient! *)

datatype ('a, 'b) smerge =
  SM "'a" "'b"


end

