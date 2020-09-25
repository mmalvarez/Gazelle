theory Alt_Sym
  imports Syntax_Utils
begin

(* DEPRECATED EXPERIMENT
   see Syntax_Utils.thy for current version *)

(* implementation of syntax, not using records *)
(* we might also consider doing an implementation that uses
nested records so that extension isn't horrible *)

(*
another idea: can we use "intermediate" fields
(plus discriminators) to allow for more flexible
extension (e.g. adding language features
"earlier" in the stack)?
 *)

fun reassoc_prod ::
  "(('a * 'b) * 'c) \<Rightarrow> ('a * 'b * 'c)" where
"reassoc_prod ((a, b), c) = (a, b, c)"

fun deassoc_prod ::
  "('a * 'b * 'c) \<Rightarrow> (('a * 'b) * 'c)" where
"deassoc_prod (a, b, c) = ((a, b), c)"

fun reassoc3_prod ::
  "(('a * 'b * 'c) * 'd) \<Rightarrow> ('a * 'b * 'c * 'd)" where
"reassoc3_prod p =
  (case reassoc_prod p of
    (a, bcd) \<Rightarrow> (a, reassoc_prod bcd))"

fun deassoc3_prod ::
  "('a * 'b * 'c * 'd) \<Rightarrow> (('a * 'b * 'c) * 'd)" where
"deassoc3_prod p =
  (case p of
    (a, bcd) \<Rightarrow> 
    (case deassoc_prod bcd of
       (bc, d) \<Rightarrow> ((a, bc), d)))"

fun reassoc4_prod ::
  "(('a * 'b * 'c * 'd) * 'e) \<Rightarrow> ('a * 'b * 'c * 'd * 'e)" where
"reassoc4_prod p =
  (case reassoc_prod p of
    (a, bcde) \<Rightarrow> (a, reassoc3_prod bcde))"

fun deassoc4_prod ::
"('a * 'b * 'c * 'd * 'e) \<Rightarrow> (('a * 'b * 'c * 'd) * 'e)" where
"deassoc4_prod p =
  (case p of
    (a, bcde) \<Rightarrow>
    (case deassoc3_prod bcde of
      (bcd, e) \<Rightarrow> ((a, bcd), e)))"

fun reassoc_sum ::
  "(('a + 'b) + 'c) \<Rightarrow> ('a + 'b + 'c)" where
"reassoc_sum (Inl (Inl a)) = Inl a"
| "reassoc_sum (Inl (Inr b)) = Inr (Inl b)"
| "reassoc_sum (Inr c) = Inr (Inr c)"

fun deassoc_sum ::
  "('a + 'b + 'c) \<Rightarrow> (('a + 'b) + 'c)" where
"deassoc_sum (Inl a) = Inl (Inl a)"
| "deassoc_sum (Inr (Inl b)) = Inl (Inr b)"
| "deassoc_sum (Inr (Inr c)) = Inr c"

fun reassoc3_sum ::
  "(('a + 'b + 'c) + 'd) \<Rightarrow> ('a + 'b + 'c + 'd)" where
"reassoc3_sum s =
  (case reassoc_sum s of
    Inl a \<Rightarrow> Inl a
  | Inr bcd \<Rightarrow> Inr (reassoc_sum bcd))"

fun deassoc3_sum ::
  "('a + 'b + 'c + 'd) \<Rightarrow> (('a + 'b + 'c) + 'd)" where
"deassoc3_sum s =
  (case s of
    Inl a \<Rightarrow> Inl (Inl a)
  | Inr bcd \<Rightarrow> 
    (case deassoc_sum bcd of
        Inl bc \<Rightarrow> Inl (Inr bc)
      | Inr d \<Rightarrow> Inr d))"

fun reassoc4_sum ::
  "(('a + 'b + 'c + 'd) + 'e) \<Rightarrow> ('a + 'b + 'c + 'd + 'e)" where
"reassoc4_sum s =
  (case reassoc_sum s of
    Inl a \<Rightarrow> Inl a
  | Inr bcd \<Rightarrow> Inr (reassoc3_sum bcd))"

fun deassoc4_sum ::
  "('a + 'b + 'c + 'd + 'e) \<Rightarrow>
  (('a + 'b + 'c + 'd) + 'e)" where
"deassoc4_sum s =
  (case s of
    Inl a \<Rightarrow> Inl (Inl a)
  | Inr bcde \<Rightarrow> (case deassoc3_sum bcde of
      Inl bcd \<Rightarrow> Inl (Inr bcd)
    | Inr e \<Rightarrow> Inr e))"

(* writing associators becomes formulaic *)

(* unit functions *)
fun unitl :: "(unit * 'a) \<Rightarrow> 'a" where
"unitl (_, a) = a"

fun deunitl :: "'a \<Rightarrow> (unit * 'a)" where
"deunitl a = ((), a)"

fun unitr :: "('a * unit) \<Rightarrow> 'a" where
"unitr (a, _) = a"

fun deunitr :: "'a \<Rightarrow> ('a * unit)" where
"deunitr a = (a, ())"

(* clone of unit,
used instead of the empty type which we can't
have in Isabelle. *)
datatype Empty = emp

(* using these we can pretend that empty
is the unit for sums, so long as we never
actually construct one. *)

fun emp_unitl :: "Empty + 'a \<Rightarrow> 'a" where
"emp_unitl (Inl _) = undefined"
| "emp_unitl (Inr a) = a"

fun emp_deunitl :: "'a \<Rightarrow> Empty + 'a" where
"emp_deunitl a = Inr a"

fun emp_unitr :: "'a + Empty \<Rightarrow> 'a" where
"emp_unitr (Inl a) = a"
| "emp_unitr (Inr _) = undefined"

fun emp_deunitr :: "'a \<Rightarrow> 'a + Empty" where
"emp_deunitr a = Inl a"

fun empE :: "Empty \<Rightarrow> 'a" where
"empE _ = undefined"

(* now we have our (re) definition of
instruction sym *)

type_synonym ('i, 'xb, 'xa) sym_i = "('xb + 'i + 'xa)"

(*
fun sget_inst :: "('i, 'xb, 'xa) sym_i \<Rightarrow> 'i option" where
"sget_inst (Inl i) = Some i"
| "sget_inst _ = None"
*)

(*
'x \<Rightarrow> 'o, or just 'x?
return a different type?
options?
 *)
type_synonym ('i, 'xb, 'xa, 'o) sym_i_disc =
  "(('xb \<Rightarrow> 'o) * ('i \<Rightarrow> 'o) * ('xa \<Rightarrow> 'o))"

type_synonym ('i, 'xb, 'xa, 'o) sym_i_disc' =
  "('xb + 'i + 'xa) \<Rightarrow> 'o"

(* treating extension points specially
problem: now we need to pack extension points in with
descriptions of how we get them to 'o
'xb \<Rightarrow> 'xbe \<Rightarrow> 'o (?)
 *)
type_synonym ('i, 'xb, 'xa, 'o) sym_i_disc'2 =
  "(('xb) * ('i \<Rightarrow> 'o) * ('xa))"

type_synonym ('i, 'xb, 'xbe, 'xa, 'xae, 'o) sym_i_disc'3 =
  "(('xb \<Rightarrow> 'xbe \<Rightarrow> 'o) * ('i \<Rightarrow> 'o) * ('xa \<Rightarrow> 'xae \<Rightarrow> 'o))"


(* can we generalize this discriminator pattern? *)

fun disc ::
  "('a + 'b) \<Rightarrow> (('a \<Rightarrow> 'o) * ('b \<Rightarrow> 'o)) \<Rightarrow> 'o" where
"disc (Inl a) (fa, _) = fa a"
| "disc (Inr b) (_, fb) = fb b"

fun disc3 ::
  "('a + 'b + 'c) \<Rightarrow> (('a \<Rightarrow> 'o) * ('b \<Rightarrow> 'o) * ('c \<Rightarrow> 'o)) \<Rightarrow> 'o" where
"disc3 (Inl a) (fa, _) = fa a"
| "disc3 (Inr bc) (_, fbc) = disc bc fbc"

fun dmerge :: "(('a \<Rightarrow> 'o) * ('b \<Rightarrow> 'o)) \<Rightarrow> ('a + 'b) \<Rightarrow> 'o"
  where
"dmerge (fa, _) (Inl a) = fa a"
| "dmerge (_, fb) (Inr b) = fb b"

fun dmerge3 :: 
  "(('a \<Rightarrow> 'o) * ('b \<Rightarrow> 'o) * ('c \<Rightarrow> 'o)) \<Rightarrow>
  ('a + 'b + 'c) \<Rightarrow> 'o" where
"dmerge3 (fa, _) (Inl a) = fa a"
| "dmerge3 (_, fb) (Inr bc) = dmerge fb bc"

fun dmerge4 :: 
  "(('a \<Rightarrow> 'o) * ('b \<Rightarrow> 'o) * ('c \<Rightarrow> 'o) * ('d \<Rightarrow> 'o)) \<Rightarrow>
  ('a + 'b + 'c + 'd) \<Rightarrow> 'o" where
"dmerge4 (fa, _) (Inl a) = fa a"
| "dmerge4 (_, fb) (Inr bc) = dmerge3 fb bc"

fun dmerge5 :: 
  "(('a \<Rightarrow> 'o) * ('b \<Rightarrow> 'o) * ('c \<Rightarrow> 'o) * ('d \<Rightarrow> 'o) * ('e \<Rightarrow> 'o)) \<Rightarrow>
  ('a + 'b + 'c + 'd + 'e) \<Rightarrow> 'o" where
"dmerge5 (fa, _) (Inl a) = fa a"
| "dmerge5 (_, fb) (Inr bc) = dmerge4 fb bc"

(* failed experiment in using coercion_map *)
(*
declare [[coercion_enabled]]

fun sillyext :: "'a \<Rightarrow> ('a * unit)" where
"sillyext a = (a, ())"

datatype 'a wrap =
  DoW "'a"

fun unwrap :: "'a wrap \<Rightarrow> 'a" where
"unwrap (DoW a) = a"

fun unwrap2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a wrap \<Rightarrow> 'b wrap" where
"unwrap2 f (DoW a) = DoW (f a)"


declare [[coercion_map unwrap2]]

datatype ('a, 'b) myprod =
  DoP "'a" "'b"

(*declare [[coercion "unwrap :: (unit, unit) myprod wrap \<Rightarrow> (unit, unit) myprod"]]*)

fun reassc :: "(('a, 'b) myprod, 'c) myprod \<Rightarrow> ('a, ('b, 'c)myprod )myprod wrap" where
"reassc (DoP (DoP a b) c) = DoW (DoP a (DoP b c))"

declare [[coercion reassc]]
declare [[coercion "unwrap :: unit wrap \<Rightarrow> unit"]]

fun third :: "('a, ('b, 'c) myprod) myprod \<Rightarrow> 'c" where
"third (DoP _ (DoP _ c)) = c"

fun myco1 :: "(unit, unit) myprod \<Rightarrow> unit wrap" where
"myco1 _ = DoW ()"

declare [[coercion myco1]]

fun myco2 :: "unit \<Rightarrow> (unit, unit) myprod wrap" where
"myco2 _ = DoW ( DoP () ())"

declare [[coercion myco2]]

value "third (unwrap (reassc ((DoP (DoP () ()) ()))))"

fun reasscy :: "(('a * 'b) \<Rightarrow> 'a wrap) \<Rightarrow> ('c \<Rightarrow> ('b * 'c) wrap) \<Rightarrow> (('a * 'b) * 'c) \<Rightarrow> ('a wrap * ('b * 'c) wrap)" where
"reasscy fab fc x =
  (DoW (fst (fst x)), DoW (snd (fst x), (snd x)))"

fun reassc2 :: "((unit * unit) \<Rightarrow> unit wrap) \<Rightarrow> (unit \<Rightarrow> (unit * unit) wrap) \<Rightarrow> ((unit * unit) * unit) \<Rightarrow>
  (unit wrap * (unit * unit) wrap)" where
"reassc2 fab fc x =
 (DoW (fst (fst x)), DoW (snd (fst x), (snd x)))"


fun reassc2' :: "((unit * unit) * unit) \<Rightarrow>
  (unit wrap * (unit * unit) wrap)" where
"reassc2' x =
 (DoW (fst (fst x)), DoW (snd (fst x), (snd x)))"


declare [[coercion_map reassc2]]

fun third :: "(unit wrap * (unit * unit) wrap) \<Rightarrow> unit" where
"third (a, DoW (b, c)) = c"

fun wildcard :: "'a \<Rightarrow> 'b" where
"wildcard _ = undefined"

(*
fun boolco1 :: "((bool * nat)) \<Rightarrow> bool" where
"boolco1 _ = True"

declare [[coercion boolco1]]
*)

  

fun myfst :: "(unit * unit) \<Rightarrow> unit wrap" where
"myfst x = DoW ()"

declare [[coercion myfst]]

fun co1 :: "(unit) \<Rightarrow> (unit * unit) wrap" where
"co1 x = DoW ((), ())"

declare [[coercion co1]]

value "third ((((), ()), ()))"

fun boolco2 :: "unit \<Rightarrow> (nat * unit)" where
"boolco2 b = (undefined, undefined)"
*)
fun tnth1h :: "('a * 'b) \<Rightarrow> 'a" where
"tnth1h (a, b) = a"

fun tnth1t :: "('a * 'b) \<Rightarrow> 'b" where
"tnth1t (a, b) = b"

fun tnth2h :: "('a * 'b * 'c) \<Rightarrow> 'b" where
"tnth2h x = tnth1h (tnth1t x)"

fun tnth2t :: "('a * 'b * 'c) \<Rightarrow> 'c" where
"tnth2t x = tnth1t (tnth1t x)"

fun tnth3h :: "('a * 'b * 'c * 'd) \<Rightarrow> 'c" where
"tnth3h x = tnth1h (tnth2t x)"

fun tnth3t :: "('a * 'b * 'c * 'd) \<Rightarrow> 'd" where
"tnth3t x = tnth1t (tnth2t x)"

fun tnth4h :: "('a * 'b * 'c * 'd * 'e) \<Rightarrow> 'd" where
"tnth4h x = tnth1h (tnth3t x)"

fun tnth4t :: "('a * 'b * 'c * 'd * 'e) \<Rightarrow> 'e" where
"tnth4t x = tnth1t (tnth3t x)"

fun tnth5h :: "('a * 'b * 'c * 'd * 'e * 'f) \<Rightarrow> 'e" where
"tnth5h x = tnth1h (tnth4t x)"

fun tnth5t :: "('a * 'b * 'c * 'd * 'e * 'f) \<Rightarrow> 'f" where
"tnth5t x = tnth1t (tnth4t x)"

(* these maps probably aren't really what we want. *)
fun tmap1h ::
  "('a \<Rightarrow> 'o) \<Rightarrow> ('a * 'b) \<Rightarrow> ('o * 'b)" where
"tmap1h f (a, b) = (f a, b)"

fun tmap1t ::
  "('b \<Rightarrow> 'o) \<Rightarrow> ('a * 'b) \<Rightarrow> ('a * 'o)" where
"tmap1t f (a, b) = (a, f b)"

fun tmap2h ::
  "('b \<Rightarrow> 'o) \<Rightarrow> ('a * 'b * 'c) \<Rightarrow> ('a * 'o * 'c)" where
"tmap2h f (a, b) = (a, tmap1h f b)"

fun tmap2t ::
  "('c \<Rightarrow> 'o) \<Rightarrow> ('a * 'b * 'c) \<Rightarrow> ('a * 'b * 'o)" where
"tmap2t f (a, b) = (a, tmap1t f b)"

fun tmap3h ::
  "('c \<Rightarrow> 'o) \<Rightarrow> ('a * 'b * 'c * 'd) \<Rightarrow> ('a * 'b * 'o * 'd)" where
"tmap3h f (a, b) = (a, tmap2h f b)"

fun tmap3t ::
  "('d \<Rightarrow> 'o) \<Rightarrow> ('a * 'b * 'c * 'd) \<Rightarrow> ('a * 'b * 'c * 'o)" where
"tmap3t f (a, b) = (a, tmap2t f b)"

fun tmap4h ::
  "('d \<Rightarrow> 'o) \<Rightarrow> ('a * 'b * 'c * 'd * 'e) \<Rightarrow> ('a * 'b * 'c * 'o * 'e)" where
"tmap4h f (a, b) = (a, tmap3h f b)"

fun tmap4t ::
  "('e \<Rightarrow> 'o) \<Rightarrow> ('a * 'b * 'c * 'd * 'e) \<Rightarrow> ('a * 'b * 'c * 'd * 'o)" where
"tmap4t f (a, b) = (a, tmap3t f b)"

fun tmap5h ::
  "('e \<Rightarrow> 'o) \<Rightarrow> ('a * 'b * 'c * 'd * 'e * 'f) \<Rightarrow> ('a * 'b * 'c * 'd * 'o * 'f)" where
"tmap5h f (a, b) = (a, tmap4h f b)"

fun tmap5t ::
  "('f \<Rightarrow> 'o) \<Rightarrow> ('a * 'b * 'c * 'd * 'e * 'f) \<Rightarrow> ('a * 'b * 'c * 'd * 'e * 'o)" where
"tmap5t f (a, b) = (a, tmap4t f b)"


(* writing more of these is formulaic *)

fun sym_i_cases_gen ::
"('i, 'xb, 'xa) sym_i \<Rightarrow> ('i, 'xb, 'xa, 'o) sym_i_disc \<Rightarrow> 'o" where
"sym_i_cases_gen s d = disc3 s d"


fun sym_i_cases_gen' ::
"('i, 'xb, 'xa) sym_i \<Rightarrow> ('i, 'xb, 'xa, 'o) sym_i_disc' \<Rightarrow> 'o" where
"sym_i_cases_gen' s d = d s"

fun sym_i_cases_gen'2 ::
"('i, 'xb, 'xa) sym_i \<Rightarrow> ('i, ('xb \<Rightarrow> 'o), ('xa \<Rightarrow> 'o), 'o) sym_i_disc'2 \<Rightarrow> 'o" where
"sym_i_cases_gen'2 s d =
  disc3 s d"

(* now we need to throw around xbe and xae manually...
however, maybe this is OK. *)
(*
fun sym_i_cases_gen'3 ::
"('i, 'xb, 'xa) sym_i \<Rightarrow> ('i, 'xb, 'xbe, 'xa, 'xae, 'o) sym_i_disc'3 \<Rightarrow> 'xbe \<Rightarrow> 'xae \<Rightarrow> 'o" where
"sym_i_cases_gen'3 s d = d s"
*)
(*
fun sym_i_cases ::
"('i, 'x) sym_i \<Rightarrow> ('i, 'o, 'x) sym_i_disc \<Rightarrow> 'o option" where
"sym_i_cases s d = 
*)

definition LInst :: "'i \<Rightarrow> ('i, 'xb, 'xa) sym_i" where
"LInst i = Inr (Inl i)"


(* now on to Elle *)

(* question: use nested sums, or just straight sum? *)
(* i think we want to nest so that we can handle things at this level correctly *)

type_synonym ('lix, 'ljx, 'ljix, 'xb, 'xa) sym_elle_new =
  "'xb + 'lix + 'ljx + 'ljix + 'xa "

type_synonym ('lix, 'ljx, 'ljix, 'xb, 'xa, 'o) sym_elle_disc_new =
  "('xb \<Rightarrow> 'o) * ('lix \<Rightarrow> 'o) * ('ljx \<Rightarrow> 'o) * ('ljix \<Rightarrow> 'o) * ('xa \<Rightarrow> 'o)"

type_synonym ('lix, 'ljx, 'ljix, 'xb, 'xa, 'o) sym_elle_disc_new' =
  "('xb + 'lix + 'ljx + 'ljix + 'xa) \<Rightarrow> 'o"

(* OK, now we need to figure out how to use xb and xa correctly here *)
type_synonym ('lix, 'ljx, 'ljix, 'xb, 'xa, 'o) sym_elle_disc_new'2 =
  "('xb) * ('lix \<Rightarrow> 'o) * ('ljx \<Rightarrow> 'o) * ('ljix \<Rightarrow> 'o) * ('xa)"

(* where do we insert extension points?
we need to do it inside the sym_elle_new so as not to disturb things *)
type_synonym ('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa) sym_elle =
  "('i, 'xb1, ('lix, 'ljx, 'ljix, 'xb2, 'xa) sym_elle_new) sym_i"

type_synonym ('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa, 'o) sym_elle_disc =
  "('i, 'xb1, ('lix, 'ljx, 'ljix, 'xb2, 'xa, 'o) sym_elle_disc_new,
    'o) sym_i_disc"

type_synonym ('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa, 'o) sym_elle_disc' =
  "('i, 'xb1, ('lix, 'ljx, 'ljix, 'xb2, 'xa, 'o) sym_elle_disc_new',
    'o) sym_i_disc'"

type_synonym ('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa, 'o) sym_elle_disc'' =
"('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa) sym_elle \<Rightarrow> 'o"

type_synonym ('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa, 'o) sym_elle_disc'2 =
  "('i, 'xb1, ('lix, 'ljx, 'ljix, 'xb2, 'xa, 'o) sym_elle_disc_new'2,
    'o) sym_i_disc'2"

typ "('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa, 'o) sym_elle_disc'2"

(* i might need to do something interesting here -
perhaps normalize? or merge?
or, change second argument to disc3
either need a normalize, or need a different definition for
disc_new/disc*)
(*
fun sym_elle_cases_gen ::
"('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa) sym_elle \<Rightarrow> 
 ('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa, 'o) sym_elle_disc \<Rightarrow> 'o" where
"sym_elle_cases_gen s d = sym_i_cases_gen s (d)"
*)

(* applyBefore vs applyAfter? *)

(* this is still not great but may be sort of what we want *)
fun sym_elle_cases_gen'2 ::
"('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa) sym_elle \<Rightarrow> 
 ('i, 'lix, 'ljx, 'ljix, ('xb1 \<Rightarrow> 'o), ('xb2 \<Rightarrow> 'o), ('xa \<Rightarrow> 'o), 'o) sym_elle_disc'2 \<Rightarrow> 'o" where
"sym_elle_cases_gen'2 s d = sym_i_cases_gen'2 s (tmap2t dmerge5 d)"

(* yet another option: change our normal form. this will be the focus of
Alt_Sym2

this seems like more trouble than it's worth...
 *)

(* another option: give extension points special treatments in sym_i_disc? *)
(* that is, assume extension points already come with an "\<Rightarrow> 'o" *)
typ "('i, 'lix, 'ljx, 'ljix, ('xb1 \<Rightarrow> 'o), ('xb2 \<Rightarrow> 'o), ('xa \<Rightarrow> 'o), 'o) sym_elle_disc'2"

typ "('i, 'xb, 'xa, 'o) sym_i_disc'2"


(*value "((\<lambda> (x :: nat) . x + 1), (\<lambda> (x :: nat) . x + 1), (\<lambda> (x :: nat) . x + 1)) (Inl (3 :: nat))"*)

fun sym_elle_cases_gen'2 ::
"('i, 'lix, 'ljx, 'ljix, 'xb1, 'xb2, 'xa) sym_elle \<Rightarrow> 
 ('i, 'lix, 'ljx, 'ljix, ('xb1 \<Rightarrow> 'o), ('xb2 \<Rightarrow> 'o), ('xa \<Rightarrow> 'o), 'o) sym_elle_disc'2 \<Rightarrow> 'o" where
"sym_elle_cases_gen'2 s d = sym_i_cases_gen'2 s d"


(*
type_synonym ('i, 'xb, 'xa, 'o) sym_i_disc =
  "(('xb \<Rightarrow> 'o) * ('i \<Rightarrow> 'o) * ('xa \<Rightarrow> 'o))"
*)


end