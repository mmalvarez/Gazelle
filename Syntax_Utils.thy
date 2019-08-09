theory Syntax_Utils imports Main
begin

(* general utilities for use in our extensible
syntax (see Syntaxes/ directory) *)

(* used for validity checks to ensure only
one node type is selected *)
fun onetrue :: "bool list \<Rightarrow> bool" where
"onetrue l = 
    (case List.filter (\<lambda> b . b) l of
        [_] \<Rightarrow> True
        | _ \<Rightarrow> False)"

fun is_some :: "'o option \<Rightarrow> bool" where
"is_some None = False"
| "is_some _ = True"

(* used to make discriminators look more like
   normal functions (for valid syntax nodes,
   undefined should never be reached) *)
fun oforce :: "'o option \<Rightarrow> 'o" where
"oforce (Some out) = out"
| "oforce None = undefined"

(* utilities for managing
   normalization/reassociation of syntax-parameter types *)

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

fun reassoc5_sum ::
  "(('a + 'b + 'c + 'd + 'e) + 'f) \<Rightarrow> ('a + 'b + 'c + 'd + 'e + 'f)" where
"reassoc5_sum s =
  (case reassoc_sum s of
    Inl a \<Rightarrow> Inl a
  | Inr bcd \<Rightarrow> Inr (reassoc4_sum bcd))"

fun deassoc5_sum ::
  "('a + 'b + 'c + 'd + 'e + 'f) \<Rightarrow>
  (('a + 'b + 'c + 'd + 'e) + 'f)" where
"deassoc5_sum s =
  (case s of
    Inl a \<Rightarrow> Inl (Inl a)
  | Inr bcde \<Rightarrow> (case deassoc4_sum bcde of
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


(* discriminators *)

fun disc ::
  "('a + 'b) \<Rightarrow> (('a \<Rightarrow> 'o) * ('b \<Rightarrow> 'o)) \<Rightarrow> 'o" where
"disc (Inl a) (fa, _) = fa a"
| "disc (Inr b) (_, fb) = fb b"

fun disc3 ::
  "('a + 'b + 'c) \<Rightarrow> (('a \<Rightarrow> 'o) * ('b \<Rightarrow> 'o) * ('c \<Rightarrow> 'o)) \<Rightarrow> 'o" where
"disc3 (Inl a) (fa, _) = fa a"
| "disc3 (Inr bc) (_, fbc) = disc bc fbc"

(*
  resolving type issues that show up when applying differently
  associated discriminators
 NB: I think these are just "flip" applied to the disc combinators
*)

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


(*
  accessing individual elements of tuples
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

(* duals of tnth for sums *)
fun snth1h :: "'a \<Rightarrow> 'a + 'b" where
"snth1h a = Inl a"

fun snth1t :: "'b \<Rightarrow> 'a + 'b" where
"snth1t b = Inr b"

fun snth2h :: "'b \<Rightarrow> ('a + 'b + 'c)" where
"snth2h b = snth1t (snth1h b)"

fun snth2t :: "'c \<Rightarrow> ('a + 'b + 'c)" where
"snth2t c = snth1t (snth1t c)"

fun snth3h :: "'c \<Rightarrow> ('a + 'b + 'c + 'd)" where
"snth3h c = snth2t (snth1h c)"

fun snth3t :: "'d \<Rightarrow> ('a + 'b + 'c + 'd)" where
"snth3t d = snth2t (snth1t d)"

fun snth4h :: "'d \<Rightarrow> ('a + 'b + 'c + 'd + 'e)" where
"snth4h c = snth3t (snth1h c)"

fun snth4t :: "'e \<Rightarrow> ('a + 'b + 'c + 'd + 'e)" where
"snth4t d = snth3t (snth1t d)"

(*
    functor-style map for tuples
*)
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

(* duals of tmap for sums *)

fun smap1h ::
  "('a \<Rightarrow> 'o) \<Rightarrow> ('a + 'b) \<Rightarrow> ('o + 'b)" where
"smap1h f (Inl a) = Inl (f a)"
| "smap1h f (Inr b) = Inr b"

fun smap1t ::
  "('b \<Rightarrow> 'o) \<Rightarrow> ('a + 'b) \<Rightarrow> ('a + 'o)" where
"smap1t f (Inl a) = Inl a"
| "smap1t f (Inr b) = Inr (f b)"

fun smap2h ::
  "('b \<Rightarrow> 'o) \<Rightarrow> ('a + 'b + 'c) \<Rightarrow> ('a + 'o + 'c)" where
"smap2h f (Inl a) = Inl a"
| "smap2h f (Inr x) = Inr (smap1h f x)"

fun smap2t ::
  "('c \<Rightarrow> 'o) \<Rightarrow> ('a + 'b + 'c) \<Rightarrow> ('a + 'b + 'o)" where
"smap2t f (Inl a) = Inl a"
| "smap2t f (Inr x) = Inr (smap1t f x)"

fun smap3h ::
  "('c \<Rightarrow> 'o) \<Rightarrow> ('a + 'b + 'c + 'd) \<Rightarrow> ('a + 'b + 'o + 'd)" where
"smap3h f (Inl a) = Inl a"
| "smap3h f (Inr x) = Inr (smap2h f x)"

fun smap3t ::
  "('d \<Rightarrow> 'o) \<Rightarrow> ('a + 'b + 'c + 'd) \<Rightarrow> ('a + 'b + 'c + 'o)" where
"smap3t f (Inl a) = Inl a"
| "smap3t f (Inr x) = Inr (smap2t f x)"

end