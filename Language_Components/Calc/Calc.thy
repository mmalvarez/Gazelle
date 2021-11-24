theory Calc imports Main begin

datatype calc = 
  Cadd
  | Csub
  | Cmul
  | Cdiv
  | Cnum int
  | Cskip

type_synonym calc_state =
  "(int * int * int)"

fun calc_sem :: "calc \<Rightarrow> calc_state \<Rightarrow> calc_state" where
"calc_sem (Cadd) (x1, x2, x3) =
  (x1, x2, x1 + x2)"
| "calc_sem (Csub) (x1, x2, _) = (x1, x2, x1 - x2)"
| "calc_sem (Cmul) (x1, x2, _) = (x1, x2, x1 * x2)"
| "calc_sem (Cdiv) (x1, x2, _) = (x1, x2, divide_int_inst.divide_int x1 x2)"
| "calc_sem (Cnum i) (x1, x2, _) = (x1, x2, i)"
| "calc_sem (Cskip) st = st"


end