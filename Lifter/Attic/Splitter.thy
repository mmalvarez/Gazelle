theory Splitter
  imports LifterX "HOL-Library.Adhoc_Overloading" "Auto_Lifter"
begin

datatype iNIL =
  NIL

datatype 'a iFST =
  FST 'a

datatype 'a iSND =
  SND 'a

datatype 'a iJUST =
  JUST 'a

datatype ('a, 'b) iCONS =
  CONS 'a 'b

type_synonym ('t1, 'i, 't2) split =
  "'t1 \<Rightarrow> 'i \<Rightarrow> 't2"

definition split_nil ::
  "('a, iNIL, 'a) split" where
"split_nil x _ = x"

definition split_fst ::
  "('a, 'i, 'z) split \<Rightarrow> ('a * 'b, 'i iFST, 'z) split" where
"split_fst s x i =
 (case i of
  FST i' \<Rightarrow>
  (case x of
    (x', _) \<Rightarrow> s x' i'))"

definition split_snd ::
  "('b, 'i, 'z) split \<Rightarrow> ('a * 'b, 'i iSND, 'z) split" where
"split_snd s x i =
 (case i of
  SND i' \<Rightarrow>
  (case x of
    (_, x') \<Rightarrow> s x' i'))"

definition split_just ::
  "(('a :: Bogus), 'i, 'z) split \<Rightarrow> ('a option, 'i iJUST, 'z) split" where
"split_just s x i =
  (case i of
    JUST i' \<Rightarrow>
    (case x of
      Some x' \<Rightarrow> s x' i'
      | _ \<Rightarrow> s bogus i'))"

consts split ::
  "('a \<Rightarrow> 'i \<Rightarrow> 'b)"

adhoc_overloading split
"split_nil"
"split_fst split"
"split_snd split"
"split_just split"

term "split (a, (b, c), d) (SND (FST NIL))"

(* idea: can we use CONS to enumerate all our splittings? *)

type_synonym ('t1, 't2) splits =
  "'t1 \<Rightarrow> 't2"


(*
need: source type
splits descriptor

  definition splits_prod ::
    "(('a, 's1) splits \<Rightarrow> ('b, 's2) splits \<Rightarrow> ('a * 'b, _) splits)" where
  "splits_prod s1 s2 x =
   
*)

end