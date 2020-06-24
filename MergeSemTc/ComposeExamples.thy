theory ComposeExamples imports Compose "../MergeableTc/MergeableInstances" "../MergeableTc/SplittableInstances" HOL.Lifting HOL.Lifting_Set

begin

(* new approach
   - define syntax, semantics as normal
   - define a combined representation using Mergeable+Splittable
   - ** use "lifting" to translate semantics into the projected version
*)

datatype calc =
  Cadd int
  | Csub int
  | Cmul int
  | Cdiv int
  | Creset int

(*
datatype calc_st = CSi int
*)
definition calc_sem :: "calc \<Rightarrow> int \<Rightarrow> int" where
"calc_sem syn st = 
  (case syn of
     (Cadd i) \<Rightarrow> st + i
    |(Csub i) \<Rightarrow> st - i
    |(Cmul i) \<Rightarrow> st * i
    |(Cdiv i) \<Rightarrow> divide_int_inst.divide_int st i)"

definition syn_lift_triv :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a md_triv \<Rightarrow> ('b \<Rightarrow> 'c)" where
"syn_lift_triv = case_md_triv"

(* here we are assuming no syntax = no-op
   another option would be to return \<bottom> (b, c different; c being a Pordb) *)
definition syn_lift_option :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> ('b \<Rightarrow> 'b)" where
"syn_lift_option =
  case_option id"
                              
definition sem_lift_triv :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a md_triv \<Rightarrow> 'a md_triv)" where
"sem_lift_triv = map_md_triv"

definition sem_lift_option :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a option \<Rightarrow> 'a option)" where
"sem_lift_option = map_option"

definition sem_lift_prio_keep :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a md_prio \<Rightarrow> 'a md_prio)" where
"sem_lift_prio_keep = map_md_prio"

definition prio_inc :: "'a md_prio \<Rightarrow> 'a md_prio" where
"prio_inc = case_md_prio (\<lambda> n x . mdp (1 + n) x)"

definition sem_lift_prio_inc :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a md_prio \<Rightarrow> 'a md_prio)" where
"sem_lift_prio_inc f = prio_inc o map_md_prio f"

definition lift_sem_prod ::
  "('a1 \<Rightarrow> 'a2) \<Rightarrow>
   ('a2 \<Rightarrow> 'a1) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2) \<Rightarrow>
   ('b2 \<Rightarrow> 'b1) \<Rightarrow>
   (('a1 * 'b1) \<Rightarrow> ('a1 * 'b1)) \<Rightarrow>
   (('a2 * 'b2) \<Rightarrow> ('a2 * 'b2))" where
"lift_sem_prod in1 out1 in2 out2 sem x =
  (case x of
    (xa, xb) \<Rightarrow>
    case (sem (out1 xa, out2 xb)) of
      (res1, res2) \<Rightarrow> (in1 res1, in2 res2))"

definition lift_sem_prod' ::
  "('a1 \<Rightarrow> 'a2) \<Rightarrow>
   ('a2 \<Rightarrow> 'a1) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2) \<Rightarrow>
   ('b2 \<Rightarrow> 'b1) \<Rightarrow>
   (('a1 * 'b1) \<Rightarrow> ('a1 * 'b1)) \<Rightarrow>
   (('a2 * 'b2) \<Rightarrow> ('a2 * 'b2))" where
"lift_sem_prod' in1 out1 in2 out2 =
  map_fun (map_prod out1 out2) (map_prod in1 in2)"

(*
definition splittable_td ::
  "char list \<Rightarrow>
   ('b \<Rightarrow> ('a :: Splittable)) \<Rightarrow>
   ('a \<Rightarrow> 'b) \<Rightarrow>
   bool" where
"splittable_td s Rep Abs =
  (\<exists> S . sdom' s = Some S \<and>
  type_definition Rep Abs S)"
*)

(* do we also need a "re-merge" here?
   (basically taking returned result from a semantics over a,
    and merging it back into b, taking into account the data that may
    have been lost)?
   is bsup enough? *)

(*
type_synonym ('a, 'b) ptd = 
"char list * ('a \<Rightarrow> 'b) * ('b \<Rightarrow> 'a option) * ('b set)"

definition precomp_td ::
  "('a, 'b :: Splittableb) ptd \<Rightarrow>
   bool" where
"precomp_td ptd =
  (case ptd of
    (s, ToC, OfC, Dom') \<Rightarrow>
      (\<exists> S . sdom' s = Some S \<and>
       Dom' \<subseteq> S \<and>
       (\<forall> a . ToC a \<in> Dom') \<and>
       (\<forall> b . b \<in> Dom' \<longrightarrow>
              (\<exists> b' . OfC b = Some b' \<and> ToC b' <[ b)) \<and>
       (\<forall> a . OfC (ToC a) = Some a)))"
*)

(* idea: need to augment this with a way to keep data *)
type_synonym ('a, 'b) ptd' = 
"('a \<Rightarrow> 'b) * ('b \<Rightarrow> 'a option)"

record ('a, 'b) lifting =
  LIn :: "('a \<Rightarrow> 'b \<Rightarrow> 'b)"
  LOut :: "('b \<Rightarrow> 'a option)"


(* supply a default value?
   this feels like we're just redefining option though.
   is \<bottom> always what we want?
   i think maybe this should be identity when we can't translate it *)
(*
definition ptd_map ::
  "('a, 'b) ptd \<Rightarrow>
   ('a \<Rightarrow> 'a) \<Rightarrow>
   ('b :: {Mergeableb, Splittableb} \<Rightarrow> 'b)" where
"ptd_map ptd sem b =
  (case ptd of
      (s, ToC, OfC, _) \<Rightarrow>
        (case OfC b of
          None \<Rightarrow> b
          | Some b' \<Rightarrow> bsup (ToC (sem (b'))) b))"

definition ptd_map2 ::
    "('a1, 'b :: {Mergeableb, Splittableb}) ptd \<Rightarrow>
     ('a2, 'b) ptd \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b \<Rightarrow> 'b \<Rightarrow> 'b)" where
"ptd_map2 ptd1 ptd2 sem syn st =
  (case ptd1 of
    (s1, ToC1, OfC1, _) \<Rightarrow>
      (case ptd2 of
        (s2, ToC2, OfC2, _) \<Rightarrow>
          (case OfC1 syn of
            None \<Rightarrow> st
            | Some syn' \<Rightarrow>
              (case OfC2 st of
                None \<Rightarrow> st
                | Some st' \<Rightarrow>
                  bsup (ToC2 (sem syn' st')) st))))"
  *)
definition ptd_map ::
  "('a, 'b) ptd' \<Rightarrow>
   ('a \<Rightarrow> 'a) \<Rightarrow>
   ('b \<Rightarrow> 'b)" where
"ptd_map ptd sem b =
  (case ptd of
      (ToC, OfC) \<Rightarrow>
        (case OfC b of
          None \<Rightarrow> b
          | Some b' \<Rightarrow> (ToC (sem (b')))))"

definition l_map ::
  "('a, 'b) lifting \<Rightarrow>
   ('a \<Rightarrow> 'a) \<Rightarrow>
   ('b \<Rightarrow> 'b)" where
"l_map l sem b =
  (case (LOut l) b of
    None \<Rightarrow> b
    | Some b' \<Rightarrow> 
      (LIn l) (sem b') b)"

definition ptd_map2 ::
    "('a1, 'b ) ptd' \<Rightarrow>
     ('a2, 'b) ptd' \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b \<Rightarrow> 'b \<Rightarrow> 'b)" where
"ptd_map2 ptd1 ptd2 sem syn st =
  (case ptd1 of
    (ToC1, OfC1) \<Rightarrow>
      (case ptd2 of
        (ToC2, OfC2) \<Rightarrow>
          (case OfC1 syn of
            None \<Rightarrow> st
            | Some syn' \<Rightarrow>
              (case OfC2 st of
                None \<Rightarrow> st
                | Some st' \<Rightarrow>
                  (ToC2 (sem syn' st'))))))"

definition l_map2 ::
  "('a1, 'b) lifting \<Rightarrow>
   ('a2, 'b) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> 'b)" where
"l_map2 l1 l2 sem syn st =
  (case (LOut l1) syn of
    None \<Rightarrow> st
    | Some syn' \<Rightarrow> (case (LOut l2) st of
                    None \<Rightarrow> st
                    | Some st' \<Rightarrow>
                      (LIn l2 (sem syn' st') st)))"

(*
definition
*)
(*
definition splittable_td ::
  "char list \<Rightarrow>
   ('b ::  Splittable \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> 'b) \<Rightarrow>
   bool" where
"splittable_td s Rep Abs =
  (\<exists> S . sdom' s = Some S \<and>
  type_definition Rep Abs (Rep ` S))"
*)

(*
definition triv_td ::
  "('a, 'a md_triv) ptd'" where
"triv_td =
  (''triv'', mdt, Some o (case_md_triv id), UNIV)"

definition option_td ::
  "('a, 'b) ptd \<Rightarrow>
   ('a, 'b option) ptd" where
"option_td t =
  (case t of
    (s, ToC, OfC, Dom) \<Rightarrow>
      (''some.''[@]s, Some o ToC, (case_option undefined OfC), Some ` Dom))"
*)

definition id_td ::
  "('a, 'a) ptd'" where
"id_td =
  (id, Some)"

definition triv_td ::
  "('a, 'b) ptd' \<Rightarrow> ('a, 'b md_triv) ptd'" where
"triv_td t =
  (case t of
    (ToC, OfC) \<Rightarrow>
      (mdt o ToC, (case_md_triv OfC)))"

(* another option would be to require a second mergeable
   dealing with conversion from unit to a *)
definition option_td ::
  "('a, 'b) ptd' \<Rightarrow>
   ('a, 'b option) ptd'" where
"option_td t =
  (case t of
    (ToC, OfC) \<Rightarrow>
      (Some o ToC, (case_option None OfC)))"

(*
definition prod_td ::
  "('a1, 'b :: Mergeable) ptd' \<Rightarrow>
   ('a2, 'b) ptd' \<Rightarrow>
   ('a1 * 'a2, 'b) ptd'" where
"prod_td t1 t2 =
  (case t1 of
    (ToC1, OfC1) \<Rightarrow>
      (case t2 of
        (ToC2, OfC2) \<Rightarrow>
          (\<lambda> x . (case x of (x1, x2) \<Rightarrow> [^ToC1 x1, ToC2 x2^]),
          (\<lambda> x .
            case (OfC1 x) of
              None \<Rightarrow> None
              | Some x1 \<Rightarrow> 
                (case (OfC2 x) of 
                  None \<Rightarrow> None
                  | Some x2 \<Rightarrow> Some (x1,x2))))))"
*)

(* need to find a way to somehow save the priority value *)
definition prio_td ::
  "('a, 'b) ptd' \<Rightarrow>
   ('a, 'b md_prio) ptd'" where
"prio_td t =
  (case t of
    (ToC, OfC) \<Rightarrow> 
      (mdp 0 o ToC, 
       (\<lambda> x . case (OfC x) of None \<Rightarrow> None
                              | Some x' \<Rightarrow> Some (case_md_prio (\<lambda> _ . OfC ) x))))"
      

definition fst_td ::
  "('a, 'b1 :: Pordb) ptd' \<Rightarrow>
   ('a, 'b1 * ('b2 :: Pordb)) ptd'" where
"fst_td t =
  (case t of
    (ToC, OfC) \<Rightarrow>
          ((\<lambda> x . (ToC x, \<bottom>)),
          (\<lambda> x . (OfC (fst x)))))"

definition snd_td ::
  "('a, 'b2 :: Pordb) ptd' \<Rightarrow>
   ('a, ('b1 :: Pordb) * 'b2) ptd'" where
"snd_td t =
  (case t of
    (ToC, OfC) \<Rightarrow>
          ((\<lambda> x . (\<bottom>, ToC x)),
          (\<lambda> x . (OfC (snd x)))))"

definition prod_td ::
  "('a1, 'b1) ptd' \<Rightarrow>
   ('a2, 'b2) ptd' \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2) ptd'" where
"prod_td t1 t2 =
  (case t1 of
    (ToC1, OfC1) \<Rightarrow>
      (case t2 of
        (ToC2, OfC2) \<Rightarrow>
          (\<lambda> x . (case x of (x1, x2) \<Rightarrow> (ToC1 x1, ToC2 x2)),
          (\<lambda> x . (case x of (x1, x2) \<Rightarrow>
                    (case (OfC1 x1) of
                       None \<Rightarrow> None
                       | Some x1' \<Rightarrow> 
                         (case (OfC2 x2) of 
                           None \<Rightarrow> None
                           | Some x2' \<Rightarrow> Some (x1',x2'))))))))"
(*
definition sum_td ::
  "('a1, 'b1) ptd' \<Rightarrow>
   ('a2, 'b2) ptd' \<Rightarrow>
   ('a1 + 'a2, 'b1 + 'b2) ptd'" where
"sum_td t1 t2 =
  (case t1 of
    (ToC1, OfC1) \<Rightarrow>
      (case t2 of
        (ToC2, OfC2) \<Rightarrow>
          (\<lambda> x . (case x of (Inl x1) \<Rightarrow> Inl (ToC1 x1)
                            | (Inr x2) \<Rightarrow> Inr (ToC2 x2)))
          (\<lambda> x . (case x of
                    Inl x1 \<Rightarrow> (case (OfC1 x1) of None \<Rightarrow> None | Some x1' \<Rightarrow> Some (Inl x1'))
                    | Inr x2 \<Rightarrow> (case (OfC2 x2) of None \<Rightarrow> None | Some x2' \<Rightarrow> Some (Inr x2'))))))"
*)
value "ptd_map
          (triv_td (id_td))
          (\<lambda> x . x + 1 :: int)
          (mdt (1 :: int))"

value "ptd_map
        (option_td (triv_td (id_td)))
        (\<lambda> x . x + 1)
        (Some (mdt (1 :: int)))"

(* something is off here. *)
term "
        (prod_td (option_td (triv_td (id_td))) (option_td (triv_td (id_td))))"

term "ptd_map
        (prod_td (option_td (triv_td (id_td))) (option_td (triv_td (id_td))))
        (\<lambda> x . case x of (x1, x2) \<Rightarrow> (x1 + 1, x2 + 1))"

value "ptd_map
        (prod_td (option_td (triv_td (id_td))) (option_td (triv_td (id_td))))
        (\<lambda> x . case x of (x1, x2) \<Rightarrow> (x1 + 1, x2 + 1))
        (Some (mdt (1 :: int)), Some (mdt (2 :: int)))"


term "sem_lift_prio_inc o sem_lift_option o sem_lift_triv o ((syn_lift_option o syn_lift_triv) calc_sem)"

term "map_fun ((syn_lift_option o syn_lift_triv))"

term " ((syn_lift_option o syn_lift_triv) calc_sem)"

term "sem_lift_prio_inc o sem_lift_option o sem_lift_triv"

(* need "liftable" typeclass"? *)
definition calc_sem' :: "calc md_triv option \<Rightarrow> int md_triv option md_prio \<Rightarrow> int md_triv option md_prio" where
"calc_sem' =
  sem_lift_prio_inc o sem_lift_option o sem_lift_triv o ((syn_lift_option o syn_lift_triv) calc_sem)"

datatype print =
  Pprint
  | Preset

datatype  reified =
  RNat nat
  | RInt int
  | RUnit unit
  | RTriv "reified md_triv"
  | RPrio "reified md_prio"
  | RList "reified list"
  | RBool bool
  | RCalc calc
  | RPrint print
  | ROption "reified option"
  | RProd "reified * reified"
  | RSum "reified + reified"

definition ptd_lift :: "('a, 'b) ptd' \<Rightarrow> 'a \<Rightarrow> 'b" where
"ptd_lift t = fst t"

(*
definition calc_sem_l where
  "calc_sem_l = ptd_map2 (fst_td (option_td (triv_td (id_td)))) 
                         (snd_td (option_td (triv_td (id_td)))) calc_sem"
*)
term "calc_sem_l"

type_synonym synsem =
  "calc option * print option * (int md_triv option md_prio * int list md_triv option)"

definition calc_sem_l :: "synsem \<Rightarrow> synsem \<Rightarrow> synsem" where
  "calc_sem_l = ptd_map2 ((fst_td (option_td (triv_td (id_td)))))
                         (snd_td (snd_td (fst_td (option_td (triv_td (id_td)))))) calc_sem"


class reified_td =
  fixes rei_t :: "('a, reified) ptd'"

instantiation nat :: reified_td begin
definition nat_rei_t: 
  "rei_t = (RNat, (\<lambda> x . case x of RNat x' \<Rightarrow> Some x' | _ \<Rightarrow> None))"
instance proof qed
end

instantiation int :: reified_td begin
definition int_rei_t:
  "rei_t = (RInt, (\<lambda> x . case x of RInt x' \<Rightarrow> Some x' | _ \<Rightarrow> None))"
instance proof qed
end

datatype 'a weakr =
  WR 'a

(*
definition reified_td ::
  "('a :: reified_td, 'b) ptd'" where
"
*)

class wr_td =
  fixes wrei_t :: "('a, 'a weakr) ptd'"

term "triv_td"

instantiation md_triv :: (wr_td)wr_td begin
definition triv_rei_t:
  "wrei_t = triv_td wrei_t"
instance proof qed
end

class GetTd =
  fixes rget :: "reified \<Rightarrow> ('a, synsem) ptd'"


type_synonym print_st = "(int * int list)"
print_classes
definition print_sem :: "print \<Rightarrow> print_st \<Rightarrow> print_st" where
"print_sem syn st =
  (case st of
    (sti, stl) \<Rightarrow>
      (case syn of
         Pprint \<Rightarrow> (sti, stl @ [sti])
       | Preset \<Rightarrow> (sti, [])))"
(*
definition print_sem' :: "print md_triv option \<Rightarrow> 
                          (int md_triv option md_prio * int list md_triv option) \<Rightarrow>
                          (int md_triv option md_prio * int list md_triv option)"
  where
"print_sem' = 
  (map_prod ((sem_lift_prio_keep o sem_lift_option o sem_lift_triv) id)
                ((sem_lift_option o sem_lift_triv) id)) o
    ((syn_lift_option o syn_lift_triv) print_sem)"
*)

definition print_sem' :: "print md_triv option \<Rightarrow> 
                          (int md_triv option md_prio * int list md_triv option) \<Rightarrow>
                          (int md_triv option md_prio * int list md_triv option)"
  where
"print_sem' = lift_sem_prod'"

(*
definition sem_lift_triv_prod1 :: "(('a * 'b) \<Rightarrow> ('a * 'b)) \<Rightarrow>
                                   (('a triv * 'b) \<Rightarrow> ('a triv * 'b))" where
"sem_lift_triv_prod1 =
  "
*)

(*
definition print_sem' :: "print md_triv option \<Rightarrow> (int md_triv option md_prio * int list md_triv option)" where
"print_sem'
*)

(* Here the user has to specify the combined state explicitly. I wonder if
  there is a way to avoid even this. *)
(*
   I also wonder if there is a nicer way to specify the overlap.
*)
(* define subtype, 
*)
type_synonym ex_st_t = "(int md_triv option md_prio * int list md_triv option)"
type_synonym ex_syn_t = "(calc md_triv option)"
type_synonym ex_t = "(ex_syn_t * ex_st_t)"

typedef example = "UNIV :: ex_t set"
  by auto
setup_lifting type_definition_example

lemma prio_inc_Q :
  "Quotient (\<lambda> (a :: int md_triv option md_prio) b . 
                    (case (a, b) of
                         (mdp ai a', mdp bi b') \<Rightarrow> a' = b'))
                (\<lambda> x . case (x) of (mdp xi x') \<Rightarrow> x')
                (\<lambda> x . mdp 1 x)
                (\<lambda> x x' . (case x of mdp xi x'' \<Rightarrow> x' = x''))"
  apply(rule QuotientI)
     apply(simp split:md_prio.splits)
  apply(simp split:md_prio.splits)
   apply(simp split:md_prio.splits)
  apply(simp split:md_prio.splits)
  apply(rule ext)
apply(rule ext)
  apply(auto)
  done
(*
declare prio_inc_Q [lifting_restore prio_inc_Q]
*)
declare md_triv.Quotient [quot_map]

print_quotients

definition map_md_prio_inc :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a md_prio) \<Rightarrow> ('b md_prio)" where
"map_md_prio_inc f =
  (case_md_prio (\<lambda> n a . mdp (1 + n) (f a)))"

lift_definition calc_sem' :: "calc \<Rightarrow> int md_triv option md_prio \<Rightarrow> int md_triv option md_prio" is calc_sem

definition ex_calc_sem :: "ex_t \<Rightarrow> ex_t \<Rightarrow> ex_t" where
"ex_calc_sem =
  map_fun (map_prod (map_md_prio o map_option o fst))"


(* next interesting thing: finding a convenient way to respect the md_prio
   when combining together these semantics *)




definition exi :: "(int md_triv option md_prio * int list md_triv option) \<Rightarrow> example"
  where "exi = Abs_example"

definition seml' :: "int md_triv option md_prio \<Rightarrow> int md_triv option md_prio" where
"seml' xo = 
  (case xo of
    mdp n (Some (mdt i)) \<Rightarrow> mdp (n + 1) (Some (mdt (i + 1)))
    | mdp n None \<Rightarrow> mdp n None)"

definition seml'' :
  "seml'' (x :: ex_syn) = 
  (case x of (x', y') \<Rightarrow> ((seml' x', None) :: ex_syn))"

lift_definition seml_e :: "example \<Rightarrow> example" is seml'' .

definition semr :: "(int * int list) \<Rightarrow> (int * int list)" where
"semr x =
(case x of
  (i, ints) \<Rightarrow> (i, ints @ [i]))"

(* n, None or 0, None ? *)
definition semr' :: "(int md_triv option md_prio * int list md_triv option) \<Rightarrow> (int md_triv option md_prio * int list md_triv option)" where
"semr' x =
(case x of
  (mdp n (Some (mdt i)), Some (mdt ints)) \<Rightarrow> (mdp n (Some (mdt i)), Some (mdt (ints @ [i])))
  | ((mdp n x'1), x'2) \<Rightarrow> (mdp n x'1, x'2))"

lift_definition semr_e :: "example \<Rightarrow> example" is semr' .

definition injl :: "nat * int option \<Rightarrow> ((nat * int option) * int list option)" where
"injl x = (x, None)"

definition prjl :: "((nat * int option) * int list option) \<Rightarrow> nat * int option" where
"prjl = fst"

definition injr :: "((nat * int option) * int list option) \<Rightarrow> ((nat * int option) * int list option)" where
"injr = id"

definition prjr :: "((nat * int option) * int list option) \<Rightarrow> ((nat * int option) * int list option)" where
"prjr = id"

definition dom1' :: "(int md_triv option md_prio * int list md_triv option) set" where
"dom1' = {x . \<exists> n x' . x = (mdp n x', None)}"

lift_definition dom1_e :: "example set" is "{x . \<exists> n x' . x = (mdp n x', None)}" .

definition dom2' :: "(int md_triv option md_prio * int list md_triv option) set"
  where "dom2' = {x . \<exists> l r' . x = (l, Some r')}"

lift_definition dom2_e :: "example set" is "UNIV" .

definition bot' :: "(int md_triv option md_prio * int list md_triv option)" where
"bot' = (bot, bot)"

lift_definition bot_e :: "example" is bot .

definition pleq' :: "ex_syn \<Rightarrow> ex_syn \<Rightarrow> bool" where
"pleq' = pleq"

lift_definition pleq_e :: "example \<Rightarrow> example \<Rightarrow> bool" is pleq done

definition bsup' :: "ex_syn \<Rightarrow> ex_syn \<Rightarrow> ex_syn" where
"bsup' = bsup"

lift_definition bsup_e :: "example \<Rightarrow> example \<Rightarrow> example" is bsup .

declare dom1'_def and dom1_e_def and dom2'_def and dom2_e_def and
        seml'_def and seml_e_def and semr'_def and semr_e_def and
        bot'_def and bot_e_def and bsup'_def and bsup_e_def and pleq'_def and pleq_e_def [simp]

declare pleq'_def [simp]

lift_definition is_least_e :: "(example \<Rightarrow> bool) \<Rightarrow> example \<Rightarrow> bool"
is is_least .

lift_definition is_ub_e :: "example set \<Rightarrow> example \<Rightarrow> bool"
  is is_ub.

lift_definition has_ub_e :: "example set \<Rightarrow> bool"
is has_ub .

lift_definition is_sup_e :: "example set \<Rightarrow> example \<Rightarrow> bool"
  is is_sup .

lift_definition has_sup_e :: "example set \<Rightarrow> bool"
  is has_sup.

lift_definition is_bsup_e :: "example \<Rightarrow> example \<Rightarrow> example \<Rightarrow> bool"
  is is_bsup.


(* Goal: make it so we don't have to reprove everything here *)
instantiation example :: Pord_Weak begin
definition example_pleq :
  "pleq = pleq_e"
instance proof
  fix a :: example
  show "a <[ a" unfolding example_pleq
(* apply(transfer_start)  *)
    by(transfer; rule leq_refl)
next
  show 
"\<And>(a::example) (b::example) c::example.
       a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c" unfolding example_pleq
    by(transfer; rule leq_trans)
qed
end


context includes lifting_syntax
begin


end

(* lift in the other direction? *)

instantiation example :: "Pord" begin
instance proof
  show
"\<And>(a::example) b::example.
       a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b" unfolding example_pleq

    by(transfer;  rule leq_antisym; auto)
qed
end

lemma thing' :
  fixes S 
  shows "(has_ub :: example set \<Rightarrow> bool) S = has_ub_e S" unfolding has_ub_e.rep_eq has_ub_def is_ub_def example_pleq pleq_e.rep_eq
  apply(transfer)
  apply(auto)
  done


instantiation example :: "Pordc" begin
instance proof
  fix a b :: example
  assume H : "has_ub {a, b}"
  show "has_sup {a, b}" using H 
    unfolding has_ub_def is_ub_def has_sup_def is_sup_def is_least_def example_pleq
      
    apply(transfer)
    apply(fold is_ub_def; fold has_ub_def; 
          fold is_least_def; fold is_sup_def; fold has_sup_def)
    apply(rule_tac complete2; auto)
    done
qed

end

instantiation example :: Pordb begin

definition example_bot :
  "bot = bot_e"
instance proof
  fix a :: example
  show "\<bottom> <[ a" unfolding example_pleq example_bot
    apply(transfer)
    apply(rule bot_spec)
    done
qed
end

declare is_ub_e.transfer [Transfer.transferred, transfer_rule]

instantiation example :: Mergeable begin
definition example_bsup :
  "bsup = bsup_e"
instance proof
  show
"\<And>(a::example) b::example. is_bsup a b [^ a, b ^]" 
    unfolding is_bsup_def is_sup_def is_least_def is_bub_def is_ub_def example_pleq example_bsup
    
    apply(transfer)
    apply(fold is_ub_def; fold is_least_def; fold is_sup_def; fold is_bub_def)
    apply(fold is_least_def) apply(fold is_bsup_def) apply(rule bsup_spec)
    done
qed
end

instantiation example :: Mergeableb begin
instance proof qed
end

instantiation example :: Comp begin
definition example_dom1 :
  "dom1 = dom1_e"
definition example_dom2 :
  "dom2 = dom2_e"
definition example_sem1 :
  "sem1 = seml_e"
definition example_sem2 :
  "sem2 = semr_e"

instance proof
  show "(\<bottom> :: example) \<in> dom1"
    unfolding example_dom1 example_bot
    apply(transfer)
    apply(simp add:prio_bot prod_bot option_bot)
    done
next
  show "(\<bottom> :: example) \<in> dom2"
    unfolding example_dom2 example_bot
    apply(transfer)
    apply(simp add:prio_bot prod_bot option_bot)
    done
next
  fix x :: example
  assume H1 : "x \<in> dom1"
  show "sem1 x \<in> dom1" using H1
    apply(simp add:example_sem1 example_dom1)
    apply(transfer)
    apply(simp add:seml'' seml'_def split:prod.splits option.splits md_triv.splits md_prio.splits)
    done
next
  fix x :: example
  assume H1 : "x \<in> dom2"
  show "sem2 x \<in> dom2" using H1
    apply(simp add:example_sem2 example_dom2)
    apply(transfer)
    apply(simp add:seml'' seml'_def split:prod.splits option.splits md_triv.splits md_prio.splits)
    done
next

  fix x1 x2 :: example
  assume H1 : "x1 \<in> dom1"
  assume H2 : "x2 \<in> dom2"
  assume Hsup : "has_sup {x1, x2}"

  have "has_ub {x1, x2}" using Hsup by(auto simp add:has_sup_def is_least_def has_ub_def is_sup_def)
  then obtain ub  where Hub :  "is_ub {x1, x2} ub" by (auto simp add:has_ub_def)

  have "has_ub {sem1 x1, sem2 x2}" using H1 H2 Hub
     unfolding has_sup_def has_ub_def is_sup_def is_least_def is_ub_def example_sem1 example_sem2 example_dom1 example_dom2 example_pleq
   proof(transfer)
     fix x1 x2 ub :: ex_syn
     assume H1t : "x1 \<in> {x. \<exists>n x'. x = (mdp n x', None)}"
     assume H2t : "x2 \<in> UNIV"
     assume "\<forall>x\<in>{x1, x2}. x <[ ub"
     hence  Hubt : "is_ub {x1, x2} ub" by(auto simp add:is_ub_def)

     obtain x1l and x1r where "x1 = (x1l, x1r)" by (cases x1; auto)
     then obtain x1p and x1' where Hx1 : "x1 = (mdp x1p x1', x1r)" by (cases x1l; auto)
     obtain x2l and x2r where "x2 = (x2l, x2r)" by (cases x2; auto)
     then obtain x2p and x2' where Hx2 : "x2 = (mdp x2p x2', x2r)" by (cases x2l; auto)
     obtain ubl and ubr where "ub = (ubl, ubr)" by (cases ub; auto)
     then obtain ubp and ub' where Hub' : "ub = (mdp ubp ub', ubr)" by (cases ubl; auto)

     obtain x1'l and x1'r where "seml'' x1 = (x1'l, x1'r)" by(cases "seml'' x1"; auto) 
     then obtain x1'p and x1'' where Hx1' : "seml'' x1 = (mdp x1'p x1'', x1'r)" by (cases x1'l; auto)

     obtain x2'l and x2'r where "semr' x2 = (x2'l, x2'r)" by (cases "semr' x2"; auto)
     then obtain x2'p and x2'' where Hx2' : "semr' x2 = (mdp x2'p x2'', x2'r)" by (cases x2'l; auto)

     have 0 : "ubp \<ge> x1p" using Hx1 Hubt Hub'
       by(auto simp add:is_ub_def prod_pleq prio_pleq triv_pleq split:md_prio.splits if_splits)

     have 1 : "ubp \<ge> x2p" using Hx2 Hubt Hub'
       by(auto simp add:is_ub_def prod_pleq prio_pleq triv_pleq split:md_prio.splits if_splits)

     have Conc'1 : "seml'' x1 <[ (mdp (2 + ubp) None, x2'r)" using Hx1 Hx2 Hx1' Hx2' Hubt Hub' H1t 0
       apply(auto simp add:seml'' semr'_def seml'_def prod_pleq prio_pleq triv_pleq leq_refl option_pleq option_bot is_ub_def split:option.splits md_triv.splits)
       done

     have Conc'2 : "semr' x2 <[ (mdp (2 + ubp) None, x2'r)" using Hx1 Hx2 Hx1' Hx2' Hubt Hub' H1t 1
       by(auto simp add:seml'' semr'_def seml'_def prod_pleq prio_pleq triv_pleq leq_refl option_pleq option_bot split:option.splits md_triv.splits)

     show "\<exists>a. \<forall>x\<in>{seml'' x1, semr' x2}. x <[ a" using Conc'1 Conc'2 by auto
   qed

   thus "has_sup {sem1 x1, sem2 x2}" using complete2 by auto

 qed
end


value [simp] "pcomp (exi (mdp (0 :: nat) (Some (mdt (5 :: int))), Some (mdt [])))"

end