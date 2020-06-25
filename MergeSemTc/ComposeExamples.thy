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

(* we cannot always get a b out, so in order to
   be able to compose we need 1 and 2-argument versions
   of LIn. This feels ugly but I will try to revisit this
   later if I have time. *)
record ('a, 'b) lifting =
  LIn1 :: "('a \<Rightarrow> 'b)"
  LIn2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'b)"
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
      (LIn2 l) (sem b') b)"

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
                      (LIn2 l2 (sem syn' st') st)))"

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

definition id_l ::
  "('a, 'a) lifting" where
"id_l =
  \<lparr> LIn1 = id
  , LIn2 = (\<lambda> x y . id x)
  , LOut = Some\<rparr>" 

definition triv_td ::
  "('a, 'b) ptd' \<Rightarrow> ('a, 'b md_triv) ptd'" where
"triv_td t =
  (case t of
    (ToC, OfC) \<Rightarrow>
      (mdt o ToC, (case_md_triv OfC)))"

definition triv_l ::
  "('a, 'b) lifting \<Rightarrow> ('a, 'b md_triv) lifting" where
"triv_l t =
  \<lparr> LIn1 = mdt o (LIn1 t)
  , LIn2 = (\<lambda> a b . (case b of (mdt b') \<Rightarrow> (mdt ( (LIn2 t a b')))))
  , LOut = (case_md_triv (LOut t))\<rparr>"

(* another option would be to require a second mergeable
   dealing with conversion from unit to a *)
definition option_td ::
  "('a, 'b) ptd' \<Rightarrow>
   ('a, 'b option) ptd'" where
"option_td t =
  (case t of
    (ToC, OfC) \<Rightarrow>
      (Some o ToC, (case_option None OfC)))"

definition option_l ::
  "('a, 'b) lifting \<Rightarrow>
   ('a, 'b option) lifting" where
"option_l t =
  \<lparr> LIn1 = Some o (LIn1 t)
  , LIn2 = (\<lambda> a b . (case b of None \<Rightarrow> Some (LIn1 t a)
                    | Some b' \<Rightarrow> Some (LIn2 t a b')))
  , LOut = case_option None (LOut t) \<rparr>"

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
(*
definition prio_td ::
  "('a, 'b) ptd' \<Rightarrow>
   ('a, 'b md_prio) ptd'" where
"prio_td t =
  (case t of
    (ToC, OfC) \<Rightarrow> 
      (mdp 0 o ToC, 
       (\<lambda> x . case (OfC x) of None \<Rightarrow> None
                              | Some x' \<Rightarrow> Some (case_md_prio (\<lambda> _ . OfC ) x))))"
*)
(*
definition prio_l_keep ::
  "('a, 'b) lifting \<Rightarrow>
   ('a, 'b md_prio) lifting" where
"prio_l_keep t =
  \<lparr> LIn1 = mdp 0 o (LIn1 t)
  , LIn2 =
    (\<lambda> a p . (case p of
                mdp n b \<Rightarrow> mdp n (LIn2 t a b)))
  , LOut =
    (\<lambda> p . (case p of
              mdp n b \<Rightarrow> LOut t b))\<rparr>"

definition prio_l_inc ::
  "('a, 'b) lifting \<Rightarrow>
   ('a, 'b md_prio) lifting" where
"prio_l_inc t =
  \<lparr> LIn1 = mdp 0 o (LIn1 t)
  , LIn2 =
    (\<lambda> a p . (case p of
                mdp n b \<Rightarrow> mdp (1 + n) (LIn2 t a b)))
  , LOut =
    (\<lambda> p . (case p of
              mdp n b \<Rightarrow> LOut t b))\<rparr>"

definition prio_l_const ::
  "nat \<Rightarrow>
  ('a, 'b) lifting \<Rightarrow>
  ('a, 'b md_prio) lifting" where
"prio_l_const n t =
  \<lparr> LIn1 = mdp n o (LIn1 t)
  , LIn2 =
    (\<lambda> a p . (case p of
                mdp n' b \<Rightarrow> mdp (n) (LIn2 t a b)))
  , LOut =
    (\<lambda> p . (case p of
              mdp n' b \<Rightarrow> LOut t b))\<rparr>"

definition prio_l_zero ::
  "('a, 'b) lifting \<Rightarrow>
   ('a, 'b md_prio) lifting" where
"prio_l_zero =
  prio_l_const 0"

definition prio_l_one ::
  "('a, 'b) lifting \<Rightarrow>
   ('a, 'b md_prio) lifting" where
"prio_l_one =
  prio_l_const 1"
*)
definition prio_l ::
  "nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow>
  ('a, 'b) lifting \<Rightarrow>
  ('a, 'b md_prio) lifting" where
"prio_l n f t =
  \<lparr> LIn1 = mdp n o (LIn1 t)
  , LIn2 = (\<lambda> a p . (case p of
                mdp m b \<Rightarrow> mdp (f m) (LIn2 t a b)))
  , LOut =
      (\<lambda> p . (case p of
              mdp m b \<Rightarrow> LOut t b))\<rparr>"

definition prio_l_keep :: "('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_keep =
  prio_l 0 id"

definition prio_l_inc :: "('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_inc =
  prio_l 0 (\<lambda> x . 1 + x)"

definition prio_l_const :: "nat \<Rightarrow> ('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_const n =
  prio_l n (\<lambda> _ . n)"

definition prio_l_zero ::
"('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_zero =
  prio_l_const 0"

definition prio_l_one ::
"('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_one =
  prio_l_const 1"

definition fst_td ::
  "('a, 'b1) ptd' \<Rightarrow>
   ('a, 'b1 * ('b2 :: Pordb)) ptd'" where
"fst_td t =
  (case t of
    (ToC, OfC) \<Rightarrow>
          ((\<lambda> x . (ToC x, \<bottom>)),
          (\<lambda> x . (OfC (fst x)))))"

definition fst_l ::
  "('a, 'b1) lifting \<Rightarrow>
   ('a, 'b1 * ('b2 :: Pordb)) lifting" where
"fst_l t =
  \<lparr> LIn1 = (\<lambda> x . (LIn1 t x, \<bottom>))
  , LIn2 = (\<lambda> a b . (case b of
                      (b1, b2) \<Rightarrow> ((LIn2 t a b1), \<bottom>)))
  , LOut = (\<lambda> x . (LOut t (fst x))) \<rparr>"

definition snd_td ::
  "('a, 'b2) ptd' \<Rightarrow>
   ('a, ('b1 :: Pordb) * 'b2) ptd'" where
"snd_td t =
  (case t of
    (ToC, OfC) \<Rightarrow>
          ((\<lambda> x . (\<bottom>, ToC x)),
          (\<lambda> x . (OfC (snd x)))))"

definition snd_l ::
  "('a, 'b2) lifting \<Rightarrow>
   ('a, ('b1 :: Pordb) * 'b2) lifting" where
"snd_l t =
  \<lparr> LIn1 = (\<lambda> x . (\<bottom>, LIn1 t x))
  , LIn2 = (\<lambda> a b . (case b of
                      (b1, b2) \<Rightarrow> (\<bottom>, (LIn2 t a b2))))
  , LOut = (\<lambda> x . (LOut t (snd x))) \<rparr>"

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

definition prod_l ::
  "('a1, 'b1) lifting \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2) lifting" where
"prod_l t1 t2 =
  \<lparr> LIn1 = 
    (\<lambda> x . (case x of (x1, x2) \<Rightarrow> (LIn1 t1 x1, LIn1 t2 x2)))
  , LIn2 =
    (\<lambda> a b . (case a of (a1, a2) \<Rightarrow>
                (case b of (b1, b2) \<Rightarrow>
                  (LIn2 t1 a1 b1, LIn2 t2 a2 b2))))
  , LOut =
    (\<lambda> x . (case x of (x1, x2) \<Rightarrow>
              (case (LOut t1 x1) of
                None \<Rightarrow> None
                | Some x1' \<Rightarrow>
                  (case (LOut t2 x2) of
                    None \<Rightarrow> None
                    | Some x2' \<Rightarrow> Some (x1', x2'))))) \<rparr>"

(* this biases toward the first component. *)
definition prod_lm ::
  "('a1, 'b :: Mergeableb) lifting \<Rightarrow>
   ('a2, 'b) lifting \<Rightarrow>
   ('a1 * 'a2, 'b) lifting" where
"prod_lm t1 t2 =
  \<lparr> LIn1 = 
    (\<lambda> x . (case x of (x1, x2) \<Rightarrow> [^LIn1 t1 x1, LIn1 t2 x2^]))
  , LIn2 =
    (\<lambda> a b . (case a of (a1, a2) \<Rightarrow>
                  [^LIn2 t1 a1 b, LIn2 t2 a2 b^]))
  , LOut =
    (\<lambda> x . (case (LOut t1 x) of
              None \<Rightarrow> None
              | Some x1' \<Rightarrow>
                (case (LOut t2 x) of
                  None \<Rightarrow> None
                  | Some x2' \<Rightarrow> Some (x1', x2')))) \<rparr>"

value "ptd_map
          (triv_td (id_td))
          (\<lambda> x . x + 1 :: int)
          (mdt (1 :: int))"

value "l_map
          (triv_l (id_l))
          (\<lambda> x . x + 1 :: int)
          (mdt (1 :: int))"

value "ptd_map
        (option_td (triv_td (id_td)))
        (\<lambda> x . x + 1)
        (Some (mdt (1 :: int)))"

value "l_map
        (option_l (triv_l (id_l)))
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

definition ptd_lift :: "('a, 'b) ptd' \<Rightarrow> 'a \<Rightarrow> 'b" where
"ptd_lift t = fst t"

definition l_val :: "('a, 'b) lifting \<Rightarrow> 'a \<Rightarrow> 'b" where
"l_val t = LIn1 t"

(*
definition calc_sem_l where
  "calc_sem_l = ptd_map2 (fst_td (option_td (triv_td (id_td)))) 
                         (snd_td (option_td (triv_td (id_td)))) calc_sem"
*)
term "calc_sem_l"

type_synonym synsem =
  "calc md_triv option * print md_triv  option * (int md_triv option md_prio * int list md_triv option)"

definition calc_sem_l :: "synsem \<Rightarrow> synsem \<Rightarrow> synsem" where
  "calc_sem_l = l_map2 ((fst_l (option_l (triv_l (id_l)))))
                        (snd_l (snd_l (fst_l (prio_l_one (option_l (triv_l (id_l))))))) calc_sem"

term "l_map2 ((fst_l (option_l (triv_l (id_l)))))
                        (snd_l (snd_l (fst_l (prio_l_one (option_l (triv_l (id_l))))))) calc_sem"

(* is False the right default here? *)
definition l_pred :: "('a, 'b) lifting \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" where
"l_pred t P =
  (\<lambda> b . (case LOut t b of
          None \<Rightarrow> False
          | Some a \<Rightarrow> P a))"

(* we also want 2 notions of lifting preds over functions
   (1 for semantics only; 1 for syntax) *)

definition l_pred_step ::
  "('a, 'b) lifting \<Rightarrow>
   ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step l P st1 st2 =
  (case (LOut l) st1 of
    None \<Rightarrow> False
    | Some st1' \<Rightarrow> (case (LOut l) st2 of
                    None \<Rightarrow> False
                    | Some st2' \<Rightarrow>
                      (P st1' st2')))"

(* Is False the right default for "couldn't find syntax"?
   In this case I think so... *)
definition l_pred_step2 ::
  "('a1, 'b) lifting \<Rightarrow>
   ('a2, 'b) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2 \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step2 l1 l2 P syn st1 st2 =
  (case (LOut l1) syn of
    None \<Rightarrow> False
    | Some syn' \<Rightarrow>
       (case (LOut l2) st1 of
          None \<Rightarrow> False
          | Some st1' \<Rightarrow>
            (case (LOut l2) st2 of
              None \<Rightarrow> False
              | Some st2' \<Rightarrow> P syn' st1' st2')))"

(* I am not sure if this one is useful. *)
(*
definition l_pred_sem ::
  "('a, 'b) lifting \<Rightarrow>
   (('a \<Rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow>
   (('b \<Rightarrow> 'b) \<Rightarrow> bool)" where
"l_pred_sem l P f =
  (\<forall> g :: "'a \<Rightarrow> 'a" . 
     P g \<longrightarrow> (\<forall> x . \<exists> x' . LOut l (g x) = Some x')) \<and>
  P (\<lambda> a . (case LOut l (sem (LIn1 l a)) of Some a' \<Rightarrow> a'))
*)

(* what we want:
   Lout (Lin1 a) = Some a
   Lout (Lin2 a b) = Some a
   Lout b = Some a \<longrightarrow> Lin2 a b = b
  this last one doesn't really work - see for instance prio
*)

definition lifting_valid ::
  "('a, 'b) lifting \<Rightarrow> bool" where
"lifting_valid l =
 ((\<forall> a .  LOut l (LIn1 l a) = Some a) \<and>
  (\<forall> a b . LOut l (LIn2 l a b) = Some a))"

lemma lifting_valid_intro :
  assumes H1 : "\<And> a .  LOut l (LIn1 l a) = Some a"
  assumes H2 : "\<And> a b . LOut l (LIn2 l a b) = Some a"
  shows "lifting_valid l"
  using H1 H2
  by(auto simp add:lifting_valid_def)

lemma lifting_valid_unfold1 :
  assumes H : "lifting_valid l"
  shows "LOut l (LIn1 l a) = Some a"
  using H by (auto simp add:lifting_valid_def)

lemma lifting_valid_unfold2 :
  assumes H : "lifting_valid l"
  shows "LOut l (LIn2 l a b) = Some a"
  using H by (auto simp add:lifting_valid_def)

(* need to universally quantify over x? *)
(* prove versions for all 4 combinations In1/In2?*)
lemma pred_lift :
  assumes Hv : "lifting_valid l"
  assumes HP : "P x (f x)"
  shows "l_pred_step l P (LIn2 l x b) (l_map l f (LIn2 l x b))"
  using HP lifting_valid_unfold1[OF Hv] lifting_valid_unfold2[OF Hv]
  by(cases l; auto simp add:l_pred_step_def l_map_def split:option.splits)

lemma pred_lift2 :
  assumes Hv1 : "lifting_valid l1"
  assumes Hv2 : "lifting_valid l2"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step2 l1 l2 P (LIn2 l1 x1 y1) (LIn2 l2 x2 y2) (l_map2 l1 l2 f (LIn2 l1 x1 y1) (LIn2 l2 x2 y2))"
  using HP lifting_valid_unfold1[OF Hv1] lifting_valid_unfold2[OF Hv1]
           lifting_valid_unfold1[OF Hv2] lifting_valid_unfold2[OF Hv2]
  by(cases l1; cases l2; auto simp add:l_pred_step2_def l_map2_def split:option.splits)


lemma id_l_valid : "lifting_valid (id_l)"
  by (rule lifting_valid_intro; auto simp add:id_l_def)

lemma triv_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (triv_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (triv_l l) (LIn1 (triv_l l) a) = Some a" using lifting_valid_unfold1[OF H]
    by(auto simp add:triv_l_def)
next
  fix a :: 'a
  fix b :: "'b md_triv"
  show "LOut (triv_l l) (LIn2 (triv_l l) a b) = Some a"
    using lifting_valid_unfold2[OF H]
    by(auto simp add:triv_l_def split:md_triv.splits)
qed

lemma option_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (option_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (option_l l) (LIn1 (option_l l) a) = Some a" using lifting_valid_unfold1[OF H]
    by(auto simp add:option_l_def)
next
  fix a :: 'a
  fix b :: "'b option"
  show "LOut (option_l l) (LIn2 (option_l l) a b) = Some a"
    using lifting_valid_unfold2[OF H] lifting_valid_unfold1[OF H]
    by(auto simp add:option_l_def split:option.splits)
qed

(* next up:
   - prio (prove general one)
   - fst, snd *)
lemma prio_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (prio_l n f l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (prio_l n f l) (LIn1 (prio_l n f l) a) = Some a"
    using lifting_valid_unfold1[OF H] by(auto simp add:prio_l_def)
next
  fix a :: 'a
  fix b :: "'b md_prio"
  show "LOut (prio_l n f l) (LIn2 (prio_l n f l) a b) = Some a"
    using lifting_valid_unfold2[OF H] by(auto simp add:prio_l_def split:md_prio.splits)
qed

lemma fst_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (fst_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (fst_l l) (LIn1 (fst_l l) a) = Some a"
    using lifting_valid_unfold1[OF H] by(auto simp add:fst_l_def)
next
  fix a :: 'a
  fix b :: "('b * 'c)"
  show "LOut (fst_l l) (LIn2 (fst_l l) a b) = Some a"
    using lifting_valid_unfold2[OF H] by(auto simp add:fst_l_def split:prod.splits)
qed

lemma snd_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (snd_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (snd_l l) (LIn1 (snd_l l) a) = Some a"
    using lifting_valid_unfold1[OF H] by(auto simp add:snd_l_def)
next
  fix a :: 'a
  fix b :: "('c * 'b)"
  show "LOut (snd_l l) (LIn2 (snd_l l) a b) = Some a"
    using lifting_valid_unfold2[OF H] by(auto simp add:snd_l_def split:prod.splits)
qed



type_synonym print_st = "(int * int list)"
definition print_sem :: "print \<Rightarrow> print_st \<Rightarrow> print_st" where
"print_sem syn st =
  (case st of
    (sti, stl) \<Rightarrow>
      (case syn of
         Pprint \<Rightarrow> (sti, stl @ [sti])))"

term "(snd_l (fst_l (option_l (triv_l (id_l)))))"
term "(snd_l (snd_l (fst_l (prio_l_zero (option_l (triv_l (id_l)))))))"

term
"l_map2 (snd_l (fst_l (option_l (triv_l (id_l)))))
            (prod_l (snd_l (snd_l (fst_l (prio_l_zero (option_l (triv_l (id_l)))))))
                    (snd_l (snd_l (snd_l (option_l (triv_l (id_l)))))))"

definition print_sem_l :: "synsem \<Rightarrow> synsem \<Rightarrow> synsem" where
  "print_sem_l = 
    l_map2 (snd_l (fst_l (option_l (triv_l (id_l)))))
            (prod_lm (snd_l (snd_l (fst_l (prio_l_zero (option_l (triv_l (id_l)))))))
                     (snd_l (snd_l (snd_l (option_l (triv_l (id_l))))))) print_sem"

value
  "print_sem_l (l_val (snd_l (fst_l (option_l (triv_l (id_l))))) Pprint)
               (\<bottom>, \<bottom>, mdp 1 (Some (mdt 1)), Some (mdt []))"

class exl =
  fixes ex_l :: "('a, synsem) lifting"

instantiation

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
*)
end