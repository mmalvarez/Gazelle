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

definition splittable_td ::
  "char list \<Rightarrow>
   ('b ::  Splittable \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> 'b) \<Rightarrow>
   bool" where
"splittable_td s Rep Abs =
  (\<exists> S . sdom' s = Some S \<and>
  type_definition Rep Abs (Rep ` S))"


(* problem: we need to deal with
   - option type: can't project all values
   - but maybe this is ok, since we don't need to pull things out. just need to map.

So. We need a way to inject, which should always be in the domain
And we need a way to project, which is only guaranteed to be well-defined
in certain cases.
  (or we need a sensible default for what to do if we fail, e.g. for option)

*)

(*
definition splittable_td ::
  "char list \<Rightarrow>
   ('a \<Rightarrow> ('b :: Splittable)) \<Rightarrow>
   ('b \<Rightarrow> 'a) \<Rightarrow>
   ('a set) \<Rightarrow>
   bool" where
"splittable_td ToS OfS s A =
  (\<exists> S . sdom' s = Some S \<and>
   (\<forall> b . ToS b \<in> S \<and>
   ))"
*)

lemma splittable_td_unfold :
  fixes s :: "char list"
  fixes Rep :: "('b :: Splittable \<Rightarrow> 'a)" 
  fixes Abs :: "('a \<Rightarrow> 'b)"
  assumes H : "splittable_td s Rep Abs"
  shows
   "(\<exists> S . sdom' s = Some S \<and>
    type_definition Rep Abs (Rep ` S))" using H
  by(auto simp add:splittable_td_def)

lemma splittable_td_unfold' :
  fixes s :: "char list"
  fixes Rep :: "('b :: Splittable \<Rightarrow> 'a)" 
  fixes Abs :: "('a \<Rightarrow> 'b)"
  assumes H : "splittable_td s Rep Abs"
  shows
  "type_definition Rep Abs (Rep ` (sdom s))" using H
  by(auto simp add:splittable_td_def sdom_def)

lemma splittable_td_unfold1 :
  fixes s :: "char list"
  fixes Rep :: "('b :: Splittable \<Rightarrow> 'a)" 
  fixes Abs :: "('a \<Rightarrow> 'b)"
  assumes Htd : "splittable_td s Rep Abs"
  assumes Hdom : "sdom' s = Some S"
  shows "type_definition Rep Abs (Rep ` S)" using Htd Hdom
  by(auto simp add:splittable_td_def)

lemma splittable_td_unfold2 :
  fixes s :: "char list"
  fixes Rep :: "('b :: Splittable \<Rightarrow> 'a)" 
  fixes Abs :: "('a \<Rightarrow> 'b)"
  assumes Htd : "splittable_td s Rep Abs"
  assumes Hdom : "sdom' s = (None :: 'b set option)"
  shows "False" using Htd Hdom
  by(auto simp add:splittable_td_def)

lemma splittable_td_intro :
  fixes s :: "char list"
  fixes Rep :: "('b :: Splittable \<Rightarrow> 'a)" 
  fixes Abs :: "('a \<Rightarrow> 'b)"
  fixes S :: "'b set"
  assumes Htd : "type_definition Rep Abs (Rep ` S)"
  assumes Hdom : "sdom' s = Some S"
  shows "splittable_td s Rep Abs" using Htd Hdom
  by(auto simp add:splittable_td_def)

lemma splittable_td_intro' :
  fixes s :: "char list"
  fixes Rep :: "('b :: Splittable \<Rightarrow> 'a)" 
  fixes Abs :: "('a \<Rightarrow> 'b)"
  fixes S :: "'b set"
  assumes Htd : "type_definition Rep Abs (Rep ` (sdom s))"
  assumes Hdom : "sdom' s = (Some (sdom s) :: 'b set option)"
  shows "splittable_td s Rep Abs" using Htd Hdom
  by(simp add:splittable_td_def)

lemma triv_td :
  "splittable_td ''triv'' (case_md_triv id) (mdt :: 'a \<Rightarrow> 'a md_triv)"
proof(rule splittable_td_intro')
  show "type_definition (case_md_triv id) mdt (case_md_triv id ` sdom ''triv'')"
    by(auto intro: type_definition.intro simp add:sdom_def triv_projs sdom'_def split:md_triv.splits)
next
  show "sdom' ''triv'' = (Some (sdom ''triv'') :: 'a md_triv set option)"
    by(auto simp add:sdom_def sdom'_def triv_projs )
qed


(* now we need to figure out how to use these to do lifting in a nicer way. *)
(* goals: liftings for
    (int \<Rightarrow> int) \<Rightarrow> (int option \<Rightarrow> int option) 
    (int option \<Rightarrow> int option) \<Rightarrow> (int option md_prio \<Rightarrow> int option md_prio) 
*)

lemma map_of_inj_None : "map_of m k = None \<Longrightarrow>
                         inj f \<Longrightarrow>
                         map_of (map (map_prod f f') m) (f k) = None"
proof(induction m)
  case Nil
  then show ?case by auto
next
  case (Cons a m)
  then show ?case
    by(auto simp add:inj_def split:if_splits)
qed

lemma map_of_inj_Some : "map_of m k = Some v \<Longrightarrow>
                         inj f \<Longrightarrow>
                         map_of (map (map_prod f f') m) (f k) = Some (f' v)"
proof(induction m)
  case Nil
  then show ?case by auto
next
  case (Cons a m)
  then show ?case
    by(auto simp add:inj_def split:if_splits)
qed


lemma option_td :
  assumes H : "splittable_td s1 Rep1 Abs1"
  shows "splittable_td (''some.''[@]s1) (map_option Rep1) (map_option Abs1)"
proof(rule splittable_td_intro')
  show "type_definition (map_option Rep1) (map_option Abs1) (map_option Rep1 ` sdom (''some.''[@]s1))"
  proof(rule type_definition.intro)
    fix x :: "'a option"
    show "map_option Rep1 x \<in> map_option Rep1 ` sdom (''some.'' [@] s1)"
    proof(cases "sdom' (s1) :: 'a set option")
      assume Hi : "sdom' (s1::char list) = (None :: 'a set option)"
      thus ?thesis using splittable_td_unfold2[OF H]
        by(auto)
    next
      fix A :: "'a set"
      assume Hi : "sdom' (s1::char list) = Some (A::'a set)"
      obtain p where Hp : "Map.map_of (projs :: 'a projs_t) s1 = Some(A, p)" using Hi
        by(auto simp add:sdom'_def option_projs)

      have 0 : "sdom (''some.'' [@] s1) = (Some ` A) \<union> {None}"
        using map_of_inj_Some[OF Hp str_app_inj[of "''some.''"],
              of "(map_prod (\<lambda>d::'a set. (Some ` d) \<union> {None}) map_option)"]
        by(auto simp add:sdom'_def sdom_def option_projs)

      thus ?thesis 
      proof(cases x)
        assume Hii : "x = None"
        thus ?thesis using 0 by auto
      next
        fix a :: "'a"
        assume Hii : "x = Some a"

        thus ?thesis using 0
            type_definition.Rep[OF splittable_td_unfold1[OF H Hi], of a]
          by(auto simp add: Set.image_iff)
      qed
    qed
  next
    fix x :: "'a option"

    show "map_option Abs1 (map_option Rep1 x) = x"
    proof(cases "sdom' (s1) :: 'a set option")
      assume Hi : "sdom' (s1::char list) = (None :: 'a set option)"
      thus ?thesis using splittable_td_unfold2[OF H]
        by(auto)
    next
      fix A :: "'a set"
      assume Hi : "sdom' (s1::char list) = Some (A::'a set)"
      obtain p where Hp : "Map.map_of (projs :: 'a projs_t) s1 = Some(A, p)" using Hi
        by(auto simp add:sdom'_def option_projs)

      have 0 : "sdom (''some.'' [@] s1) = (Some ` A) \<union> {None}"
        using map_of_inj_Some[OF Hp str_app_inj[of "''some.''"],
              of "(map_prod (\<lambda>d::'a set. (Some ` d) \<union> {None}) map_option)"]
        by(auto simp add:sdom'_def sdom_def option_projs)

      thus ?thesis 
      proof(cases x)
        assume Hii : "x = None"
        thus ?thesis using 0 by auto
      next
        fix a :: "'a"
        assume Hii : "x = Some a"

        thus ?thesis using 0
            type_definition.Rep_inverse[OF splittable_td_unfold1[OF H Hi], of a]
          by(auto)
      qed
    qed
  next
    fix y :: "'b option"
    assume Helem : " y \<in> map_option Rep1 ` sdom (''some.'' [@] s1)"

    show "map_option Rep1 (map_option Abs1 y) = y"
    proof(cases "sdom' (s1) :: 'a set option")
      assume Hi : "sdom' (s1::char list) = (None :: 'a set option)"
      thus ?thesis using splittable_td_unfold2[OF H]
        by(auto)
    next
      fix A :: "'a set"
      assume Hi : "sdom' (s1::char list) = Some (A::'a set)"
      obtain p where Hp : "Map.map_of (projs :: 'a projs_t) s1 = Some(A, p)" using Hi
        by(auto simp add:sdom'_def option_projs)

      have 0 : "sdom (''some.'' [@] s1) = (Some ` A) \<union> {None}"
        using map_of_inj_Some[OF Hp str_app_inj[of "''some.''"],
              of "(map_prod (\<lambda>d::'a set. (Some ` d) \<union> {None}) map_option)"]
        by(auto simp add:sdom'_def sdom_def option_projs)

      thus ?thesis
      proof(cases y)
        assume Hii : "y = None"
        thus ?thesis using 0 by auto
      next
        fix b :: "'b"
        assume Hii : "y = Some b"

        thus ?thesis using 0 Helem
            type_definition.Abs_inverse[OF splittable_td_unfold1[OF H Hi], of b]
          by(auto)
      qed
    qed
  qed
next
  show "sdom' (''some.'' [@] s1) = Some (sdom (''some.'' [@] s1) :: 'a option set)"
  proof(cases "sdom' (s1) :: 'a set option")
    assume Hi : "sdom' (s1::char list) = (None :: 'a set option)"
    thus ?thesis using splittable_td_unfold2[OF H]
      by(auto)
  next
    fix A :: "'a set"
    assume Hi : "sdom' (s1::char list) = Some (A::'a set)"
    obtain p where Hp : "Map.map_of (projs :: 'a projs_t) s1 = Some(A, p)" using Hi
      by(auto simp add:sdom'_def option_projs)

     have 0 : "sdom' (''some.'' [@] s1) = Some ((Some ` A) \<union> {None})"
      using map_of_inj_Some[OF Hp str_app_inj[of "''some.''"],
            of "(map_prod (\<lambda>d::'a set. (Some ` d) \<union> {None}) map_option)"]
      by(auto simp add:sdom'_def sdom_def option_projs)

    thus ?thesis by (auto simp add:sdom_def split:option.splits)
  qed
qed

(* TODO: repeat this for prod and prio *)

(*
      proof(cases "sdom' (''some.''[@]s1) :: 'a option set option")
        assume Hi2 : "sdom' (''some.''[@]s1)  = (None :: 'a option set option)"
        hence 0 : "map_of (projs :: 'a option projs_t) (''some.'' [@] s1) = None" by(auto simp add:sdom'_def)
        thus ?thesis using map_of_inj_Some[OF Hp str_app_inj[of "''some.''"],
              of "(map_prod (\<lambda>d::'a set. (Some ` d) \<union> {None}) map_option)"] Hi
          by(auto simp add:sdom'_def option_projs)
      next
        fix AO :: "'a option set"
        assume Hi2 : "sdom' (''some.'' [@] s1) = Some AO"

        thus ?thesis using map_of_inj_Some[OF Hp str_app_inj[of "''some.''"],
              of "(map_prod (\<lambda>d::'a set. (Some ` d) \<union> {None}) map_option)"] Hi
              type_definition.Rep[OF splittable_td_unfold1[OF H Hi]]
          apply(auto simp add:sdom_def sdom'_def option_projs)
          apply(case_tac x; auto)
      next
        fix AO :: "'a option set"
        assume Hi2 : "sdom' (''some.'' @ s1) = Some AO"
        thus ?thesis using Hi H
*)
(*           projs_distinct'[of "(projs :: ('a option) projs_t)", OF refl]
*)
(*
        apply(auto simp add:map_of_eq_None_iff)
*)
(*
definition is_inject_ext :: "char list \<Rightarrow> ('a \<Rightarrow> ('b :: Splittable)) \<Rightarrow> bool" where
"is_inject_ext s f = 
  (\<exists> S . sdom' s = Some S \<and> (\<forall> x . f x \<in> S))"

definition is_project_ext :: "char list \<Rightarrow> (('a :: Splittable) \<Rightarrow> 'b) \<Rightarrow> bool" where
"is_project_ext s f =
  (\<exists> S . sdom' s = Some S \<and> (\<forall> sp . sp \<in> S \<longrightarrow> f sp = )

definition sem_lift_prio_inc' :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a md_prio \<Rightarrow> 'a md_prio)" where
"sem_lift_prio_inc' = map_fun prio_inc o map_md_prio f"

declare syn_lift_triv_def syn_lift_option_def sem_lift_triv_def
        sem_lift_option_def sem_lift_prio_keep_def
        prio_inc_def sem_lift_prio_inc_def [simp]
*)
(*
definition sem_lift_prod :: " ('a1 \<Rightarrow> 'a2) \<Rightarrow> ('b1 \<Rightarrow> 'b2) \<Rightarrow>
                              (('a * 'b) \<Rightarrow> ('a * 'b)) \<Rightarrow>
                              ('a
*)                             

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