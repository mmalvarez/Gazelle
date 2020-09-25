theory Functor imports Main "HOL-Library.Adhoc_Overloading"

begin

consts fmap' :: "('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'd"
fun fmap_opt :: "('b \<Rightarrow> 'c) \<Rightarrow> 'b option \<Rightarrow> 'c option" where
"fmap_opt _ None = None"
| "fmap_opt f (Some x) = Some (f x)"

fun fmap_list :: "('b \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'c list" where
"fmap_list f x = List.map f x"

adhoc_overloading fmap' fmap_opt
adhoc_overloading fmap' fmap_list

consts bind :: "'x \<Rightarrow> ('a \<Rightarrow> 'y) \<Rightarrow> 'y"
consts return :: "'a \<Rightarrow> 'x"

fun return_opt :: "'x \<Rightarrow> 'x option" where 
"return_opt x = Some x"

fun return_list :: "'x \<Rightarrow> 'x list" where
"return_list x = [x]"

fun bind_opt :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option" where
"bind_opt None _ = None"
| "bind_opt (Some x) f = f x"

fun bind_list :: "'b list \<Rightarrow> ('b \<Rightarrow> 'c list) \<Rightarrow> 'c list" where
"bind_list x f = List.concat (List.map f x)"

consts jmeq :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

adhoc_overloading jmeq "\<lambda> (a :: 'a) (b :: 'a) . a = b"

value "jmeq True True"

adhoc_overloading jmeq "\<lambda> a b . False"


adhoc_overloading bind bind_list
adhoc_overloading bind bind_opt
adhoc_overloading return return_list
adhoc_overloading return return_opt

(* law : fmap (f o g) x = fmap f ( fmap g x) *)
locale myfunctor =
  fixes fmap1 :: "('a \<Rightarrow> 'c) \<Rightarrow> 'x \<Rightarrow> 'z"
  fixes fmap2 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'y"
  fixes fmap3 :: "('b \<Rightarrow> 'c) \<Rightarrow> 'y \<Rightarrow> 'z"
  fixes jmq1 :: "(('a \<Rightarrow> 'c) \<Rightarrow> 'x \<Rightarrow> 'z) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'y) \<Rightarrow> bool"
  fixes jmq2 :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'x \<Rightarrow> 'y) \<Rightarrow> (('b \<Rightarrow> 'c) \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> bool"
  assumes "\<And> (f :: 'b \<Rightarrow> 'c) (g :: 'a \<Rightarrow> 'b) (x :: 'x) .
      fmap1 (f o g) x = fmap3 f (fmap2 g x)"


interpretation myfunctor_opt : myfunctor "fmap_opt" "fmap_opt" "fmap_opt"
  apply(unfold_locales) apply(case_tac x) apply(auto)
  
  done


lemma hmm : "\<And> (x :: _ option) . fmap' (Suc o Suc) x = fmap' Suc (fmap' Suc x)"
  apply(insert myfunctor_opt.myfunctor_axioms)
  apply(auto simp add:myfunctor_def)
  done
             

locale mymonad =
  fixes return1 :: "'a \<Rightarrow> 'x"
  fixes bind1 :: "'x \<Rightarrow> ('a \<Rightarrow> 'x) \<Rightarrow> 'x"

  fixes bind2 :: "'x \<Rightarrow> ('a \<Rightarrow> 'y) \<Rightarrow> 'y"
  fixes return2 :: "'a \<Rightarrow> 'x"

  fixes bind3a :: "'x \<Rightarrow> ('a \<Rightarrow> 'z) \<Rightarrow> 'z"
  fixes bind3b :: "'y \<Rightarrow> ('c \<Rightarrow> 'z) \<Rightarrow> 'z"
  fixes bind3c :: "'y \<Rightarrow> ('c \<Rightarrow> 'z) \<Rightarrow> 'z"
  fixes bind3d :: "'x \<Rightarrow> ('a \<Rightarrow> 'y) \<Rightarrow> 'y"

  assumes "\<And> (a :: 'a) (k :: 'a \<Rightarrow> 'y) .
      bind2 (return2 a) k = k a"
  assumes "\<And> (m :: 'x) . bind1 m (return1) = m"
  assumes "\<And> (m :: 'x) (k :: 'a \<Rightarrow> 'y) (h :: 'c \<Rightarrow> 'z) .
    bind3a m (\<lambda> x . bind3b (k x) h) = bind3c (bind3d m k) h"
(* ok, how do we apply these lemmata? *)

interpretation mymonad_opt: mymonad "return_opt" "bind_opt" 
                                    "bind_opt" "return_opt"
                                    "bind_opt" "bind_opt" "bind_opt" "bind_opt"
  apply(unfold_locales) apply(simp)
   apply(case_tac m, auto)
  apply(case_tac m, auto)
  done



(* need a locale with fmaps *)

(* need a way to index on instances *)

end