theory Slicing imports Main

begin

(*
consts get :: "('b \<Rightarrow> 'a)"
consts put :: "('a \<Rightarrow> 'b \<Rightarrow> 'b)"
*)

declare [[show_types]]

definition getput_spec :: "('b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"getput_spec get put1 put2 =
        ((\<forall> a . get (put1 a) = a) \<and>
         (\<forall> a b . get (put2 a b) = a))"


typedef ('a, 'b) slicer =
  "{ (gp :: 
     ('b \<Rightarrow> 'a) *
     ('a \<Rightarrow> 'b) *
     ('a \<Rightarrow> 'b \<Rightarrow> 'b)) .
     (\<forall> (get' :: 'b \<Rightarrow> 'a) (put1' :: 'a \<Rightarrow> 'b) (put2' :: 'a \<Rightarrow> 'b \<Rightarrow> 'b) .
         getput_spec get' put1' put2' \<longrightarrow>
         (\<forall> get put1 put2 .  
          gp = (get, put1, put2) \<longrightarrow>
          getput_spec get put1 put2))}"
proof(cases "\<exists> get' put1' put2' . getput_spec (get' :: 'b \<Rightarrow> 'a) put1' put2'")
  case True
  obtain get' :: "'b \<Rightarrow> 'a" and put1' put2' where "getput_spec get' put1' put2'" using True by auto
  then show ?thesis  by auto
next
  case False
  then show ?thesis by auto
qed

typedef (overloaded) ('a, 'b) slice =
  "{ (x :: ('a  * 'b)) .
     (case x of
        (z, get, put1, put2) \<Rightarrow> fst x = get (snd x) }"


end