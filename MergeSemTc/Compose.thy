theory Compose
  imports "../MergeableTc/Mergeable" "../MergeableTc/Pord" "../MergeableTc/Splittable"
begin

(* idea. for composition we need
- an ordered domain (for the output semantics)
- two input types
- semantics on the input types
- inject and project

*)

(* NOTE: while we don't require the Mergeable instance here
to have a least element, it very likely will need one to
make the injections/projections work. Likewise, the "source" types
for the Views will need to be ordered *)

(* TODO: do we need ordering on domains? or can we get away with just
   ordering on range? *)

(* TODO: is what follows sufficient?

*)


class Comp = Mergeableb + Splittableb +
  fixes sem1 :: "('a :: Splittable) \<Rightarrow> 'a"
  fixes sem2 :: "'a \<Rightarrow> 'a"
  fixes sem1_name :: "'a itself \<Rightarrow> char list"
  fixes sem2_name :: "'a itself \<Rightarrow> char list"
  assumes Proj_Wf1 : "sem1_name t \<in> projs_names (t)"
  assumes Proj_Wf2 : "sem2_name t \<in> projs_names (t)"
  assumes Sem1_Dom : "x \<in> (sdom (sem1_name t)) \<Longrightarrow> sem1 x \<in> (sdom (sem1_name t))"
  assumes Sem2_Dom : "x \<in> (sdom (sem2_name t)) \<Longrightarrow> sem2 x \<in> (sdom (sem2_name t))"
  assumes Pres :
  "x1 \<in> (sdom (sem1_name t)) \<Longrightarrow> x2 \<in> (sdom (sem2_name t)) \<Longrightarrow>
   has_sup {x1, x2} \<Longrightarrow>
   has_sup {sem1 x1, sem2 x2}"

definition cdom_l :: "('a :: Comp) set" where
"cdom_l = (sdom (sem1_name (TYPE('a))))"

definition cdom_r :: "('a :: Comp) set" where
"cdom_r = (sdom (sem2_name (TYPE('a))))"


typedef (overloaded) 'a cdom1t = "cdom_l :: ('a :: Comp) set"
proof(-)

  obtain d and f where Hdf : "Some (d, f) = map_of (projs :: ('a projs_t)) (sem1_name (TYPE('a)))"
      using Proj_Wf1[of "(TYPE('a))"]
            projs_distinct'[of "projs :: 'a projs_t"]
      by(auto simp add:projs_names_def)
    

  hence "(sem1_name (TYPE('a)), d, f) \<in> set (projs :: 'a projs_t)"
    by(auto intro:map_of_SomeD)

  hence "\<bottom> \<in> d" by (auto elim:projs_bot)

  thus ?thesis using Hdf by(cases "map_of (projs :: 'a projs_t) (sem1_name (TYPE('a)))"; auto simp add:cdom_l_def sdom_def sdom'_def)
qed

typedef (overloaded) 'a cdom2t = "cdom_r :: ('a :: Comp) set"
proof(-)
  obtain d and f where Hdf : "Some (d, f) = map_of (projs :: ('a projs_t)) (sem2_name (TYPE('a)))"
      using Proj_Wf2[of "(TYPE('a))"]
            projs_distinct'[of "projs :: 'a projs_t"]
      by(auto simp add:projs_names_def)
    

  hence "(sem2_name (TYPE('a)), d, f) \<in> set (projs :: 'a projs_t)"
    by(auto intro:map_of_SomeD)

  hence "\<bottom> \<in> d" by (auto elim:projs_bot)

  thus ?thesis using Hdf by(cases "map_of (projs :: 'a projs_t) (sem2_name (TYPE('a)))"; auto simp add:cdom_r_def sdom_def sdom'_def)
qed

(*
typedef (overloaded) 'a dom2 = "cdom_r :: ('a :: Comp) set"
*)
(* parallel composition *)
definition pcomp :: "('a :: Comp) \<Rightarrow> 'a" where
"pcomp x =
  [^ [^ sem1 x, sem2 x ^], x ^]"

definition pcomp' :: "('a :: Comp) \<Rightarrow> 'a" where
"pcomp' x =
  [^ [^ sem2 x, sem1 x ^], x ^]"

(* "real" parallel semantics, which may contain more information *)
definition pcomp_real :: "('a :: Comp) \<Rightarrow> 'a" where
"pcomp_real x =
  [^ sem1 x, [^ sem2 x, x ^]^]"

definition pcomp_real' :: "('a :: Comp) \<Rightarrow> 'a" where
"pcomp_real' x =
  [^ sem2 x, [^ sem1 x, x ^]^]"


(* next: extend this with syntaxes
   idea: we now have 4 domains. syntax1, syntax2, semantics1, semantics2
   6, if we count full syntax and full semantics *)

end