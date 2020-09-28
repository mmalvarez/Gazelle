theory SynCompose
  imports "../MergeableTc/Mergeable" "../MergeableTc/Pord"
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


class Comp = Mergeableb +
  fixes dom1 :: "('a :: Pordb) set"
  fixes dom2 :: "'a set"
  fixes sem1 :: "'a \<Rightarrow> 'a"
  fixes sem2 :: "'a \<Rightarrow> 'a"
  assumes Dom1 : "bot \<in> dom1"
  assumes Dom2 : "bot \<in> dom2"
  assumes Sem1 : "x \<in> dom1 \<Longrightarrow> sem1 x \<in> dom1"
  assumes Sem2 : "x \<in> dom2 \<Longrightarrow> sem2 x \<in> dom2"
  assumes Pres :
  "x1 \<in> dom1 \<Longrightarrow> x2 \<in> dom2 \<Longrightarrow>
   has_sup {x1, x2} \<Longrightarrow>
   has_sup {sem1 x1, sem2 x2}"

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


end