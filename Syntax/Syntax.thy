theory Syntax
  imports "../Reify" 


begin

record ('x, 'r) reiden_parms =
  reify :: "('x \<Rightarrow> 'r)"
  denote :: "('r \<Rightarrow> 'x option)"

declare reiden_parms.defs[simp]

(* redefine C and Case in terms of reify/denote and footprint *)
record ('x, 'r) syn_parms = "('x, 'r) reiden_parms" +
  footprint :: "char list set"
  (*C :: "char list \<Rightarrow> 'r \<Rightarrow> 'x option"
  Case :: "char list \<Rightarrow> 'x \<Rightarrow> 'r option" *)

declare syn_parms.defs[simp]

locale Syn =
  fixes Syn_parms :: "('x, 'r) syn_parms"
begin

abbreviation reify :: "'x \<Rightarrow> 'r" where
"reify \<equiv> reiden_parms.reify Syn_parms"

abbreviation denote :: "'r => 'x option" where
"denote \<equiv> reiden_parms.denote Syn_parms"

abbreviation footprint :: "char list set" where
"footprint \<equiv> syn_parms.footprint Syn_parms"

abbreviation C :: "char list \<Rightarrow> 'r \<Rightarrow> ('x) option" where
"C s r \<equiv>
  (if s \<in> footprint then denote r
   else None)"

abbreviation Case :: "char list \<Rightarrow> 'x \<Rightarrow> 'r option" where
"Case s x \<equiv> 
  (if s \<in> footprint then Some (reify x)
   else None)"

(* we're going to see if we can get away without an explicit
case by just doing equality checks on C forms *)
(*
abbreviation Case :: "char list \<Rightarrow> 'r option" where
"Case \<equiv> syn_parms.Case Syn_parms"
*)
end

(* we could also require reify and denote to be true inverses;
not sure if this is necessary *)
locale Syn_Spec = Syn + 
  assumes rdvalid : "denote (reify x) = Some x"
  assumes drvalid : "denote r = Some a \<Longrightarrow> reify a = r"

record ('x, 'r) syn_sym_parms = "('x, 'r) reiden_parms" +
  sym :: "char list"

declare syn_sym_parms.defs[simp]

locale Syn_Sym =
  fixes Syn_Sym_parms :: "('x, 'r) syn_sym_parms"
begin

abbreviation sreify :: "'x \<Rightarrow> 'r" where
"sreify \<equiv> reiden_parms.reify Syn_Sym_parms"

abbreviation sdenote :: "'r => 'x option" where
"sdenote \<equiv> reiden_parms.denote Syn_Sym_parms"

abbreviation sym :: "char list" where
"sym \<equiv> syn_sym_parms.sym Syn_Sym_parms"

definition sfootprint :: "char list set" where
"sfootprint = {sym}"

(* problem. how do we pull data back out? *)

abbreviation syn_parms :: "('x, 'r) syn_parms" where
"syn_parms \<equiv>
  syn_parms.make sreify sdenote sfootprint"


end

locale Syn_Sym_Spec = Syn_Sym +
  assumes rdvalid : "sdenote (sreify x) = Some x"
  assumes drvalid : "sdenote r = Some a \<Longrightarrow> sreify a = r"

sublocale Syn_Sym_Spec \<subseteq> Syn_Spec "syn_parms"
  apply(unfold_locales)
   apply(auto)
     apply(simp add:rdvalid)
    apply(simp add:drvalid)

done  

end