theory Sym_Elle imports Sym_I
begin
(* Elle syntax *)
    
record ('i, 'lix, 'ljx, 'ljix) sym_elle = "'i sym_i" +
  llab' :: "'lix option"
  ljmp' :: "'ljx option"
  ljmpi' :: "'ljix option"

  definition sym_elle_emp :: "('i, 'lix, 'ljx, 'ljix) sym_elle" where
  "sym_elle_emp = sym_i.extend sym_i_emp \<lparr> llab' = None, ljmp' = None, ljmpi' = None \<rparr>"
  
  record ('i, 'lix, 'ljx, 'ljix, 'o) sym_elle_disc =
    "('i, 'o) sym_i_disc" +
      llab'd :: "'lix \<Rightarrow> 'o"
      ljmp'd :: "'ljx \<Rightarrow> 'o"
      ljmpi'd :: "'ljix \<Rightarrow> 'o"

  (* TODO: want to have cases for just the new things? *)
  fun sym_elle_cases' ::
  "('i, 'lix, 'ljx, 'ljix, 'x) sym_elle_scheme \<Rightarrow>
   ('i, 'lix, 'ljx, 'ljix, 'o, 'xs) sym_elle_disc_scheme \<Rightarrow> 'o option" where
   "sym_elle_cases' s d =
      (case sym_i_cases' s d of Some out \<Rightarrow> Some out
| _ \<Rightarrow> case llab' s of Some x \<Rightarrow> Some (llab'd d x)
| _ \<Rightarrow> case ljmp' s of Some x \<Rightarrow> Some (ljmp'd d x)
|_ \<Rightarrow>  case ljmpi' s of Some x \<Rightarrow> Some (ljmpi'd d x))"

definition LLab :: "'lix \<Rightarrow> ('i, 'lix, 'ljx, 'ljix) sym_elle" where
"LLab x = sym_elle.llab'_update (\<lambda> _ . Some x) sym_elle_emp"

definition LJmp :: "'ljx \<Rightarrow> ('i, 'lix, 'ljx, 'ljix) sym_elle" where
"LJmp x = sym_elle.ljmp'_update (\<lambda> _ . Some x) sym_elle_emp"

definition LJmpI :: "'ljix \<Rightarrow> ('i, 'lix, 'ljx, 'ljix) sym_elle" where
"LJmpI x = sym_elle.ljmpi'_update (\<lambda> _ . Some x) sym_elle_emp"

fun sym_elle_fieldstatus :: "('i, 'lix, 'ljx, 'ljix, 'x) sym_elle_scheme  \<Rightarrow> bool list" where
"sym_elle_fieldstatus i = sym_i_fieldstatus i @ 
                      [is_some (llab' i)
                      ,is_some (ljmp' i)
                      ,is_some (ljmpi' i)]"
end