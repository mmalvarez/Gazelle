theory Elle_Semantics imports "Gensyn_Semantics_TypeParam" "../Syntax/Syn_Elle" "../Gensyn_Descend_Facts"
begin

(* this doesn't check whether the childpath is valid for a particular tree,
   which should be ok *)
(*
fun drop_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list option"
  where
"drop_opt xs 0 = Some xs"
| "drop_opt (h#t) (Suc n) = drop_opt t n"
| "drop_opt ([]) (Suc n) = None"
*)
(*
fun drop_opt :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list option"
  where
"drop_opt n l =
 (let out = drop n l in
  if length out + n = length l then Some out
  else None)"
*)

fun drop_opt :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list option"
  where
"drop_opt n l =
 (if n \<le> length l then Some (drop n l)
  else None)"


fun drop_opt_rev :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
"drop_opt_rev n l =
  (if n \<le> length l then Some (take (length l - n) l)
    else None)"

(*
fun drop_opt_rev :: "nat \<Rightarrow> 'a list \<Rightarrow>  'a list option"
  where
"drop_opt_rev n xs =
  (case drop_opt n (rev xs) of
    None \<Rightarrow> None
    | Some xs' \<Rightarrow> Some (rev xs'))"
*)

(* gather all labels corresponding to the given scope *)
fun get_scope_targets ::
  "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   childpath list"
and get_scope_targets_list ::
  "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn list \<Rightarrow>
   childpath \<Rightarrow>
   nat \<Rightarrow>
   childpath list"
  where
"get_scope_targets (GRec gg gr l) cp = get_scope_targets_list l cp 0"
| "get_scope_targets (GBase gb x) cp =
  syn_elle_cases x
    (
     \<lambda> _ . [],
    (\<lambda> dt . 
      if get_dat dt + 1 = length cp then [(cp)] else []
    ),
    \<lambda> _ . [],
    \<lambda> _ . [],
    \<lambda> _ . []
    )"
| "get_scope_targets_list [] cp n = []"
| "get_scope_targets_list (h#t) cp n =
   (get_scope_targets h (cp@[n])) @
   get_scope_targets_list t cp (n+1)"

value "get_scope_targets (GRec () () [(GBase () (LLab ((),0,())))]) []"

value "get_scope_targets (GBase () (LLab ((),0,()))) [1]"


(* get_jump_targets *)
fun get_jump_targets ::
  "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   childpath list" where
"get_jump_targets t cp =
 (case gensyn_get t cp of
    Some (GBase gb x) \<Rightarrow>
      (let to_drop = syn_elle_cases x
        (
          \<lambda> _ . None,
          \<lambda> _ . None,
          (\<lambda> dt . Some (get_dat dt)),
          (\<lambda> dt . Some (get_dat dt)),
          \<lambda> _ . None)
        in 
        (case to_drop of
          None \<Rightarrow> []
          | Some n \<Rightarrow> (case drop_opt_rev (n+1) cp of
                        None \<Rightarrow> []
                       | Some cp' \<Rightarrow> 
                         (case gensyn_get t cp' of
                          None \<Rightarrow> []
                          | Some t' \<Rightarrow> 
                  map (\<lambda> x . (cp' @ x)) (get_scope_targets t' [])))))
    | _ \<Rightarrow> [])"


inductive_set get_jump_targets_ind ::
  "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn \<Rightarrow>
   childpath \<Rightarrow>
   childpath set"
  for t :: "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn"
  and cp :: childpath
  where
"\<And>  t' nj cpre cpost cp' cpost' t'' nl .
 gensyn_get t cp = Some t' \<Longrightarrow>
 t' = GBase _ (LJump (_, nj, _)) \<Longrightarrow>
 cp = cpre @ cpost \<Longrightarrow>
 length cpost = nj + 1 \<Longrightarrow>
 cp' = cpre @ cpost' \<Longrightarrow>
 gensyn_get t cp' = Some t'' \<Longrightarrow>
 t'' = GBase _ (LLab (_, nl, _)) \<Longrightarrow>
 length cpost' = nl + 1 \<Longrightarrow>
 cp' \<in> get_jump_targets_ind t cp"
| "\<And>  t' nj cpre cpost cp' cpost' t'' nl .
 gensyn_get t cp = Some t' \<Longrightarrow>
 t' = GBase _ (LJumpI (_, nj, _)) \<Longrightarrow>
 cp = cpre @ cpost \<Longrightarrow>
 length cpost = nj + 1 \<Longrightarrow>
 cp' = cpre @ cpost' \<Longrightarrow>
 gensyn_get t cp' = Some t'' \<Longrightarrow>
 t'' = GBase _ (LLab (_, nl, _)) \<Longrightarrow>
 length cpost' = nl + 1 \<Longrightarrow>
 cp' \<in> get_jump_targets_ind t cp"

type_synonym syn_elle_full_a =
  "(_, _, _, _, _, _, _, _) syn_elle_full"

type_synonym syn_elle_gensyn_full_a =
  "(syn_elle_full_a, _, _) gensyn"

lemma get_scope_targets_elem :
  fixes t :: "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn"
  and ts :: "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn list"
shows C1 :"\<And> cpl cp . cpl \<in> set (get_scope_targets t cp) \<Longrightarrow>
   \<exists> cpost x y z nl. 
    cpl = cp@cpost \<and>
   gensyn_get t cpost = Some (GBase x (LLab (y, nl, z))) \<and>
   nl + 1 = length cpl"
  and
  C2 : "\<And> cpl cp n . cpl \<in> set (get_scope_targets_list ts cp n) \<Longrightarrow>
   \<exists> cpost off x y z nl .
    cpl = cp@[n+off]@cpost \<and> off < length ts \<and>
    gensyn_get (ts ! off) cpost = Some (GBase x (LLab (y, nl, z))) \<and>
   nl + 1 = length cpl"
proof(induction t and ts rule:gensyn_induct)
  case (1 g b) then show ?case
    apply(simp cong:sum.case_cong)
    apply(case_tac cp, auto)
    apply(simp add:LLab_def)
    done
next
  case (2 g r l)
  show ?case using "2.prems" "2.IH"[of cpl cp 0]
    apply(simp)
    apply(clarsimp)
    apply(rule_tac x = x in exI) apply(rule_tac x = y in exI) apply(rule_tac x = z in exI)
    apply(drule_tac gensyn_get_list_child2)
      apply(auto)
    done
next
  case 3
  then show ?case
    apply(clarsimp)
    done
next
  case (4 t l)
  thus ?case
    apply(fastforce)
    done  
qed

lemma get_scope_targets_elem2 [rule_format] :
  fixes t :: "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn"
  and ts :: "(('u, 'v, 'w, 'x, 'y, 'z, 'xb, 'xa) syn_elle_full, 'b, 'c) gensyn list"
shows "! cpl cp cpost x y z nl. 
    cpl = cp@cpost \<longrightarrow>
   gensyn_get t cpost = Some (GBase x (LLab (y, nl, z))) \<longrightarrow>
   nl + 1 = length cpl \<longrightarrow>
  (cpl) \<in> set (get_scope_targets t cp)"
  and
  "! cpl cp n cpost off x y z nl .
    cpl = cp@[n+off]@cpost \<longrightarrow> off < length ts \<longrightarrow>
    gensyn_get (ts ! off) cpost = Some (GBase x (LLab (y, nl, z))) \<longrightarrow>
   nl + 1 = length cpl \<longrightarrow>
  cpl \<in> set (get_scope_targets_list ts cp n)"
proof(induction t and ts rule:gensyn_induct)
case (1 g b)
  then show ?case 
    apply(rule_tac allI) apply(rule_tac allI) apply(rule_tac allI)
    apply(case_tac cpost) apply(auto)   
    apply(simp add:LLab_def split:sum.splits)
    done
next
  case (2 g r l)
  then show ?case
    apply(auto)
    apply(case_tac cpost, auto)
    apply(frule_tac gensyn_get_list_child)
    apply(drule_tac x = cp in spec)
    apply(drule_tac x = 0 in spec)
    apply(drule_tac x = list in spec)
    apply(drule_tac x = a in spec) apply(auto)
    apply(drule_tac gensyn_get_list_child(2)) apply(auto)
    done
next
  case 3
  then show ?case 
    apply(auto)
    done
next
  case (4 t l)
  then show ?case 
    apply(clarsimp)
    apply(case_tac off, auto)
     apply(drule_tac x = "cp@[n]" in spec) apply(rotate_tac -1)
     apply(drule_tac x = cpost in spec)
     apply(auto)
    apply(rotate_tac 1) apply(drule_tac x = cp in spec)
    apply(rotate_tac -1) apply(drule_tac x = "n + 1" in spec) apply(rotate_tac -1)
    apply(drule_tac x = cpost in spec) apply(rotate_tac -1)
    apply(drule_tac x = nat in spec) apply(auto)
    done
qed


lemma get_jump_targets_ind_valid2 :
  "cpl \<in> set (get_jump_targets (t :: syn_elle_gensyn_full_a) cp) \<Longrightarrow>
   cpl \<in> get_jump_targets_ind t cp"

  (* jump *)
  apply(clarsimp)
  apply(simp split:sum.split_asm)
  apply(simp split:if_split_asm)
   apply( rename_tac uu uua uub uuc uud x2 x2a x1)
   apply(case_tac x1, clarsimp)
     apply(frule_tac get_scope_targets_elem) apply(clarsimp)
   apply(simp add: LLab_def)

   apply(rule_tac uu = uu and uv = ab and nj = ba and uw = c
        and cpre = "take (length cp - Suc ba) cp"
        and cpost = "drop (length cp - Suc ba) cp"
        and ux = x and uy = y and nl = nl and uz = z
            in "get_jump_targets_ind.intros"(1))


          apply(auto simp add:LJump_def LLab_def)
   apply(simp add:gensyn_get_comp)

  (* jumpI *)
  apply(simp split:if_split_asm)
   apply( rename_tac uua uub uuc x a aa b)
         apply(frule_tac get_scope_targets_elem) apply(clarsimp)
  apply(simp add: LLab_def)
  apply(rule_tac va = uua and vb = a and nj = aa and vc = b
         and cpost = "drop (length cp - Suc aa) cp"
         
          in get_jump_targets_ind.intros(2))

         apply(auto simp add:LJump_def LJumpI_def LLab_def)
   apply(simp add:gensyn_get_comp)
  apply(simp)

  done
  

lemma get_jump_targets_ind_valid1 :
"cpl \<in> get_jump_targets_ind (t :: syn_elle_gensyn_full_a) cp \<Longrightarrow>
 cpl \<in> set (get_jump_targets t cp)"
proof(induction rule:get_jump_targets_ind.induct)
  case (1 uu uv uw ux uy uz t' nj cpre cpost1 cp2 cpost2 t'' nl)
  then show ?case 
    apply(simp add:LJump_def LLab_def)
    apply(frule_tac gensyn_get_comp2) apply(clarsimp)
    apply(frule_tac gensyn_get_comp2[of _ _ cpost2])
    apply(clarsimp)
    apply(rule_tac Set.imageI)
    apply(rule_tac "get_scope_targets_elem2"(1))
      apply(auto simp add:LLab_def)
    done next
    
next
  case (2 va vb vc vd ve vf t' nj cpre cpost1 cp2 cpost2 t'' nl)
  then show ?case 
     apply(simp add:LJumpI_def LLab_def)
    apply(frule_tac gensyn_get_comp2) apply(clarsimp)
    apply(frule_tac gensyn_get_comp2[of _ _ cpost2])
    apply(clarsimp)
    apply(rule_tac Set.imageI)
    apply(rule_tac "get_scope_targets_elem2"(1))
      apply(auto simp add:LLab_def)
    done
qed


(* this is really something like "elle_full_base_sem"
for modularity it might be a good idea to include a more general version *)
locale Elle_Semantics_Sig =
  fixes xr :: "'rs itself"
  fixes ms :: "'mstate itself"
  fixes lab_sem :: "(nat, 'xbl, 'xal) dat_elle_lab \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"
  fixes jump_sem :: "(nat, 'xbj, 'xaj ) dat_elle_jump \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"
  fixes jumpi_sem :: "(nat, 'xbji, 'xaji ) dat_elle_jumpi \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool \<Rightarrow> bool"


fun lab_sem_noop :: "(nat, 'xbl, 'xal) dat_elle_lab \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"lab_sem_noop _ m m' = (m = m')"

fun jump_sem_noop :: "(nat, 'xbl, 'xal) dat_elle_jump \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"jump_sem_noop _ m m' = (m = m')"

fun jumpi_sem_noop :: "(nat, 'xbl, 'xal) dat_elle_jumpi \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"jumpi_sem_noop _ m m' = (m = m')"


locale Elle_Semantics = Elle_Semantics_Sig
begin

print_context

inductive elle_base_sem ::
  "'g \<Rightarrow>
    ('c, 'd, 'e, 'f, 'g, 'h, 'xb, 'xa) syn_elle_full \<Rightarrow>
    'b \<Rightarrow> 'b \<Rightarrow>
    childpath \<Rightarrow>
    (('c, 'd, 'e, 'f, 'g, 'h, 'xb, 'xa) syn_elle_full, 'r, 'g) gensyn \<Rightarrow>
    ('a) gs_result \<Rightarrow> bool" where
"lab_sem l m m' \<Longrightarrow> 
    elle_base_sem g (LLab l) m m' cp t GRUnhandled"
| "jump_sem j m m' \<Longrightarrow>
    cpl \<in> get_jump_targets_ind t cp \<Longrightarrow>
    elle_base_sem g (LJump j) m m' cp t (GRPath cpl)"
| "jumpi_sem ji m m' False \<Longrightarrow>
    elle_base_sem g (LJumpI ji) m m' cp t GRUnhandled"
| "jumpi_sem ji m m' True \<Longrightarrow>
    cpl \<in> get_jump_targets_ind t cp \<Longrightarrow>
    elle_base_sem g (LJumpI ji) m m' cp t (GRPath X)"

end


end