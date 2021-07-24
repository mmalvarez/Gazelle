theory Hoare_Direct_Dominant imports Hoare Hoare_Indexed Hoare_Direct
 "../Lifter/Auto_Lifter_Proofs"
 "../Mergeable/Mergeable_Instances"
 "../Composition/Composition" "../Composition/Dominant"
 "../Language_Components/Seq/Seq_Hoare"
begin

(* 
 * When dealing with single-step languages, we have an important special case - that is,
 * the case where the single-step language is _dominant_ (see Composition/Dominant.thy)
 * for one or more pieces of syntax. In such cases we can show that the
 * lifted version of the rule holds without side conditions.
 *)

(* However, we might be able to avoid reasoning about liftings at all in such cases (?)
 * by playing the same parametricity trick as with the control languages?
 *)

(* turn an f on payloads into an f on control that ignores the control contents.
 * this can probably be a lifting actually *)
(*
definition no_control_lifting :: "('a, 'b :: {Bogus, Pord}, ('x, 'b) control) lifting" where
"no_control_lifting =
  schem_lift NC (SP NX (SP NX (SID NC)))"
*)
definition no_control_lifting :: "('a, 'b1, 'b2 :: {Bogus, Pord}) lifting \<Rightarrow>
  ('a, 'b1 :: {Bogus, Pord}, ('x, 'b2) control) lifting" where
"no_control_lifting l =
  schem_lift NC (SP NX (SP NX (SINJ l NC)))"


definition no_control_l :: "
('a, 'b1, 'b2 :: {Bogus, Pord}) lifting \<Rightarrow>
('a \<Rightarrow> 'b1 \<Rightarrow> 'b1 :: {Bogus, Pord}) \<Rightarrow>
('a \<Rightarrow> ('x, 'b2 :: {Bogus, Pord}) control \<Rightarrow> ('x, 'b2 ) control)" where
"no_control_l l f =
  lift_map_s id (no_control_lifting l) f"

(* TODO: this hypothesis is rather inconvenient. *)
(* TODO: there is a not-very-nice control flow interaction here, wherein we actually
 * need to remove the head...
 * seq handles this, but we need to figure out how to express that this will be handled
 * by another semantics - something like a generalization of dominates?
 *)
(* so, if we merge with sequence, we are most of the way there.
 * however, we need to show that sequence doesn't get overridden
 * by other control semantics.
   * idea: we can actually use dominance here.
   * all we need to do is say that seq is dominant for that syntax
   * for all _other_ semantics. no_control_lifting should do the rest. i think.
 *)
lemma HTS_imp_HT' :
  assumes H: "f % {{P1}} c {{P2}}"
  assumes Hf' : "f' = no_control_l l f"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hseq : "seq_sem_l_gen lfts \<in> set fs"
  assumes Hnemp : "g \<in> (set fs - {seq_sem_l_gen lfts})"
  assumes Hdom : "(f' \<downharpoonleft> (set fs - {seq_sem_l_gen lfts}) c)"
  shows "|gs| {~ P1 ~} [G c z] {~ P2 ~}"
proof(rule HT'I)
  fix npost

  have "|#gs#| {#-P1, (0 + npost)-#} [G c z] {#-P2, npost-#}"
    unfolding add_0
  proof
    fix c'

    assume Guard : "|#gs#| {#P2, npost#} c'"
    show "|#gs#| {#P1, npost#} ([G c z] @ c')"
    proof
      fix m :: "('a, 'b) control"
      assume Hpay : "P1 (payload m)"
      assume Hcont : "cont m = Inl ([G c z] @ c')"

      have Hpay' : "(P2 (f c (payload m)))"
        using HTSE[OF H Hpay] by auto

      show "safe_for gs m npost"
      proof(cases "(sem_step gs m)")
        case (Inr bad)
  
        then have False using Hcont H0
          by(auto simp add: sem_step_def)
  
        then show ?thesis by auto
      next
        case (Inl m')

        have Pres' : "sups_pres (set fs - {seq_sem_l_gen lfts})"
          using sups_pres_subset[OF Hpres, of "set fs - {seq_sem_l_gen lfts}"] by auto

        obtain fs_sub where Fs_sub : "set fs_sub = set fs - {seq_sem_l_gen lfts}"
          using finite_list[of "set fs - {seq_sem_l_gen lfts}"]
          by auto

(* ok, so the idea now is:
- we know full step (op + control flow) leads to m'
- dominance over everything but the seq means we can treat it as
  "op (dominant thing) then seq"
- we can then unfold these things in order and everything should be ok.
*)

        have "gs = pcomps [pcomps fs_sub, seq_sem_l_gen lfts]"
          sorry

(* key sub-result. *)
        have Pay_final : "payload m' = f c (payload m)"
          sorry

(* key sub-result *)
        have Cont_final : "cont m' = cont (seq_sem_l_gen lfts c m)" sorry

        hence Cont_final' : "cont m' = Inl c'" sorry


(*
        have F_eq : "sem_step f' m = Inl m'"
          using sym[OF dominant_pcomps_set[OF Pres' Hnemp Hdom Fs_sub]] Hcont Inl H0
          by(simp add: sem_step_def)
  *)

        have Conc' : "safe_for gs m' npost"
          using guardediD[OF Guard, of "m'"] Hpay' Cont_final'
          unfolding Pay_final Cont_final'
          by auto

        have Inl_alt : "sem_step_p gs m m'"
          using Inl unfolding sem_step_p_eq by simp

        show  "safe_for gs m npost"
          using safe_for_weaken[OF safe_for_extend[OF Conc' Excp_1[OF Inl_alt]], of npost]
          by simp
      qed
    qed
  qed

  thus "\<exists>npre. |#gs#| {#-P1, (npre + npost)-#} [G c z] {#-P2, npost-#}"
    by blast
qed
end