theory Hoare_Direct_Dominant imports Hoare Hoare_Indexed Hoare_Direct
 "../Lifter/Auto_Lifter_Proofs"
 "../Mergeable/Mergeable_Instances"
 "../Composition/Composition" "../Composition/Dominant"
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
definition no_control_lifting :: "('a, 'b :: {Bogus, Pord}, ('x, 'b) control) lifting" where
"no_control_lifting =
  schem_lift NC (SP NX (SP NX (SID NC)))"

definition no_control_l :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 
('a \<Rightarrow> ('x, 'b :: {Bogus, Pord}) control \<Rightarrow> ('x, 'b ) control)" where
"no_control_l f =
  lift_map_s id no_control_lifting f"

(* TODO: this hypothesis is rather inconvenient. *)
(* TODO: there is a not-very-nice control flow interaction here, wherein we actually
 * need to remove the head...
 * seq handles this, but we need to figure out how to express that this will be handled
 * by another semantics - something like a generalization of dominates?
 *)
lemma HTS_imp_HT' :
  assumes H: "f % {{P1}} c {{P2}}"
  assumes Hf' : "f' = no_control_l f"
  assumes H0 : "gs = pcomps fs"
  assumes Hpres : "sups_pres (set fs)"
  assumes Hnemp : "g \<in> set fs"
  assumes Hdom : "(f' \<downharpoonleft> (set fs) c)"
  shows "|gs| {~ P1 ~} [G c l] {~ P2 ~}"
proof(rule HT'I)
  fix npost

  have "|#gs#| {#-P1, (npost)-#} [G c l] {#-P2, npost-#}"
  proof
    fix c'

    assume Guard : "|#gs#| {#P2, npost#} c'"
    show "|#gs#| {#P1, npost#} ([G c l] @ c')"
    proof
      fix m :: "('a, 'b) control"
      assume Hpay : "P1 (payload m)"
      assume Hcont : "cont m = Inl ([G c l] @ c')"

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
  
        have F_eq : "sem_step f' m = Inl m'"
          using sym[OF dominant_pcomps[OF Hpres Hnemp Hdom]] Hcont Inl H0
          by(simp add: sem_step_def)
  
        show "safe_for gs m npost"
          using Guard
end