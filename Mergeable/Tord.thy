theory Tord imports Pord

begin

locale Tord_Spec = Pord_Spec +
  assumes Total : "\<And> a b . pleq a b \<or> pleq b a"

sublocale Tord_Spec \<subseteq> Pordc_Spec
proof(auto simp only: Pordc_Spec_def)
  show "Pord_Spec pleq" by (rule Pord_Spec_axioms)
next

  show "Pordc_Spec_axioms pleq"
  proof(unfold_locales)

    fix a :: 'a
    fix b :: 'a
    assume H: "has_ub {a, b}"

    show "has_sup {a, b}"
    proof(cases "pleq a b")
      case True
      hence "is_sup {a, b} b" using H leq_refl by(auto simp add:is_sup_def is_ub_def is_least_def)
      thus "has_sup {a, b}" by(auto simp add:has_sup_def)
    next 
      case False
      hence "pleq b a" using Total by auto
      hence "is_sup {a, b} a" using H leq_refl by(auto simp add:is_sup_def is_ub_def is_least_def)
      thus "has_sup {a, b}" by(auto simp add:has_sup_def)
    qed
  qed
qed
end