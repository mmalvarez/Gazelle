theory Mg_Triv
  imports "../Pord" "../Mergeable"
begin

(* Trivial ordering: (x <[ x \<leftrightarrow> x = x)
 * md_triv is complete, but lacks a least element.
 *)
instantiation md_triv :: (_) Pord_Weak
begin
definition triv_pleq : "(a :: 'a md_triv) <[ b = (a = b)"
  instance proof
    fix a :: "'a md_triv"
    show "a <[ a" unfolding triv_pleq
      by auto
  next
    fix a b c :: "'a md_triv"
    show "a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c"
      unfolding triv_pleq by auto
  qed
end

instantiation md_triv :: (_) Pord
begin
instance proof
  fix a b :: "'a md_triv"
  show "a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b"
    unfolding triv_pleq by auto
qed
end

instantiation md_triv :: (_) Pordc
begin
instance proof
 fix a b :: "'a md_triv"
    assume "has_ub {a, b :: 'a md_triv}"
    show "has_ub {a, b} \<Longrightarrow> has_sup {a, b}" unfolding triv_pleq
      by(auto simp add:
    has_ub_def is_ub_def
    has_sup_def is_sup_def is_least_def triv_pleq)
  qed
end

instantiation md_triv :: (_) Pordps
begin
instance proof
  fix a b c :: "'a md_triv"

  assume "has_sup {a, b}"
  then have "a = b"
  by(auto simp add:
      has_ub_def is_ub_def
      has_sup_def is_sup_def is_least_def triv_pleq)

  assume "has_sup {b, c}"
  then have "b = c"
  by(auto simp add:
      has_ub_def is_ub_def
      has_sup_def is_sup_def is_least_def triv_pleq)

  assume "has_sup {a, c}"

  show "has_sup {a, b, c}"
    unfolding `a = b` `b = c`
  by(auto simp add:
      has_ub_def is_ub_def
      has_sup_def is_sup_def is_least_def triv_pleq)
qed
end

instantiation md_triv :: (_) Pordpsok
begin
instance proof
  fix a b supr :: "'a md_triv"
  show "supr \<in> ok_S"
    by(auto simp add: triv_ok_S)
qed
end

instantiation md_triv :: (_) Pordpsc
begin
instance proof qed
end

instantiation md_triv :: (_) Mergeable 
begin

definition triv_bsup : "[^(a :: 'a md_triv), b^] = a"

instance proof
    fix a b :: "'a md_triv"
    show "is_bsup a b (bsup a b)" unfolding triv_pleq triv_bsup
      by( simp only:
             triv_pleq triv_bsup is_bsup_def is_least_def is_bub_def is_sup_def is_ub_def;
             fast)
  qed
end

end