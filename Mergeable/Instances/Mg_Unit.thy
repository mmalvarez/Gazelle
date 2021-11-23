theory Mg_Unit
  imports "../Pord" "../Mergeable"
begin


(*
 * Finally we derive Mergeable for the unit type. This is useful in the
 * implementation of Mergeable for RAList (see Mergeable_RAList.thy), as well as
 * (presumably) some other applications.
 *)

instantiation unit :: Pord_Weak begin
definition unit_pleq : 
"(a :: unit) <[ b = True"

instance proof 
  show "\<And>a::unit. a <[ a" by (auto simp add: unit_pleq)
next
  show "\<And>(a::unit) (b::unit) c::unit. a <[ b \<Longrightarrow> b <[ c \<Longrightarrow> a <[ c"
    by(auto simp add: unit_pleq)
qed
end

instantiation unit :: Pord begin
instance proof
  show " \<And>(a::unit) b::unit. a <[ b \<Longrightarrow> b <[ a \<Longrightarrow> a = b"
    by(auto simp add: unit_pleq)
qed
end

instantiation unit :: Pordc begin
instance proof
  show "\<And>(a::unit) b::unit. has_ub {a, b} \<Longrightarrow> has_sup {a, b}"
    by(auto simp add: unit_pleq has_ub_def has_sup_def is_ub_def is_sup_def is_least_def)
qed
end

instantiation unit :: Pord_Weakb begin
definition unit_bot :
"(\<bottom> :: unit) = ()"
instance proof
  show "\<And>a::unit. \<bottom> <[ a"
    by(auto simp add: unit_pleq unit_bot)
qed
end


instantiation unit :: Pordb begin
instance proof
qed
end

instantiation unit :: Mergeable begin
definition unit_bsup :
"[^ (a :: unit), (b :: unit) ^] = ()"

instance proof
  show "\<And>(a::unit) b::unit. is_bsup a b [^ a, b ^]"
    by(auto simp add:
          unit_pleq is_bsup_def is_least_def is_ub_def is_bub_def)
qed
end

instantiation unit :: Mergeableb begin
instance proof qed
end

end