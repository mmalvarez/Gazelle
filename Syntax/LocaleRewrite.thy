theory LocaleRewrite imports Main

begin

locale doubleResult =
  fixes f :: "nat \<Rightarrow> nat"

begin

definition f' :: "nat \<Rightarrow> nat" where
  "f' x = f x + f x"


end

locale doubleResult' =
  fixes f :: "nat \<Rightarrow> nat"

begin

definition f' :: "nat \<Rightarrow> nat" where
  "f' x = 2 * f x"

end

sublocale doubleResult \<subseteq> Z : doubleResult' 
  rewrites "Z.f' = local.f'"
proof
  fix x
  show "doubleResult'.f' f x = f' x"
  apply(unfold_locales)
  apply(insert local.f'_def[of x])
    apply(insert doubleResult'.f'_def[of f x])
  apply(arith)
    done
qed



end