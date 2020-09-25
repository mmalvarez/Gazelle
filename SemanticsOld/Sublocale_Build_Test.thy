theory Sublocale_Build_Test imports Main
begin

locale test =
  fixes param :: "'a \<Rightarrow> 'a"

begin

definition out :: "'a \<Rightarrow> 'a" where
"out a = param (param a)"
end

locale test2 =
  fixes blech :: nat

begin

definition bloo :: nat where
"bloo = blech + 1"

end

locale hmm = A : test

locale boo = B : test2

(* ok, here is how we ought to do it *)
locale both = A : test A + B : test B for A B



print_locale! both


end