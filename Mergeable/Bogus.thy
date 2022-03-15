theory Bogus
  imports Wrappers
begin

(* Definition and instances of bogus typeclass
 * (datatypes where we can pull out a specified member
 * instead of crashing with undefined)
 *)
text_raw \<open>%Snippet gazelle__mergeable__bogus__bogus\<close>
class Bogus =
  fixes bogus :: "'a"
text_raw \<open>%EndSnippet\<close>

(* Instances of bogus typeclass *)
text_raw \<open>%Snippet gazelle__mergeable__bogus__nat\<close>
instantiation nat :: Bogus begin
definition nat_bogus : "bogus = (0 :: nat)"
instance proof qed
end
text_raw \<open>%EndSnippet\<close>

instantiation bool :: Bogus begin
definition bool_bogus : "bogus = True"
instance proof qed
end

instantiation int :: Bogus begin
definition int_bogus : "bogus = (0 :: int)"
instance proof qed
end

instantiation unit :: Bogus begin
definition unit_bogus : "bogus = ()"
instance proof qed
end

instantiation prod :: (Bogus, Bogus) Bogus begin
definition prod_bogus : "bogus = (bogus, bogus)"
instance proof qed
end

instantiation sum :: (Bogus, _) Bogus begin
definition sum_bogus : "bogus = Inl bogus"
instance proof qed
end

text_raw \<open>%Snippet gazelle__mergeable__bogus__option\<close>
instantiation option :: (Bogus) Bogus begin
definition option_bogus : "bogus = Some bogus"
instance proof qed
end
text_raw \<open>%EndSnippet\<close>

(* TODO: why not [bogus]? *)
instantiation list :: (_) Bogus begin
definition list_bogus : "bogus = []"
instance proof qed
end

instantiation String.literal :: Bogus begin
definition string_literal_bogus :
"bogus = STR ''''"
instance proof qed
end

instantiation md_triv :: (Bogus) Bogus begin
definition md_triv_bogus : "bogus = mdt bogus"
instance proof qed
end
instantiation md_prio :: (Bogus) Bogus begin
definition md_prio_bogus : "bogus = mdp 0 bogus"
instance proof qed
end

end