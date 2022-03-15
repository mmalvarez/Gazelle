theory Okay imports Wrappers
begin
(* Okay typeclass - attaches a set of "valid" values to a type
 * (useful in specifying liftings.
 *)
text_raw \<open>%Snippet gazelle__mergeable__okay__okay\<close>
class Okay =
  fixes ok_S :: "('a) set"
text_raw \<open>%EndSnippet\<close>

(* Instances of ok typeclass *)
text_raw \<open>%Snippet gazelle__mergeable__okay__option\<close>
instantiation option :: (Okay) Okay
begin
definition option_ok_S : "(ok_S :: 'a option set) = (Some ` ok_S)"
instance proof qed
end
text_raw \<open>%EndSnippet\<close>

instantiation prod :: (Okay, Okay) Okay
begin
definition prod_ok_S : "(ok_S :: ('a * 'b) set) = { x :: 'a * 'b . \<exists> a' b' . x = (a', b') \<and> a' \<in> ok_S \<and> b' \<in> ok_S}"
instance proof qed
end

instantiation unit :: Okay
begin
definition unit_ok_S :
  "(ok_S :: unit set) = UNIV"
instance proof qed
end

instantiation md_triv :: (_) Okay
begin
definition triv_ok_S : "(ok_S :: 'a md_triv set) = UNIV"
instance proof
qed
end

instantiation md_prio :: (Okay) Okay
begin
definition prio_ok_S : "(ok_S :: 'a md_prio set) = ({x . \<exists> px vx . x = mdp vx px \<and> px \<in> ok_S})"
instance proof qed
end


end