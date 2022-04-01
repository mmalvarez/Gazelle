theory Lift_Id imports "../Lifter"
begin
(*
 * id
 *)
text_raw \<open>%Snippet gazelle__lifter__instances__lift_id__id_l\<close>
definition id_l ::
  "('x, 'a :: {Pord, Bogus}, 'a) lifting" where
"id_l =
  LMake (\<lambda> s a a' . a) (\<lambda> s a . a) (\<lambda> s . bogus)"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__lifter__instances__lift_id__id_l_S\<close>
definition id_l_S :: "'x \<Rightarrow> 'a md_triv set" where
"id_l_S = (\<lambda> _ . UNIV)"
text_raw \<open>%EndSnippet\<close>

(* TODO: change this along the lines of triv_l. *)
interpretation id_l: lifting_valid_weak "id_l" "\<lambda> _ . UNIV"
proof
  show "\<And>s a b. LOut id_l s (LUpd id_l s a b) = a"
    by(auto simp add: id_l_def)
next
  show "\<And>s b. b \<in> UNIV \<Longrightarrow>
           b <[ LUpd id_l s (LOut id_l s b) b"
    by(auto simp add: id_l_def leq_refl)
next
  show "\<And>s a b. LUpd id_l s a b \<in> UNIV"
    by auto
qed

end