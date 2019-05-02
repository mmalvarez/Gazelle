theory ExploreML
  imports Main
begin

setup
"
  Sign.add_type @{context} (
  Binding.make (\"abcd\", @{here}), 0, NoSyn)
                ;
"

notepad
begin
  fix a :: "abcd"
end

ML
\<open>
  Context.>>
  (fn cx =>
  Context.Theory (
  ((Sign.add_type (Context.proof_of cx) 
  (Binding.make ("abce", @{here}), 3, NoSyn)) (Context.theory_of cx) )))
           ;
  
\<close>

ML
\<open>
  Context.put_generic_context (SOME (Context.Theory (
  Sign.add_type @{context} (
  Binding.make ("abcdef", @{here}), 0, NoSyn) (Proof_Context.theory_of @{context}))))
                ;
\<close>


ML
\<open>
  Context.>>
  (fn cx =>
    Context.Theory (((Sign.declare_const (Context.proof_of cx)
      ((Binding.make ("abcdthing", @{here}), @{typ abcdef}), NoSyn) (Context.theory_of cx)
  ) |> snd)))
\<close>

ML
\<open>
  Context.>>
  (fn cx =>
    Context.Theory (((Sign.declare_const (Context.proof_of cx)
      ((Binding.make ("mythingy", @{here}), @{typ int}), NoSyn) (Context.theory_of cx)
  ) |> snd)))
\<close>

term "mythingy"

term "abcdthing"

(*

goals:

- allow definition of type synonyms more easily
- allow for a more sane way of specifying which parameters we want to plug

*)


notepad
begin
  fix a :: "abcdef"
end
end