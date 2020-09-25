theory Join_SemiLattice imports "HOL-Lattice.Orders" "HOL-Lattice.Bounds" "HOL-Lattice.Lattice" begin

record 'a join_semilattice_parms =
  lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

locale Join_Semilattice_Spec' =
  fixes ty :: "'t itself"
  fixes lt :: "'t \<Rightarrow> 't \<Rightarrow> bool"

print_locale Join_Semilattice_Spec'
print_locale partial_order

locale Join_Semilattice_Spec =
  partial_order 
begin

print_context

term "who \<sqsubseteq> who"

locale Join_Semilattice_Spec2 = Join_Semilattice_Spec +
  fixes thing :: "type_of(ty)"
  assumes huh : "leq thing thing"
begin
print_context
term "thing"

print_context
 

lemma test :
  "leq foo foo"

end

print_locale! Join_Semilattice_Spec'


locale Join_Semilattice_Spec =
  Join_Semilattice_Spec' +
  partial_order "(lt :: 'a \<Rightarrow> 'a \<Rightarrow> bool)" +
  fixes foo :: 'a
  fixes bar :: 'a
  (*assumes Hinf :
  "\<And> (x :: 'a) (y :: 'a) . \<exists> i . PO.is_inf x y i"*)
begin

lemma test :
  "Bounds.is_inf foo foo foo"

end

print_locale! Join_Semilattice_Spec'
