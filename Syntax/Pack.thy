theory Pack imports "../Syntax_Utils"
begin


(* idea: 'x gensyn parameter is a product of sums *)

type_synonym ('d, 'bp, 'ap, 'bs, 'as) pack =
  "('bp * ('bs + 'd + 'as) * 'ap)"

(* this one may be easier to write a discriminator for *)
type_synonym ('d, 'bp, 'ap, 'bs, 'as) pack2 =
  "('bs + ('bp * 'd * 'as) + 'as)"


type_synonym ('d, 'bp, 'ap, 'bs, 'as, 'o) pack_disc =
  "('bp * ('bs * ('d \<Rightarrow> 'o) * 'as) * 'ap)"

type_synonym ('d, 'bp, 'ap, 'bs, 'as, 'os, 'op) pack_disc_final =
  "('d, 'bp, 'ap, ('bs \<Rightarrow> 'os), ('as \<Rightarrow> 'os), 'os) pack_disc \<Rightarrow> 'op"

type_synonym ('d, 'bs, 'as) spack =
  "('d, _, _, 'bs, 'as) pack"

type_synonym ('d, 'bp, 'ap) ppack =
  "('d, 'bp, 'ap, _, _) pack"

type_synonym 'd dpack =
  "('d, _, _, _, _) pack"

end