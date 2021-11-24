theory Mergeable_Instances
  imports Mergeable Wrappers Mergeable_Facts
          "Instances/Mg_Triv" "Instances/Mg_Option" "Instances/Mg_Prio" "Instances/Mg_Unit"
          "Instances/Mg_Prod"
 (* imports "./Instances/Mg_Triv" "./Instances/Mg_Option.thy" "./Instances/Mg_Prio.thy"
          "./Instances/Mg_Prod.thy" (* "./Instances/Mg_Oalist.thy" "./Instances/Mg_Roalist.thy *)
          "./Mergeable_Facts.thy" *)
begin

(* 
 * Here we instantiate the Mergeable typeclass (and friends) for a of built-in
 * Isabelle types, as well as for the types defined in Wrappers.
 * The instances defined here are sufficient for many purposes.
 * In order to work with Gazelle, data (state types used by merged semantics)
 * need to (at least) satisfy the Mergeable typeclass.
 * Any datatype can be used with Gazelle if wrapped in the "md_triv" wrapper, which induces
 * a trivial ordering. If a more interesting ordering is desired, 
 * Mergeable must be instantiated at a new datatype corresponding to data with that
 * ordering (see, for instance Mergeable_AList.thy)
 *)

(*
 * See the individual imported files for more details.
 *)

end