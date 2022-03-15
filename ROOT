(* chapter Gazelle *)

session Gazelle = "HOL-Library" +
  options [document = pdf, document_output = "output"]
  directories Syntax Lib "Lib/Oalist"
  	      Semantics Mergeable "Mergeable/Instances" Lifter
  	      "Lifter/Instances" "Lifter/Velocity" Composition Hoare
	      Language_Components
	      "Language_Components/Mem" "Language_Components/Calc"
	      "Language_Components/Cond" "Language_Components/Seq"
	      "Language_Components/Imp_Ctl"
	      Languages
	      "Languages/Imp"
	      "Paper_Examples"
(*theories [document = false]
    A
    B
  theories
    C
    D*)
  theories
    "Languages/Imp/Calc_Mem_Imp_Hoare"
    "Paper_Examples/Intro_Example"
    "Paper_Examples/Intro_Example_Gazelle"
    "Paper_Examples/Composition1"
    "Paper_Examples/Composition_Tuple_Components"
    "Paper_Examples/Composition_Option"
    "Paper_Examples/Composition_Priority"
  document_files
    "root.tex"

(*
session Paper_Examples in Paper_Examples = "Gazelle" +
  options [document = pdf, document_output = "output"]
(*theories [document = false]
    A
    B
  theories
    C
    D*)
  theories
(*    "Composition1"
    "Lens"
    "My_Lift"
    "Need_Toggle" *)
    "Intro_Example"
  document_files
    "root.tex"
*)
