(* Empty-unit feasibility for the zero-capacity convert probe. *)
Theory bodyMemTbConvertZeroFixture
Ancestors
  bodyMemTbConvertZeroProbe compileVyper venomCompilerTypes venomPolicyTypes

Theorem convert_zero_empty_unit_exists:
  IS_SOME (lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> )
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED
