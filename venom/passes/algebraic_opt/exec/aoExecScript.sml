(*
 * Executable support for differential-testing the algebraic-optimization pass
 * against the Python compiler (see diff/ao_diff.py and aoDiffRunScript.sml).
 *
 * NOTE: cv_eval (the fast evaluator used by tests/) cannot run this pass:
 * dfg_build_function and range_analyze are built on finite_map, which
 * cv_compute does not support ("finite_map$fmap is not a datatype").
 * Plain EVAL (computeLib) does support finite maps, so the pass is executed
 * via EVAL.  ao_exec_example is a smoke test that EVAL fully reduces the pass.
 *)

Theory aoExec
Ancestors
  algebraicOptDefs venomInst venomState
Libs
  wordsLib

(* Zero every instruction id, so two functions can be compared modulo the
 * internal object-identity ids (which never reach bytecode and legitimately
 * differ between the HOL pass output and the Python serialization). *)
Definition strip_inst_ids_def:
  strip_inst_ids fn =
    fn with fn_blocks :=
      MAP (λbb. bb with bb_instructions :=
             MAP (λi. i with inst_id := 0) bb.bb_instructions) fn.fn_blocks
End

(* A tiny function exercising one peephole rule: or x (-1) -> assign (-1). *)
Definition ao_exec_test_fn_def:
  ao_exec_test_fn : ir_function = <|
    fn_name := "main";
    fn_blocks := [
      <| bb_label := "entry";
         bb_instructions := [
           <| inst_id := 0; inst_opcode := PARAM;
              inst_operands := []; inst_outputs := ["x"] |>;
           <| inst_id := 1; inst_opcode := OR;
              inst_operands := [Var "x"; Lit (0w - 1w)]; inst_outputs := ["y"] |>;
           <| inst_id := 2; inst_opcode := RETURN;
              inst_operands := [Lit (0w:bytes32); Var "y"]; inst_outputs := [] |>
         ] |>
    ] |>
End

Theorem ao_exec_example =
  EVAL “ao_transform_function ao_exec_test_fn”
