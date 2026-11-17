(* Actual memory-write result safety at the cleared-gas suffix boundary. *)
Theory augAssignFullMemoryResultSafety
Ancestors
  stmtSimAugAssignPlaceMemory gasContext stmtSimDefs vyperState vyperInterpreter

Theorem augassign_memory_suffix_result_safe:
  gas_admissible
    (bind
      (lift_sum
        (evaluate_binop
          (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
          ptv bop cur rhs))
      (write_place cx (MemoryPlace id path)))
    (stmt_res_ok lctx) (ee with gas_obs := []) /\
  evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur rhs = INL v /\
  write_place cx (MemoryPlace id path) v ee = (res,ff) ==>
  stmt_res_ok lctx res
Proof
  strip_tac >>
  drule aug_place_memory_write_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >>
  fs[gas_admissible_def, bind_def, lift_sum_def, return_def] >>
  metis_tac[]
QED
