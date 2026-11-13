(* Joint entry rejection, independent of successful-body correctness. *)
Theory loweringCalldataRevert
Ancestors
  vyperCalldata calldataExact e2eDefs vyperLoweringCorrect
  sourceUnitExecution

(* S1, calldata that dispatches to nothing: no fallback, a short head, or a
   failed decode.  The entry reverts with empty returndata before any
   function body runs, reading no GAS on the way (zero-mark memory and
   pointer paths from __entry), and every run from __entry is pointer safe. *)
(* supported_program excludes default arguments, so the dispatcher is linear.
   A missing selector enters REVERT 0 0; a short head fails the size ASSERT;
   a rejected argument fails its pointer guard or CALLDATALOAD decoder.
   Earlier arguments may already have allocated and decoded: their pointer
   provenance and access bounds must reach the failing decoder. The success
   arm alone cannot establish that path. Entry code reads no GAS or INVOKE,
   so its memory and pointer paths have zero marks. Choose their common
   endpoint and ghost before D; derive the run and all-fuel safety there.
   emit_abort_origin_ptr already covers the terminal fallback instruction. *)
Theorem lower_vyper_runtime_unit_reverts:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs
    ==>
    ?func s G' tn'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>) 0 G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
                  (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                              vs_inst_idx := 0 |>))
Proof
  (* HELD ADMISSION SEQ-4940: S1 revert on a NONE dispatch; needs the selector-miss and decode-failure entry runs *)
  cheat
QED
