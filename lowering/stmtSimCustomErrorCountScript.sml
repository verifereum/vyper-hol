(* Local execution regions certify that memory-safe paths observe no GAS. *)
Theory stmtSimCustomErrorCount
Ancestors
  fragGasPathMem runFromGasPathMem gasCount fragExec venomExecSemantics
  venomInst venomState arithmetic

Theorem custom_error_region_edge_zero[local]:
  (!u bb inst. R u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst ==>
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE) /\
  R s /\ gas_path_mem_edge ctx fn s n r ==> n = 0
Proof
  rw[gas_path_mem_edge_def] >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by metis_tac[] >>
  simp[gas_count_step_def]
QED

Theorem custom_error_region_count_zero:
  !ctx fn s n r. gas_path_mem ctx fn s n r ==>
  !R. (!u bb inst. R u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst ==>
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE) /\
  (!u k v. R u /\ gas_path_mem_edge ctx fn u k (OK v) ==> R v) /\
  R s ==> n = 0
Proof
  ho_match_mp_tac gas_path_mem_ind >>
  rpt strip_tac >>
  metis_tac[custom_error_region_edge_zero, ADD_0]
QED

Theorem custom_error_region_safe_exit:
  (!u bb inst. R u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst ==>
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE) /\
  (!u k v. R u /\ gas_path_mem_edge ctx fn u k (OK v) ==> R v) /\
  R s /\ run_from fuel ctx fn s = r /\ exit_result r /\
  mem_safe_run fuel ctx fn s /\ ~s.vs_halted ==>
  gas_path_mem ctx fn s 0 r
Proof
  strip_tac >> drule_all run_from_gas_path_mem >> strip_tac >>
  `n = 0` by metis_tac[custom_error_region_count_zero] >> gvs[]
QED
