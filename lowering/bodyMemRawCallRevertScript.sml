(* Counted memory path for the exempt revert-forwarding pair. *)
Theory bodyMemRawCallRevert
Ancestors
  fragGasPathMem fragExecMem fragExec gasCount unitTransformDefs
  exprSimRawCallCalldata loweringHalt emitHelper compileEnv
  venomExecSemantics venomExecProofs venomInstProofs venomState venomInst

Theorem revert_pair_counted_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst cid RETURNDATACOPY [dst;Lit 0w;sz] []) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst rid REVERT [dst;sz] []) /\
  step_inst_base (mk_inst cid RETURNDATACOPY [dst;Lit 0w;sz] []) s = OK u /\
  step_inst_base (mk_inst rid REVERT [dst;sz] [])
    (u with vs_inst_idx := SUC s.vs_inst_idx) = Abort Revert_abort t ==>
  gas_path_mem ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `revert_forward_at bb s.vs_inst_idx /\
   revert_forward_at bb (SUC s.vs_inst_idx)` by
    (drule_all revert_forward_pair_adjacent >> simp[]) >>
  `step_inst 0 ctx (mk_inst cid RETURNDATACOPY [dst;Lit 0w;sz] []) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (drule step_preserves_halted >>
     drule step_preserves_control_flow >> simp[mk_inst_def, is_terminator_def]) >>
  `gas_path_mem_edge ctx func s 0
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          is_terminator_def]) >>
  `gas_path_mem_edge ctx func
    (u with vs_inst_idx := SUC s.vs_inst_idx) 0 (Abort Revert_abort t)` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          exit_result_def]) >>
  metis_tac[gas_path_mem_rules, exit_result_def, arithmeticTheory.ADD]
QED
