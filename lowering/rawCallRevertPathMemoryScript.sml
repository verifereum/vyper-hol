(* Counted execution of the exempt revert-forwarding pair. *)
Theory rawCallRevertPathMemory
Ancestors
  bodyMemRawCallRevert fragGasPathMem fragExecMem fragExec gasCount unitTransformDefs
  exprSimRawCallCalldata loweringHalt emitHelper compileEnv
  venomExecSemantics venomExecProofs venomInstProofs venomState venomInst

Theorem revert_pair_counted_path[local]:
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

Theorem raw_call_failure_tail_counted_mem:
  emit_void RETURNDATACOPY [dst;Lit 0w;sz] sa = ((),sb) /\
  emit_inst REVERT [dst;sz] [] sb = ((),sc) /\
  eval_operand dst s = SOME addr /\
  eval_operand sz s = SOME (n2w (LENGTH s.vs_returndata)) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  fn_has_code sa sc func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (Abort Revert_abort t) /\
      t.vs_returndata = s.vs_returndata
Proof
  strip_tac >>
  `sc.cs_current_bb = sa.cs_current_bb /\
   sc.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id RETURNDATACOPY [dst;Lit 0w;sz] [];
      mk_inst sb.cs_next_id REVERT [dst;sz] []]` by
    (gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
         emit_def, comp_ignore_bind_def, comp_return_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
      (mk_inst sa.cs_next_id RETURNDATACOPY [dst;Lit 0w;sz] []) /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME
      (mk_inst sb.cs_next_id REVERT [dst;sz] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       qspec_then `0` mp_tac th >> qspec_then `1` mp_tac th) >>
     simp[arithmeticTheory.ADD1]) >>
  qexists_tac `revert_state (set_returndata s.vs_returndata
    (write_memory_with_expansion (w2n addr) s.vs_returndata s with
      vs_inst_idx := SUC s.vs_inst_idx))` >>
  reverse conj_tac >- simp[revert_state_def, set_returndata_def] >>
  irule revert_pair_counted_path >> simp[] >>
  qexistsl_tac [`sa.cs_next_id`, `dst`, `sb.cs_next_id`, `sz`,
    `write_memory_with_expansion (w2n addr) s.vs_returndata s`] >>
  simp[] >>
  conj_tac >- (irule (cj 1 raw_call_revert_copy) >> simp[]) >>
  qspec_then `s with vs_inst_idx := SUC s.vs_inst_idx` mp_tac
    (cj 2 raw_call_revert_copy) >>
  simp[write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  Cases_on `dst` >> Cases_on `sz` >>
  gvs[eval_operand_def, lookup_var_def]
QED
