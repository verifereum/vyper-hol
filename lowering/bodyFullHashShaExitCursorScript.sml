(* Recover the failing instruction of the already executed SHA suffix. *)
Theory bodyFullHashShaExitCursor
Ancestors
  builtinHashing context emitHelper compileEnv exprLoweringProps
  fragGasSeqAbort fragGasOriginPtrExec createSizeExit fragGasPath
  venomExecSemantics venomInstProofs venomState venomInst fragExec instIdxIndep
  arithmetic list rich_list

Theorem sha_exhalt_step_cursor[local]:
  MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD;GAS;STATICCALL;ASSERT] /\
  step_inst_base i s = Abort ExHalt_abort t ==>
  i.inst_opcode = STATICCALL /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  simp[] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_alloca_def, exec_pure2_def,
    exec_read1_def, exec_write2_def, exec_gas_def, exec_ext_call_def,
    AllCaseEqs(), halt_state_def, set_returndata_def]
QED

Theorem sha_emitted_exit_opcodes[local]:
  (compile_sha256_bytes value sa = (op,sb) \/
   (?m. compile_sha256_bytesm value m sa = (op,sb))) ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD;GAS;STATICCALL;ASSERT])
    (emitted_insts sa sb)
Proof
  strip_tac >>
  gvs[compile_sha256_bytes_def, compile_sha256_bytesm_def,
      compile_alloc_buffer_def, emit_op_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  gvs[emitted_insts_def, APPEND_ASSOC, mk_inst_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem sha_suffix_straight_opcode[local]:
  MEM op [ALLOCA;MSTORE;MLOAD;ADD;GAS;STATICCALL;ASSERT] ==>
  op <> INVOKE /\ ~is_terminator op
Proof
  simp[] >> strip_tac >> gvs[is_terminator_def]
QED

Theorem sha_seq_exhalt_cursor[local]:
  !code s t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD;GAS;STATICCALL;ASSERT]) code /\
    run_inst_seq code s = Abort ExHalt_abort t ==>
    ?j i. run_from 0 ctx fn s = Abort ExHalt_abort (t with vs_inst_idx := j) /\
      lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb j = SOME i /\ i.inst_opcode = STATICCALL
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule instruction_prefix_cursor >> strip_tac >>
  qpat_x_assum `EVERY _ (h::code)` (strip_assume_tac o BETA_RULE o REWRITE_RULE [EVERY_DEF]) >>
  drule sha_suffix_straight_opcode >> strip_tac >>
  qpat_x_assum `run_inst_seq (h::code) s = _` mp_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac
  >- (rename1 `step_inst_base h s = OK u` >>
      `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `u.vs_current_bb = s.vs_current_bb` by (drule_all step_preserves_control_flow >> simp[]) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by
        (simp[EVERY_MEM] >> rpt strip_tac >>
         qpat_assum `EVERY _ code` (drule_then assume_tac o
           BETA_RULE o REWRITE_RULE [EVERY_MEM]) >>
         drule sha_suffix_straight_opcode >> simp[]) >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >>
      strip_tac >> qexistsl_tac [`j`,`i`] >> simp[] >>
      drule_all run_from_step >> simp[]) >>
  rename1 `step_inst_base h s = Abort reason u` >>
  qpat_x_assum `reason = ExHalt_abort` SUBST_ALL_TAC >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  drule_all sha_exhalt_step_cursor >> strip_tac >>
  qexistsl_tac [`t.vs_inst_idx`,`h`] >> simp[run_from_def] >>
  `step_inst 0 ctx h s = Abort ExHalt_abort t` by simp[step_inst_non_invoke] >>
  drule_all exec_block_step_abort >> simp[]
QED

Theorem sha_exhalt_path_exit_size[local]:
  (compile_sha256_bytes value sa = (op,sb) \/
   (?m. compile_sha256_bytesm value m sa = (op,sb))) /\
  MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = Abort ExHalt_abort t /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks
    (Abort ExHalt_abort (t with vs_inst_idx := j),G',tn') ==>
  create_size_exit_ok ctx res (Abort ExHalt_abort (t with vs_inst_idx := j))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule sha_emitted_exit_opcodes >> strip_tac >>
  drule_all sha_seq_exhalt_cursor >>
  disch_then (qspec_then `ctx` (qx_choosel_then [`k`,`i`] strip_assume_tac)) >>
  drule gas_origin_ptr_path_exec >> simp[exit_result_def] >>
  disch_then (qx_choose_then `fuel` strip_assume_tac) >>
  (* Both derivations execute the same starting state, so their cursors agree. *)
  `run_from fuel ctx fn s = Abort ExHalt_abort (t with vs_inst_idx := k)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `0` >> simp[]) >>
  `j = k` by
    (qpat_assum `run_from fuel ctx fn s = Abort ExHalt_abort (t with vs_inst_idx := k)` mp_tac >>
     qpat_assum `run_from fuel ctx fn s = Abort ExHalt_abort (t with vs_inst_idx := j)`
       (fn th => rewrite_tac[th]) >> simp[] >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_inst_idx`) >> simp[]) >>
  qpat_x_assum `j = k` SUBST_ALL_TAC >>
  simp[create_size_exit_ok_def] >> strip_tac >>
  `~oversized_create_abort ctx (Abort ExHalt_abort (t with vs_inst_idx := k))` by
    (irule oversized_create_abort_non_create_cursor >>
     simp[] >> qexistsl_tac [`bb`,`fn`,`i`] >> simp[]) >>
  fs[]
QED

Theorem sha_abort_path_exit_size:
  (compile_sha256_bytes value sa = (op,sb) \/
   (?m. compile_sha256_bytesm value m sa = (op,sb))) /\
  MEM fn ctx.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s =
    Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort) t /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks
    (Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort)
      (t with vs_inst_idx := j),G',tn') ==>
  create_size_exit_ok ctx res
    (Abort (if s.vs_outcomes = [] then ExHalt_abort else Revert_abort)
      (t with vs_inst_idx := j))
Proof
  Cases_on `s.vs_outcomes = []` >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all sha_exhalt_path_exit_size >> simp[]
QED
