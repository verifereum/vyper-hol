(* First-exit and selected-cut facts for buffer-valued builtins. *)
Theory entryCreateBuiltinBufferCases
Ancestors
  entryCreateEffectFocus entryCreateAdminSequence
  createSizeCutCode abiEncoderProps exprSimHash builtinHashing context
  emitHelper emitHelperProps compileEnv exprLoweringProps fragExec
  entryCreateFocusSpec entryCreatePathScope entryCreateCompletedCut
  createSizePrefixReplay createMarkedPath fragGasOrigin fragGasSeqAbort gasEvents
  venomState venomInst venomInstProps venomExecSemantics venomExecProofs instIdxIndep
  list rich_list arithmetic relation

(* The suffix starts after the hash argument has been evaluated. In
   particular SHA's STATICCALL is not a Venom INVOKE. *)
Theorem create_hash_suffix_layout:
  (compile_keccak256_bytes x a = (op,b) \/
   compile_keccak256_bytesm x m a = (op,b) \/
   compile_sha256_bytes x a = (op,b) \/
   compile_sha256_bytesm x m a = (op,b)) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\
             i.inst_opcode <> CREATE2) (emitted_insts a b)
Proof
  strip_tac >>
  gvs[compile_keccak256_bytes_def, compile_keccak256_bytesm_def,
      compile_sha256_bytes_def, compile_sha256_bytesm_def,
      contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
      fresh_var_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[is_terminator_def, mk_inst_def, frag_ids_def]
QED

Theorem create_hash_suffix_cut:
  (compile_keccak256_bytes x a = (op,b) \/
   compile_keccak256_bytesm x m a = (op,b) \/
   compile_sha256_bytes x a = (op,b) \/
   compile_sha256_bytesm x m a = (op,b)) /\
  fn_has_code a b f /\ create_operand_at a s ==>
  create_operand_cut a b E C f tops cx st0 source (es,s)
Proof
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP create_hash_suffix_layout) strip_assume_tac) >>
  irule create_admin_sequence_cut >> fs[EVERY_MEM]
QED

Theorem buffer_straight_edge[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK u ==>
  gas_origin_edge F E C f s
    (if i.inst_opcode = GAS then [(f.fn_name,i.inst_id) IN E] else [])
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  `step_inst 0 C i s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  rewrite_tac[gas_origin_edge_def] >> simp[] >>
  qexists_tac `0` >>
  Cases_on `i.inst_opcode = GAS` >> simp[gas_events_step_def]
QED

Theorem buffer_sequence_prefix[local]:
  !code s u bb.
    ~s.vs_halted /\ lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK u ==>
    create_expr_prefix a b E C f s
      (MAP (\i. (f.fn_name,i.inst_id) IN E) (FILTER (\i. i.inst_opcode = GAS) code))
      (u with vs_inst_idx := LENGTH b.cs_current_insts) /\
    u.vs_current_bb = s.vs_current_bb
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base h s = OK v` >>
  drule_all buffer_straight_edge >> strip_tac >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
  qabbrev_tac `t = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  `create_prefix_step a b E C f s
     (if h.inst_opcode = GAS then [(f.fn_name,h.inst_id) IN E] else []) t` by
    (simp[create_prefix_step_def, Abbr `t`] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  `run_inst_seq code t = OK (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Abbr `t`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qpat_x_assum `!s u bb. _` (qspecl_then [`t`,`u with vs_inst_idx := SUC s.vs_inst_idx`,`bb`] mp_tac) >>
  simp[Abbr `t`, ADD_CLAUSES] >> strip_tac >>
  `create_expr_prefix a b E C f s
     (if h.inst_opcode = GAS then [(f.fn_name,h.inst_id) IN E] else [])
     (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     fs[create_marked_edge_def]) >>
  drule_all create_expr_prefix_append >>
  Cases_on `h.inst_opcode = GAS` >> simp[]
QED

Theorem buffer_layout_fetch[local]:
  fn_has_code a b f /\ create_operand_at a s /\
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b ==>
  LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts a b) /\
  ?bb. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts a b) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> qpat_assum `fn_has_code a b f`
    (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  fs[create_operand_at_def, IS_PREFIX_APPEND] >> qexists_tac `bb` >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[] >> metis_tac[]
QED

Theorem create_hash_suffix_success_scope:
  (compile_keccak256_bytes x a = (op,b) \/
   compile_keccak256_bytesm x m a = (op,b) \/
   compile_sha256_bytes x a = (op,b) \/
   compile_sha256_bytesm x m a = (op,b)) /\
  fn_has_code a b f /\ create_operand_at a s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts a b) s = OK u ==>
  create_operand_full_scope a b E C f s
    (MAP (\i. (f.fn_name,i.inst_id) IN E)
       (FILTER (\i. i.inst_opcode = GAS) (emitted_insts a b)))
    (OK (u with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP create_hash_suffix_layout) strip_assume_tac) >>
  drule_all buffer_layout_fetch >> strip_tac >>
  `EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts a b)` by fs[EVERY_MEM] >>
  qspecl_then [`emitted_insts a b`,`s`,`u`,`bb`] mp_tac buffer_sequence_prefix >>
  fs[create_operand_full_scope_def,create_operand_at_def]
QED

(* Matching the installed fetch and the actual step is enough here; an
   abort cannot complete a caller transition to the continuation. *)
Theorem buffer_origin_at_fetch[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  gas_origin_edge T E C f s ms r ==>
  ?u. step_inst_base i s = OK u /\ ~u.vs_halted /\
      u.vs_current_bb = s.vs_current_bb /\
      r = OK (u with vs_inst_idx := SUC s.vs_inst_idx) \/
      exit_result (step_inst_base i s) /\ r = step_inst_base i s
Proof
  simp[gas_origin_edge_def, step_inst_non_invoke] >> rpt strip_tac >>
  gvs[] >> metis_tac[step_preserves_control_flow, step_inst_non_invoke]
QED

Theorem buffer_origin_unchecked[local]:
  gas_origin_edge T E C f s marks r ==> gas_origin_edge F E C f s marks r
Proof
  simp[gas_origin_edge_def] >> metis_tac[]
QED

Theorem buffer_abort_scope_prepend[local]:
  create_prefix_step a b E C f s left t /\ exit_result r /\
  create_operand_full_scope a b E C f t right r ==>
  create_operand_full_scope a b E C f s (left ++ right) r
Proof
  strip_tac >>
  `create_expr_prefix a b E C f s left t` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def]) >>
  Cases_on `r` >> fs[create_operand_full_scope_def, exit_result_def] >>
  metis_tac[create_expr_prefix_append, APPEND_ASSOC]
QED

Theorem buffer_sequence_abort_scope[local]:
  !code s w bb marks r.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = Abort err w /\
    gas_origin_path T E C f s marks (Abort err r) ==>
    create_operand_full_scope a b E C f s marks (Abort err r)
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> drule instruction_prefix_cursor >> strip_tac >>
  fs[EVERY_DEF] >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
  qpat_x_assum `gas_origin_path _ _ _ _ _ _ _` mp_tac >>
  once_rewrite_tac[gas_origin_path_cases] >> simp[] >> strip_tac
  >- (drule_all buffer_origin_at_fetch >> simp[exit_result_def] >>
      disch_then (qx_choose_then `u` strip_assume_tac)
      >~ [`exit_result (step_inst_base h s)`]
      >- (qpat_x_assum `OK _ = step_inst_base h s` (assume_tac o SYM) >>
          fs[exit_result_def]) >>
      gvs[] >> `create_prefix_step a b E C f s left (u with vs_inst_idx := SUC s.vs_inst_idx)` by
        (simp[create_prefix_step_def] >> metis_tac[buffer_origin_unchecked]) >>
      irule buffer_abort_scope_prepend >> simp[exit_result_def] >>
      first_assum (irule_at Any) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      qpat_assum `!s w bb marks r. _` irule >>
      gvs[run_inst_seq_def, run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES] >>
      metis_tac[]) >>
  irule (SIMP_RULE (srw_ss()) [APPEND] (Q.INST [`left` |-> `[]`]
    create_operand_full_scope_terminal)) >>
  simp[exit_result_def] >> qexists_tac `s` >> simp[] >> decide_tac
QED

(* The exact same marked abort witness supplied by the checked SHA run
   remains within the installed suffix. The abstract path alone does not
   imply this: run_inst_seq certifies an abort before the end of the slice. *)
Theorem create_hash_suffix_abort_scope:
  (compile_sha256_bytes x a = (op,b) \/
   compile_sha256_bytesm x m a = (op,b)) /\
  fn_has_code a b f /\ create_operand_at a s /\
  run_inst_seq (emitted_insts a b) s = Abort err w /\
  gas_origin_path T E C f s marks (Abort err r) ==>
  create_operand_full_scope a b E C f s marks (Abort err r)
Proof
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> strip_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts a b)` by
    (mp_tac (Q.INST [`m` |-> `m`, `op` |-> `op`, `x` |-> `x`]
        create_hash_suffix_layout) >> simp[EVERY_MEM]) >>
  drule_all buffer_layout_fetch >> strip_tac >>
  irule buffer_sequence_abort_scope >>
  qpat_assum `run_inst_seq _ _ = Abort _ _` (irule_at Any) >>
  qexists_tac `bb` >> simp[]
QED
