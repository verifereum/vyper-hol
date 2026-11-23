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
  qpat_assum `fn_has_code a b f`
    (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  fs[create_operand_at_def, IS_PREFIX_APPEND] >>
  `isPREFIX (emitted_insts a b) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts a b)` by fs[EVERY_MEM] >>
  `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by metis_tac[] >>
  qspecl_then [`emitted_insts a b`,`s`,`u`,`bb`] mp_tac buffer_sequence_prefix >>
  simp[create_operand_full_scope_def]
QED
