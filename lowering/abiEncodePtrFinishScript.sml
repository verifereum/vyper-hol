(* Pointer boundary for the length-store phase, from a supplied body endpoint. *)
Theory abiEncodePtrFinish
Ancestors
  exprSimAbiEncodeConcreteBuiltinWrappers abiBuiltinEncodeCode
  bodyPtrAttributeAdd exprSimPtrTopLevelImmutableCopy typedCopyPtr wordLoadStorePtr
  fragGasSeqPtr bodyPtrBopEntry bodyPtrDefs ptrDiscipline
  exprLoweringProps emitHelper emitHelperProps compileEnv context
  venomExecSemantics venomInstProofs venomInst venomState finite_map words
  list rich_list arithmetic abiDecoderReentry abiDecoderContract
  decoderGhostFramePtr loweringStateRelDefs ghostPcTransportPtr instIdxIndep
  exprSimAbiEncodeFramedBuiltin abiEncoderExtendSim

Theorem abi_encode_finish_ptr_sequence[local]:
  abi_builtin_encode_finish (Var x) encoded_len mid_size st = ((),final) /\
  run_inst_seq (emitted_insts st final) s = OK raw /\
  eval_operand (Var x) s = SOME (n2w p) /\
  eval_operand encoded_len s = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var (Var x) /\
  ptr_covers G tn x s outsz /\ 32 <= outsz /\ p < dimword (:256) /\
  op_taint tn encoded_len = {} /\ ~ctx_has_dalloca ctx ==>
  ?H tf.
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st final) s H tf /\
    ptr_covers H tf x raw outsz /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint tf (Var y) = op_taint tn (Var y)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {i | p <= i /\ i < p+32}
Proof
  Cases_on `mid_size > 0` >>
  simp[abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[] >>
  fs[emitted_insts_def] >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
  >- suspend "add_store"
  >> suspend "store"
QED

Resume abi_encode_finish_ptr_sequence[store]:
  `step_inst_base (mk_inst st.cs_next_id MSTORE [Var x;encoded_len] []) s =
    OK (mstore p (n2w len) s)` by
    (drule_all (Q.SPECL [`Var x`, `encoded_len`] step_MSTORE) >> simp[w2n_n2w]) >>
  gvs[run_inst_seq_def] >> fs[eval_operand_def] >>
  drule_all toplevel_immutable_mstore_ghost_frame >>
  disch_then (qspecl_then [`st.cs_next_id`, `PG`, `G`] assume_tac) >>
  `ptr_covers G tn x s 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  gvs[w2n_n2w, LESS_MOD] >>
  simp[inst_seq_ptr_def, fragExecPtrTheory.ptr_inst_ok_mstore, w2n_n2w] >>
  gvs[ptr_covers_def, mstore_def, lookup_var_def, op_taint_def, w2n_n2w, LESS_MOD]
QED

Resume abi_encode_finish_ptr_sequence[add_store]:
  qmatch_goalsub_abbrev_tac `mk_inst _ ADD _ [dst]` >>
  `x <> dst` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, Abbr `dst`] >> metis_tac[LESS_EQ_REFL]) >>
  `step_inst_base (mk_inst st.cs_next_id ADD [encoded_len; Lit (n2w mid_size)] [dst]) s =
    OK (update_var dst (n2w len + n2w mid_size) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  qabbrev_tac `u = update_var dst (n2w len + n2w mid_size) s` >>
  qabbrev_tac `H = step_prov PG G (mk_inst st.cs_next_id ADD
    [encoded_len; Lit (n2w mid_size)] [dst]) u` >>
  qabbrev_tac `tm = step_taint (mk_inst st.cs_next_id ADD
    [encoded_len; Lit (n2w mid_size)] [dst]) s u tn` >>
  `op_taint tm (Var dst) = {} /\ tm.t_mem = tn.t_mem /\
   tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
   (!y. y <> dst ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint tm (Var y) = op_taint tn (Var y))` by
    (simp[Abbr `H`, Abbr `tm`, Abbr `u`, copy_len_binop_ghost_frame]) >>
  `tm.t_imm = tn.t_imm` by
    (simp[Abbr `tm`] >> irule (cj 3 step_taint_nonmemory_frame) >> simp[mk_inst_def]) >>
  `lookup_var x u = SOME (n2w p) /\
   eval_operand (Var dst) u = SOME (n2w len + n2w mid_size)` by
    fs[Abbr `u`, lookup_var_def, update_var_def, eval_operand_def, FLOOKUP_UPDATE] >>
  `ptr_covers H tm x u outsz` by
    (gvs[ptr_covers_def, Abbr `u`, lookup_var_def, update_var_def,
      eval_operand_def, FLOOKUP_UPDATE, w2n_n2w, LESS_MOD] >> metis_tac[]) >>
  `ptr_covers H tm x u 32` by (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `step_inst_base (mk_inst (st.cs_next_id+1) MSTORE [Var x;Var dst] []) u =
    OK (mstore p (n2w len + n2w mid_size) u)` by
    (`eval_operand (Var x) u = SOME (n2w p)` by simp[eval_operand_def] >>
     mp_tac (Q.SPECL [`Var x`, `Var dst`] step_MSTORE) >>
     disch_then (qspecl_then [`n2w p`, `n2w len + n2w mid_size`,
       `st.cs_next_id+1`, `u`] mp_tac) >> simp[w2n_n2w]) >>
  gvs[run_inst_seq_def, GSYM markerTheory.Abbrev_def] >>
  drule_all toplevel_immutable_mstore_ghost_frame >>
  disch_then (qspecl_then [`st.cs_next_id+1`, `PG`, `H`] assume_tac) >>
  gvs[w2n_n2w, LESS_MOD] >>
  qexistsl [`H`, `tm with t_mem := tm.t_mem DIFF {i | p <= i /\ i < p+32}`] >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst st.cs_next_id ADD [encoded_len; Lit (n2w mid_size)] [dst]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base (mk_inst (st.cs_next_id+1) MSTORE [Var x;Var dst] [])
     (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK ((mstore p (n2w len + n2w mid_size) u) with vs_inst_idx := SUC s.vs_inst_idx)` by
    (`~is_terminator (mk_inst (st.cs_next_id+1) MSTORE [Var x;Var dst] []).inst_opcode` by
       simp[mk_inst_def, is_terminator_def] >>
     simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
  simp[inst_seq_ptr_def, fragExecPtrTheory.ptr_inst_ok_mstore, w2n_n2w] >>
  conj_tac
  >- (gvs[ptr_covers_def, mstore_def, lookup_var_def, op_taint_def]) >>
  rpt strip_tac >>
  `y <> dst` by
    (gvs[not_fresh_at_def, Abbr `dst`] >> metis_tac[LESS_EQ_REFL]) >>
  qpat_x_assum `!y. y <> dst ==> _` (qspec_then `y` mp_tac) >>
  simp[op_taint_def]
QED

Finalise abi_encode_finish_ptr_sequence

Theorem abi_encode_finish_ptr_from_body_semantic:
  abi_builtin_encode_finish (Var x) encoded_len mid_size st = ((),final) /\
  fn_has_code st final func /\
  eval_operand (Var x) encoded = SOME (n2w p) /\
  eval_operand encoded_len encoded = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var (Var x) /\
  p < dimword (:256) /\ ~encoded.vs_halted /\
  encoded.vs_current_bb = st.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH st.cs_current_insts /\
  mem_bytes_at (p+32) (mid_size+len) encoded.vs_memory = bytes /\
  window_strong_result ctx func body_st body_end out at av d initial encoded /\
  ptr_covers G tn x encoded outsz /\ 32 <= outsz /\
  op_taint tn encoded_len = {} /\ ~ctx_has_dalloca ctx ==>
  ?actual H tf.
    eval_operand (Var x) actual = SOME (n2w p) /\
    mload p actual = n2w (len+mid_size) /\
    mem_bytes_at (p+32) (mid_size+len) actual.vs_memory = bytes /\
    abi_decode_frame p 32 encoded actual /\
    abi_encoder_registered_effect {} [(p,32)] encoded actual /\
    actual.vs_allocas = encoded.vs_allocas /\
    actual.vs_alloca_next = encoded.vs_alloca_next /\
    window_alloca_growth initial actual /\ actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect
      (window_alloca_sites func (frag_ids body_st body_end))
      [(p,32);(d,LENGTH (enc at av))] initial actual /\
    (!i b sz. i IN window_alloca_sites func (frag_ids body_st body_end) /\
      FLOOKUP actual.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op encoded = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual /\
    gas_path_ptr D 0 ctx func PG G tn encoded 0 H tf (OK actual) /\
    ptr_covers H tf x actual outsz /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint tf (Var y) = op_taint tn (Var y)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {i | p <= i /\ i < p+32} /\
    abi_encode_exec_frame func encoded actual /\
    abi_encoder_extend_sim ctx func encoded actual
Proof
  strip_tac >>
  drule_all abi_encode_window_finish_concrete >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_finish_ptr_sequence >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  `abi_encode_exec_frame func encoded raw` by
    (irule abi_encode_framed_finish_sequence >>
     fs[] >> metis_tac[]) >>
  `abi_encoder_extend_sim ctx func encoded
     (raw with vs_inst_idx := LENGTH final.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     simp[] >> qexists_tac `st` >> simp[]) >>
  `?bb. lookup_block encoded.vs_current_bb func.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts st final) (DROP encoded.vs_inst_idx bb.bb_instructions)` by
    (fs[fragExecTheory.fn_has_code_def, inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st final)) = 0` by
    (qpat_x_assum `abi_builtin_encode_finish _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `mid_size > 0` >>
     simp[abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, mk_inst_def]) >>
  `encoded.vs_inst_idx + LENGTH (emitted_insts st final) = LENGTH final.cs_current_insts` by
    (fs[inst_extends_def, emitted_insts_def] >>
     qpat_x_assum `final.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qpat_x_assum `encoded.vs_inst_idx = _` kall_tac >>
  qexistsl [`raw with vs_inst_idx := LENGTH final.cs_current_insts`, `H`, `tf`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `ptr_covers H tf x raw outsz` mp_tac >>
  simp_tac (srw_ss()) [ptr_covers_def, lookup_var_def] >>
  metis_tac[]
QED

(* Compatibility projection: the finite pointer execution is proved only above. *)
Theorem abi_encode_finish_ptr_from_body:
  abi_builtin_encode_finish (Var x) encoded_len mid_size st = ((),final) /\
  fn_has_code st final func /\
  eval_operand (Var x) encoded = SOME (n2w p) /\
  eval_operand encoded_len encoded = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var (Var x) /\
  p < dimword (:256) /\ ~encoded.vs_halted /\
  encoded.vs_current_bb = st.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH st.cs_current_insts /\
  mem_bytes_at (p+32) (mid_size+len) encoded.vs_memory = bytes /\
  window_strong_result ctx func body_st body_end out at av d initial encoded /\
  ptr_covers G tn x encoded outsz /\ 32 <= outsz /\
  op_taint tn encoded_len = {} /\ ~ctx_has_dalloca ctx ==>
  ?actual H tf.
    eval_operand (Var x) actual = SOME (n2w p) /\
    mload p actual = n2w (len+mid_size) /\
    mem_bytes_at (p+32) (mid_size+len) actual.vs_memory = bytes /\
    abi_decode_frame p 32 encoded actual /\
    abi_encoder_registered_effect {} [(p,32)] encoded actual /\
    actual.vs_allocas = encoded.vs_allocas /\
    actual.vs_alloca_next = encoded.vs_alloca_next /\
    window_alloca_growth initial actual /\ actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect
      (window_alloca_sites func (frag_ids body_st body_end))
      [(p,32);(d,LENGTH (enc at av))] initial actual /\
    (!i b sz. i IN window_alloca_sites func (frag_ids body_st body_end) /\
      FLOOKUP actual.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op encoded = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual /\
    gas_path_ptr D 0 ctx func PG G tn encoded 0 H tf (OK actual) /\
    ptr_covers H tf x actual outsz /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint tf (Var y) = op_taint tn (Var y)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {i | p <= i /\ i < p+32}
Proof
  strip_tac >> drule_all abi_encode_finish_ptr_from_body_semantic >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`actual`, `H`, `tf`] >> asm_rewrite_tac[]
QED
