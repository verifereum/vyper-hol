Theory bodyPtrPrecompileBuiltinsRecoveryResidual
Ancestors bodyPtrPrecompileBuiltinsRecoveryRun bodyPtrPrecompileBuiltinsRecoveryFrame
          bodyPtrPrecompileBuiltinsFramedContinuation bodyPtrPrecompileBuiltinsRecoveryValue
          bodyPtrPrecompileBuiltinsRecoveryContinuation
          bodyPtrPrecompileBuiltinsCompilerStages bodyPtrPrecompileBuiltinsRunAllocation
          stmtSimDeclPath valueEncodingProps venomExecSemantics venomInst venomState
          compileEnv loweringStateRelDefs emitHelper exprLoweringProps rich_list emitHelperProps fragGasSeqPtr fragGasPathPtr entrySinkExtraction
          bodyPtrPrecompileBuiltinsPrefixFrames bodyPtrPrecompileBuiltinsBounds
          exprSimPtrLiteralBuffer ghostPcTransportPtr venomCallOracleDefs extCallOracle
          exprSimWordArgs wordArgsPtr loweringPosts exprSimProps bodyPtrDefs

(* Transport through ALLOCA is purely ordinary memory transport, independent
   of the provenance assigned to the newly allocated variable. *)
Theorem emitted_allocation_memory:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_memory = s.vs_memory
Proof
  strip_tac >> drule_all emitted_allocation_step >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  metis_tac[exec_alloca_memory]
QED

Theorem recovery_input_after_zero:
  compile_alloc_buffer 32 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  s4 = mstore (w2n c) 0w s3 /\
  regions_disjoint (w2n b) 128 (w2n c) 32 /\
  mem_bytes_at (w2n b) 128 s2.vs_memory = bytes ==>
  mem_bytes_at (w2n b) 128 s4.vs_memory = bytes
Proof
  strip_tac >> drule_all emitted_allocation_memory >> strip_tac >>
  gvs[regions_disjoint_def] >>
  metis_tac[mstore_mem_bytes_at_disjoint]
QED

Theorem recovery_payload_group:
  emit_void MSTORE [buf; h] sa = ((),s0) /\
  (do dst <- emit_op ADD [buf; Lit 32w];
      emit_void MSTORE [dst; v] od) s0 = ((),s1) /\
  (do dst <- emit_op ADD [buf; Lit 64w];
      emit_void MSTORE [dst; r] od) s1 = ((),s2) /\
  (do dst <- emit_op ADD [buf; Lit 96w];
      emit_void MSTORE [dst; q] od) s2 = ((),sp) ==>
  (do emit_void MSTORE [buf; h];
      p1 <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [buf; Lit 64w]; emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [buf; Lit 96w]; emit_void MSTORE [p3; q] od)
    sa = ((),sp)
Proof
  simp[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

(* The input site's registration, not an allocation-growth bound, separates
   it from the output even when the allocator reuses a site. *)
Theorem recovery_registered_input_transport:
  compile_alloc_buffer 32 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s2 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sp /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  eval_operand ob.buf_operand s3 = SOME c /\
  FLOOKUP s2.vs_allocas aid = SOME (w2n b,128) /\ aid < sp.cs_next_id /\
  s4 = mstore (w2n c) 0w s3 /\
  mem_bytes_at (w2n b) 128 s2.vs_memory = bytes ==>
  mem_bytes_at (w2n b) 128 s4.vs_memory = bytes
Proof
  strip_tac >>
  `32 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  drule_all exprSimLiteralBufferTheory.alloc_buffer_frame_run >> strip_tac >>
  gvs[] >>
  `regions_disjoint (w2n c) 32 (w2n b) 128` by metis_tac[] >>
  qpat_x_assum `s3.vs_memory = s2.vs_memory`
    (fn th => rewrite_tac[GSYM th]) >>
  irule mstore_mem_bytes_at_disjoint >>
  gvs[regions_disjoint_def] >> decide_tac
QED

Theorem recovery_payload_opcodes:
  (do emit_void MSTORE [buf; h];
      p1 <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [buf; Lit 64w]; emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [buf; Lit 96w]; emit_void MSTORE [p3; q] od)
    sa = ((),sp) ==>
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sa sp)
Proof
  simp[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_APPEND1, mk_inst_def]
QED

Theorem recovery_framed_input:
  compile_ecrecover h v r q sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand q s = SOME wq /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!p. x = Var p ==> not_fresh_at sf p)) [h;v;r;q] ==>
  ?sz src dst t Gf tnf b c.
    comp_bind
      (do gas <- emit_op GAS [];
          success <- emit_op STATICCALL
            [gas; Lit 1w; Var src; Lit 128w; Var dst; Lit 32w];
          emit_void ASSERT [success]; return (Var dst) od)
      (\out. emit_op MLOAD [out]) sz = (res,sb) /\
    emitted_insts sf sb = emitted_insts sf sz ++ emitted_insts sz sb /\
    run_inst_seq (emitted_insts sf sz) s = OK t /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
      i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sf sz) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sf sz)
      (s with vs_inst_idx := k) Gf tnf) /\
    not_fresh_at sz src /\ not_fresh_at sz dst /\
    sf.cs_next_var <= sz.cs_next_var /\ sf.cs_next_id <= sz.cs_next_id /\
    local_ptrs_reserved cenv sz /\
    lookup_var src t = SOME b /\ lookup_var dst t = SOME c /\
    ptr_covers Gf tnf src t 128 /\ ptr_covers Gf tnf dst t 32 /\
    (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN tnf.t_mem) /\
    (!i. w2n c <= i /\ i < w2n c + 32 ==> i NOTIN tnf.t_mem) /\
    mem_bytes_at (w2n b) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes wq T /\
    mem_word_at (w2n c) t.vs_memory = 0w /\
    stmt_state_rel ctx fn cenv cx es t /\ wb_frame cenv es sf s t /\
    ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sf G tn s Gf tnf /\
    (!name lo len. local_region cenv es.scopes t name lo len ==>
       regions_disjoint (w2n c) 32 lo len) /\
    (!aid lo len. aid < sf.cs_next_id /\
       FLOOKUP t.vs_allocas aid = SOME (lo,len) ==>
       regions_disjoint (w2n c) 32 lo len) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
       regions_disjoint (w2n c) 32 off (type_memory_size tv))
Proof
  strip_tac >> drule recovery_compiler_stages >> strip_tac >>
  `sa.cs_next_var <= sp.cs_next_var` by simp[] >>
  drule_all allocated_stage_frame >> strip_tac >>
  drule_all recovery_payload_group >> strip_tac >>
  `!x. MEM (Var x) [h;v;r;q] ==> not_fresh_at sf x` by
    (gvs[listTheory.EVERY_DEF, listTheory.MEM] >> metis_tac[]) >>
  drule_all recovery_prefix_runtime >> strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s /\
   local_ptrs_rel fn cenv es.scopes s2'` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_assum `ib.buf_operand = _` (fn ei =>
    qpat_assum `ob.buf_operand = _` (fn eo =>
      map_every (fn pat => qpat_assum pat
        (fn th => assume_tac (REWRITE_RULE [ei,eo] th)))
        [`_ sa = ((),s0)`, `_ s0 = ((),s1)`, `_ s1 = ((),s2)`,
         `_ s2 = ((),sp)`, `_ so = ((),sm)`, `_ sm = (res,sb)`])) >>
  drule_all recovery_prefix_framed >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "transport"
QED

Resume recovery_framed_input[transport]:
  `FLOOKUP s2'.vs_allocas sf.cs_next_id = SOME (w2n b,128)` by
    (`128 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
     qpat_assum `stmt_state_rel ctx fn cenv cx es s`
       (mp_then Any (drule_all_then strip_assume_tac)
         exprSimLiteralBufferTheory.alloc_buffer_frame_run) >> gvs[]) >>
  `sf.cs_next_id < sp.cs_next_id` by (simp[] >> decide_tac) >>
  drule_all recovery_registered_input_transport >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists `so` >> simp[]) >>
  `not_fresh_at sm x /\ not_fresh_at sm x'` by
    gvs[not_fresh_at_def] >>
  `sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id` by
    (simp[] >> decide_tac) >>
  suspend "pack"
QED

Resume recovery_framed_input[pack]:
  drule direct_store_compiler_shape >> strip_tac >>
  `so.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf so` by
    (qpat_assum `compile_alloc_buffer 128 sf = _`
       (mp_then Any strip_assume_tac loweringHaltTheory.compile_alloc_buffer_insts) >>
     qpat_assum `compile_alloc_buffer 32 sp = _`
       (mp_then Any strip_assume_tac loweringHaltTheory.compile_alloc_buffer_insts) >>
     imp_res_tac bodyPtrPrecompileBuiltinsAllocationFrameTheory.emitted_allocation_singleton >>
     gvs[listTheory.APPEND_ASSOC]) >>
  `emitted_insts sf sm = emitted_insts sf so ++ emitted_insts so sm` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq (emitted_insts sf sm) s = OK s4` by
    (qpat_assum `run_inst_seq (emitted_insts sf sa) s = OK _`
       (mp_then Any assume_tac run_inst_seq_append) >>
     qpat_assum `run_inst_seq (emitted_insts sa sp) _ = OK _`
       (mp_then Any assume_tac run_inst_seq_append) >>
     qpat_assum `run_inst_seq (emitted_insts sp so) _ = OK _`
       (mp_then Any assume_tac run_inst_seq_append) >>
     asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC]) >>
  drule recovery_payload_opcodes >> strip_tac >>
  imp_res_tac bodyPtrPrecompileBuiltinsAllocationFrameTheory.emitted_allocation_singleton >>
  qpat_assum `emit_void MSTORE [_; Lit 0w] so = _`
    (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_void) >>
  `EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sf sm)` by
    simp[mk_inst_def] >>
  drule computed_load_suffix_compiler_shape >> strip_tac >>
  qexistsl [`sm`,`x`,`x'`,`s4`,`Gf`,`tnf`,`b`,`c`] >>
  gvs[] >> conj_tac
  >- (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise recovery_framed_input

(* Staging has no gas observations.  The counted endpoint uses the original
   instruction cursor, while the ordinary runtime endpoint retains its cursor. *)
Theorem staging_counted_prefix:
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code /\
  run_inst_seq code s = OK t /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn code
    (s with vs_inst_idx := k) Gf tnf) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
     gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i code ==> _ \/ _` drule >> strip_tac >> gvs[]) >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >> gvs[] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem straightline_continuation_placement:
  run_inst_seq pre s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (pre ++ post) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  t.vs_halted = s.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX post (DROP (s.vs_inst_idx + LENGTH pre) bb.bb_instructions)
Proof
  strip_tac >> drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  simp[] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `DROP (LENGTH pre) (DROP s.vs_inst_idx bb.bb_instructions) = post ++ l` by
    (asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  gvs[rich_listTheory.DROP_DROP_T] >> metis_tac[]
QED

Theorem staging_sequence_outcomes:
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code /\
  run_inst_seq code s = OK t ==> t.vs_outcomes = s.vs_outcomes
Proof
  strip_tac >>
  irule (BETA_RULE (ISPEC ``\u:venom_state. u.vs_outcomes`` run_inst_seq_preserves_field)) >>
  qexists `code` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `EVERY _ code` mp_tac >> simp[listTheory.EVERY_MEM] >>
  disch_then drule >> strip_tac >>
  gvs[] >> gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_alloca_def, exec_pure2_def,
      exec_read1_def, exec_write2_def, AllCaseEqs()] >>
  gvs[update_var_def, mstore_def]
QED

Theorem precompile_frame_cursor:
  (wb_frame cenv es sf s (t with vs_inst_idx := k) <=> wb_frame cenv es sf s t) /\
  (wb_frame cenv es sf (s with vs_inst_idx := j) t <=> wb_frame cenv es sf s t) /\
  (ghost_kept cenv es sf G tn (s with vs_inst_idx := j) G' tn' <=>
   ghost_kept cenv es sf G tn s G' tn')
Proof
  simp[wb_frame_def, ghost_kept_def, locals_kept_def,
       local_region_def, lookup_var_def]
QED

Theorem recovery_residual_success:
  compile_ecrecover h v r q sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand q s = SOME wq /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!p. x = Var p ==> not_fresh_at sf p)) [h;v;r;q] /\
  allocas_from 0 s /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 1 G' tn' (OK t) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sf sb) /\
    eval_operand res t = SOME (typed_val_to_w256 (BaseTV AddressT)
      (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n wq) of
        NONE => 0w | SOME addr => addr))) /\
    op_prov G' res = NONE /\ op_taint tn' res = {} /\
    stmt_state_rel ctx fn cenv cx
      (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\
    wb_frame cenv es sf s t /\
    ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G' tn' t /\
    ghost_kept cenv es sf G tn s G' tn'
Proof
  strip_tac >>
  drule_all recovery_framed_input >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `isPREFIX (emitted_insts sf sz) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  drule_all staging_counted_prefix >> strip_tac >>
  suspend "suffix"
QED

Resume recovery_residual_success[suffix]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sf sz)` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _ \/ _` drule >> strip_tac >>
     gvs[is_terminator_def]) >>
  `isPREFIX (emitted_insts sf sz ++ emitted_insts sz sb)
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all straightline_continuation_placement >> strip_tac >>
  drule_all staging_sequence_outcomes >> strip_tac >>
  drule_all staging_prefix_nonmemory_frames >> strip_tac >>
  drule recovery_request_result >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` >>
  `eval_operand (Var src) u = SOME b /\ eval_operand (Var dst) u = SOME c` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def] >>
  `stmt_state_rel ctx fn cenv cx es u` by simp[Abbr `u`, stmt_state_rel_inst_idx] >>
  `ghost_inv d cenv cx es Gf tnf u` by
    simp[Abbr `u`, SRULE [] (Q.INST [`gs` |-> `es.gas_obs`]
      literal_ptr_ghost_inv_normalize)] >>
  suspend "apply_suffix"
QED

Resume recovery_residual_success[apply_suffix]:
  `ptr_covers Gf tnf src u (w2n (128w:bytes32)) /\ ptr_covers Gf tnf dst u 32 /\
   allocas_from 0 u /\ ~u.vs_halted /\
   lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sz sb) (DROP u.vs_inst_idx bb.bb_instructions) /\
   tnf.t_stor SUBSET D.d_stor u.vs_call_ctx.cc_address
     (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
   tnf.t_trans SUBSET D.d_trans u.vs_call_ctx.cc_address
     (u.vs_transient u.vs_call_ctx.cc_address)` by
    (simp[Abbr `u`, wordsTheory.dimword_def] >>
     qpat_x_assum `isPREFIX (emitted_insts sz sb) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at (w2n b) 128 u.vs_memory =
    word_to_bytes wh T ++ word_to_bytes wv T ++
    word_to_bytes wr T ++ word_to_bytes wq T` by simp[Abbr `u`] >>
  drule recovery_request_result >> strip_tac >>
  `computed_precompile (venom_call_request u 1w 0w b 128w T)` by
    (simp[computed_precompile_def] >> simp[venom_call_request_def]) >>
  drule_all bodyPtrPrecompileBuiltinsContinuationFrameTheory.return_pointer_reservation_mono >>
  strip_tac >>
  Q.SUBGOAL_THEN `?co rest. u.vs_outcomes = co::rest /\ co.co_success` assume_tac
  >- (qexistsl [`co`,`rest`] >> simp[Abbr `u`]) >>
  `(!name lo len. local_region cenv es.scopes u name lo len ==>
      regions_disjoint (w2n c) 32 lo len) /\
   (!aid lo len. aid < sf.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (lo,len) ==>
      regions_disjoint (w2n c) 32 lo len)` by
    (conj_tac
     >- (rpt strip_tac >>
         `local_region cenv es.scopes t name lo len` by
           gvs[Abbr `u`, local_region_def, lookup_var_def] >> metis_tac[]) >>
     simp[Abbr `u`] >> first_assum ACCEPT_TAC) >>
  `!i. w2n b <= i /\ i < w2n b + w2n (128w:bytes32) ==> i NOTIN tnf.t_mem` by
    simp[wordsTheory.dimword_def] >>
  drule_all computed_load_suffix_framed_path >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "finish"
QED

Resume recovery_residual_success[finish]:
  `mem_word_at (w2n c) u.vs_memory = 0w` by simp[Abbr `u`] >>
  `mem_word_at (w2n c)
     (write_memory_with_expansion (w2n c)
       (TAKE 32 (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n wq) of
         NONE => [] | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T))) u).vs_memory =
   typed_val_to_w256 (BaseTV AddressT)
     (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n wq) of
        NONE => 0w | SOME addr => addr))` by
    (irule recovery_output_write >> simp[] >>
     Cases_on `vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n wq)` >> simp[]) >>
  `wb_frame cenv es sf s u` by
    simp[Abbr `u`, precompile_frame_cursor] >>
  `sf.cs_next_var <= sf.cs_next_var /\ sf.cs_next_id <= sf.cs_next_id /\
   MAP FDOM es.scopes = MAP FDOM es.scopes` by simp[] >>
  drule_all ghost_kept_wb_trans >> strip_tac >>
  drule_all wb_frame_trans >> strip_tac >>
  suspend "pack_success"
QED

Resume recovery_residual_success[pack_success]:
  `LENGTH (emitted_insts sz sb) = 4` by
    (drule computed_load_suffix_parts >> strip_tac >>
     drule exprSimPrecompilesTheory.computed_suffix_shape >> strip_tac >> simp[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qpat_x_assum `G' = _` kall_tac >>
  qpat_x_assum `tn' = _` kall_tac >>
  qpat_x_assum `t' = _` kall_tac >>
  qpat_x_assum `res = _` kall_tac >>
  drule_all gas_path_ptr_then >> strip_tac >>
  qexistsl [`t' with vs_inst_idx := u.vs_inst_idx + 4`,`G'`,`tn'`] >>
  conj_tac >- (gvs[] >> first_assum ACCEPT_TAC) >>
  simp[stmt_state_rel_inst_idx, precompile_frame_cursor,
       SRULE [] (Q.INST [`gs` |-> `es.gas_obs`] literal_ptr_ghost_inv_normalize)] >>
  gvs[Abbr `u`]
QED

Finalise recovery_residual_success

Theorem recovery_residual_oracle_failure:
  compile_ecrecover h v r q sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand q s = SOME wq /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!p. x = Var p ==> not_fresh_at sf p)) [h;v;r;q] /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sf sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(?co rest. s.vs_outcomes = co::rest /\ co.co_success) ==>
  ?t n G' tn'. gas_path_ptr D 0 ctx fn PG G tn s n G' tn' (Abort Revert_abort t)
Proof
  strip_tac >> drule_all recovery_framed_input >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `isPREFIX (emitted_insts sf sz) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  drule_all staging_counted_prefix >> strip_tac >>
  suspend "suffix"
QED

Resume recovery_residual_oracle_failure[suffix]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sf sz)` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _ \/ _` drule >> strip_tac >>
     gvs[is_terminator_def]) >>
  `isPREFIX (emitted_insts sf sz ++ emitted_insts sz sb)
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all straightline_continuation_placement >> strip_tac >>
  drule_all staging_sequence_outcomes >> strip_tac >>
  drule_all staging_prefix_nonmemory_frames >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sf sz)` >>
  `eval_operand (Var src) u = SOME b /\ eval_operand (Var dst) u = SOME c` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def] >>
  suspend "apply_suffix"
QED

Resume recovery_residual_oracle_failure[apply_suffix]:
  `ptr_covers Gf tnf src u (w2n (128w:bytes32)) /\ ptr_covers Gf tnf dst u 32 /\
   allocas_from 0 u /\ ~u.vs_halted /\
   lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sz sb) (DROP u.vs_inst_idx bb.bb_instructions) /\
   tnf.t_stor SUBSET D.d_stor u.vs_call_ctx.cc_address
     (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
   tnf.t_trans SUBSET D.d_trans u.vs_call_ctx.cc_address
     (u.vs_transient u.vs_call_ctx.cc_address)` by
    (simp[Abbr `u`, wordsTheory.dimword_def] >>
     qpat_x_assum `isPREFIX (emitted_insts sz sb) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at (w2n b) 128 u.vs_memory =
    word_to_bytes wh T ++ word_to_bytes wv T ++
    word_to_bytes wr T ++ word_to_bytes wq T` by simp[Abbr `u`] >>
  drule recovery_request_result >> strip_tac >>
  `computed_precompile (venom_call_request u 1w 0w b 128w T)` by
    (simp[computed_precompile_def] >> simp[venom_call_request_def]) >>
  `!i. w2n b <= i /\ i < w2n b + w2n (128w:bytes32) ==> i NOTIN tnf.t_mem` by
    simp[wordsTheory.dimword_def] >>
  Q.SUBGOAL_THEN `(u.vs_outcomes = [] \/
    ?co rest. u.vs_outcomes = co::rest /\ ~co.co_success)` assume_tac
  >- (Cases_on `s.vs_outcomes` >> gvs[Abbr `u`]) >>
  `ptr_covers Gf tnf dst u (w2n (32w:bytes32))` by simp[wordsTheory.dimword_def] >>
  drule_all computed_load_suffix_oracle_failure_path >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all gas_path_ptr_then >> strip_tac >>
  qexistsl [`t' with vs_inst_idx := j`,`0+n`,`G'`,`tn'`] >>
  first_assum ACCEPT_TAC
QED

Finalise recovery_residual_oracle_failure
