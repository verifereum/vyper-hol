Theory bodyPtrPrecompileBuiltinsRecoveryResidual
Ancestors bodyPtrPrecompileBuiltinsRecoveryRun bodyPtrPrecompileBuiltinsRecoveryFrame
          bodyPtrPrecompileBuiltinsFramedContinuation bodyPtrPrecompileBuiltinsRecoveryValue
          bodyPtrPrecompileBuiltinsCompilerStages bodyPtrPrecompileBuiltinsRunAllocation
          stmtSimDeclPath valueEncodingProps venomExecSemantics venomInst venomState
          compileEnv emitHelper exprLoweringProps rich_list emitHelperProps

(* Transport through ALLOCA is purely ordinary memory transport, independent
   of the provenance assigned to the newly allocated variable. *)
Theorem emitted_allocation_memory:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_memory = s.vs_memory
Proof
  strip_tac >> drule_all emitted_allocation_step >>
  simp[Once step_inst_base_def, mk_inst_def] >>
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
