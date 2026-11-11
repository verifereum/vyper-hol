Theory bodyPtrPrecompileBuiltinsRecoveryRun
Ancestors bodyPtrPrecompileBuiltinsCompletePrefixes
          bodyPtrPrecompileBuiltinsPayloadCallbacks
          bodyPtrPrecompileBuiltinsRunWitnesses exprSimLiteralBuffer
          exprSimPrecompiles venomState venomInst compileEnv loweringStateRelDefs words arithmetic list
          bodyPtrPrecompileBuiltinsRecoveryPostFrame allocaFootprint
          emitHelper context

Theorem recovery_payload_counters[local]:
  (do emit_void MSTORE [buf; h];
      p1 <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [buf; Lit 64w]; emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [buf; Lit 96w]; emit_void MSTORE [p3; q] od)
    sa = ((),sp) ==>
  sp.cs_next_var = sa.cs_next_var + 3 /\
  sp.cs_next_id = sa.cs_next_id + 7
Proof
  simp[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem recovery_prefix_runtime:
  compile_alloc_buffer 128 sf = (ib,sa) /\
  (do emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w]; emit_void MSTORE [p3; q] od)
    sa = ((),sp) /\
  compile_alloc_buffer 32 sp = (ob,sm) /\
  emit_void MSTORE [ob.buf_operand; Lit 0w] sm = ((),sz) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sp /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  eval_operand h s0 = SOME wh /\ eval_operand v s0 = SOME wv /\
  eval_operand r s0 = SOME wr /\ eval_operand q s0 = SOME wq /\
  (!x. MEM (Var x) [h;v;r;q] ==> not_fresh_at sf x) ==>
  ?s1 s2 s3 s4 b c.
    run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
    run_inst_seq (emitted_insts sa sp) s1 = OK s2 /\
    run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
    run_inst_seq (emitted_insts sm sz) s3 = OK s4 /\
    stmt_state_rel ctx fn cenv cx es s1 /\
    stmt_state_rel ctx fn cenv cx es s2 /\
    stmt_state_rel ctx fn cenv cx es s3 /\
    eval_operand ib.buf_operand s1 = SOME b /\
    eval_operand ib.buf_operand s2 = SOME b /\
    eval_operand ob.buf_operand s3 = SOME c /\
    w2n b + 128 < dimword(:256) /\ w2n c + 32 < dimword(:256) /\
    mem_bytes_at (w2n b) 128 s2.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes wq T /\
    (!x. not_fresh_at sf x ==> lookup_var x s2 = lookup_var x s0) /\
    wb_frame cenv es sf s0 s1 /\ wb_frame cenv es sf s1 s2 /\
    s2.vs_allocas = s1.vs_allocas /\
    s4 = mstore (w2n c) 0w s3 /\
    FLOOKUP s3.vs_allocas sp.cs_next_id = SOME (w2n c,32) /\
    wb_frame cenv es sp s2 s3 /\
    (!name lo len. local_region cenv es.scopes s3 name lo len ==>
       regions_disjoint (w2n c) 32 lo len) /\
    (!aid entry. FLOOKUP s2.vs_allocas aid = SOME entry ==>
       FLOOKUP s3.vs_allocas aid = SOME entry) /\
    stmt_state_rel ctx fn cenv cx es s4 /\
    mem_word_at (w2n c) s4.vs_memory = 0w /\
    FLOOKUP s4.vs_allocas sp.cs_next_id = SOME (w2n c,32) /\
    wb_frame cenv es sp s3 s4 /\
    wb_frame cenv es sf s0 s4 /\
    sf.cs_next_var <= sp.cs_next_var /\ sf.cs_next_id <= sp.cs_next_id /\
    (!aid lo len. aid < sf.cs_next_id /\
       FLOOKUP s4.vs_allocas aid = SOME (lo,len) ==>
       regions_disjoint (w2n c) 32 lo len) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
       regions_disjoint (w2n c) 32 off (type_memory_size tv)) /\
    (!name lo len. local_region cenv es.scopes s4 name lo len ==>
       regions_disjoint (w2n c) 32 lo len)
Proof
  strip_tac >>
  `128 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  qpat_assum `compile_alloc_buffer 128 sf = _`
    (mp_then Any (drule_all_then strip_assume_tac) alloc_buffer_frame_run) >>
  rename1 `run_inst_seq (emitted_insts sf sa) s0 = OK s1` >>
  rename1 `eval_operand ib.buf_operand s1 = SOME b` >>
  qpat_assum `compile_alloc_buffer 128 sf = _`
    (mp_then Any strip_assume_tac allocation_progress) >>
  `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
  `!x. not_fresh_at sf x ==> not_fresh_at sa x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. MEM x [h;v;r;q] ==> eval_operand x s1 = eval_operand x s0` by
    (rpt strip_tac >> Cases_on `x` >> simp[eval_operand_def] >>
     metis_tac[]) >>
  `eval_operand h s1 = SOME wh /\ eval_operand v s1 = SOME wv /\
   eval_operand r s1 = SOME wr /\ eval_operand q s1 = SOME wq` by
    metis_tac[listTheory.MEM] >>
  `!x. MEM (Var x) [ib.buf_operand;h;v;r;q] ==> not_fresh_at sa x` by
    (simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `!aid a len. aid < sf.cs_next_id /\
    FLOOKUP s1.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n b) 128 a len` by
    (rpt strip_tac >> irule state_allocations_disjoint >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `?s2. run_inst_seq (emitted_insts sa sp) s1 = OK s2 /\
    stmt_state_rel ctx fn cenv cx es s2 /\ wb_frame cenv es sf s1 s2 /\
    (!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s1) /\
    s2.vs_allocas = s1.vs_allocas /\ eval_operand ib.buf_operand s2 = SOME b /\
    mem_bytes_at (w2n b) 128 s2.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes wq T` by
    (irule recovery_payload_callback >> simp[] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     conj_tac
     >- (qexistsl [`h`,`r`,`q`,`v`] >> simp[] >> metis_tac[]) >>
     qexists `mk_inst sf.cs_next_id ALLOCA [Lit 128w]
       [STRING #"%" (toString sf.cs_next_var)]` >>
     simp[venomInstTheory.mk_inst_def]) >>
  suspend "finish"
QED

Resume recovery_prefix_runtime[finish]:
  `32 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  qpat_assum `compile_alloc_buffer 32 sp = _`
    (mp_then Any (drule_all_then strip_assume_tac) alloc_buffer_frame_run) >>
  rename1 `run_inst_seq (emitted_insts sp sm) s2 = OK s3` >>
  rename1 `eval_operand ob.buf_operand s3 = SOME c` >>
  `eval_operand (Lit 0w) s3 = SOME 0w` by simp[eval_operand_def] >>
  drule_all bodyPtrPrecompileBuiltinsPayloadRunsTheory.direct_store_run >>
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx es (mstore (w2n c) 0w s3) /\
   mem_word_at (w2n c) (mstore (w2n c) 0w s3).vs_memory = 0w` by
    (irule registered_word_store_state >> goal_assum (drule_at Any) >>
     simp[] >>
     qexists `mk_inst sp.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sp.cs_next_var)]` >> simp[mk_inst_def]) >>
  `wb_frame cenv es sp s3 (mstore (w2n c) 0w s3)` by
    (irule registered_word_store_wb_frame >>
     goal_assum (drule_at Any) >> simp[] >> conj_tac
     >- (qexists `sp.cs_next_id` >> simp[]) >>
     qexistsl [`ctx`,`cx`,`fn`] >> simp[]) >>
  suspend "frame"
QED

Resume recovery_prefix_runtime[frame]:
  drule recovery_payload_counters >> strip_tac >>
  `sf.cs_next_var <= sp.cs_next_var /\ sf.cs_next_id <= sp.cs_next_id` by decide_tac >>
  qpat_x_assum `sp.cs_next_id = _` kall_tac >>
  qpat_x_assum `sp.cs_next_var = _` kall_tac >>
  `wb_frame cenv es sf s2 s3 /\ wb_frame cenv es sf s3 (mstore (w2n c) 0w s3)` by
    (conj_tac >> irule wb_frame_counter_weaken >> qexists `sp` >> simp[]) >>
  `wb_frame cenv es sf s0 s2` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> conj_tac
     >- (qexistsl [`es`,`sf`,`s1`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `wb_frame cenv es sf s0 s3` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> conj_tac
     >- (qexistsl [`es`,`sf`,`s2`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `wb_frame cenv es sf s0 (mstore (w2n c) 0w s3)` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> conj_tac
     >- (qexistsl [`es`,`sf`,`s3`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  qexistsl [`s1`,`s2`,`s3`,`mstore (w2n c) 0w s3`,`b`,`c`] >>
  simp[] >> conj_tac
  >- (qpat_assum `!name lo len. local_region _ _ s3 _ _ _ ==> _` ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> irule state_allocations_disjoint >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> irule precompile_alloca_immutable_disjoint >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      qexists `mk_inst sp.cs_next_id ALLOCA [Lit 32w]
        [STRING #"%" (toString sp.cs_next_var)]` >> simp[mk_inst_def]) >>
  rpt strip_tac >>
  qpat_x_assum `!name lo len. local_region _ _ s3 _ _ _ ==> _` irule >>
  gvs[local_region_def] >> metis_tac[]
QED

Finalise recovery_prefix_runtime
