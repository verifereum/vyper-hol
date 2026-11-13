Theory bodyPtrPrecompileBuiltinsArithmeticRun
Ancestors bodyPtrPrecompileBuiltinsRecoveryRun wordArgsPtr
          bodyPtrPrecompileBuiltinsCompilerStages loweringPosts
          bodyPtrPrecompileBuiltinsPayloadCallbacks exprSimLiteralBuffer
          exprSimPrecompiles venomState venomInst compileEnv words arithmetic
          list emitHelper context allocaFootprint

Theorem expr_val_at_wb_frame:
  expr_val_at cenv cx ty lo sf es v op s /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sf /\
  wb_frame cenv es es' sf s t /\ eval_operand op t = eval_operand op s ==>
  expr_val_at cenv cx ty lo sf es v op t
Proof
  strip_tac >>
  `!n b sz. local_region cenv es.scopes s n b sz <=>
     local_region cenv es.scopes t n b sz` by
    (irule wb_frame_local_regions >> simp[] >> metis_tac[]) >>
  fs[expr_val_at_def, wb_frame_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `tv` mp_tac) >> simp[] >> strip_tac >>
  qexists `w` >> simp[] >> metis_tac[]
QED

Theorem allocation_point_operand:
  compile_alloc_buffer n sf = (ib,sa) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ n < dimword(:256) /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  expr_val_at cenv cx ty lo sf es v op s /\
  (!x. op = Var x ==> not_fresh_at sf x) ==>
  ?t b. run_inst_seq (emitted_insts sf sa) s = OK t /\
    stmt_state_rel ctx fn cenv cx es t /\
    eval_operand ib.buf_operand t = SOME b /\
    FLOOKUP t.vs_allocas sf.cs_next_id = SOME (w2n b,n) /\
    w2n b + n < dimword(:256) /\ t.vs_memory = s.vs_memory /\
    sf.cs_next_id < sa.cs_next_id /\ t.vs_labels = s.vs_labels /\ 
    wb_frame cenv es es sf s t /\
    expr_val_at cenv cx ty lo sf es v op t /\
    eval_operand op t = eval_operand op s /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (!name a len. local_region cenv es.scopes t name a len ==>
       regions_disjoint (w2n b) n a len) /\
    (!aid a len. aid < sf.cs_next_id /\
       FLOOKUP t.vs_allocas aid = SOME (a,len) ==>
       regions_disjoint (w2n b) n a len) /\
    (?p. ib.buf_operand = Var p /\ not_fresh_at sa p)
Proof
  strip_tac >> drule_all exprSimLiteralBufferTheory.alloc_buffer_frame_run >>
  strip_tac >>
  `eval_operand op t = eval_operand op s` by
    (Cases_on `op` >> simp[venomStateTheory.eval_operand_def]) >>
  `expr_val_at cenv cx ty lo sf es v op t` by
    (irule expr_val_at_wb_frame >> simp[] >> metis_tac[]) >>
  qexistsl [`t`,`w`] >> simp[] >> conj_tac
  >- first_assum ACCEPT_TAC >> rpt strip_tac >>
  irule exprSimPrecompilesTheory.state_allocations_disjoint >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> decide_tac
QED

Theorem point_payload_counters[local]:
  (do src <- emit_op ADD [point; Lit a]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit b]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit c]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit d]; emit_void MSTORE [dst; value] od)
    sa = ((),sb) ==>
  sb.cs_next_var = sa.cs_next_var + 6 /\ sb.cs_next_id = sa.cs_next_id + 8
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem ecmul_prefix_runtime:
  compile_alloc_buffer 96 sf = (ib,sa) /\
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [dst; value] od)
    sa = ((),smid) /\
  (do dst <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [dst; scalar] od) smid = ((),sp) /\
  compile_alloc_buffer 64 sp = (ob,sm) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sp /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  eval_operand point s0 = SOME p /\ eval_operand scalar s0 = SOME w /\
  w2n p + 64 < dimword(:256) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v point s0 /\
  (!x. MEM (Var x) [point;scalar] ==> not_fresh_at sf x) ==>
  ?s1 s2 s3 b c.
    run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
    run_inst_seq (emitted_insts sa smid ++ emitted_insts smid sp) s1 = OK s2 /\
    run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
    stmt_state_rel ctx fn cenv cx es s1 /\
    stmt_state_rel ctx fn cenv cx es s2 /\
    stmt_state_rel ctx fn cenv cx es s3 /\
    eval_operand ib.buf_operand s1 = SOME b /\
    eval_operand ib.buf_operand s2 = SOME b /\
    eval_operand ob.buf_operand s3 = SOME c /\
    w2n b + 96 < dimword(:256) /\ w2n c + 64 < dimword(:256) /\
    mem_bytes_at (w2n b) 96 s2.vs_memory =
      word_to_bytes (mload (w2n p) s0) T ++
      word_to_bytes (mload (w2n p+32) s0) T ++ word_to_bytes w T /\
    (!x. not_fresh_at sf x ==> lookup_var x s2 = lookup_var x s0) /\
    wb_frame cenv es es sf s0 s1 /\ wb_frame cenv es es sf s1 s2 /\
    s2.vs_allocas = s1.vs_allocas /\
    FLOOKUP s3.vs_allocas sp.cs_next_id = SOME (w2n c,64) /\
    wb_frame cenv es es sp s2 s3 /\ wb_frame cenv es es sf s0 s3 /\
    sf.cs_next_var <= sp.cs_next_var /\ sf.cs_next_id <= sp.cs_next_id /\
    (!name a len. local_region cenv es.scopes s3 name a len ==>
       regions_disjoint (w2n c) 64 a len) /\
    (!aid entry. FLOOKUP s2.vs_allocas aid = SOME entry ==>
       FLOOKUP s3.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sf.cs_next_id /\ FLOOKUP s3.vs_allocas aid = SOME (a,len) ==>
       regions_disjoint (w2n c) 64 a len) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
       regions_disjoint (w2n c) 64 off (type_memory_size tv)) /\
    pure_frame cenv fn es sf s0 s3
Proof
  strip_tac >>
  `96 < dimword(:256)` by simp[dimword_def] >>
  `!x. point = Var x ==> not_fresh_at sf x` by metis_tac[MEM] >>
  drule_all allocation_point_operand >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sa) s0 = OK s1` >>
  rename1 `eval_operand ib.buf_operand s1 = SOME b` >>
  qpat_assum `compile_alloc_buffer 96 sf = _`
    (mp_then Any strip_assume_tac bodyPtrPrecompileBuiltinsCompletePrefixesTheory.allocation_progress) >>
  `sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
  `!x. not_fresh_at sf x ==> not_fresh_at sa x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand scalar s1 = SOME w` by
    (Cases_on `scalar` >> gvs[eval_operand_def] >> metis_tac[MEM]) >>
  `!x. MEM (Var x) [point;ib.buf_operand;scalar] ==> not_fresh_at sa x` by
    (simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `sa.cs_next_var <= smid.cs_next_var` by
    (qpat_assum `(do src <- _; value <- _; dst <- _; _ od) sa = _`
       (mp_then Any strip_assume_tac point_payload_counters) >> decide_tac) >>
  `?s2. run_inst_seq (emitted_insts sa smid ++ emitted_insts smid sp) s1 = OK s2 /\
    stmt_state_rel ctx fn cenv cx es s2 /\ wb_frame cenv es es sf s1 s2 /\
    (!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s1) /\
    s2.vs_allocas = s1.vs_allocas /\ eval_operand ib.buf_operand s2 = SOME b /\
    mem_bytes_at (w2n b) 96 s2.vs_memory =
      word_to_bytes (mload (w2n p) s1) T ++
      word_to_bytes (mload (w2n p+32) s1) T ++ word_to_bytes w T /\
    (!a len. regions_disjoint (w2n b) 96 a len ==>
       mem_bytes_at a len s2.vs_memory = mem_bytes_at a len s1.vs_memory)` by
    (irule mul_payload_callback >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac
     >- (qexists `mk_inst sf.cs_next_id ALLOCA [Lit 96w]
           [STRING #"%" (toString sf.cs_next_var)]` >> simp[mk_inst_def]) >>
     qexistsl [`lo`,`point`,`scalar`,`v`] >> simp[] >> metis_tac[MEM]) >>
  suspend "finish"
QED

Resume ecmul_prefix_runtime[finish]:
  `64 < dimword(:256)` by simp[dimword_def] >>
  qpat_assum `compile_alloc_buffer 64 sp = _`
    (mp_then Any (drule_all_then strip_assume_tac) alloc_buffer_frame_run) >>
  rename1 `run_inst_seq (emitted_insts sp sm) s2 = OK s3` >>
  rename1 `eval_operand ob.buf_operand s3 = SOME c` >>
  `sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id` by
    (qpat_x_assum `(do src <- _; value <- _; dst <- _; _ od) sa = _` mp_tac >>
     qpat_x_assum `(do dst <- _; _ od) smid = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `sf.cs_next_var <= sp.cs_next_var /\ sf.cs_next_id <= sp.cs_next_id` by decide_tac >>
  `wb_frame cenv es es sf s2 s3` by
    (irule bodyPtrPrecompileBuiltinsRecoveryPostFrameTheory.wb_frame_counter_weaken >>
     qexists `sp` >> simp[]) >>
  `wb_frame cenv es es sf s0 s2` by
    (qspecl_then [`fn`,`cenv`,`cx`,`es`,`s0`,`sf`,`es`,`es`,`sf`,`s1`,`s2`,`ctx`]
       mp_tac exprSimWordArgsTheory.wb_frame_trans >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `wb_frame cenv es es sf s0 s3` by
    (qspecl_then [`fn`,`cenv`,`cx`,`es`,`s0`,`sf`,`es`,`es`,`sf`,`s2`,`s3`,`ctx`]
       mp_tac exprSimWordArgsTheory.wb_frame_trans >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `pure_frame cenv fn es sf s0 s3` by
    (match_mp_tac (Q.SPECL [`fn`, `cenv`, `es`, `sf`, `s0`, `s3`, `s1`, `s2`,
       `sf.cs_next_id`, `[Lit 96w]`, `[STRING #"%" (toString sf.cs_next_var)]`,
       `w2n (b:256 word)`, `96`] scratch_prefix_pure_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  `mload (w2n p) s1 = mload (w2n p) s0 /\
   mload (w2n p+32) s1 = mload (w2n p+32) s0` by
    simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  qexistsl [`s1`,`s2`,`s3`,`b`,`c`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> irule state_allocations_disjoint >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> decide_tac) >>
  rpt strip_tac >> irule precompile_alloca_immutable_disjoint >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexists `mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]` >> simp[mk_inst_def]
QED
Finalise ecmul_prefix_runtime

Theorem ecadd_prefix_runtime:
  compile_alloc_buffer 128 sf = (ib,sa) /\
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [dst; value] od)
    sa = ((),smid) /\
  (do src <- emit_op ADD [other; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [other; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [ib.buf_operand; Lit 96w]; emit_void MSTORE [dst; value] od)
    smid = ((),sp) /\
  compile_alloc_buffer 64 sp = (ob,sm) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sp /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  eval_operand point s0 = SOME p /\ eval_operand other s0 = SOME q /\
  w2n p + 64 < dimword(:256) /\ w2n q + 64 < dimword(:256) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vp point s0 /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vq other s0 /\
  (!x. MEM (Var x) [point;other] ==> not_fresh_at sf x) ==>
  ?s1 s2 s3 b c.
    run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
    run_inst_seq (emitted_insts sa smid ++ emitted_insts smid sp) s1 = OK s2 /\
    run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
    stmt_state_rel ctx fn cenv cx es s1 /\
    stmt_state_rel ctx fn cenv cx es s2 /\
    stmt_state_rel ctx fn cenv cx es s3 /\
    eval_operand ib.buf_operand s1 = SOME b /\
    eval_operand ib.buf_operand s2 = SOME b /\
    eval_operand ob.buf_operand s3 = SOME c /\
    w2n b + 128 < dimword(:256) /\ w2n c + 64 < dimword(:256) /\
    mem_bytes_at (w2n b) 128 s2.vs_memory =
      word_to_bytes (mload (w2n p) s0) T ++ word_to_bytes (mload (w2n p+32) s0) T ++
      word_to_bytes (mload (w2n q) s0) T ++ word_to_bytes (mload (w2n q+32) s0) T /\
    (!x. not_fresh_at sf x ==> lookup_var x s2 = lookup_var x s0) /\
    wb_frame cenv es es sf s0 s1 /\ wb_frame cenv es es sf s1 s2 /\
    s2.vs_allocas = s1.vs_allocas /\
    FLOOKUP s3.vs_allocas sp.cs_next_id = SOME (w2n c,64) /\
    wb_frame cenv es es sp s2 s3 /\ wb_frame cenv es es sf s0 s3 /\
    sf.cs_next_var <= sp.cs_next_var /\ sf.cs_next_id <= sp.cs_next_id /\
    (!name a len. local_region cenv es.scopes s3 name a len ==>
       regions_disjoint (w2n c) 64 a len) /\
    (!aid entry. FLOOKUP s2.vs_allocas aid = SOME entry ==>
       FLOOKUP s3.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sf.cs_next_id /\ FLOOKUP s3.vs_allocas aid = SOME (a,len) ==>
       regions_disjoint (w2n c) 64 a len) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
       regions_disjoint (w2n c) 64 off (type_memory_size tv)) /\
    pure_frame cenv fn es sf s0 s3
Proof
  strip_tac >>
  `128 < dimword(:256)` by simp[dimword_def] >>
  `!x. point = Var x ==> not_fresh_at sf x` by metis_tac[MEM] >>
  qpat_assum `expr_val_at _ _ _ _ _ _ vp point s0`
    (mp_then Any mp_tac allocation_point_operand) >>
  disch_then (drule_all_then strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sf sa) s0 = OK s1` >>
  rename1 `eval_operand ib.buf_operand s1 = SOME b` >>
  `eval_operand other s1 = SOME q` by
    (Cases_on `other` >> gvs[eval_operand_def] >> metis_tac[MEM]) >>
  `expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vq other s1` by
    (irule expr_val_at_wb_frame >> simp[] >> metis_tac[]) >>
  qpat_assum `compile_alloc_buffer 128 sf = _`
    (mp_then Any strip_assume_tac bodyPtrPrecompileBuiltinsCompletePrefixesTheory.allocation_progress) >>
  `sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
  `!x. not_fresh_at sf x ==> not_fresh_at sa x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. MEM (Var x) [point;other;ib.buf_operand] ==> not_fresh_at sa x` by
    (simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `sa.cs_next_var <= smid.cs_next_var` by
    (qpat_assum `(do src <- _; value <- _; dst <- _; _ od) sa = _`
       (mp_then Any strip_assume_tac point_payload_counters) >> decide_tac) >>
  suspend "payload"
QED

Resume ecadd_prefix_runtime[payload]:
  `?s2. run_inst_seq (emitted_insts sa smid ++ emitted_insts smid sp) s1 = OK s2 /\
    stmt_state_rel ctx fn cenv cx es s2 /\ wb_frame cenv es es sf s1 s2 /\
    (!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s1) /\
    s2.vs_allocas = s1.vs_allocas /\ eval_operand ib.buf_operand s2 = SOME b /\
    mem_bytes_at (w2n b) 128 s2.vs_memory =
      word_to_bytes (mload (w2n p) s1) T ++ word_to_bytes (mload (w2n p+32) s1) T ++
      word_to_bytes (mload (w2n q) s1) T ++ word_to_bytes (mload (w2n q+32) s1) T /\
    (!a len. regions_disjoint (w2n b) 128 a len ==>
       mem_bytes_at a len s2.vs_memory = mem_bytes_at a len s1.vs_memory)` by
    (irule add_payload_callback >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac
     >- (qexists `mk_inst sf.cs_next_id ALLOCA [Lit 128w]
           [STRING #"%" (toString sf.cs_next_var)]` >> simp[mk_inst_def]) >>
     qexistsl [`lo`,`other`,`point`,`vp`,`vq`] >> simp[] >> metis_tac[MEM]) >>
  suspend "finish"
QED

Resume ecadd_prefix_runtime[finish]:
  `64 < dimword(:256)` by simp[dimword_def] >>
  qpat_assum `compile_alloc_buffer 64 sp = _`
    (mp_then Any (drule_all_then strip_assume_tac) alloc_buffer_frame_run) >>
  rename1 `run_inst_seq (emitted_insts sp sm) s2 = OK s3` >>
  rename1 `eval_operand ob.buf_operand s3 = SOME c` >>
  `sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id` by
    (qpat_assum `(do src <- _; value <- _; dst <- _; _ od) sa = _`
       (mp_then Any strip_assume_tac point_payload_counters) >>
     qpat_assum `(do src <- _; value <- _; dst <- _; _ od) smid = _`
       (mp_then Any strip_assume_tac point_payload_counters) >> decide_tac) >>
  `sf.cs_next_var <= sp.cs_next_var /\ sf.cs_next_id <= sp.cs_next_id` by decide_tac >>
  `wb_frame cenv es es sf s2 s3` by
    (irule bodyPtrPrecompileBuiltinsRecoveryPostFrameTheory.wb_frame_counter_weaken >>
     qexists `sp` >> simp[]) >>
  `wb_frame cenv es es sf s0 s2` by
    (qspecl_then [`fn`,`cenv`,`cx`,`es`,`s0`,`sf`,`es`,`es`,`sf`,`s1`,`s2`,`ctx`]
       mp_tac exprSimWordArgsTheory.wb_frame_trans >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `wb_frame cenv es es sf s0 s3` by
    (qspecl_then [`fn`,`cenv`,`cx`,`es`,`s0`,`sf`,`es`,`es`,`sf`,`s2`,`s3`,`ctx`]
       mp_tac exprSimWordArgsTheory.wb_frame_trans >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `pure_frame cenv fn es sf s0 s3` by
    (match_mp_tac (Q.SPECL [`fn`, `cenv`, `es`, `sf`, `s0`, `s3`, `s1`, `s2`,
       `sf.cs_next_id`, `[Lit 128w]`, `[STRING #"%" (toString sf.cs_next_var)]`,
       `w2n (b:256 word)`, `128`] scratch_prefix_pure_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  `!a. mload a s1 = mload a s0` by
    simp[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  qexistsl [`s1`,`s2`,`s3`,`b`,`c`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> irule state_allocations_disjoint >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> decide_tac) >>
  rpt strip_tac >> irule precompile_alloca_immutable_disjoint >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexists `mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]` >> simp[mk_inst_def]
QED
Finalise ecadd_prefix_runtime
