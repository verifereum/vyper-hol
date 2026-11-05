(* ECRecover-specific buffer boundaries restated from the local lemmas of
   the same names in exprSimPrecompilesScript.sml, using the S1 base proofs.
   Generic allocation and scratch interfaces are reused. *)
Theory bodyMemBiECRecoverBuffers
Ancestors
  bodyMemBiECRecoverStores exprSimPrecompiles exprSimAlloc
  exprSimLiteralBuffer exprSimDefs exprSimProps exprLoweringProps
  compileEnv context emitHelper emitHelperProps fragExec
  venomExecSemantics venomMemDefs venomState venomInst
  loweringPosts words rich_list list ASCIInumbers valueEncodingProps loweringHalt
  exprSimWordArgs
Libs
  monadsyntax

Theorem ecrecover_buffers_prefix_shape:
  (do ib <- context$compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [p3; sig];
      ob <- context$compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      return (ib.buf_operand,ob.buf_operand)
   od) sf = ((ip,op),sm) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sb sc.
    ip = ib.buf_operand /\ op = ob.buf_operand /\
    context$compile_alloc_buffer 128 sf = (ib,sa) /\
    (do emit_void MSTORE [ib.buf_operand; h];
        p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [p1; v];
        p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [p2; r];
        p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [p3; sig] od) sa = ((),sb) /\
    context$compile_alloc_buffer 32 sb = (ob,sc) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] sc = ((),sm) /\
    emitted_insts sf sc = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sc /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sc ++ emitted_insts sc sm /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
    local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sb.cs_next_id < sc.cs_next_id /\ sc.cs_next_id < sm.cs_next_id /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >>
  ` (do ib <- context$compile_alloc_buffer 128;
        (do emit_void MSTORE [ib.buf_operand; h];
            p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
            emit_void MSTORE [p1; v];
            p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
            emit_void MSTORE [p2; r];
            p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
            emit_void MSTORE [p3; sig] od);
        ob <- context$compile_alloc_buffer 32;
        emit_void MSTORE [ob.buf_operand; Lit 0w];
        return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  pop_assum mp_tac >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  rename1 `context$compile_alloc_buffer 128 sf = (ib,sa)` >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >>
  rename1 `_ sa = (u,sb)` >> Cases_on `u` >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  rename1 `context$compile_alloc_buffer 32 sb = (ob,sc)` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_void MSTORE _ sc = (u0,_)` >> Cases_on `u0` >> gvs[] >>
  rename1 `emit_void MSTORE _ sc = ((),sm)` >>
  ` (do ib <- context$compile_alloc_buffer 128;
        (do emit_void MSTORE [ib.buf_operand; h];
            p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
            emit_void MSTORE [p1; v];
            p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
            emit_void MSTORE [p2; r];
            p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
            emit_void MSTORE [p3; sig] od);
        ob <- context$compile_alloc_buffer 32;
        return (ib.buf_operand,ob.buf_operand) od) sf =
      ((ib.buf_operand,ob.buf_operand),sc)` by
    (simp[Once comp_bind_def] >>
     simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
     simp[comp_bind_def, comp_return_def]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `sc.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sc` by
    (drule ecrecover_input_stores_shape >> strip_tac >>
     qpat_assum `context$compile_alloc_buffer 128 _ = _`
       (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
     qpat_assum `context$compile_alloc_buffer 32 _ = _`
       (strip_assume_tac o MATCH_MP compile_alloc_buffer_insts) >>
     once_rewrite_tac[emitted_insts_def] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  `emitted_insts sf sm = emitted_insts sf sc ++ emitted_insts sc sm` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  drule (BETA_RULE (Q.INST [`payload` |->
    `\ib. do emit_void MSTORE [ib.buf_operand; h];
             p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
             emit_void MSTORE [p1; v];
             p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
             emit_void MSTORE [p2; r];
             p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
             emit_void MSTORE [p3; sig] od`] (SPEC_ALL allocated_payload_shape))) >>
  disch_then (qspecl_then [`func`, `cenv`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> drule ecrecover_input_stores_shape >> simp[]) >>
  strip_tac >> gvs[] >>
  drule ecrecover_input_stores_shape >> strip_tac >> simp[] >>
  rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sc` >> simp[]) >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ecrecover_buffers_shape:
  (do ib <- context$compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [p3; sig];
      ob <- context$compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      return (ib.buf_operand,ob.buf_operand)
   od) sf = ((ip,op),sm) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sb sc.
    ip = ib.buf_operand /\ op = ob.buf_operand /\
    context$compile_alloc_buffer 128 sf = (ib,sa) /\
    (do emit_void MSTORE [ib.buf_operand; h];
        p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [p1; v];
        p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [p2; r];
        p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [p3; sig] od) sa = ((),sb) /\
    context$compile_alloc_buffer 32 sb = (ob,sc) /\
    emit_void MSTORE [ob.buf_operand; Lit 0w] sc = ((),sm) /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sc ++ emitted_insts sc sm /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
    local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sb.cs_next_id < sc.cs_next_id /\ sc.cs_next_id < sm.cs_next_id /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  strip_tac >> drule_all ecrecover_buffers_prefix_shape >> strip_tac >>
  qexistsl_tac [`ib`, `ob`, `sa`, `sb`, `sc`] >> simp[] >> metis_tac[]
QED

Theorem ecrecover_buffers_run:
  (do ib <- context$compile_alloc_buffer 128;
      emit_void MSTORE [ib.buf_operand; h];
      p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [p3; sig];
      ob <- context$compile_alloc_buffer 32;
      emit_void MSTORE [ob.buf_operand; Lit 0w];
      return (ib.buf_operand,ob.buf_operand)
   od) sf = ((ip,op),sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sf x) ==>
  ?t pi po. run_inst_seq (emitted_insts sf sm) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sf s t /\
    eval_operand ip t = SOME pi /\ eval_operand op t = SOME po /\
    w2n pi + 128 < dimword (:256) /\ w2n po + 32 < dimword (:256) /\
    mem_bytes_at (w2n pi) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes ws T /\
    mem_word_at (w2n po) t.vs_memory = 0w /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n po) 32 b sz) /\
    (!aid b sz. aid < sf.cs_next_id /\
      FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n po) 32 b sz) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (tv,iv) ==>
       regions_disjoint (w2n po) 32 off (type_memory_size tv)) /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >> drule_all ecrecover_buffers_prefix_shape >> strip_tac >>
  qpat_x_assum `_ sf = ((ip,op),sm)` kall_tac >>
  `128 < dimword (:256) /\ 32 < dimword (:256)` by
    simp[wordsTheory.dimword_def] >>
  mp_tac (Q.INST [`insz` |-> `128`, `outsz` |-> `32`,
    `sm` |-> `sc`, `code` |-> `emitted_insts sa sb`,
    `bytes` |-> `word_to_bytes (wh:256 word) T ++ word_to_bytes (wv:256 word) T ++
                word_to_bytes (wr:256 word) T ++ word_to_bytes (ws:256 word) T`]
    (SPEC_ALL allocated_payload_run)) >>
  (impl_tac >- (
    simp[] >> rpt strip_tac >>
    `!z. MEM z [h;v;r;sig] ==> eval_operand z s1 = eval_operand z s` by
      (rpt strip_tac >> Cases_on `z` >>
       simp[eval_operand_def] >> metis_tac[]) >>
    `eval_operand h s1 = SOME wh /\ eval_operand v s1 = SOME wv /\
     eval_operand r s1 = SOME wr /\ eval_operand sig s1 = SOME ws` by
      metis_tac[listTheory.MEM] >>
    `!x. MEM (Var x) [ib.buf_operand;h;v;r;sig] ==> not_fresh_at sa x` by
      (qpat_x_assum `!x. MEM (Var x) [h;v;r;sig] ==> _` mp_tac >>
       qpat_x_assum `context$compile_alloc_buffer 128 sf = (ib,sa)`
         (mp_tac o MATCH_MP compile_alloc_buffer_parts) >>
       POP_ASSUM_LIST (K all_tac) >> simp[listTheory.MEM] >> metis_tac[]) >>
    `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
    `cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (tv,iv) ==>
       regions_disjoint (w2n wi) 128 off (type_memory_size tv)` by
      (match_mp_tac (Q.INST
         [`s` |-> `s1`, `inst` |-> `mk_inst sf.cs_next_id ALLOCA [Lit 128w]
           [STRING #"%" (toString sf.cs_next_var)]`]
         precompile_alloca_immutable_disjoint) >>
       simp[mk_inst_def]) >>
    drule_all ecrecover_input_stores_sim >> strip_tac >>
    `t.vs_allocas = s1.vs_allocas` by
      (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
        (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
    `eval_operand ib.buf_operand t = SOME wi` by
      (Cases_on `ib.buf_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
    qexists_tac `t` >> simp[])) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sc) s = OK s3` >>
  rename1 `eval_operand ib.buf_operand s3 = SOME wi` >>
  rename1 `eval_operand ob.buf_operand s3 = SOME wo` >>
  `eval_operand (Lit 0w) s3 = SOME 0w` by simp[eval_operand_def] >>
  drule_all literal_emit_mstore_run >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore (w2n wo) 0w s3)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n wo`,
       `mk_inst sb.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString sb.cs_next_var)]`, `32`] >> simp[mk_inst_def] >>
     gvs[compileEnvTheory.regions_disjoint_def]) >>
  `!aid b sz. aid < sf.cs_next_id /\
     FLOOKUP s3.vs_allocas aid = SOME (b,sz) ==>
     w2n wo + 32 <= b \/ b + sz <= w2n wo` by
    (gvs[compileEnvTheory.regions_disjoint_def]) >>
  `wb_frame cenv es sf s3 (mstore (w2n wo) 0w s3)` by
    (irule scratch_mstore_frame >> conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es sf s (mstore (w2n wo) 0w s3)` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`es`,`sf`,`s3`] >> simp[]) >>
     qexistsl_tac [`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl_tac [`mstore (w2n wo) 0w s3`,`wi`,`wo`] >>
  conj_tac
  >- (`emitted_insts sf sm = emitted_insts sf sc ++ emitted_insts sc sm` by
        metis_tac[APPEND_ASSOC] >>
      qpat_x_assum `emitted_insts sf sm = emitted_insts sf sc ++ _` SUBST1_TAC >>
      qpat_x_assum `run_inst_seq (emitted_insts sf sc) s = OK s3` mp_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts sc sm) s3 = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[run_inst_seq_append]) >>
  simp[] >>
  conj_tac
  >- (gvs[eval_operand_def, mstore_def] >>
      `not_fresh_at sb p` by
        (gvs[not_fresh_at_def] >>
         metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  conj_tac >- gvs[eval_operand_def, mstore_def] >>
  conj_tac
  >- (`mem_bytes_at (w2n wi) 128 (mstore (w2n wo) 0w s3).vs_memory =
         mem_bytes_at (w2n wi) 128 s3.vs_memory` by
        (irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
         gvs[compileEnvTheory.regions_disjoint_def]) >> simp[]) >>
  simp[valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ s3 _ _ _ ==> _` irule >>
      qexists_tac `name` >>
      gvs[local_region_def, mstore_def]) >>
  simp[mstore_def] >> conj_tac >- first_assum ACCEPT_TAC >>
  match_mp_tac (Q.INST
    [`s` |-> `s3`, `inst` |-> `mk_inst sb.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sb.cs_next_var)]`]
    precompile_alloca_immutable_disjoint) >>
  simp[mk_inst_def]
QED
