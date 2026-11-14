(* ECRecover's two buffers, staged words and zero output on one joint path. *)
Theory bodyFullBuiltinPrecompileRecoveryBuffers
Ancestors
  bodyFullAllocaFresh bodyFullUnwrapRun bodyFullUnwrapSlotPost
  bodyMemBiECRecoverMemory bodyPtrPrecompileBuiltinsRecoveryInput
  bodyPtrPrecompileBuiltinsCompilerStages bodyPtrPrecompileBuiltinsSeq
  exprSimPrecompiles exprSimAlloc exprSimLiteralBuffer exprSimWordArgs
  exprSimPtrLiteralBuffer bodyMemoryDefs bodyPtrDefs loweringPosts
  fragGasCopyLoop fragGasSeqPtr fragGasOriginPtr fragExecMem fragExec
  logTopicScalarPtr wordLoadStorePtr allocaFootprint stmtSimProps
  ptrSafetyTransport ptrDiscipline ghostPcTransportPtr instIdxIndep
  exprLoweringProps emitHelperProps emitHelper context compileEnv freshWrites
  loweringStateRelDefs venomMemDefs instMemFrontier
  vyperStorageTrace vyperStorageFootprint vyperState
  venomExecSemantics venomState venomInst words arithmetic list rich_list finite_map pred_set
Libs
  monadsyntax

Theorem ecrecover_buffers_full_run:
compile_alloc_buffer 128 sf = (ib,sa) /\
emit_void MSTORE [ib.buf_operand; h] sa = ((),sb) /\
(do dst <- emit_op ADD [ib.buf_operand; Lit 32w];
    emit_void MSTORE [dst; v] od) sb = ((),sc) /\
(do dst <- emit_op ADD [ib.buf_operand; Lit 64w];
    emit_void MSTORE [dst; r] od) sc = ((),sd) /\
(do dst <- emit_op ADD [ib.buf_operand; Lit 96w];
    emit_void MSTORE [dst; sig] od) sd = ((),sp) /\
compile_alloc_buffer 32 sp = (ob,sm) /\
emit_void MSTORE [ob.buf_operand; Lit 0w] sm = ((),sz) /\
fn_has_code sf sz func /\ fn_inst_ids_distinct func /\
local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
       not_fresh_at sf x) /\
(!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
       not_fresh_at sf x) /\
storage_trace_domain cx st0 es.storage_trace /\
(!H. valid_horizon cx st0 H es.storage_trace ==>
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
  (!q. x = Var q ==> not_fresh_at sf q)) [h;v;r;sig] /\
alloca_history func s /\ return_buf_frame d cenv sf s /\
~s.vs_halted /\ s.vs_current_bb = sf.cs_current_bb /\
s.vs_inst_idx = LENGTH sf.cs_current_insts ==>
?t Gf tnf qi qo wi wo.
  ib.buf_operand = Var qi /\ ob.buf_operand = Var qo /\
  not_fresh_at sz qi /\ not_fresh_at sz qo /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tnf)) /\
  ~t.vs_halted /\ t.vs_current_bb = sz.cs_current_bb /\
  t.vs_inst_idx = LENGTH sz.cs_current_insts /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  local_ptrs_reserved cenv sz /\ return_buf_frame d cenv sz t /\
  lookup_var qi t = SOME wi /\ lookup_var qo t = SOME wo /\
  lo <= w2n wi /\ lo <= w2n wo /\
  ptr_covers Gf tnf qi t 128 /\ ptr_covers Gf tnf qo t 32 /\
  FLOOKUP t.vs_allocas sf.cs_next_id = SOME (w2n wi,128) /\
  FLOOKUP t.vs_allocas sp.cs_next_id = SOME (w2n wo,32) /\
  w2n wi+128 < dimword (:256) /\ w2n wo+32 < dimword (:256) /\
  w2n wi+128 <= t.vs_alloca_next /\ w2n wo+32 <= t.vs_alloca_next /\
  regions_disjoint (w2n wi) 128 (w2n wo) 32 /\
  mem_bytes_at (w2n wi) 128 t.vs_memory =
    word_to_bytes wh T ++ word_to_bytes wv T ++
    word_to_bytes wr T ++ word_to_bytes ws T /\
  mem_word_at (w2n wo) t.vs_memory = 0w /\
  (!i. w2n wi <= i /\ i < w2n wi+128 ==> i NOTIN tnf.t_mem) /\
  (!i. w2n wo <= i /\ i < w2n wo+32 ==> i NOTIN tnf.t_mem) /\
  (!x. not_fresh_at sf x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid off len. aid < sf.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  wb_frame cenv es es sf s t /\ pure_frame cenv func es sf s t /\
  (!name b len. local_region cenv es.scopes t name b len ==>
    regions_disjoint (w2n wo) 32 b len) /\
  (!aid b len. aid < sf.cs_next_id /\
    FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n wo) 32 b len) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wo) 32 off (type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es t /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es Gf tnf t) /\
  (!es0 sk s0 G0 tn0.
    sk.cs_next_var <= sf.cs_next_var /\
    ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn /\
    (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
      aid < sk.cs_next_id ==> off+len <= s.vs_alloca_next) /\
    (!name b len. local_region cenv es0.scopes s0 name b len ==>
      b+len <= s.vs_alloca_next) ==>
    ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gf tnf)

Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (fn th => qpat_assum
      `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
      (strip_assume_tac o MATCH_MP th)) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at (DF (storage_trace_horizon _)) _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `(do emit_void MSTORE [ib.buf_operand; h];
       p1 <- emit_op ADD [ib.buf_operand; Lit 32w];
       emit_void MSTORE [p1; v];
       p2 <- emit_op ADD [ib.buf_operand; Lit 64w];
       emit_void MSTORE [p2; r];
       p3 <- emit_op ADD [ib.buf_operand; Lit 96w];
       emit_void MSTORE [p3; sig] od) sa = ((),sp)` by
    (irule recovery_payload_group >> simp[]) >>
  drule_all ecrecover_input_stores_shape >> strip_tac >>
  `ci_mono sf sa /\ ci_mono sp sm /\ ci_mono sm sz` by
    (mp_tac (Q.SPECL [`128`,`sf`] ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`32`,`sp`] ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`MSTORE`,`[ob.buf_operand;Lit 0w]`,`sm`] ci_mono_emit_void) >>
     simp[] >> metis_tac[]) >>
  `ci_mono sa sp` by
    (simp[ci_mono_def,cs_extends_def] >> qexists_tac `[]` >>
     fs[same_blocks_def] >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sf sa /\ cs_extends sa sp /\
   cs_extends sp sm /\ cs_extends sm sz /\
   sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sp.cs_next_var /\
   sp.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sz.cs_next_var /\
   sf.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id <= sp.cs_next_id /\
   sp.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sz.cs_next_id` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
   local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sz` by
    metis_tac[local_ptrs_reserved_next_var,LESS_EQ_TRANS] >>
  `fn_has_code sf sa func /\ fn_has_code sa sp func /\
   fn_has_code sp sm func /\ fn_has_code sm sz func` by
    (rpt conj_tac >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `128 < dimword (:256) /\ 32 < dimword (:256)` by
    simp[wordsTheory.dimword_def] >>
  qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s`
    (fn ssr => let
       val horizon = hd (snd (strip_comb (concl ssr)));
       val th = alloc_buffer_origin_ptr_path;
       val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
         (free_vars (concl th)));
       val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
       val (_,post) = strip_exists (snd (dest_imp (concl typed)));
       val hv' = fst (dest_forall (List.nth (strip_conj post,6)));
       val typed = INST_TYPE (match_type (type_of hv') (type_of horizon)) typed;
     in mp_tac (Q.INST [`n` |-> `128`,`sa` |-> `sf`,`sb` |-> `sa`,
       `buf` |-> `ib`,`H` |-> `storage_trace_horizon es.storage_trace`] typed) end) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `qi` (qx_choose_then `wi`
    (qx_choose_then `s1` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac))))) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s1 /\
    ghost_inv_at (DF H) lo d cenv cx es G1 tn1 s1` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (fn th => qpat_assum `valid_horizon cx st0 H es.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     conj_tac
     >- (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
           (fn initial => FIRST_ASSUM (fn th => let
              val actualH = hd (snd (strip_comb (concl initial)));
            in ACCEPT_TAC (MATCH_MP (SPEC actualH th) initial) end))) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (fn ssr => let
          val horizon = hd (snd (strip_comb (concl ssr)));
          val th = alloc_buffer_ghost_inv_at;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in MATCH_MP_TAC (Q.INST [`D` |-> `DF H`,`H` |-> `H`,`ctx` |-> `ctx`,
          `func` |-> `func`,`sa` |-> `sf`,`s` |-> `s`,`t` |-> `s1`,
          `G` |-> `G`,`tn` |-> `tn`,`G'` |-> `G1`,`tn'` |-> `tn1`,
          `e` |-> `w2n (wi:256 word)+128`] typed) end) >> simp[]) >>
  `!a. MEM a [h;v;r;sig] ==>
    eval_operand a s1 = eval_operand a s /\ op_taint tn1 a = {} /\
    (!l. a <> Label l) /\ (!q. a = Var q ==> not_fresh_at sa q)` by
    (qpat_assum `!x. not_fresh_at sf x ==> lookup_var x s1 = _ /\ _`
       (fn frame => qpat_assum `EVERY _ [h;v;r;sig]`
         (fn shapes => qpat_assum `sf.cs_next_var <= sa.cs_next_var`
           (fn growth => POP_ASSUM_LIST (K all_tac) >>
             MAP_EVERY assume_tac [frame,shapes,growth]))) >>
     qx_gen_tac `a` >> disch_tac >>
     `op_taint tn a = {} /\ (!l. a <> Label l) /\
      (!q. a = Var q ==> not_fresh_at sf q)` by
       (qpat_assum `EVERY _ [h;v;r;sig]`
          (fn shapes => qpat_assum `MEM a [h;v;r;sig]`
            (ACCEPT_TAC o BETA_RULE o MATCH_MP (REWRITE_RULE [EVERY_MEM] shapes)))) >>
     qpat_x_assum `EVERY _ [h;v;r;sig]` kall_tac >>
     Cases_on `a` >> gvs[eval_operand_def,op_taint_def] >>
     metis_tac[not_fresh_at_mono]) >>
  `eval_operand h s1 = SOME wh /\ eval_operand v s1 = SOME wv /\
   eval_operand r s1 = SOME wr /\ eval_operand sig s1 = SOME ws` by simp[] >>
  `EVERY (\a. op_taint tn1 a = {} /\ (!l. a <> Label l) /\
     (!q. a = Var q ==> not_fresh_at sa q)) [h;v;r;sig]` by
    simp[EVERY_DEF] >>
  `emitted_insts sa sp = emitted_insts sa sb ++ emitted_insts sb sc ++
    emitted_insts sc sd ++ emitted_insts sd sp` by
    (imp_res_tac direct_store_compiler_shape >>
     imp_res_tac offset_store_compiler_shape >>
     imp_res_tac compiler_append_trans >> simp[APPEND_ASSOC] >> metis_tac[]) >>
  mp_tac (Q.INST [`D` |-> `ARB`,`fn` |-> `func`,`bufroot` |-> `qi`,
    `s` |-> `s1`,`G` |-> `G1`,`tn` |-> `tn1`,`b` |-> `wi`,
    `q` |-> `sig`,`wq` |-> `ws`,`se` |-> `sp`] recovery_input_staging_checked) >>
  (impl_tac >-
    (qpat_assum `ib.buf_operand = Var qi`
       (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >> simp[])) >>
  disch_then (qx_choose_then `raw2` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  `run_inst_seq_mem_ok (emitted_insts sa sp) s1` by
    (MATCH_MP_TAC (Q.INST [`sb` |-> `sp`,`s` |-> `s1`,
       `base_op` |-> `ib.buf_operand`,`p` |-> `wi`]
       ecrecover_input_stores_mem) >>
     simp[eval_operand_def] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA /\
       i.inst_opcode <> GAS /\ i.inst_opcode <> ISTORE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sp)` by
    (qpat_assum `(do emit_void MSTORE _; _ od) sa = ((),sp)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def,emit_void_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,fresh_id_def,fresh_var_def,emit_def] >>
     strip_tac >> gvs[] >>
     simp[emitted_insts_def,DROP_APPEND1,mk_inst_def,is_terminator_def]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G1 tn1 (emitted_insts sa sp)
       s1 G2 tn2` by
    (gen_tac >>
     mp_tac (Q.INST [`D` |-> `D`,`fn` |-> `func`,`bufroot` |-> `qi`,
       `s` |-> `s1`,`G` |-> `G1`,`tn` |-> `tn1`,`b` |-> `wi`,
       `q` |-> `sig`,`wq` |-> `ws`,`se` |-> `sp`] recovery_input_staging_checked) >>
     (impl_tac >-
       (qpat_assum `ib.buf_operand = Var qi`
          (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >> simp[])) >>
     disch_then (qx_choose_then `u` (qx_choose_then `Gu`
       (qx_choose_then `tnu` strip_assume_tac))) >>
     `s1 with vs_inst_idx := s1.vs_inst_idx = s1` by
       simp[venom_state_component_equality] >>
     qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ Gu tnu`
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `s1.vs_inst_idx`) >>
     qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ G2 tn2`
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `s1.vs_inst_idx`) >>
     `Gu = G2 /\ tnu = tn2` by
       (MATCH_MP_TAC (Q.INST [`D1` |-> `D`,`D2` |-> `ARB`,
          `lo` |-> `0`,`ctx` |-> `ctx`,`fn` |-> `func`,`PG` |-> `PG`]
         (Q.SPECL [`emitted_insts sa sp`,`s1`,`G1`,`tn1`,
           `Gu`,`tnu`,`G2`,`tn2`] inst_seq_ptr_ghost_unique)) >> simp[]) >>
     gvs[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G1 tn1 (emitted_insts sa sp)
       s1 G2 tn2` by
    (gen_tac >> MATCH_MP_TAC (Q.INST [`lo0` |-> `0`]
       (Q.SPECL [`emitted_insts sa sp`,`s1`,`G1`,`tn1`,`G2`,`tn2`]
         inst_seq_ptr_lower_bound_transport)) >> simp[] >> fs[EVERY_MEM]) >>
  `~s1.vs_halted` by
    (qpat_assum `s1 with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o AP_TERM ``\z. z.vs_halted``) >> simp[]) >>
  qabbrev_tac `s2 = raw2 with vs_inst_idx := LENGTH sp.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s1,G1,tn1) [] (OK s2,G2,tn2)` by
    (gen_tac >> qunabbrev_tac `s2` >>
     MATCH_MP_TAC (Q.SPECL [`emitted_insts sa sp`,`sa`,`sp`,`s1`,
       `raw2`,`G1`,`tn1`,`G2`,`tn2`]
       bodyFullUnwrapRunTheory.emitted_origin_ptr_path) >>
     fs[EVERY_MEM,same_blocks_def] >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace)
     ctx func cenv cx es s1` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ s1`
       (fn th => qpat_assum
         `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >> simp[]) >>
  `MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w 128)]
       [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `(cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n wi) 128 off (type_memory_size tv))` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s1`
       (fn ssr => let
          val horizon = hd (snd (strip_comb (concl ssr)));
          val th = precompile_alloca_immutable_disjoint;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in mp_tac (Q.INST [`s` |-> `s1`,`b` |-> `w2n (wi:256 word)`,
          `sz` |-> `128`,`H` |-> `storage_trace_horizon es.storage_trace`,
          `inst` |-> `mk_inst sf.cs_next_id ALLOCA [Lit (n2w 128)]
            [STRING #"%" (toString sf.cs_next_var)]`] typed) end) >>
     simp[mk_inst_def]) >>
  `!aid b len. aid < sf.cs_next_id /\
       FLOOKUP s1.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n wi) 128 b len` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s1`
       (fn ssr => let
          val horizon = hd (snd (strip_comb (concl ssr)));
          val th = state_allocations_disjoint;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in MATCH_MP_TAC (Q.INST [`t` |-> `s1`,`a` |-> `sf.cs_next_id`,
          `b` |-> `aid`,`p` |-> `w2n (wi:256 word)`,`n` |-> `128`,
          `q` |-> `b`,`m` |-> `len`,
          `H` |-> `storage_trace_horizon es.storage_trace`] typed) end) >>
     simp[] >> decide_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es raw2 /\
     wb_frame cenv es es sf s1 raw2 /\
     (raw2 with <|vs_vars := s1.vs_vars; vs_memory := s1.vs_memory|>) = s1 /\
     mem_bytes_at (w2n wi) 128 raw2.vs_memory =
       word_to_bytes wh T ++ word_to_bytes wv T ++
       word_to_bytes wr T ++ word_to_bytes ws T /\
     (!b len. regions_disjoint (w2n wi) 128 b len ==>
       mem_bytes_at b len raw2.vs_memory = mem_bytes_at b len s1.vs_memory)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ s1`
       (fn th => qpat_assum `valid_horizon cx st0 H es.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s1`
       (fn ssr => let
          val horizon = hd (snd (strip_comb (concl ssr)));
          val th = ecrecover_input_stores_sim;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in mp_tac (Q.INST [`sb` |-> `sp`,`sc` |-> `sf`,`s` |-> `s1`,
          `base_op` |-> `ib.buf_operand`,`p` |-> `wi`,`H` |-> `H`] typed) end) >>
     (impl_tac >- (simp[eval_operand_def] >> fs[EVERY_MEM] >> metis_tac[])) >>
     disch_then (qx_choose_then `u` strip_assume_tac) >>
     `u = raw2` by
       (qpat_assum `run_inst_seq _ s1 = OK u`
          (fn ru => qpat_assum `run_inst_seq _ s1 = OK raw2`
            (fn rr => qpat_assum `emitted_insts sa sp = _`
              (fn cut => POP_ASSUM_LIST (K all_tac) >>
                MAP_EVERY assume_tac [ru,rr,cut]))) >>
        fs[APPEND_ASSOC] >> metis_tac[]) >> gvs[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ raw2 /\ _`
    (fn th => qpat_assum
      `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
      (strip_assume_tac o MATCH_MP th)) >>
  qpat_assum `raw2 with <|vs_vars := _; vs_memory := _|> = s1`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `tn2.t_imm = tn1.t_imm` by
    (MATCH_MP_TAC (Q.INST [`D` |-> `ARB`,`lo` |-> `0`,
       `ctx` |-> `ctx`,`func` |-> `func`,`PG` |-> `PG`]
       (Q.SPECL [`emitted_insts sa sp`,`G1`,`tn1`,`s1`,`G2`,`tn2`]
         inst_seq_ptr_immutable_taint_frame)) >> simp[] >> fs[EVERY_MEM]) >>
  `lo <= w2n wi /\ lo <= s1.vs_alloca_next` by
    (fs[allocas_from_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `allocas_from lo s2 /\ lo <= s2.vs_alloca_next /\
   ~s2.vs_halted /\ s2.vs_current_bb = sp.cs_current_bb /\
   s2.vs_inst_idx = LENGTH sp.cs_current_insts` by
    (fs[Abbr`s2`,allocas_from_def,same_blocks_def] >> metis_tac[]) >>
  `alloca_history func s2` by
    (qunabbrev_tac `s2` >>
     `alloca_inv s1` by
       (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s1`
          (strip_assume_tac o PURE_REWRITE_RULE [stmt_state_rel_def]) >> simp[]) >>
     MATCH_MP_TAC (Q.SPECL [`emitted_insts sa sp`,`sa`,`sp`,`s1`,`raw2`]
       emitted_alloca_history) >>
     fs[EVERY_MEM,same_blocks_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s1` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s1`
       (strip_assume_tac o PURE_REWRITE_RULE [stmt_state_rel_def,state_rel_def]) >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s2 /\
    ghost_inv_at (DF H) lo d cenv cx es G2 tn2 s2` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ s1`
       (fn th => qpat_assum `valid_horizon cx st0 H es.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ raw2 /\ _`
       (fn th => qpat_assum `valid_horizon cx st0 H es.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     conj_tac >- simp[Abbr`s2`,stmt_state_rel_inst_idx] >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G1 tn1 s1`
       (fn initial => let
          val actualD = hd (snd (strip_comb (concl initial)));
          val th = unwrap_slot_copy_ghost_inv_at;
          val dv = valOf (List.find (fn v => fst (dest_var v) = "D")
            (free_vars (concl th)));
          val dead_inst = INST [dv |-> actualD] th;
        in MATCH_MP_TAC (Q.INST [`s` |-> `s1`,`z` |-> `s2`,
          `G` |-> `G1`,`tn` |-> `tn1`,`H` |-> `G2`,`tf` |-> `tn2`,
          `start` |-> `w2n (wi:256 word)`,`nb` |-> `128`,`sa` |-> `sa`]
          dead_inst) end) >>
     simp[Abbr`s2`] >> rpt conj_tac
     >- metis_tac[not_fresh_at_mono]
     >- metis_tac[not_fresh_at_mono]
     >- (qpat_assum `!name b len. local_region cenv es.scopes s1 name b len ==> _`
           (fn th => POP_ASSUM_LIST (K all_tac) >> assume_tac th) >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[])
     >- (rpt strip_tac >>
         qpat_assum `!p. not_fresh_at sa p ==> lookup_var p raw2 = _ /\ _`
           (fn frame => qpat_assum `not_fresh_at sa x`
             (strip_assume_tac o MATCH_MP (Q.SPEC `x` frame))) >>
         fs[venomStateTheory.lookup_var_def])
     >- (rpt strip_tac >>
         qpat_assum `!b len. regions_disjoint (w2n wi) 128 b len ==> _`
           (mp_tac o Q.SPECL [`a`,`k`]) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def])
     >- (qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G1 tn1 s1`
           (strip_assume_tac o PURE_REWRITE_RULE [ghost_inv_at_def]) >>
         gvs[stor_taint_ok_at_def])) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ s2`
    (fn th => qpat_assum
      `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
      (strip_assume_tac o MATCH_MP th)) >>
  qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s2`
    (fn ssr => let
       val horizon = hd (snd (strip_comb (concl ssr)));
       val th = alloc_buffer_origin_ptr_path;
       val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
         (free_vars (concl th)));
       val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
       val (_,post) = strip_exists (snd (dest_imp (concl typed)));
       val hv' = fst (dest_forall (List.nth (strip_conj post,6)));
       val typed = INST_TYPE (match_type (type_of hv') (type_of horizon)) typed;
     in mp_tac (Q.INST [`n` |-> `32`,`sa` |-> `sp`,`sb` |-> `sm`,
       `s` |-> `s2`,`G` |-> `G2`,`tn` |-> `tn2`,`buf` |-> `ob`,
       `H` |-> `storage_trace_horizon es.storage_trace`] typed) end) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `qo` (qx_choose_then `wo`
    (qx_choose_then `s3` (qx_choose_then `G3`
      (qx_choose_then `tn3` strip_assume_tac))))) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s3 /\
    ghost_inv_at (DF H) lo d cenv cx es G3 tn3 s3` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ s2`
       (fn th => qpat_assum `valid_horizon cx st0 H es.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     conj_tac
     >- (qpat_assum `stmt_state_rel H ctx func cenv cx es s2`
           (fn initial => FIRST_ASSUM (fn th => let
              val actualH = hd (snd (strip_comb (concl initial)));
            in ACCEPT_TAC (MATCH_MP (SPEC actualH th) initial) end))) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s2`
       (fn ssr => let
          val horizon = hd (snd (strip_comb (concl ssr)));
          val th = alloc_buffer_ghost_inv_at;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in MATCH_MP_TAC (Q.INST [`D` |-> `DF H`,`H` |-> `H`,`ctx` |-> `ctx`,
          `func` |-> `func`,`sa` |-> `sp`,`s` |-> `s2`,`t` |-> `s3`,
          `G` |-> `G2`,`tn` |-> `tn2`,`G'` |-> `G3`,`tn'` |-> `tn3`,
          `e` |-> `w2n (wo:256 word)+32`] typed) end) >> simp[] >>
     metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]) >>
  mp_tac (Q.INST [`D` |-> `ARB`,`fn` |-> `func`,`bufroot` |-> `qo`,
    `sa` |-> `sm`,`sb` |-> `sz`,`s` |-> `s3`,`G` |-> `G3`,
    `tn` |-> `tn3`,`a` |-> `wo`,`v` |-> `Lit 0w`,`w` |-> `0w`]
    emitted_direct_word_store_checked) >>
  (impl_tac >-
    (qpat_assum `ob.buf_operand = Var qo`
       (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
     simp[eval_operand_def,op_taint_def])) >>
  disch_then (qx_choose_then `raw4` (qx_choose_then `tn4` strip_assume_tac)) >>
  `run_inst_seq_mem_ok (emitted_insts sm sz) s3` by
    (MATCH_MP_TAC (Q.SPECL [`ob.buf_operand`,`Lit 0w`,`sm`,`sz`,`s3`,`wo`]
       emit_mstore_mem_ok) >> simp[eval_operand_def]) >>
  `sz.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sz /\
   same_blocks sm sz /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA /\
     i.inst_opcode <> GAS /\ i.inst_opcode <> ISTORE /\
     ~is_terminator i.inst_opcode) (emitted_insts sm sz)` by
    (qpat_assum `emit_void MSTORE _ sm = ((),sz)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_void_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
       fresh_id_def,emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def,DROP_APPEND1,mk_inst_def,is_terminator_def,
       same_blocks_def]) >>
  `s3 with vs_inst_idx := s3.vs_inst_idx = s3` by
    simp[venom_state_component_equality] >>
  qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ G3 tn4`
    (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `s3.vs_inst_idx`) >>
  `!D. inst_seq_ptr D 0 ctx func PG G3 tn3 (emitted_insts sm sz)
       s3 G3 tn4` by
    (gen_tac >>
     mp_tac (Q.INST [`D` |-> `D`,`fn` |-> `func`,`bufroot` |-> `qo`,
       `sa` |-> `sm`,`sb` |-> `sz`,`s` |-> `s3`,`G` |-> `G3`,
       `tn` |-> `tn3`,`a` |-> `wo`,`v` |-> `Lit 0w`,`w` |-> `0w`]
       emitted_direct_word_store_checked) >>
     (impl_tac >-
       (qpat_assum `ob.buf_operand = Var qo`
          (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
        simp[eval_operand_def,op_taint_def])) >>
     disch_then (qx_choose_then `u` (qx_choose_then `tnu` strip_assume_tac)) >>
     qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ G3 tnu`
       (assume_tac o SIMP_RULE (srw_ss()) [] o Q.SPEC `s3.vs_inst_idx`) >>
     `G3 = G3 /\ tnu = tn4` by
       (MATCH_MP_TAC (Q.INST [`D1` |-> `D`,`D2` |-> `ARB`,
          `lo` |-> `0`,`ctx` |-> `ctx`,`fn` |-> `func`,`PG` |-> `PG`]
         (Q.SPECL [`emitted_insts sm sz`,`s3`,`G3`,`tn3`,
           `G3`,`tnu`,`G3`,`tn4`] inst_seq_ptr_ghost_unique)) >> simp[]) >>
     gvs[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G3 tn3 (emitted_insts sm sz)
       s3 G3 tn4` by
    (gen_tac >> MATCH_MP_TAC (Q.INST [`lo0` |-> `0`]
       (Q.SPECL [`emitted_insts sm sz`,`s3`,`G3`,`tn3`,`G3`,`tn4`]
         inst_seq_ptr_lower_bound_transport)) >> simp[] >> fs[EVERY_MEM]) >>
  `~s3.vs_halted` by
    (qpat_assum `s3 with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|> = s2`
       (mp_tac o AP_TERM ``\z. z.vs_halted``) >> simp[]) >>
  qabbrev_tac `t = raw4 with vs_inst_idx := LENGTH sz.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s3,G3,tn3) [] (OK t,G3,tn4)` by
    (gen_tac >> qunabbrev_tac `t` >>
     MATCH_MP_TAC (Q.SPECL [`emitted_insts sm sz`,`sm`,`sz`,`s3`,
       `raw4`,`G3`,`tn3`,`G3`,`tn4`]
       bodyFullUnwrapRunTheory.emitted_origin_ptr_path) >>
     fs[EVERY_MEM,same_blocks_def] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ s3`
    (fn th => qpat_assum
      `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
      (strip_assume_tac o MATCH_MP th)) >>
  `MEM (mk_inst sp.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ s3`
       (fn th => qpat_assum `valid_horizon cx st0 H es.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     simp[Abbr`t`,stmt_state_rel_inst_idx] >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s3`
       (fn initial => let
          val horizon = hd (snd (strip_comb (concl initial)));
          val th = literal_mstore_state_rel;
          val hv = fst (dest_forall (concl th));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in MATCH_MP_TAC (Q.SPECL [`H`,`func`,`cenv`,`cx`,`es`,`s3`,
          `w2n (wo:256 word)`,`0w`,
          `mk_inst sp.cs_next_id ALLOCA [Lit (n2w 32)]
            [STRING #"%" (toString sp.cs_next_var)]`,
          `w2n (wo:256 word)`,`32`,`ctx`] typed) end) >>
     simp[mk_inst_def] >>
     conj_tac >- gvs[] >>
     qpat_assum `!name b len. local_region cenv es.scopes s3 name b len ==> _`
       (fn th => POP_ASSUM_LIST (K all_tac) >> assume_tac th) >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `tn4.t_imm = tn3.t_imm` by
    (MATCH_MP_TAC (Q.INST [`D` |-> `ARB`,`lo` |-> `0`,
       `ctx` |-> `ctx`,`func` |-> `func`,`PG` |-> `PG`]
       (Q.SPECL [`emitted_insts sm sz`,`G3`,`tn3`,`s3`,`G3`,`tn4`]
         inst_seq_ptr_immutable_taint_frame)) >> simp[] >> fs[EVERY_MEM]) >>
  `lo <= w2n wo /\ lo <= s3.vs_alloca_next` by
    (fs[allocas_from_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next /\
   ~t.vs_halted /\ t.vs_current_bb = sz.cs_current_bb /\
   t.vs_inst_idx = LENGTH sz.cs_current_insts` by
    (gvs[Abbr`t`,venomStateTheory.mstore_def,
      venomStateTheory.write_memory_with_expansion_def,
      venomStateTheory.write_memory_def,same_blocks_def,allocas_from_def] >>
     metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s3 /\ alloca_inv s3` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s3`
       (strip_assume_tac o PURE_REWRITE_RULE [stmt_state_rel_def,state_rel_def]) >> simp[]) >>
  `!x. lookup_var x t = lookup_var x s3 /\
       op_taint tn4 (Var x) = op_taint tn3 (Var x)` by
    (gen_tac >> qunabbrev_tac `t` >>
     qpat_assum `tn4.t_var = tn3.t_var`
       (fn taint => qpat_assum `raw4 = mstore _ _ s3`
         (fn endpoint => POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [taint,endpoint])) >>
     simp[venomStateTheory.lookup_var_def,
       venomStateTheory.mstore_def,venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.write_memory_def,op_taint_def]) >>
  `!b len. regions_disjoint (w2n wo) 32 b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s3.vs_memory` by
    (rpt strip_tac >> simp[Abbr`t`] >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx es G3 tn4 t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ s3`
       (fn th => qpat_assum `valid_horizon cx st0 H es.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G3 tn3 s3`
       (fn initial => let
          val actualD = hd (snd (strip_comb (concl initial)));
          val th = unwrap_slot_copy_ghost_inv_at;
          val dv = valOf (List.find (fn v => fst (dest_var v) = "D")
            (free_vars (concl th)));
          val dead_inst = INST [dv |-> actualD] th;
        in MATCH_MP_TAC (Q.INST [`s` |-> `s3`,`z` |-> `t`,
          `G` |-> `G3`,`tn` |-> `tn3`,`H` |-> `G3`,`tf` |-> `tn4`,
          `start` |-> `w2n (wo:256 word)`,`nb` |-> `32`,`sa` |-> `sm`]
          dead_inst) end) >>
     simp[] >> rpt conj_tac
     >- metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]
     >- metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]
     >- (qpat_assum `!name b len. local_region cenv es.scopes s3 name b len ==> _`
           (fn th => POP_ASSUM_LIST (K all_tac) >> assume_tac th) >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[])
     >- (rpt strip_tac >>
         qpat_assum `!b len. regions_disjoint (w2n wo) 32 b len ==> _`
           (mp_tac o Q.SPECL [`a`,`k`]) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def])
     >- (qunabbrev_tac `t` >>
         qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G3 tn3 s3`
           (fn ghost => qpat_assum `tn4.t_stor = tn3.t_stor`
             (fn stor => qpat_assum `tn4.t_trans = tn3.t_trans`
               (fn trans => qpat_assum `tn4.t_imm = tn3.t_imm`
                 (fn imm => qpat_assum `raw4 = mstore _ _ s3`
                   (fn endpoint => POP_ASSUM_LIST (K all_tac) >>
                     MAP_EVERY assume_tac [ghost,stor,trans,imm,endpoint]))))) >>
         gvs[ghost_inv_at_def,stor_taint_ok_at_def,venomStateTheory.mstore_def,
           venomStateTheory.write_memory_with_expansion_def,
           venomStateTheory.write_memory_def])) >>
  `alloca_history func t` by
    (qunabbrev_tac `t` >>
     MATCH_MP_TAC (Q.SPECL [`emitted_insts sm sz`,`sm`,`sz`,`s3`,`raw4`]
       emitted_alloca_history) >>
     fs[EVERY_MEM,same_blocks_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G3,tn4)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (assume_tac o Q.SPEC `D`) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s1,G1,tn1) _ _`
       (assume_tac o Q.SPEC `D`) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s2,G2,tn2) _ _`
       (assume_tac o Q.SPEC `D`) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s3,G3,tn3) _ _`
       (assume_tac o Q.SPEC `D`) >>
     POP_ASSUM_LIST (fn ths => MAP_EVERY assume_tac (List.take (ths,4))) >>
     metis_tac[gas_origin_ptr_path_append,APPEND]) >>
  `s1.vs_memory = s.vs_memory` by
    (qpat_assum `s1 with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o AP_TERM ``\z. z.vs_memory``) >> simp[]) >>
  `s3.vs_memory = s2.vs_memory` by
    (qpat_assum `s3 with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s2`
       (mp_tac o AP_TERM ``\z. z.vs_memory``) >> simp[]) >>
  `s2.vs_memory = raw2.vs_memory /\ s2.vs_allocas = s1.vs_allocas /\
   s2.vs_alloca_next = s1.vs_alloca_next /\
   t.vs_allocas = s3.vs_allocas /\ t.vs_alloca_next = s3.vs_alloca_next` by
    (qunabbrev_tac `s2` >> qunabbrev_tac `t` >>
     qpat_assum `raw2.vs_allocas = s1.vs_allocas`
       (fn allocas => qpat_assum `raw2.vs_alloca_next = s1.vs_alloca_next`
         (fn frontier => qpat_assum `raw4 = mstore _ _ s3`
           (fn endpoint => POP_ASSUM_LIST (K all_tac) >>
             MAP_EVERY assume_tac [allocas,frontier,endpoint]))) >>
     simp[venomStateTheory.mstore_def,
      venomStateTheory.write_memory_with_expansion_def,
      venomStateTheory.write_memory_def]) >>
  `s.vs_alloca_next <= s2.vs_alloca_next /\
   s.vs_alloca_next <= t.vs_alloca_next` by metis_tac[LESS_EQ_TRANS] >>
  `!x. lookup_var x s2 = lookup_var x raw2` by
    simp[Abbr`s2`,venomStateTheory.lookup_var_def] >>
  `!x. not_fresh_at sf x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G3 x = FLOOKUP G x /\
     op_taint tn4 (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at sf x ==> lookup_var x s1 = _ /\ _`
       (fn a => qpat_assum `!x. not_fresh_at sa x ==> lookup_var x raw2 = _ /\ _`
         (fn b => qpat_assum `!x. not_fresh_at sp x ==> lookup_var x s3 = _ /\ _`
           (fn c => qpat_assum `!x. lookup_var x t = _ /\ _`
             (fn d => qpat_assum `!x. lookup_var x s2 = lookup_var x raw2`
               (fn idx => qpat_assum `sf.cs_next_var <= sa.cs_next_var`
                 (fn ab => qpat_assum `sa.cs_next_var <= sp.cs_next_var`
                   (fn bc => POP_ASSUM_LIST (K all_tac) >>
                     MAP_EVERY assume_tac [a,b,c,d,idx,ab,bc]))))))) >>
     metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry` by
    (rpt strip_tac >>
     qpat_assum `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> _`
       (fn th => qpat_assum `FLOOKUP s.vs_allocas aid = SOME entry`
         (assume_tac o MATCH_MP th)) >>
     qpat_assum `!aid e. FLOOKUP s2.vs_allocas aid = SOME e ==> _`
       (mp_tac o Q.SPECL [`aid`,`entry`]) >> simp[]) >>
  `FLOOKUP t.vs_allocas sf.cs_next_id = SOME (w2n wi,128) /\
   FLOOKUP t.vs_allocas sp.cs_next_id = SOME (w2n wo,32)` by
    (qpat_assum `!aid e. FLOOKUP s2.vs_allocas aid = SOME e ==> _`
       (fn frame =>
         `FLOOKUP s2.vs_allocas sf.cs_next_id = SOME (w2n wi,128)` by simp[] >>
         qpat_assum `FLOOKUP s2.vs_allocas sf.cs_next_id = SOME (w2n wi,128)`
           (assume_tac o MATCH_MP (Q.SPECL [`sf.cs_next_id`,`(w2n wi,128)`] frame))) >>
     gvs[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace)
     ctx func cenv cx es t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t`
       (fn th => qpat_assum
         `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
         (ACCEPT_TAC o MATCH_MP th))) >>
  `regions_disjoint (w2n wi) 128 (w2n wo) 32` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ t`
       (fn ssr => let
          val horizon = hd (snd (strip_comb (concl ssr)));
          val th = state_allocations_disjoint;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in MATCH_MP_TAC (Q.INST [`t` |-> `t`,`a` |-> `sf.cs_next_id`,
          `b` |-> `sp.cs_next_id`,`p` |-> `w2n (wi:256 word)`,`n` |-> `128`,
          `q` |-> `w2n (wo:256 word)`,`m` |-> `32`,
          `H` |-> `storage_trace_horizon es.storage_trace`] typed) end) >>
     simp[] >> decide_tac) >>
  `!b len. regions_disjoint (w2n wi) 128 b len /\
       regions_disjoint (w2n wo) 32 b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (qpat_assum `!b len. regions_disjoint (w2n wi) 128 b len ==> _`
       (fn input => qpat_assum `!b len. regions_disjoint (w2n wo) 32 b len ==> _`
         (fn output => qpat_assum `s1.vs_memory = s.vs_memory`
           (fn a => qpat_assum `s3.vs_memory = s2.vs_memory`
             (fn b => qpat_assum `s2.vs_memory = raw2.vs_memory`
               (fn c => POP_ASSUM_LIST (K all_tac) >>
                 MAP_EVERY assume_tac [input,output,a,b,c]))))) >> metis_tac[]) >>
  `mem_bytes_at (w2n wi) 128 t.vs_memory =
     word_to_bytes wh T ++ word_to_bytes wv T ++
     word_to_bytes wr T ++ word_to_bytes ws T /\
   mem_word_at (w2n wo) t.vs_memory = 0w` by
    (conj_tac
     >- (qpat_assum `!b len. regions_disjoint (w2n wo) 32 b len ==> _`
           (fn exterior => mp_tac (Q.SPECL [`w2n (wi:256 word)`,`128`] exterior)) >>
         `regions_disjoint (w2n wo) 32 (w2n wi) 128` by
           fs[loweringStateRelDefsTheory.regions_disjoint_def] >> simp[]) >>
     simp[Abbr`t`,valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  `not_fresh_at sp qi` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `!x. not_fresh_at sp x ==> lookup_var x s3 = _ /\ _`
    (fn frame => qpat_assum `not_fresh_at sp qi`
      (strip_assume_tac o MATCH_MP (Q.SPEC `qi` frame))) >>
  `lookup_var qi t = SOME wi /\ lookup_var qo t = SOME wo /\
   ptr_covers G3 tn4 qi t 128 /\ ptr_covers G3 tn4 qo t 32` by
    (qpat_assum `!x. lookup_var x t = _ /\ _`
       (fn frame => MAP_EVERY (strip_assume_tac o C SPEC frame)
         [``qi:string``,``qo:string``]) >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  `!aid b len. aid < sf.cs_next_id /\
     FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n wo) 32 b len` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ t`
       (fn ssr => let
          val horizon = hd (snd (strip_comb (concl ssr)));
          val th = state_allocations_disjoint;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in MATCH_MP_TAC (Q.INST [`t` |-> `t`,`a` |-> `sp.cs_next_id`,
          `b` |-> `aid`,`p` |-> `w2n (wo:256 word)`,`n` |-> `32`,
          `q` |-> `b`,`m` |-> `len`,
          `H` |-> `storage_trace_horizon es.storage_trace`] typed) end) >>
     simp[] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     regions_disjoint (w2n wi) 128 b len /\
     regions_disjoint (w2n wo) 32 b len` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s1 name b len` by
       (MATCH_MP_TAC (Q.SPECL [`cenv`,`es.scopes`,`sf`,`es.scopes`,
          `s`,`s1`,`name`,`b`,`len`] exprSimPropsTheory.local_region_frame_fwd) >>
        simp[] >> metis_tac[]) >>
     `local_region cenv es.scopes s3 name b len` by
       (MATCH_MP_TAC (Q.SPECL [`cenv`,`es.scopes`,`sf`,`es.scopes`,
          `s`,`s3`,`name`,`b`,`len`] exprSimPropsTheory.local_region_frame_fwd) >>
        simp[] >> metis_tac[]) >> metis_tac[]) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!b len. regions_disjoint (w2n wi) 128 b len /\ _ ==> _`
       (fn exterior => qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> _ /\ _`
         (fn separated => qpat_assum `local_region cenv es.scopes s name b len`
           (ACCEPT_TAC o MATCH_MP (Q.SPECL [`b`,`len`] exterior) o
             MATCH_MP (Q.SPECL [`name`,`b`,`len`] separated))))) >>
  `!aid off len. aid < sf.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_assum `!b len. regions_disjoint (w2n wi) 128 b len /\ _ ==> _`
       (fn exterior => qpat_assum `!aid b len. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==> _`
         (fn input => qpat_assum `!aid b len. aid < sf.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==> _`
           (fn output => qpat_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _`
             (fn prefix => POP_ASSUM_LIST (K all_tac) >>
               MAP_EVERY assume_tac [exterior,input,output,prefix])))) >> metis_tac[]) >>
  `wb_frame cenv es es sf s t` by
    (qpat_assum `!x. not_fresh_at sf x ==> lookup_var x t = _ /\ _`
       (fn vars => qpat_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _`
         (fn prefix => qpat_assum `!aid off len. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==> _`
           (fn memory => qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> mem_bytes_at _ _ t.vs_memory = _`
             (fn locals => POP_ASSUM_LIST (K all_tac) >>
               MAP_EVERY assume_tac [vars,prefix,memory,locals])))) >>
     `locals_kept cenv es es s t` by
       (irule exprSimPropsTheory.locals_kept_regions >> first_assum ACCEPT_TAC) >>
     simp[wb_frame_def] >> metis_tac[]) >>
  `sf.cs_next_id <= sp.cs_next_id` by decide_tac >>
  `pure_frame cenv func es sf s t` by
    (rewrite_tac[pure_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     `regions_disjoint off len (w2n wi) 128 /\
      regions_disjoint off len (w2n wo) 32` by
       (conj_tac
        >- (qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _`
              (fn clear => MATCH_MP_TAC (Q.SPECL
                [`mk_inst sf.cs_next_id ALLOCA [Lit (n2w 128)]
                    [STRING #"%" (toString sf.cs_next_var)]`,
                 `w2n (wi:256 word)`,`128`] clear)) >> simp[mk_inst_def]) >>
        qpat_assum `!inst b sz. MEM inst _ /\ _ ==> _`
          (fn clear => MATCH_MP_TAC (Q.SPECL
            [`mk_inst sp.cs_next_id ALLOCA [Lit (n2w 32)]
                [STRING #"%" (toString sp.cs_next_var)]`,
             `w2n (wo:256 word)`,`32`] clear)) >>
        qpat_assum `MEM (mk_inst sp.cs_next_id ALLOCA _ _) (fn_insts func)`
          (fn instruction => qpat_assum `FLOOKUP t.vs_allocas sp.cs_next_id = SOME (w2n wo,32)`
            (fn site => qpat_assum `sf.cs_next_id <= sp.cs_next_id`
              (fn growth => POP_ASSUM_LIST (K all_tac) >>
                MAP_EVERY assume_tac [instruction,site,growth]))) >>
        gvs[mk_inst_def]) >>
     qpat_assum `!b len. regions_disjoint (w2n wi) 128 b len /\ _ ==> _`
       (fn exterior => MATCH_MP_TAC (Q.SPECL [`off`,`len`] exterior)) >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `sf.cs_next_var <= sz.cs_next_var /\ sf.cs_next_id <= sp.cs_next_id /\
   not_fresh_at sz qi /\ not_fresh_at sz qo` by
    metis_tac[not_fresh_at_mono,LESS_EQ_TRANS] >>
  `return_buf_frame d cenv sz t` by
    (MATCH_MP_TAC (Q.SPECL [`d`,`cenv`,`cenv`,`sf`,`sz`,`s`,`t`]
       return_buf_frame_frame) >> simp[] >> metis_tac[]) >>
  `!i. w2n wi <= i /\ i < w2n wi+128 ==> i NOTIN tn4.t_mem` by
    (qpat_assum `!i. w2n wi <= i /\ i < w2n wi+128 ==> i NOTIN tn2.t_mem`
       (fn clean => qpat_assum `!i. i IN tn3.t_mem <=> _`
         (fn allocation => qpat_assum `tn4.t_mem = tn3.t_mem DIFF _`
           (fn store => qpat_assum `w2n wi+128 <= s1.vs_alloca_next`
             (fn bound => qpat_assum `s2.vs_alloca_next = s1.vs_alloca_next`
               (fn frontier => POP_ASSUM_LIST (K all_tac) >>
                 MAP_EVERY assume_tac [clean,allocation,store,bound,frontier]))))) >>
     qx_gen_tac `i` >> strip_tac >>
     `i < s2.vs_alloca_next` by decide_tac >>
     `i NOTIN tn2.t_mem` by metis_tac[] >>
     `i NOTIN tn3.t_mem` by
       (qpat_assum `!i. i IN tn3.t_mem <=> _`
          (fn allocation => PURE_REWRITE_TAC [Q.SPEC `i` allocation]) >>
        simp[] >> decide_tac) >> simp[]) >>
  `!i. w2n wo <= i /\ i < w2n wo+32 ==> i NOTIN tn4.t_mem` by
    (qpat_assum `tn4.t_mem = tn3.t_mem DIFF _`
       (fn store => POP_ASSUM_LIST (K all_tac) >> assume_tac store) >>
     simp[IN_DIFF]) >>
  `!i. i < s.vs_alloca_next /\ i IN tn4.t_mem ==> i IN tn.t_mem` by
    (qpat_assum `!i. i IN tn1.t_mem <=> _`
       (fn first => qpat_assum `!i. i IN tn3.t_mem <=> _`
         (fn second => qpat_assum `tn2.t_mem = tn1.t_mem DIFF _`
           (fn input => qpat_assum `tn4.t_mem = tn3.t_mem DIFF _`
             (fn output => qpat_assum `s.vs_alloca_next <= s2.vs_alloca_next`
               (fn growth => POP_ASSUM_LIST (K all_tac) >>
                 MAP_EVERY assume_tac [first,second,input,output,growth]))))) >>
     qx_gen_tac `i` >> strip_tac >>
     `~(s.vs_alloca_next <= i) /\ ~(s2.vs_alloca_next <= i)` by decide_tac >>
     fs[IN_DIFF] >> metis_tac[IN_DIFF]) >>
  `!es0 sk s0 G0 tn0.
    sk.cs_next_var <= sf.cs_next_var /\
    ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn /\
    (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
      aid < sk.cs_next_id ==> off+len <= s.vs_alloca_next) /\
    (!name b len. local_region cenv es0.scopes s0 name b len ==>
      b+len <= s.vs_alloca_next) ==>
    ghost_kept_at lo cenv es0 sk G0 tn0 s0 G3 tn4` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn`
       (fn initial => qpat_assum `!x. not_fresh_at sf x ==> lookup_var x t = _ /\ _`
         (fn frame => qpat_assum `!i. i < s.vs_alloca_next /\ i IN tn4.t_mem ==> _`
           (fn taint => qpat_assum `lo <= s.vs_alloca_next`
             (fn floor => qpat_assum `sk.cs_next_var <= sf.cs_next_var`
               (fn growth => qpat_assum `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ _ ==> _`
                 (fn allocations => qpat_assum `!name b len. local_region cenv es0.scopes s0 name b len ==> _`
                   (fn locals => POP_ASSUM_LIST (K all_tac) >>
                     MAP_EVERY assume_tac [initial,frame,taint,floor,growth,allocations,locals]))))))) >>
     MATCH_MP_TAC (Q.INST [`es` |-> `es0`,`sa` |-> `sk`,
       `Gi` |-> `G0`,`ti` |-> `tn0`,`H` |-> `G3`,`tf` |-> `tn4`]
       unwrap_slot_copy_ghost_kept_at) >> simp[] >>
     rpt conj_tac >> metis_tac[not_fresh_at_mono,LESS_LESS_EQ_TRANS]) >>
  `!name b len. local_region cenv es.scopes t name b len ==>
     regions_disjoint (w2n wo) 32 b len` by
    (qpat_assum `!x. lookup_var x t = _ /\ _`
       (fn frame => qpat_assum `!name b len. local_region cenv es.scopes s3 name b len ==> _`
         (fn separated => POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [frame,separated])) >>
     fs[local_region_def] >> metis_tac[]) >>
  `(cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n wo) 32 off (type_memory_size tv))` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ t`
       (fn ssr => let
          val horizon = hd (snd (strip_comb (concl ssr)));
          val th = precompile_alloca_immutable_disjoint;
          val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
            (free_vars (concl th)));
          val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
        in mp_tac (Q.INST [`s` |-> `t`,`b` |-> `w2n (wo:256 word)`,
          `sz` |-> `32`,`H` |-> `storage_trace_horizon es.storage_trace`,
          `inst` |-> `mk_inst sp.cs_next_id ALLOCA [Lit (n2w 32)]
            [STRING #"%" (toString sp.cs_next_var)]`] typed) end) >>
     qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ t`
       (fn state => qpat_assum `MEM (mk_inst sp.cs_next_id ALLOCA _ _) (fn_insts func)`
         (fn instruction => qpat_assum `FLOOKUP t.vs_allocas sp.cs_next_id = SOME (w2n wo,32)`
           (fn site => POP_ASSUM_LIST (K all_tac) >>
             MAP_EVERY assume_tac [state,instruction,site]))) >>
     gvs[mk_inst_def]) >>
  `w2n wi+128 <= t.vs_alloca_next /\
   w2n wo+32 <= t.vs_alloca_next` by metis_tac[LESS_EQ_TRANS] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es t /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es G3 tn4 t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (fn initial => qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t`
         (fn state => qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ t`
           (fn ghost => POP_ASSUM_LIST (K all_tac) >>
             MAP_EVERY assume_tac [initial,state,ghost]))) >> metis_tac[]) >>
  `!aid off len. FLOOKUP s.vs_allocas aid = SOME (off,len) /\
     aid < sf.cs_next_id ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_assum `!aid off len. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==> _`
       (fn memory => POP_ASSUM_LIST (K all_tac) >> assume_tac memory) >> metis_tac[]) >>
  qexistsl_tac [`t`,`G3`,`tn4`,`qi`,`qo`,`wi`,`wo`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

