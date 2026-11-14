(* The actual scalar operand endpoint, allocation and numeric run are one path. *)
Theory bodyFullBuiltinUint2StrSuffix
Ancestors
  bodyFullBuiltinUint2StrRun bodyFullAllocaFresh bodyFullUnwrapRun
  exprSimUint2Str exprSimHash bodyPtrDefs bodySimFull exprSimMemDefs
  exprSimHyps exprSimHypsDefs exprLowering exprLoweringProps exprSimSource exprSimProps exprSimWordArgs loweringPosts freshWrites
  fragGasOriginPtrLoop venomState venomInst finite_map words list
  compileEnv valueEncoding loweringStateRelDefs ptrDiscipline abiBuiltinAllocation emitHelperProps

Theorem uint2str_suffix_joint_full:
  expr_body_pre cenv cx env (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es /\
  expr_type e = BaseT (UintT k) /\
  lower_value compile_expr cenv ty e sa = (op,sm) /\
  as_ptr_val (BaseT (StringT n)) LocMemory
    (compile_uint2str op n (type_memory_bytes cenv (BaseT (StringT n))) sm) = (vv,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!r len. cenv.ce_return_buf = SOME (PtrVar (Var r) len) ==> not_fresh_at sm r) /\
  (!r len. cenv.ce_return_pc = SOME (PtrVar (Var r) len) ==> not_fresh_at sm r) /\
  X < dimword(:256) /\ 78 <= n /\ valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx es s0 /\
    expr_post H ctx fn cenv cx e es sa sm s0 ee (IntV (&X)) op s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history fn s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ op_prov G op = NONE /\ op_taint tn op = {} /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
    b+len <= s.vs_alloca_next) /\
  (!name b len. local_region cenv es.scopes s0 name b len ==> b+len <= s.vs_alloca_next) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t G' tn'.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn') /\
      vv_post H ctx fn cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
        es sa sb s0 ee (Value (StringV (num_to_dec_string X))) vv t /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' t) /\
    vv_store_bound cx (BaseT (StringT n)) (BaseT (StringT n)) ee
      (Value (StringV (num_to_dec_string X))) vv t /\
    ptr_vv_ok cx (BaseT (StringT n)) (Value (StringV (num_to_dec_string X))) vv ee G' tn' t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history fn t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    vv_location vv = SOME LocMemory /\
    ptr_buf_ok cenv (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) (vv_operand vv) G' t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  Cases_on `compile_uint2str op n (type_memory_bytes cenv (BaseT (StringT n))) sm` >>
  gvs[as_ptr_val_def] >>
  drule compile_uint2str_layout >>
  disch_then (qx_choose_then `ba` (qx_choose_then `a` strip_assume_tac)) >>
  drule_all u2s_alloc_layout_code >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx ee s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >>
     strip_tac >> drule expr_post_state >> simp[]) >>
  `stmt_state_rel H0 ctx fn cenv cx ee s` by metis_tac[] >>
  `type_memory_bytes cenv (BaseT (StringT n)) + n < dimword(:256)` by
    (irule (cj 6 u2s_builtin_result_requirements) >> simp[] >> metis_tac[]) >>
  drule_all (Q.INST [`sa` |-> `sm`, `es` |-> `ee`] (INST_TYPE [``:'b`` |-> ``:256``] (SPEC_ALL alloc_buffer_origin_ptr_path_exact))) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`]
    (qx_choose_then `p` (qx_choose_then `w` (qx_choose_then `ready`
      (qx_choose_then `Gr` (qx_choose_then `tr` strip_assume_tac)))))) >>
  suspend "run"
QED

Resume uint2str_suffix_joint_full[run]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx ee ready` by
    (rpt strip_tac >>
     qpat_assum `!H'. stmt_state_rel H' ctx fn cenv cx ee s ==> _` irule >>
     simp[]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `sm.cs_next_var <= a.cs_next_var` by
    (mp_tac (Q.SPECL [`type_memory_bytes cenv (BaseT (StringT n)) + n`, `sm`]
      ci_mono_compile_alloc_buffer) >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv a` by metis_tac[local_ptrs_reserved_next_var] >>
  `!z. not_fresh_at sm z ==> not_fresh_at a z` by metis_tac[not_fresh_at_mono] >>
  `lookup_var p ready = SOME (n2w (w2n w))` by simp[] >>
  `op_taint tr (Var p) = {}` by fs[ptr_covers_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    u2s_safe H ctx fn cenv cx ee a (Var p) (w2n w)
      (type_memory_bytes cenv (BaseT (StringT n)) + n)
      (mk_inst sm.cs_next_id ALLOCA
        [Lit (n2w (type_memory_bytes cenv (BaseT (StringT n)) + n))] [p]) ready ready /\
    ghost_inv_at (DF H) lo d cenv cx ee Gr tr ready` by
    (rpt strip_tac
     >- (irule u2s_safe_initial >> simp[mk_inst_def, eval_operand_def] >>
         rpt strip_tac >> fs[regions_disjoint_def] >>
         qpat_x_assum `!name b len. local_region _ _ ready _ _ _ ==> _` drule >> simp[])
     >> irule alloc_buffer_ghost_inv_at_locals >> simp[] >>
     qexistsl_tac [`G`, `w2n w + (type_memory_bytes cenv (BaseT (StringT n)) + n)`, `fn`, `s`, `sm`, `tn`] >>
     simp[] >> conj_tac
     >- (qpat_assum `ready with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     qpat_assum `stmt_state_rel H0 _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, state_rel_def] >> rpt strip_tac) >>
  mp_tac (Q.INST [`es` |-> `ee`, `s` |-> `ready`, `sr` |-> `ready`,
    `G` |-> `Gr`, `tn` |-> `tr`, `s0` |-> `ready`, `G0` |-> `Gr`, `tn0` |-> `tr`,
    `b` |-> `w2n (w:256 word)`, `sz` |-> `type_memory_bytes cenv (BaseT (StringT n)) + n`,
    `inst` |-> `mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv (BaseT (StringT n)) + n))] [p]`,
    `q` |-> `p`, `ty` |-> `BaseTV (StringT n)`, `pre` |-> `a.cs_current_insts`,
    `bb` |-> `<|bb_label := a.cs_current_bb;
      bb_instructions := a.cs_current_insts ++ u2s_setup a op (Var p)|>`]
    (INST_TYPE [``:'a`` |-> ``:256``] (SPEC_ALL u2s_setup_exit_joint))) >>
  impl_tac >- suspend "run_entry" >>
  disch_then strip_assume_tac >>
  suspend "numeric_exit"
QED

Resume uint2str_suffix_joint_full[run_entry]:
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `p = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  `!k. op <> Var (u2s_var a k)` by
    (Cases_on `op` >> fs[] >> metis_tac[u2s_var_fresh]) >>
  `~ready.vs_halted` by
    (qpat_assum `ready with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> expr_post H ctx fn cenv cx e es sa sm s0 ee (IntV (&X)) op s` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` drule >> simp[]) >>
  `not_local_ptr cenv ee.scopes p` by
    (simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `32 <= type_memory_bytes cenv (BaseT (StringT n))` by
    (irule (cj 5 u2s_builtin_result_requirements) >> simp[] >> metis_tac[]) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo ready` mp_tac >>
     pure_rewrite_tac[allocas_from_def] >> disch_then drule >> simp[]) >>
  `expr_post H0 ctx fn cenv cx e es sa sm s0 ee (IntV (&X)) op s` by metis_tac[] >>
  `eval_operand op s = SOME (n2w X)` by
    (drule expr_post_word_operand >>
     impl_tac >- (simp[loweringSliceTheory.word_value_def] >> metis_tac[expr_body_pre_type_evaluates]) >>
     simp[val_to_w256_def, integer_wordTheory.i2w_def]) >>
  `eval_operand op ready = SOME (n2w X) /\ op_prov Gr op = NONE /\ op_taint tr op = {}` by
    (Cases_on `op` >> fs[eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[]) >>
  fs[arithmeticTheory.ADD_COMM, mk_inst_def] >>
  conj_tac >- simp[ghost_kept_at_def] >>
  qpat_x_assum `!bb. MEM bb (u2s_blocks _ _ _ _) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[u2s_blocks_def] >> strip_tac >>
  rpt conj_tac >> qmatch_goalsub_abbrev_tac `SOME blk` >>
  first_x_assum (qspec_then `blk` mp_tac) >> simp[Abbr `blk`]
QED

Resume uint2str_suffix_joint_full[numeric_exit]:
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  `u2s_safe H0 ctx fn cenv cx ee a (Var p) (w2n w)
    (type_memory_bytes cenv (BaseT (StringT n)) + n)
    (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv (BaseT (StringT n)) + n))] [p]) ready t` by metis_tac[] >>
  `u2s_frame a (w2n w) (type_memory_bytes cenv (BaseT (StringT n)) + n) ready t` by fs[u2s_safe_def] >>
  drule (Q.INST [`sz` |-> `type_memory_bytes cenv (BaseT (StringT n))`, `X` |-> `X`]
    (SPEC_ALL u2s_builtin_result_requirements)) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `X` mp_tac) >> simp[] >> strip_tac >>
  `LENGTH (num_to_dec_string X) <= n` by
    (mp_tac (Q.INST [`x` |-> `X`] uint256_decimal_length) >> fs[dimword_def] >> decide_tac) >>
  `t.vs_alloca_next = ready.vs_alloca_next /\ t.vs_allocas = ready.vs_allocas` by
    (fs[u2s_frame_def, venom_state_component_equality]) >>
  conj_tac >- suspend "uniform_post" >>
  conj_tac >- suspend "store_bound" >>
  conj_tac >- suspend "pointer_post" >>
  `t.vs_current_bb = r.cs_current_bb /\ t.vs_inst_idx = LENGTH r.cs_current_insts` by
    fs[u2s_layout_def, u2s_end_def] >>
  simp[contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
  `u2s_label a 5 = r.cs_current_bb /\ r.cs_current_insts = []` by fs[u2s_layout_def, u2s_end_def] >>
  `alloca_history fn t /\ allocas_from lo t` by
    (fs[allocaHistoryTheory.alloca_history_def, allocas_from_def] >> metis_tac[]) >>
  simp[] >> conj_tac >- suspend "buffer_post" >>
  suspend "original_frame"
QED

Resume uint2str_suffix_joint_full[buffer_post]:
  simp[contextTheory.vv_operand_def, ptr_buf_ok_def] >> rpt strip_tac >>
  fs[] >>
  `w2n w + n - LENGTH (num_to_dec_string X) < dimword(:256)` by decide_tac >>
  simp[w2n_n2w] >> decide_tac
QED

Resume uint2str_suffix_joint_full[original_frame]:
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gr tr` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G`, `w2n w + (type_memory_bytes cenv (BaseT (StringT n)) + n)`, `s`, `tn`] >>
     simp[] >> metis_tac[not_fresh_at_mono]) >>
  `expr_post H0 ctx fn cenv cx e es sa sm s0 ee (IntV (&X)) op s /\
   stmt_state_rel H0 ctx fn cenv cx es s0` by metis_tac[] >>
  `local_ptrs_rel fn cenv es.scopes s0` by
    (qpat_assum `stmt_state_rel H0 ctx fn cenv cx es s0` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, state_rel_def] >> rpt strip_tac) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x ready = SOME v` by
    (fs[expr_post_def] >> metis_tac[not_fresh_at_mono]) >>
  `!name b len. local_region cenv es.scopes s0 name b len <=>
       local_region cenv ee.scopes ready name b len` by
    (qpat_assum `local_ptrs_rel fn cenv es.scopes s0` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `MAP FDOM es.scopes = MAP FDOM ee.scopes` mp_tac >>
     qpat_assum `!x v. not_fresh_at sa x /\ _ ==> lookup_var x ready = SOME v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[local_region_frame, local_region_frame_fwd]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP ready.vs_allocas aid = SOME b` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `sa.cs_next_id <= a.cs_next_id` by
    (mp_tac (Q.SPECL [`type_memory_bytes cenv (BaseT (StringT n)) + n`, `sm`]
       ci_mono_compile_alloc_buffer) >> simp[ci_mono_def] >> decide_tac) >>
  `sa.cs_next_var <= a.cs_next_var` by decide_tac >>
  qpat_assum `sa.cs_next_var <= a.cs_next_var` mp_tac >>
  qpat_assum `sa.cs_next_id <= a.cs_next_id` mp_tac >>
  qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP ready.vs_allocas aid = SOME b` mp_tac >>
  qpat_assum `!name b len. local_region cenv es.scopes s0 name b len <=> _` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv ee a Gr tr ready G' tn'` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gr tr` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac[ghost_kept_at_def] >> rpt strip_tac
  >- (`not_fresh_at a x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!x. not_fresh_at a x ==> _` (qspec_then `x` mp_tac) >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[])
  >- (`not_fresh_at a x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!x. not_fresh_at a x ==> _` (qspec_then `x` mp_tac) >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[])
  >- (`aid < a.cs_next_id` by decide_tac >>
      `FLOOKUP ready.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `!name b len. local_region cenv ee.scopes ready name b len ==>
         off + sz <= b \/ b + len <= off` by metis_tac[] >>
      `i IN tr.t_mem` by
        (qpat_x_assum `!aid off sz i. FLOOKUP ready.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >> simp[] >> metis_tac[]) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >> simp[] >> metis_tac[])
  >- (qpat_x_assum `!n b sz i. local_region cenv ee.scopes ready n b sz /\ _ ==> _`
        (qspecl_then [`n`, `b`, `sz`, `i`] mp_tac) >>
      qpat_x_assum `!n b sz i. local_region cenv es.scopes s0 n b sz /\ _ ==> _`
        (qspecl_then [`n`, `b`, `sz`, `i`] mp_tac) >> metis_tac[])
  >> metis_tac[]
QED

Resume uint2str_suffix_joint_full[uniform_post]:
  rpt strip_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl [`Gr`, `ready`, `tr`] >> simp[])
  >> `u2s_safe H ctx fn cenv cx ee a (Var p) (w2n w)
       (type_memory_bytes cenv (BaseT (StringT n)) + n)
       (mk_inst sm.cs_next_id ALLOCA
         [Lit (n2w (type_memory_bytes cenv (BaseT (StringT n)) + n))] [p]) ready t` by metis_tac[] >>
  irule (SRULE [vyperASTTheory.expr_type_def] (Q.INST
    [`e` |-> `Builtin (BaseT (StringT n)) (Uint2Str n) [e]`]
    vv_post_allocated_memory_intro)) >>
  qpat_assum `u2s_safe H ctx fn cenv cx ee a _ _ _ _ ready t` mp_tac >>
  pure_rewrite_tac[u2s_safe_def] >> strip_tac >>
  simp[contextTheory.mk_ptr_def] >>
  conj_tac >- (fs[vyperASTTheory.expr_type_def]) >>
  conj_tac >- suspend "pure_frame" >>
  conj_tac >- metis_tac[expr_post_def] >>
  reverse conj_tac >- suspend "wb_frame" >>
  qexistsl [`sm.cs_next_id`, `w2n w`, `type_memory_bytes cenv (BaseT (StringT n)) + n`,
    `BaseTV (StringT n)`] >>
  simp[arithmeticTheory.ADD_SYM] >>
  conj_tac >- (drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
    fs[u2s_layout_def, u2s_end_def]) >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_SYM] >>
  fs[vyperASTTheory.expr_type_def]
QED

Resume uint2str_suffix_joint_full[wb_frame]:
  `expr_post H ctx fn cenv cx e es sa sm s0 ee (IntV (&X)) op s` by metis_tac[] >>
  `wb_frame cenv es ee sa s0 s` by
    (qpat_assum `expr_post H ctx fn cenv cx e es sa sm s0 ee _ op s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[expr_post_def, wb_frame_def] >> metis_tac[]) >>
  `ready.vs_memory = s.vs_memory` by
    (qpat_assum `ready with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_memory`) >> simp[]) >>
  irule wb_frame_allocating_tail >>
  simp[] >> qexistsl [`s`, `ee.scopes`, `sm`] >> simp[] >>
  qpat_assum `u2s_frame a _ _ ready t` mp_tac >>
  pure_rewrite_tac[u2s_frame_def] >> strip_tac >>
  rpt conj_tac >> rpt strip_tac
  >- (`local_region cenv ee.scopes ready n' b sz` by
        (irule local_region_frame_fwd >> qexistsl [`s`, `sm`, `ee.scopes`] >>
         simp[] >> metis_tac[]) >>
      qpat_x_assum `!name b len. local_region cenv ee.scopes ready _ _ _ ==> _` drule >>
      simp[regions_disjoint_def] >> strip_tac >>
      qpat_assum `ready.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
      qpat_x_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >> decide_tac)
  >- (`not_fresh_at a x` by metis_tac[not_fresh_at_mono] >> metis_tac[])
  >> qpat_x_assum `!aid b len. aid < sm.cs_next_id /\ _ ==> _` drule_all >>
  simp[regions_disjoint_def] >> strip_tac >>
  qpat_assum `ready.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  qpat_x_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >> decide_tac
QED

Resume uint2str_suffix_joint_full[pure_frame]:
  strip_tac >>
  `~expr_has_effect e` by fs[] >>
  `expr_post H ctx fn cenv cx e es sa sm s0 ee (IntV (&X)) op s` by metis_tac[] >>
  `pure_frame cenv fn es sa s0 s` by metis_tac[expr_post_pure_frame] >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x ready = SOME v` by
    (fs[expr_post_def] >> metis_tac[not_fresh_at_mono]) >>
  `!nm lb lsz. local_region cenv es.scopes s0 nm lb lsz ==>
       local_region cenv ee.scopes ready nm lb lsz` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl [`s0`, `sa`, `es.scopes`] >> simp[]) >>
  `ready.vs_memory = s.vs_memory` by
    (qpat_assum `ready with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `\z:venom_state. z.vs_memory`) >> simp[]) >>
  mp_tac (Q.INST [`func` |-> `fn`, `s` |-> `s`, `z` |-> `t`,
    `inst` |-> `mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes cenv (BaseT (StringT n)) + n))]
      [STRING #"%" (toString sm.cs_next_var)]`,
    `bb` |-> `w2n (w:256 word)`,
    `bsz` |-> `type_memory_bytes cenv (BaseT (StringT n)) + n`]
    (SPEC_ALL pure_frame_buffer_tail)) >>
  impl_tac >- suspend "pure_tail" >> simp[]
QED

Resume uint2str_suffix_joint_full[pure_tail]:
  simp[mk_inst_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!nm lb lsz. local_region cenv es.scopes s0 _ _ _ ==> _` drule >>
      strip_tac >>
      qpat_x_assum `!name b len. local_region cenv ee.scopes ready _ _ _ ==> _` drule >>
      simp[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >>
  qpat_assum `u2s_frame a _ _ ready t` mp_tac >>
  pure_rewrite_tac[u2s_frame_def] >> strip_tac >>
  fs[regions_disjoint_def, valueEncodingDefsTheory.mem_bytes_at_def,
     arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Resume uint2str_suffix_joint_full[store_bound]:
  simp[vv_store_bound_def, contextTheory.mk_ptr_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def,
       vyperValueTheory.evaluate_type_def] >> rpt strip_tac >>
  gvs[] >>
  `w2n w + n - LENGTH (num_to_dec_string X) < dimword(:256)` by decide_tac >>
  fs[w2n_n2w] >>
  `val_store_size (BaseTV (StringT n)) (StringV (num_to_dec_string X)) <=
    type_memory_size (BaseTV (StringT n))` by metis_tac[val_store_size_le] >>
  decide_tac
QED

Resume uint2str_suffix_joint_full[pointer_post]:
  simp[ptr_vv_ok_def, contextTheory.mk_ptr_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  simp[ptr_mem_ok_def, vyperValueTheory.evaluate_type_def] >> rpt strip_tac >> gvs[] >>
  `w2n w + n - LENGTH (num_to_dec_string X) < dimword(:256)` by decide_tac >>
  simp[w2n_n2w]
  >~ [`val_in_memory _ _ _ mem`]
  >- (mp_tac (Q.INST [`cap` |-> `n`, `str` |-> `num_to_dec_string X`,
        `p` |-> `w2n (w:256 word) + n - LENGTH (num_to_dec_string X)`,
        `mem` |-> `t.vs_memory`, `dirty` |-> `tn'.t_mem`]
        (SPEC_ALL bodyPtrBytestringBuiltinsUintGhostTheory.uint_string_clean_robust)) >>
      impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      disch_then (qspec_then `mem` mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  `val_store_size (BaseTV (StringT n)) (StringV (num_to_dec_string X)) <=
    type_memory_size (BaseTV (StringT n))` by metis_tac[val_store_size_le] >> decide_tac
QED

Finalise uint2str_suffix_joint_full
