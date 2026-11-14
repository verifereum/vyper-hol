(* ECRecover's joint value and stack judgments. *)
Theory bodyFullBuiltinECRecover
Ancestors
  bodyFullExprGeneric bodyFullPreds bodySimFull
  bodyFullBuiltinPrecompileRecoveryArgs bodyFullBuiltinPrecompileRecoveryBuffers
  bodyFullBuiltinPrecompileSuffixSuccess bodyFullBuiltinPrecompileSuffixAbort
  gasOutcomeFull gasOutcomeFullCompose gasShadowCompileStmtHelpers gasShadow gasShadowState
  gasExemptCert gasSummary exprSimDefs
  exprSimPrecompiles exprSimHypsDefs exprSimSource exprSimWordArgs exprSimHash
  exprLoweringProps exprLowering builtinMisc context compileEnv fragExec
  bodyMemoryDefs bodyPtrDefs loweringPosts loweringStateRelDefs freshWrites
  bodyPtrPrecompileBuiltinsRuntime generatedGasOrigin gasShadowCompileContext
  fragGasSeqPtr fragGasOriginPtr instMemFrontier exprPtrCtorImmStore
  wordLoadStorePtr bodyFullGhostFrame bodyPtrMakeArrayMloadFrame exprSimProps valueCopy
  allocaFootprint allocaHistory allocaHistoryFragment memSafeRun venomMemDefs wordArgsPtr bodyFullUnwrapRun
  extCallOracle venomCallOracleDefs venomInst venomState venomExecSemantics venomInstProofs
  ptrDiscipline
  emitHelper emitHelperProps words rich_list
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState vyperContext
  vyperAST vyperTyping vyperValue vyperTypeSystem valueEncodingProps list finite_map
Libs
  monadsyntax

Theorem ecrecover_expr_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a args es.
    (builtin_args_length_ok ECRecover (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a ECRecover args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a ECRecover args) es
Proof
  rpt gen_tac >> strip_tac >>
  `a = BaseT AddressT /\ LENGTH args = 4 /\
   EVERY (\e. is_word_type (expr_type e)) args` by
    metis_tac[ecrecover_pre_types] >>
  `body_exprs_full_ok cx args` by
    fs[builtin_args_length_ok_def] >>
  rw[expr_sim_full_def] >>
  drule_all lower_value_ecrecover_args >>
  disch_then (qx_choose_then `h` (qx_choose_then `v`
    (qx_choose_then `r` (qx_choose_then `sig`
      (qx_choose_then `sf` strip_assume_tac))))) >>
  `!todo. gas_shadow_compiles (lower_word_args cenv (\e. ty) todo)
    (lower_word_args cenv (\e. ty) (MAP gas_shadow_expr todo))` by
    (Induct >> simp[lower_word_args_def,MAP,gas_shadow_compiles_return] >> gen_tac >>
     irule gas_shadow_compiles_bind >> simp[gas_shadow_stmt_lower_value] >>
     gen_tac >> irule gas_shadow_compiles_bind >>
     simp[gas_shadow_compiles_return]) >>
  `?shadow_sf.
     lower_word_args cenv (\e. ty) (MAP gas_shadow_expr args) shadow_sa =
       ([h;v;r;sig],shadow_sf) /\ gas_shadow_state sf shadow_sf` by
    (qpat_assum `!todo. gas_shadow_compiles _ _`
       (mp_tac o Q.SPECL [`sa`,`shadow_sa`] o
        REWRITE_RULE [gas_shadow_compiles_def] o Q.SPEC `args`) >> simp[] >>
     Cases_on `lower_word_args cenv (\e. ty)
       (MAP gas_shadow_expr args) shadow_sa` >> simp[] >> metis_tac[]) >>
  `?hh hv hr hs shadow_cut.
     lower_word_args cenv (\e. ty) (MAP gas_shadow_expr args) shadow_sa =
       ([hh;hv;hr;hs],shadow_cut) /\
     compile_ecrecover hh hv hr hs shadow_cut = (op,shadow_sb)` by
    (`lower_value compile_expr cenv ty
        (Builtin (BaseT AddressT) ECRecover (MAP gas_shadow_expr args))
        shadow_sa = (op,shadow_sb)` by
       fs[gas_shadow_expr_def,gas_shadow_builtin_def] >>
     mp_tac (Q.INST [`args` |-> `MAP gas_shadow_expr args`,
       `sa` |-> `shadow_sa`,`sb` |-> `shadow_sb`,
       `ann` |-> `BaseT AddressT`] lower_value_ecrecover_args) >>
     simp[] >> metis_tac[]) >>
  `shadow_cut = shadow_sf /\ hh = h /\ hv = v /\ hr = r /\ hs = sig` by
    metis_tac[pairTheory.PAIR_EQ,listTheory.CONS_11] >>
  gvs[] >>
  rename1 `lower_word_args cenv (\e. ty) args sa = ([h;v;r;sig],sf)` >>
  rename1 `gas_shadow_state sf shadow_sf` >>
  `!todo x y ops. lower_word_args cenv (\e. ty) todo x = (ops,y) ==>
    ci_mono x y` by
    (POP_ASSUM_LIST (K all_tac) >> Induct >>
     simp[lower_word_args_nil,ci_mono_refl] >> rpt gen_tac >>
     rw[lower_word_args_cons] >>
     metis_tac[ci_mono_lower_value_compile_expr,ci_mono_trans,pairTheory.SND]) >>
  `ci_mono sa sf /\ ci_mono shadow_sa shadow_sf` by metis_tac[] >>
  `cs_extends sa sf /\ cs_extends shadow_sa shadow_sf /\
   sa.cs_next_var <= sf.cs_next_var /\ sa.cs_next_id <= sf.cs_next_id` by
    fs[ci_mono_def] >>
  `cs_extends sf sb /\ cs_extends shadow_sf shadow_sb` by
    metis_tac[compile_ecrecover_extends] >>
  `fn_has_code sa sf func /\ fn_has_code sf sb func /\
   fn_has_code shadow_sa shadow_sf shadow_func` by
    metis_tac[fn_has_code_mid,cs_extends_refl] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  mp_tac (Q.SPECL [`args`,`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`tops`,
    `func`,`shadow_func`,`cenv`,`env`,`cx`,`ty`,`BaseT AddressT`,`args`,
    `[]`,`es`,`es`,`st0`,`sa`,`sf`,`shadow_sa`,`shadow_sf`,
    `[h;v;r;sig]`,`s0`,`G0`,`tn0`] ecrecover_args_suffix_full) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _
    (eval_exprs cx args) _ argsQ argsR` >>
  qpat_assum `LENGTH args = 4`
    (fn length => rewrite_tac [MATCH_MP eval_expr_ecrecover_read_action length]) >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      rename1 `gas_marked_exec _ _ _ _ _ (INL vals) mid (OK t)` >>
      irule gas_exempt_cert_bind_values >>
      qexistsl_tac [`mid`,`t`,`vals`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >- (gen_tac >> rw[storage_trace_frame_def] >>
      simp[ignore_bind_def,bind_def,return_def,ecrecover_source_outcome_step] >>
      rpt (CASE_TAC >> simp[])) >>
  qexists_tac `(\H rr ee G tn t. argsQ H rr ee G tn t /\ ~t.vs_halted)` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `argsR`,wb_args_exit_def,expr_exit_def] >>
      Cases_on `res` >> simp[]) >>
  BETA_TAC >> qx_genl_tac [`marks`,`rr`,`mid`,`G1`,`tn1`,`sarg`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  `?vals. rr = INL vals` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[Abbr `argsQ`] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vals` >> conj_tac >- simp[] >>
  qunabbrev_tac `argsQ` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     typed_args_post H ctx func cenv cx es sa s0 mid args [h;v;r;sig] vals sarg /\
     sarg.vs_current_bb = sf.cs_current_bb /\
     sarg.vs_inst_idx = LENGTH sf.cs_current_insts /\
     alloca_history func sarg /\ s0.vs_alloca_next <= sarg.vs_alloca_next /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 sarg /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
     EVERY (\x. op_taint tn1 x = {}) [h;v;r;sig] /\ ~sarg.vs_halted` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o BETA_RULE o MATCH_MP th)) >> gvs[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (fn th => qpat_assum
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
      (strip_assume_tac o MATCH_MP th)) >>
  `?ib ca cb cc cd cp ob cm cz cq.
     compile_alloc_buffer 128 sf = (ib,ca) /\
     emit_void MSTORE [ib.buf_operand;h] ca = ((),cb) /\
     (do dst <- emit_op ADD [ib.buf_operand;Lit 32w];
         emit_void MSTORE [dst;v] od) cb = ((),cc) /\
     (do dst <- emit_op ADD [ib.buf_operand;Lit 64w];
         emit_void MSTORE [dst;r] od) cc = ((),cd) /\
     (do dst <- emit_op ADD [ib.buf_operand;Lit 96w];
         emit_void MSTORE [dst;sig] od) cd = ((),cp) /\
     compile_alloc_buffer 32 cp = (ob,cm) /\
     emit_void MSTORE [ob.buf_operand;Lit 0w] cm = ((),cz) /\
     (do gas <- emit_op GAS [];
         success <- emit_op STATICCALL
           [gas;Lit 1w;ib.buf_operand;Lit 128w;ob.buf_operand;Lit 32w];
         emit_void ASSERT [success]; return ob.buf_operand od)
       cz = (ob.buf_operand,cq) /\
     emit_op MLOAD [ob.buf_operand] cq = (op,sb)` by
    (qpat_assum `compile_ecrecover h v r sig sf = (op,sb)`
       (fn compile => POP_ASSUM_LIST (K all_tac) >> mp_tac compile) >>
     simp[compile_ecrecover_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >>
  rename1 `compile_alloc_buffer 32 sp = (ob,cm)` >>
  `wb_args_shape cenv (\e. ty) args` by
    (simp[wb_args_shape_def] >> rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e es` by
       (drule expr_body_pre_builtin_arg >>
        disch_then (qspecl_then [`e`,`es`] mp_tac) >> simp[]) >>
     `is_word_type (expr_type e)` by fs[EVERY_MEM] >>
     metis_tac[expr_body_pre_lower_value_word_shape]) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `EVERY (\x. op_taint tn1 x = {} /\ (!l. x <> Label l) /\
     (!q. x = Var q ==> not_fresh_at sf q)) [h;v;r;sig]` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `?wh wv wr ws.
     eval_operand h sarg = SOME wh /\ eval_operand v sarg = SOME wv /\
     eval_operand r sarg = SOME wr /\ eval_operand sig sarg = SOME ws` by
    (qpat_assum `typed_args_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ sarg`
       (fn post => qpat_assum `LENGTH args = 4`
         (fn length => POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [post,length])) >>
     fs[typed_args_post_def] >> gvs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  qpat_assum `typed_args_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ sarg`
    (strip_assume_tac o PURE_REWRITE_RULE [typed_args_post_def]) >>
  `return_buf_frame d cenv sf sarg` by
    (MATCH_MP_TAC (Q.SPECL [`d`,`cenv`,`cenv`,`sa`,`sf`,`s0`,`sarg`]
       return_buf_frame_frame) >> simp[] >>
     qpat_assum `wb_frame cenv es mid sa s0 sarg`
       (fn frame => POP_ASSUM_LIST (K all_tac) >> mp_tac frame) >>
     simp[wb_frame_def]) >>
  `!base value off st.
     ci_mono st (SND ((do dst <- emit_op ADD [base;Lit off];
       emit_void MSTORE [dst;value] od) st))` by
    (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >>
     irule ci_mono_bind >> simp[ci_mono_emit_op,ci_mono_emit_void]) >>
  `ci_mono cb cc /\ ci_mono cc cd /\ ci_mono cd sp` by
    metis_tac[pairTheory.SND] >>
  `!ip op st. ci_mono st (SND ((do gas <- emit_op GAS [];
       success <- emit_op STATICCALL [gas;Lit 1w;ip;Lit 128w;op;Lit 32w];
       emit_void ASSERT [success]; comp_return op od) st))` by
    (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >> simp[comp_ignore_bind_def] >>
     rpt (match_mp_tac ci_mono_bind >> conj_tac
       >- simp[ci_mono_emit_op,ci_mono_emit_void] >> rpt gen_tac >> BETA_TAC) >>
     simp[ci_mono_comp_return]) >>
  `ci_mono cz cq` by metis_tac[pairTheory.SND] >>
  `ci_mono sf ca /\ ci_mono ca cb /\ ci_mono sp cm /\
   ci_mono cm cz /\ ci_mono cq sb` by
    (mp_tac (Q.SPECL [`128`,`sf`] ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`32`,`sp`] ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`MSTORE`,`[ib.buf_operand;h]`,`ca`] ci_mono_emit_void) >>
     mp_tac (Q.SPECL [`MSTORE`,`[ob.buf_operand;Lit 0w]`,`cm`] ci_mono_emit_void) >>
     mp_tac (Q.SPECL [`MLOAD`,`[ob.buf_operand]`,`cq`] ci_mono_emit_op) >>
     simp[] >> metis_tac[]) >>
  `ci_mono sf cz /\ ci_mono cz sb` by metis_tac[ci_mono_trans] >>
  `cs_extends sf cz /\ cs_extends cz sb` by fs[ci_mono_def] >>
  `fn_has_code sf cz func /\ local_ptrs_reserved cenv sf` by
    metis_tac[fn_has_code_mid,cs_extends_refl,local_ptrs_reserved_next_var] >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
      not_fresh_at sf x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
      not_fresh_at sf x)` by metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid sarg /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 sarg` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     qpat_assum `typed_args_post H _ _ _ _ _ _ _ _ _ _ _ sarg`
       (strip_assume_tac o PURE_REWRITE_RULE [typed_args_post_def]) >> simp[]) >>
  qpat_assum `ghost_inv_at (DF (storage_trace_horizon _)) _ _ _ _ _ _ _ sarg`
    (fn ghost => let
       val actualDF = rator (hd (snd (strip_comb (concl ghost))));
       val th = ecrecover_buffers_full_run;
       val dv = valOf (List.find (fn v => fst (dest_var v) = "DF")
         (free_vars (concl th)));
       val typed = INST_TYPE (match_type (type_of dv) (type_of actualDF)) th;
       val dv = valOf (List.find (fn v => fst (dest_var v) = "DF")
         (free_vars (concl typed)));
       val provider = INST [dv |-> actualDF] typed;
     in mp_tac (Q.INST [`sa` |-> `ca`,`sb` |-> `cb`,`sc` |-> `cc`,
       `sd` |-> `cd`,`sm` |-> `cm`,`sz` |-> `cz`,`es` |-> `mid`,
       `s` |-> `sarg`,`G` |-> `G1`,`tn` |-> `tn1`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] provider) end) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `sbuf` (qx_choose_then `Gbuf`
    (qx_choose_then `tnbuf` (qx_choose_then `qi` (qx_choose_then `qo`
      (qx_choose_then `wi` (qx_choose_then `wo` strip_assume_tac))))))) >>
  `LIST_REL (\e v. ?tv.
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v)
     args vals` by
    (irule stack_args_values_typed_body >>
     qexistsl_tac [`cenv`,`env`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []`,
       `mid with gas_obs := []`] >> simp[] >>
     qx_genl_tac [`e`,`ee`] >> strip_tac >> conj_tac
     >- (drule expr_body_pre_builtin_arg >>
         disch_then (qspecl_then [`e`,`ee`] mp_tac) >> simp[]) >>
     fs[EVERY_MEM]) >>
  `well_typed_builtin_app (BaseT AddressT) ECRecover (MAP expr_type args)` by
    fs[expr_body_pre_def,well_typed_expr_def] >>
  `builtin_result cx mid.accounts (BaseT AddressT) ECRecover
      (MAP expr_type args) vals =
     INL (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
       NONE => 0w | SOME addr => addr))` by
    (drule_all ecrecover_typed_result >>
     disch_then (qspec_then `mid.accounts` strip_assume_tac) >> gvs[]) >>
  qabbrev_tac `data = case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
    NONE => [] | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T)` >>
  `precompile_result (venom_call_request sbuf 1w 0w wi 128w T).cr_target
     (venom_call_request sbuf 1w 0w wi 128w T).cr_data = SOME (SOME data)` by
    (qpat_assum `mem_bytes_at (w2n wi) 128 sbuf.vs_memory = _`
       (mp_tac o MATCH_MP ecrecover_request_result) >> simp[Abbr `data`]) >>
  `computed_precompile (venom_call_request sbuf 1w 0w wi 128w T)` by
    (simp[computed_precompile_def] >> simp[venom_call_request_def]) >>
  qpat_assum `ib.buf_operand = Var qi`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq]) >> assume_tac eq) >>
  qpat_assum `ob.buf_operand = Var qo`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq]) >> assume_tac eq) >>
  drule_all computed_suffix_shape >> strip_tac >>
  qabbrev_tac `gv = STRING #"%" (toString cz.cs_next_var)` >>
  qabbrev_tac `cv = STRING #"%" (toString (cz.cs_next_var+1))` >>
  qabbrev_tac `gi = mk_inst cz.cs_next_id GAS [] [gv]` >>
  qabbrev_tac `ci = mk_inst (cz.cs_next_id+1) STATICCALL
    [Var gv;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w] [cv]` >>
  qabbrev_tac `ai = mk_inst (cz.cs_next_id+2) ASSERT [Var cv] []` >>
  `emitted_insts cz cq = [gi;ci;ai]` by
    simp[Abbr `gi`,Abbr `ci`,Abbr `ai`,Abbr `gv`,Abbr `cv`] >>
  `~not_fresh_at cz gv /\ ~not_fresh_at cz cv` by
    (qunabbrev_tac `gv` >> qunabbrev_tac `cv` >>
     POP_ASSUM_LIST (K all_tac) >> simp[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL,arithmeticTheory.LESS_EQ_ADD]) >>
  `qi <> gv /\ qo <> gv /\ qo <> cv` by metis_tac[] >>
  `same_blocks cz cq` by
    (qpat_assum `(do gas <- emit_op GAS []; _ od) cz = (Var qo,cq)`
       (fn cut => POP_ASSUM_LIST (K all_tac) >> mp_tac cut) >>
     simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     gvs[] >> metis_tac[same_blocks_trans]) >>
  `fn_has_code cz cq func` by
    (MATCH_MP_TAC (Q.SPECL [`sf`,`cz`,`cq`,`sb`,`func`] fn_has_code_mid) >>
     simp[] >> fs[ci_mono_def]) >>
  `?bb. lookup_block sbuf.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX [gi;ci;ai] (DROP sbuf.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code cz cq func`
       (strip_assume_tac o PURE_REWRITE_RULE [fn_has_code_def]) >>
     qpat_assum `same_blocks cz cq`
       (strip_assume_tac o PURE_REWRITE_RULE [same_blocks_def]) >>
     qexists_tac `bb` >> simp[] >> fs[rich_listTheory.IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1]) >>
  qabbrev_tac `buf_code = do bin <- compile_alloc_buffer 128;
    emit_void MSTORE [bin.buf_operand;h];
    (do dst <- emit_op ADD [bin.buf_operand;Lit 32w]; emit_void MSTORE [dst;v] od);
    (do dst <- emit_op ADD [bin.buf_operand;Lit 64w]; emit_void MSTORE [dst;r] od);
    (do dst <- emit_op ADD [bin.buf_operand;Lit 96w]; emit_void MSTORE [dst;sig] od);
    bout <- compile_alloc_buffer 32;
    emit_void MSTORE [bout.buf_operand;Lit 0w];
    comp_return (bin.buf_operand,bout.buf_operand) od` >>
  `buf_code sf = ((Var qi,Var qo),cz)` by
    simp[Abbr `buf_code`,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  `gas_shadow_compiles buf_code buf_code` by
    (qunabbrev_tac `buf_code` >> POP_ASSUM_LIST (K all_tac) >>
     simp[comp_ignore_bind_def] >>
     rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer,
            gas_shadow_compiles_emit_op,gas_shadow_compiles_emit_void,
            gas_shadow_compiles_bind] >> gen_tac >> BETA_TAC) >>
     simp[gas_shadow_compiles_return]) >>
  `?shadow_cz. buf_code shadow_sf = ((Var qi,Var qo),shadow_cz) /\
     gas_shadow_state cz shadow_cz` by
    (qpat_assum `gas_shadow_compiles buf_code buf_code`
       (mp_tac o Q.SPECL [`sf`,`shadow_sf`] o
        REWRITE_RULE [gas_shadow_compiles_def]) >> simp[] >>
     Cases_on `buf_code shadow_sf` >> simp[] >> metis_tac[]) >>
  `compile_ecrecover h v r sig =
    (do bufs <- buf_code; gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas;Lit 1w;FST bufs;Lit 128w;SND bufs;Lit 32w];
        emit_void ASSERT [success]; emit_op MLOAD [SND bufs] od)` by
    (simp[Abbr `buf_code`,compile_ecrecover_def,
       comp_ignore_bind_def,comp_bind_assoc] >>
     simp[comp_bind_def,comp_return_def,FUN_EQ_THM]) >>
  `(do gas <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w];
       emit_void ASSERT [success]; emit_op MLOAD [Var qo] od)
     shadow_cz = (op,shadow_sb)` by
    (qpat_x_assum `compile_ecrecover h v r sig shadow_sf = (op,shadow_sb)` mp_tac >>
     simp[comp_bind_def,comp_return_def]) >>
  `(do gas <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w];
       emit_void ASSERT [success]; emit_op MLOAD [Var qo] od)
     cz = (op,sb)` by
    (qpat_x_assum `compile_ecrecover h v r sig sf = (op,sb)` mp_tac >>
     simp[comp_bind_def,comp_return_def]) >>
  qabbrev_tac `cg = SND (emit_op GAS [] cz)` >>
  `emit_op GAS [] cz = (Var gv,cg)` by
    simp[Abbr `cg`,Abbr `gv`,emit_op_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
      fresh_id_def,fresh_var_def,emit_def] >>
  `?shadow_cg. emit_op GAS [] shadow_cz = (Var gv,shadow_cg) /\
     gas_shadow_state cg shadow_cg` by
    (mp_tac (Q.SPECL [`cz`,`shadow_cz`]
       (REWRITE_RULE [gas_shadow_compiles_def]
        (SIMP_RULE bool_ss [] (Q.INST [`opc` |-> `GAS`,`opc'` |-> `GAS`,
          `ops` |-> `[]`] gas_shadow_compiles_emit_op)))) >> simp[] >>
     Cases_on `emit_op GAS [] shadow_cz` >> simp[] >> metis_tac[]) >>
  `!st. ci_mono st (SND (buf_code st))` by
    (qunabbrev_tac `buf_code` >> POP_ASSUM_LIST (K all_tac) >>
     gen_tac >> simp[comp_ignore_bind_def] >>
     rpt (match_mp_tac ci_mono_bind >> conj_tac
       >- simp[ci_mono_compile_alloc_buffer,ci_mono_emit_op,
            ci_mono_emit_void,ci_mono_bind] >> rpt gen_tac >> BETA_TAC) >>
     simp[ci_mono_comp_return]) >>
  `!gas st. ci_mono st (SND ((do
       success <- emit_op STATICCALL
         [gas;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w];
       emit_void ASSERT [success]; emit_op MLOAD [Var qo] od) st))` by
    (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >> simp[comp_ignore_bind_def] >>
     rpt (match_mp_tac ci_mono_bind >> conj_tac
       >- simp[ci_mono_emit_op,ci_mono_emit_void] >> rpt gen_tac >> BETA_TAC) >>
     simp[ci_mono_emit_op]) >>
  `((do success <- emit_op STATICCALL
       [Var gv;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w];
       emit_void ASSERT [success]; emit_op MLOAD [Var qo] od) cg = (op,sb)) /\
   ((do success <- emit_op STATICCALL
       [Var gv;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w];
       emit_void ASSERT [success]; emit_op MLOAD [Var qo] od) shadow_cg =
       (op,shadow_sb))` by
    (conj_tac
     >- (qpat_x_assum `(do gas <- emit_op GAS []; _ od) cz = (op,sb)` mp_tac >>
         simp[comp_bind_def]) >>
     qpat_x_assum `(do gas <- emit_op GAS []; _ od) shadow_cz = (op,shadow_sb)` mp_tac >>
     simp[comp_bind_def]) >>
  `ci_mono cg sb /\ ci_mono shadow_cg shadow_sb /\
   ci_mono shadow_sf shadow_cz` by metis_tac[pairTheory.SND] >>
  `ci_mono cz cg /\ ci_mono shadow_cz shadow_cg` by
    (mp_tac (Q.SPECL [`GAS`,`[]`,`cz`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`GAS`,`[]`,`shadow_cz`] ci_mono_emit_op) >> simp[]) >>
  `cs_extends sa cz /\ cs_extends cz cg /\ cs_extends cg sb /\
   cs_extends shadow_sa shadow_cz /\ cs_extends shadow_cz shadow_cg /\
   cs_extends shadow_cg shadow_sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code cz cg func /\ fn_has_code shadow_cz shadow_cg shadow_func` by
    (conj_tac
     >- (MATCH_MP_TAC (Q.SPECL [`sa`,`cz`,`cg`,`sb`,`func`] fn_has_code_mid) >> simp[]) >>
     MATCH_MP_TAC (Q.SPECL [`shadow_sa`,`shadow_cz`,`shadow_cg`,`shadow_sb`,
       `shadow_func`] fn_has_code_mid) >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `cz`,`sb` |-> `cg`,`ta` |-> `shadow_cz`,
    `tb` |-> `shadow_cg`,`op` |-> `Var gv`,`shadow_op` |-> `Var gv`,
    `s0` |-> `sbuf`,`memory` |-> `T`] compile_generated_gas_origin_path) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then strip_assume_tac >>
  `eval_operand (Var qi) sbuf = SOME wi /\
   eval_operand (Var qo) sbuf = SOME wo` by simp[eval_operand_def] >>
  `?vcall. run_inst_seq [gi;ci] sbuf = OK vcall` by
    (qunabbrev_tac `gi` >> qunabbrev_tac `ci` >>
     MATCH_MP_TAC (Q.INST [`src` |-> `qi`,`dst` |-> `qo`,`gv` |-> `gv`,
       `cv` |-> `cv`,`id` |-> `cz.cs_next_id`,`addr` |-> `1w`,
       `an` |-> `128w`,`rn` |-> `32w`,`s` |-> `sbuf`,
       `wi` |-> `wi`,`wo` |-> `wo`] computed_call_prefix) >> simp[]) >>
  qabbrev_tac `u = update_var gv (HD (sbuf.vs_gas_readings ++ [0w]))
    (sbuf with vs_gas_readings := DROP 1 sbuf.vs_gas_readings)` >>
  `step_inst_base gi sbuf = OK u` by simp[Abbr `gi`,Abbr `u`,step_GAS] >>
  `step_inst_base ci u = OK vcall` by
    (qpat_assum `run_inst_seq [gi;ci] sbuf = OK vcall`
       (fn run => qpat_assum `step_inst_base gi sbuf = OK u`
         (fn gas => POP_ASSUM_LIST (K all_tac) >> mp_tac run >>
           simp[run_inst_seq_def,gas] >>
           Cases_on `step_inst_base ci u` >> simp[run_inst_seq_def])) ) >>
  qabbrev_tac `Gcall = step_prov PG (step_prov PG Gbuf gi u) ci vcall` >>
  qabbrev_tac `tncall = step_taint ci u vcall (step_taint gi sbuf u tnbuf)` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     ghost_inv_at (DF H) lo d cenv cx mid Gbuf tnbuf sbuf /\
     stmt_state_rel H ctx func cenv cx mid sbuf /\
     local_ptrs_rel func cenv mid.scopes sbuf /\ allocas_from lo sbuf /\
     tnbuf.t_stor SUBSET (DF H).d_stor sbuf.vs_call_ctx.cc_address
       (sbuf.vs_accounts sbuf.vs_call_ctx.cc_address).storage /\
     tnbuf.t_trans SUBSET (DF H).d_trans sbuf.vs_call_ctx.cc_address
       (sbuf.vs_transient sbuf.vs_call_ctx.cc_address)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       stmt_state_rel _ _ _ _ _ _ sbuf /\ _`
       (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >>
     qpat_assum `stmt_state_rel H _ _ _ _ _ sbuf`
       (strip_assume_tac o PURE_REWRITE_RULE [stmt_state_rel_def,state_rel_def]) >>
     qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ sbuf`
       (strip_assume_tac o PURE_REWRITE_RULE [ghost_inv_at_def,stor_taint_ok_at_def]) >>
     simp[]) >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
      not_fresh_at cz x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
      not_fresh_at cz x)` by metis_tac[not_fresh_at_mono,ci_mono_def] >>
  `(lo <> 0 ==> !x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at cz x)` by
    fs[local_ptrs_reserved_def] >>
  `sf.cs_next_var <= cz.cs_next_var /\ sf.cs_next_id <= cz.cs_next_id` by
    fs[ci_mono_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    stmt_state_rel _ _ _ _ _ _ sbuf /\ _`
    (fn th => qpat_assum
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
      (strip_assume_tac o MATCH_MP th)) >>
  `mid.outcomes = SOME sbuf.vs_outcomes` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ sbuf`
       (fn state => POP_ASSUM_LIST (K all_tac) >> mp_tac state) >>
     simp[stmt_state_rel_def,state_rel_def]) >>
  Cases_on `?co rest. sbuf.vs_outcomes = co::rest /\ co.co_success`
  >- (pop_assum (qx_choose_then `co` (qx_choose_then `rest` strip_assume_tac)) >>
      `?q. run_inst_seq [gi;ci;ai] sbuf = OK q` by
        (mp_tac (Q.INST [`target` |-> `1w`,`insz` |-> `128w`,
           `outsz` |-> `32w`,`ip` |-> `Var qi`,`op` |-> `Var qo`,
           `sm` |-> `cz`,`sb` |-> `cq`,`res` |-> `Var qo`,`s` |-> `sbuf`]
           computed_suffix_success) >>
         (impl_tac >- simp[]) >> simp[]) >>
      qpat_assum `ghost_inv_at (DF (storage_trace_horizon _)) _ _ _ _ _ Gbuf tnbuf sbuf`
        (fn ghost => let
           val actualDF = rator (hd (snd (strip_comb (concl ghost))));
           val th = precompile_suffix_success_full_family;
           val dv = valOf (List.find (fn v => fst (dest_var v) = "DF")
             (free_vars (concl th)));
           val typed = INST_TYPE (match_type (type_of dv) (type_of actualDF)) th;
           val dv = valOf (List.find (fn v => fst (dest_var v) = "DF")
             (free_vars (concl typed)));
           val provider = INST [dv |-> actualDF] typed;
         in mp_tac (Q.INST [`addr` |-> `1w`,`an` |-> `128w`,`rn` |-> `32w`,
           `sm` |-> `cz`,`sb` |-> `cq`,`res` |-> `Var qo`,
           `src` |-> `qi`,`dst` |-> `qo`,`id` |-> `cz.cs_next_id`,
           `s` |-> `sbuf`,`v` |-> `vcall`,`G` |-> `Gbuf`,`tn` |-> `tnbuf`,
           `G2` |-> `Gcall`,`tn2` |-> `tncall`,`es` |-> `mid`,
           `trace` |-> `mid.storage_trace`,
           `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] provider) end) >>
      (impl_tac >-
        (simp[Abbr `gi`,Abbr `ci`,Abbr `ai`,Abbr `Gcall`,Abbr `tncall`,
           wordsTheory.dimword_def] >>
         gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
           ghost_inv_at _ _ _ _ _ _ Gbuf tnbuf sbuf /\ _`
           (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
             (strip_assume_tac o MATCH_MP th)) >> simp[] >>
         rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choose_then `scall` (qx_choose_then `Gc`
        (qx_choose_then `tnc` strip_assume_tac))) >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        gas_origin_ptr_path _ _ _ _ /\ _`
        (fn th => qpat_assum
          `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
          (strip_assume_tac o MATCH_MP th)) >>
      `q.vs_current_bb = sbuf.vs_current_bb /\ ~q.vs_halted` by
        (conj_tac
         >- (MATCH_MP_TAC (BETA_RULE (Q.SPECL [`[gi;ci;ai]`,`sbuf`,`q`]
               (Q.ISPEC `\ss:venom_state. ss.vs_current_bb`
                 run_inst_seq_preserves_field))) >>
             conj_tac >- first_assum ACCEPT_TAC >>
             simp[Abbr `gi`,Abbr `ci`,Abbr `ai`] >>
             rpt strip_tac >>
             qpat_assum `step_inst_base i ss1 = OK ss2`
               (fn step => qpat_assum `i = _`
                 (fn inst => POP_ASSUM_LIST (K all_tac) >>
                   assume_tac step >> assume_tac inst)) >> gvs[] >>
             qpat_assum `step_inst_base _ ss1 = OK ss2`
               (fn step => let
                  val args = snd (strip_comb (lhs (concl step)));
                  val finish = rand (rhs (concl step));
                  val th = SPECL [hd args, List.nth (args,1), finish]
                    (Q.SPECL [`0`,`ARB`] step_preserves_control_flow);
                in mp_tac (SIMP_RULE (srw_ss())
                  [step_inst_non_invoke,mk_inst_def,is_terminator_def] th) end) >>
             fs[mk_inst_def]) >>
         qpat_assum `run_inst_seq [gi;ci;ai] sbuf = OK q`
           (mp_tac o MATCH_MP (SRULE [GSYM AND_IMP_INTRO] run_inst_seq_preserves_halted)) >>
         simp[Abbr `gi`,Abbr `ci`,Abbr `ai`,mk_inst_def,is_terminator_def]) >>
      `mem_word_at (w2n wo) scall.vs_memory =
         typed_val_to_w256 (BaseTV AddressT)
           (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
             NONE => 0w | SOME addr => addr))` by
        (simp[wordsTheory.dimword_def] >> MATCH_MP_TAC ecrecover_output_write >>
         simp[Abbr `data`] >>
         Cases_on `vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws)` >> simp[]) >>
      qpat_assum `emit_op MLOAD [Var qo] cq = (op,sb)`
        (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
      qabbrev_tac `outv = STRING #"%" (toString cq.cs_next_var)` >>
      qabbrev_tac `li = mk_inst cq.cs_next_id MLOAD [Var qo] [outv]` >>
      qabbrev_tac `loaded = update_var outv (mload (w2n wo) scall) scall` >>
      qabbrev_tac `sfin = loaded with vs_inst_idx := SUC scall.vs_inst_idx` >>
      qabbrev_tac `Gfin = step_prov PG Gc li loaded` >>
      qabbrev_tac `tnfin = step_taint li scall loaded tnc` >>
      qpat_assum `same_blocks cz cq`
        (strip_assume_tac o PURE_REWRITE_RULE [same_blocks_def]) >>
      `scall.vs_current_bb = cq.cs_current_bb /\
       scall.vs_inst_idx = LENGTH cq.cs_current_insts /\ ~scall.vs_halted` by simp[] >>
      `sb.cs_current_bb = cq.cs_current_bb` by
        (imp_res_tac emit_op_same_blocks >> fs[same_blocks_def]) >>
      `cs_extends sa cq /\ cs_extends cq sb` by
        metis_tac[cs_extends_trans,ci_mono_def] >>
      `fn_has_code cq sb func` by
        (mp_tac (Q.SPECL [`sa`,`cq`,`sb`,`func`] fn_has_code_split) >> simp[]) >>
      `?bl. lookup_block scall.vs_current_bb func.fn_blocks = SOME bl /\
        get_instruction bl scall.vs_inst_idx = SOME li` by
        (mp_tac (Q.SPECL [`cq`,`sb`,`func`,`[li]`] fn_has_code_same_block) >>
         (impl_tac >- simp[Abbr `li`,Abbr `outv`]) >>
         disch_then (qx_choose_then `bload` strip_assume_tac) >>
         qexists_tac `bload` >>
         qpat_assum `!i. i < _ ==> get_instruction bload _ = _`
           (fn inst => qpat_assum `lookup_block cq.cs_current_bb _ = SOME bload`
             (fn lookup => qpat_assum `scall.vs_current_bb = cq.cs_current_bb`
               (fn cur => qpat_assum `scall.vs_inst_idx = LENGTH cq.cs_current_insts`
                 (fn idx => POP_ASSUM_LIST (K all_tac) >>
                   MAP_EVERY assume_tac
                     [SIMP_RULE (srw_ss()) [] (Q.SPEC `0` inst),lookup,cur,idx])))) >>
         simp[]) >>
      `step_inst_base li scall = OK loaded` by
        (qunabbrev_tac `li` >> qunabbrev_tac `loaded` >>
         qpat_assum `eval_operand (Var qo) scall = SOME wo`
           (fn ev => POP_ASSUM_LIST (K all_tac) >> assume_tac ev) >>
         simp[step_inst_base_opcode_eqs,mk_inst_def,exec_read1_def]) >>
      `op_taint tnfin (Var outv) = {} /\
       tnfin.t_mem = tnc.t_mem /\ tnfin.t_stor = tnc.t_stor /\
       tnfin.t_trans = tnc.t_trans /\ tnfin.t_imm = tnc.t_imm` by
        (qunabbrev_tac `tnfin` >> qunabbrev_tac `li` >> qunabbrev_tac `loaded` >>
         qpat_assum `eval_operand (Var qo) scall = SOME wo`
           (fn ev => qpat_assum `!i. _ ==> i NOTIN tnc.t_mem`
             (fn clean => POP_ASSUM_LIST (K all_tac) >>
               MAP_EVERY assume_tac [ev,SIMP_RULE (srw_ss())
                 [wordsTheory.dimword_def] clean])) >>
         mp_tac (Q.SPECL [`ARB`,`ARB`,`tnc`,`scall`,`cq.cs_next_id`,
           `Var qo`,`outv`,`wo`] mload_ghost_clean) >>
         (impl_tac >- simp[]) >> simp[mload_ghost_frame]) >>
      `allocas_from lo scall` by
        (qpat_assum `ghost_inv_at _ _ _ _ _ _ Gc tnc scall`
           (fn ghost => POP_ASSUM_LIST (K all_tac) >> mp_tac ghost) >>
         simp[ghost_inv_at_def]) >>
      `ptr_covers Gc tnc qo scall 32` by
        (qpat_assum `ptr_covers Gc tnc qo scall _`
           (ACCEPT_TAC o SIMP_RULE (srw_ss()) [wordsTheory.dimword_def])) >>
      `w2n wo + 32 <= scall.vs_alloca_next` by simp[] >>
      `inst_mem_below_frontier li scall` by
        (qunabbrev_tac `li` >>
         qpat_assum `eval_operand (Var qo) scall = SOME wo`
           (fn ev => qpat_assum `w2n wo + 32 <= scall.vs_alloca_next`
             (fn bound => POP_ASSUM_LIST (K all_tac) >>
               MAP_EVERY assume_tac [ev,bound])) >>
         simp[below_frontier_MLOAD]) >>
      `li.inst_opcode = MLOAD /\ inst_dload_in_section li scall` by
        simp[Abbr `li`,mk_inst_def,inst_dload_in_section_def] >>
      `!D. ptr_inst_ok D lo 0 ctx func Gc tnc li scall` by
        (gen_tac >> qunabbrev_tac `li` >>
         qpat_assum `ptr_covers Gc tnc qo scall 32`
           (fn covers => qpat_assum `allocas_from lo scall`
             (fn allocas => qpat_assum `~ctx_has_dalloca ctx`
               (fn nd => POP_ASSUM_LIST (K all_tac) >>
                 MAP_EVERY assume_tac [covers,allocas,nd]))) >>
         irule ptr_inst_ok_mload_lo >> simp[]) >>
      rename1 `lookup_block scall.vs_current_bb func.fn_blocks = SOME bfin` >>
      `!D. gas_origin_ptr_edge (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (scall,Gc,tnc) [] (OK sfin,Gfin,tnfin)` by
        (gen_tac >>
         qpat_assum `!D. ptr_inst_ok D lo 0 ctx func Gc tnc li scall`
           (assume_tac o Q.SPEC `D`) >>
         mp_tac (Q.INST [`s` |-> `scall`,`G` |-> `Gc`,`tn` |-> `tnc`,
           `i` |-> `li`,`u` |-> `loaded`,`bb` |-> `bfin`,
           `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
           straight_line_origin_ptr_edge) >>
         (impl_tac >-
           (qpat_assum `li.inst_opcode = MLOAD`
              (fn opcode => simp[NoAsms,opcode,is_terminator_def]) >>
            rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         simp[Abbr `sfin`,Abbr `Gfin`,Abbr `tnfin`]) >>
      `~sfin.vs_halted` by simp[Abbr `sfin`,Abbr `loaded`,update_var_def] >>
      `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (scall,Gc,tnc) [] (OK sfin,Gfin,tnfin)` by
        (gen_tac >>
         qpat_assum `!D. gas_origin_ptr_edge _ _ _ _`
           (fn edge => qpat_assum `~sfin.vs_halted`
             (fn nh => POP_ASSUM_LIST (K all_tac) >>
               MAP_EVERY assume_tac [Q.SPEC `D` edge,nh])) >>
         metis_tac[gas_origin_ptr_path_rules,APPEND_NIL]) >>
      `!H:(bool # 256 word # type_value) list # num list.
         valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (sarg,G1,tn1) [F] (OK sfin,Gfin,tnfin)` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
           gas_origin_ptr_path _ _ _ _ /\ _`
           (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
             (strip_assume_tac o MATCH_MP th)) >>
         qpat_assum `!D. gas_origin_ptr_path _ (sarg,G1,tn1) [] _`
           (fn prefix => qpat_assum `!D. gas_origin_ptr_path _ (scall,Gc,tnc) [] _`
             (fn load => qpat_assum `gas_origin_ptr_path (DF H,_,_,_,_,_) (sbuf,Gbuf,tnbuf) [F] _`
               (fn call => let
                  val actualD = fst (pairSyntax.dest_pair
                    (hd (snd (strip_comb (concl call)))));
                  fun join left right = let
                    val args = snd (strip_comb (concl right));
                    val st = pairSyntax.strip_pair (List.nth (args,1));
                    val out = pairSyntax.strip_pair (List.nth (args,3));
                    val th = SPECL (st @ [List.nth (args,2)] @ out)
                      (MATCH_MP gas_origin_ptr_path_append left);
                    val endpoint = List.nth (snd (strip_comb (concl left)),3);
                  in MATCH_MP th (CONJ (REFL endpoint) right) end;
                  val total = join (join (SPEC actualD prefix) call) (SPEC actualD load);
                in ACCEPT_TAC (SIMP_RULE (srw_ss()) [APPEND,APPEND_NIL] total) end)))) >>
      `!x. not_fresh_at cz x ==> x <> outv` by
        (rw[loweringStateRelDefsTheory.not_fresh_at_def] >>
         first_x_assum (qspec_then `cq.cs_next_var` mp_tac) >> simp[Abbr `outv`]) >>
      `!x. not_fresh_at cz x ==>
         lookup_var x sfin = lookup_var x scall /\
         FLOOKUP Gfin x = FLOOKUP Gc x /\
         op_taint tnfin (Var x) = op_taint tnc (Var x)` by
        (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at cz x ==> x <> outv`
           (fn fresh => qpat_assum `not_fresh_at cz x`
             (assume_tac o MATCH_MP fresh)) >>
         qunabbrev_tac `sfin` >> qunabbrev_tac `loaded` >>
         qunabbrev_tac `Gfin` >> qunabbrev_tac `tnfin` >> qunabbrev_tac `li` >>
         qpat_assum `x <> outv`
           (fn neq => POP_ASSUM_LIST (K all_tac) >> assume_tac neq) >>
         simp[mload_ghost_frame,update_var_def,lookup_var_def,FLOOKUP_UPDATE]) >>
      `!H:(bool # 256 word # type_value) list # num list.
         valid_horizon cx st0 H mid.storage_trace ==>
         stmt_state_rel H ctx func cenv cx
           (mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes)) sfin /\
         ghost_inv_at (DF H) lo d cenv cx
           (mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes)) Gfin tnfin sfin` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
           gas_origin_ptr_path _ _ _ _ /\ _`
           (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
             (strip_assume_tac o MATCH_MP th)) >>
         conj_tac
         >- (qunabbrev_tac `sfin` >> qunabbrev_tac `loaded` >>
             pure_rewrite_tac[stmt_state_rel_inst_idx] >>
             irule stmt_state_rel_update_var >> rpt conj_tac >>
             FIRST [first_assum ACCEPT_TAC,
               (simp[NoAsms,Abbr `outv`] >>
                MATCH_MP_TAC (Q.SPECL [`cenv`,`cz`,`mid.scopes`,`cq.cs_next_var`]
                  local_ptrs_reserved_fresh) >> simp[])]) >>
         irule ghost_inv_at_exterior_frame >>
         qexistsl_tac [`Gc`,`mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes)`,
           `scall`,`cz`,`tnc`] >>
         rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
           simp[Abbr `sfin`,Abbr `loaded`,update_var_def]]) >>
      `storage_trace_frame (eval_exprs cx args)` by simp[evaluate_storage_trace_frame] >>
      `?observations. mid.storage_trace = es.storage_trace ++ observations` by
        (qpat_assum `storage_trace_frame (eval_exprs cx args)`
           (fn frame => qpat_assum `!tail. eval_exprs cx args _ = _`
             (fn run => mp_tac (MATCH_MP storage_trace_frame_prefix
               (CONJ frame (Q.SPEC `[]` run))))) >> simp[]) >>
      qpat_assum `mid.storage_trace = es.storage_trace ++ observations`
        (fn trace => qpat_assum
          `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
          (fn valid => assume_tac (REWRITE_RULE [GSYM trace]
            (MATCH_MP valid_horizon_append (REWRITE_RULE [trace] valid))))) >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
        stmt_state_rel _ _ _ _ _ _ s0 /\ _`
        (fn th => qpat_assum
          `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace`
          (strip_assume_tac o MATCH_MP th)) >>
      `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
        (qpat_assum `wb_frame cenv es mid sa s0 sarg`
           (fn frame => POP_ASSUM_LIST (K all_tac) >> assume_tac frame) >>
         fs[wb_frame_def,locals_kept_def]) >>
      `sa.cs_next_var <= cz.cs_next_var` by
        (qpat_assum `sa.cs_next_var <= sf.cs_next_var`
           (fn a => qpat_assum `sf.cs_next_var <= cz.cs_next_var`
             (fn b => POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac [a,b])) >>
         decide_tac) >>
      `wb_frame cenv es mid sa s0 sbuf` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx es s0`
           (fn state => let
              val actualH = hd (snd (strip_comb (concl state)));
              val th = wb_frame_trans;
              val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
                (free_vars (concl th)));
              val typed = INST_TYPE (match_type (type_of hv) (type_of actualH)) th;
              val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
                (free_vars (concl typed)));
              val provider = INST [hv |-> actualH] typed;
            in MATCH_MP_TAC (Q.SPECL [`func`,`cenv`,`cx`,`es`,`s0`,`sa`,
              `mid`,`mid`,`sf`,`sarg`,`sbuf`,`ctx`] provider) end) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `wb_frame cenv es (mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes))
         sa s0 scall` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx es s0`
           (fn state => let
              val actualH = hd (snd (strip_comb (concl state)));
              val th = wb_frame_trans;
              val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
                (free_vars (concl th)));
              val typed = INST_TYPE (match_type (type_of hv) (type_of actualH)) th;
              val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
                (free_vars (concl typed)));
              val provider = INST [hv |-> actualH] typed;
            in MATCH_MP_TAC (Q.SPECL [`func`,`cenv`,`cx`,`es`,`s0`,`sa`,
              `mid`,`mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes)`,
              `sf`,`sbuf`,`scall`,`ctx`] provider) end) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `!x w. not_fresh_at cz x /\ lookup_var x scall = SOME w ==>
         lookup_var x sfin = SOME w` by
        (qx_genl_tac [`x`,`resultword`] >> strip_tac >>
         qpat_assum `!x. not_fresh_at cz x ==>
           lookup_var x sfin = lookup_var x scall /\ _`
           (fn frame => qpat_assum `not_fresh_at cz x`
             (fn fresh => qpat_assum `lookup_var x scall = SOME resultword`
               (fn value => ACCEPT_TAC (TRANS
                 (CONJUNCT1 (MATCH_MP (Q.SPEC `x` frame) fresh)) value))))) >>
      `wb_frame cenv es (mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes))
         sa s0 sfin` by
        (MATCH_MP_TAC (Q.SPECL [`cenv`,`es`,
           `mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes)`,
           `sa`,`s0`,`scall`,`cz`,`sfin`] wb_frame_readonly_tail) >>
         rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
           simp[Abbr `sfin`,Abbr `loaded`,update_var_def]]) >>
      `sfin.vs_memory = scall.vs_memory /\
       sfin.vs_allocas = scall.vs_allocas /\
       sfin.vs_alloca_next = scall.vs_alloca_next /\
       sfin.vs_current_bb = sb.cs_current_bb /\
       sfin.vs_inst_idx = LENGTH sb.cs_current_insts` by
        simp[Abbr `sfin`,Abbr `loaded`,update_var_def] >>
      `alloca_next_valid s0` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx es s0`
           (fn state => POP_ASSUM_LIST (K all_tac) >> assume_tac state) >>
         fs[stmt_state_rel_def,alloca_inv_def]) >>
      `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id ==>
         off + len <= sarg.vs_alloca_next` by
        (rpt gen_tac >> strip_tac >>
         qpat_assum `alloca_next_valid s0`
           (fn next => qpat_assum `FLOOKUP s0.vs_allocas aid = SOME (off,len)`
             (fn lookup => qpat_assum `s0.vs_alloca_next <= sarg.vs_alloca_next`
               (fn growth => POP_ASSUM_LIST (K all_tac) >>
                 MAP_EVERY assume_tac [next,lookup,growth]))) >>
         fs[alloca_next_valid_def] >> res_tac >> decide_tac) >>
      `!name b len. local_region cenv es.scopes s0 name b len ==>
         b + len <= sarg.vs_alloca_next` by
        (rpt gen_tac >> strip_tac >>
         qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx es s0`
           (fn state => qpat_assum `local_region cenv es.scopes s0 name b len`
             (fn region => qpat_assum `s0.vs_alloca_next <= sarg.vs_alloca_next`
               (fn growth => POP_ASSUM_LIST (K all_tac) >>
                 MAP_EVERY assume_tac [MATCH_MP body_local_region_frontier
                   (CONJ state region),growth]))) >> decide_tac) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 Gbuf tnbuf` by
        (qpat_assum `!es0 sk s0 G0 tn0. _ ==> ghost_kept_at _ _ _ _ _ _ _ Gbuf tnbuf`
           (mp_tac o Q.SPECL [`es`,`sa`,`s0`,`G0`,`tn0`]) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then ACCEPT_TAC) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 Gc tnc` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func cenv cx es s0`
           (fn state => let
              val actualH = hd (snd (strip_comb (concl state)));
              val th = SPEC_ALL ghost_kept_at_wb_trans;
              val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
                (free_vars (concl th)));
              val typed = INST_TYPE (match_type (type_of hv) (type_of actualH)) th;
              val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
                (free_vars (concl typed)));
              val provider = INST [hv |-> actualH] typed;
            in MATCH_MP_TAC (Q.INST [`G1` |-> `Gbuf`,`tn1` |-> `tnbuf`,
              `es1` |-> `mid`,`sm` |-> `sf`,`G2` |-> `Gc`,`tn2` |-> `tnc`,
              `s1` |-> `sbuf`,`es'` |-> `mid`] provider) end) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `!oldvar. not_fresh_at sa oldvar ==> not_fresh_at cz oldvar` by
        (gen_tac >> strip_tac >>
         MATCH_MP_TAC (Q.SPECL [`sa`,`cz`,`oldvar`] not_fresh_at_mono) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `!oldvar. not_fresh_at sa oldvar ==>
         FLOOKUP Gfin oldvar = FLOOKUP Gc oldvar /\
         op_taint tnfin (Var oldvar) = op_taint tnc (Var oldvar)` by
        (gen_tac >> strip_tac >>
         qpat_assum `!oldvar. not_fresh_at sa oldvar ==> not_fresh_at cz oldvar`
           (fn lift => qpat_assum `not_fresh_at sa oldvar`
             (assume_tac o MATCH_MP (Q.SPEC `oldvar` lift))) >>
         qpat_assum `!x. not_fresh_at cz x ==> lookup_var x sfin = lookup_var x scall /\ _`
           (fn frame => qpat_assum `not_fresh_at cz oldvar`
             (ACCEPT_TAC o CONJUNCT2 o MATCH_MP (Q.SPEC `oldvar` frame)))) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 Gfin tnfin` by
        (MATCH_MP_TAC (Q.INST [`G` |-> `Gc`,`tn` |-> `tnc`,
           `G'` |-> `Gfin`,`tn'` |-> `tnfin`] ghost_kept_at_clean_suffix) >>
         rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
           (qpat_assum `tnfin.t_mem = tnc.t_mem`
              (fn frame => rewrite_tac[frame]) >> simp[])]) >>
      `mload (w2n wo) scall = typed_val_to_w256 (BaseTV AddressT)
         (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
           NONE => 0w | SOME addr => addr))` by
        (qpat_assum `mem_word_at (w2n wo) scall.vs_memory = _`
           (ACCEPT_TAC o REWRITE_RULE [mem_word_at_eq_mload])) >>
      `eval_operand op sfin = SOME (typed_val_to_w256 (BaseTV AddressT)
         (AddressV (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
           NONE => 0w | SOME addr => addr)))` by
        (qunabbrev_tac `sfin` >> qunabbrev_tac `loaded` >>
         qpat_assum `mload (w2n wo) scall = _`
           (fn encoded => qpat_assum `op = Var outv`
             (fn result => POP_ASSUM_LIST (K all_tac) >>
               MAP_EVERY assume_tac [encoded,result])) >>
         simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]) >>
      `op_taint tnfin op = {} /\ op_prov Gfin op = NONE` by
        (qpat_assum `op = Var outv` (fn result => pure_rewrite_tac[result]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qunabbrev_tac `Gfin` >> qunabbrev_tac `li` >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[op_prov_def,step_prov_def,set_prov_def,out_prov_def,mk_inst_def,
           FLOOKUP_DRESTRICT]) >>
      `alloca_inv sbuf /\ alloca_inv scall` by
        (conj_tac
         >- (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ sbuf`
               (fn state => POP_ASSUM_LIST (K all_tac) >> assume_tac state) >>
             fs[stmt_state_rel_def]) >>
         qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ scall`
           (fn state => POP_ASSUM_LIST (K all_tac) >> assume_tac state) >>
         fs[stmt_state_rel_def]) >>
      `alloca_history func scall` by
        (qpat_assum `isPREFIX [gi;ci;ai] (DROP sbuf.vs_inst_idx bb.bb_instructions)`
           (qx_choose_then `code_rest` assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
         qpat_assum `scall = q with vs_inst_idx := sbuf.vs_inst_idx + 3`
           (fn cursor => pure_rewrite_tac[cursor]) >>
         MATCH_MP_TAC (SIMP_RULE (srw_ss()) []
           (Q.SPECL [`func`,`bb`,`sbuf`,`[gi;ci;ai]`,`code_rest`,`q`]
             alloca_history_run_inst_seq)) >>
         rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
           (simp[NoAsms,Abbr `gi`,Abbr `ci`,Abbr `ai`,mk_inst_def,is_terminator_def] >>
            qpat_assum `DROP sbuf.vs_inst_idx bb.bb_instructions = _`
              (ACCEPT_TAC o SIMP_RULE (srw_ss()) [mk_inst_def,APPEND]))]) >>
      `alloca_history func sfin` by
        (qunabbrev_tac `sfin` >>
         qpat_assum `li.inst_opcode = MLOAD`
           (fn opcode => MATCH_MP_TAC (SIMP_RULE (srw_ss()) [opcode,is_terminator_def]
             (Q.SPECL [`func`,`scall`,`bfin`,`li`,`loaded`] alloca_history_base_step))) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `s0.vs_alloca_next <= sfin.vs_alloca_next` by
        (qpat_assum `s0.vs_alloca_next <= sarg.vs_alloca_next`
           (fn a => qpat_assum `sarg.vs_alloca_next <= sbuf.vs_alloca_next`
             (fn b => qpat_assum `sfin.vs_alloca_next = scall.vs_alloca_next`
               (fn c => qpat_assum `scall.vs_alloca_next = sbuf.vs_alloca_next`
                 (fn d => POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac [a,b,c,d])))) >>
         fs[] >> decide_tac) >>
      `emit_op ALLOCA [Lit 32w] sp = (Var qo,cm)` by
        (qpat_assum `compile_alloc_buffer 32 sp = (ob,cm)`
           (fn alloc => qpat_assum `ob.buf_operand = Var qo`
             (fn result => POP_ASSUM_LIST (K all_tac) >>
               MAP_EVERY assume_tac [alloc,result])) >>
         Cases_on `emit_op ALLOCA [Lit 32w] sp` >>
         gvs[compile_alloc_buffer_def,comp_bind_def,comp_return_def]) >>
      `emitted_insts sp cm = [mk_inst sp.cs_next_id ALLOCA [Lit 32w] [qo]]` by
        (qpat_assum `emit_op ALLOCA [Lit 32w] sp = (Var qo,cm)`
           (fn alloc => POP_ASSUM_LIST (K all_tac) >>
             strip_assume_tac (MATCH_MP emitted_insts_emit_op alloc)) >> gvs[]) >>
      `ci_mono sf sp` by
        (qpat_assum `ci_mono sf ca` (fn a =>
         qpat_assum `ci_mono ca cb` (fn b =>
         qpat_assum `ci_mono cb cc` (fn c =>
         qpat_assum `ci_mono cc cd` (fn d =>
         qpat_assum `ci_mono cd sp` (fn e =>
           ACCEPT_TAC (List.foldl (fn (edge,whole) =>
             MATCH_MP ci_mono_trans (CONJ whole edge)) a [b,c,d,e]))))))) >>
      `cs_extends sf sp /\ cs_extends sp cm /\ cs_extends cm cz /\
       sf.cs_next_id <= sp.cs_next_id` by
        (qpat_assum `ci_mono sf sp` (fn a =>
         qpat_assum `ci_mono sp cm` (fn b =>
         qpat_assum `ci_mono cm cz` (fn c =>
           POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac [a,b,c]))) >>
         fs[ci_mono_def]) >>
      `fn_has_code sp cm func` by
        (MATCH_MP_TAC (Q.SPECL [`sf`,`sp`,`cm`,`cz`,`func`] fn_has_code_mid) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w] [qo]) (fn_insts func)` by
        (MATCH_MP_TAC (Q.INST [`sa` |-> `sp`,`sb` |-> `cm`,
           `inst` |-> `mk_inst sp.cs_next_id ALLOCA [Lit 32w] [qo]`]
           hash_emitted_inst_mem) >> simp[]) >>
      `!name b len. local_region cenv mid.scopes sarg name b len ==>
         regions_disjoint (w2n wo) 32 b len` by
        (rpt gen_tac >> DISCH_TAC >>
         `local_region cenv mid.scopes sbuf name b len` by
           (MATCH_MP_TAC (Q.SPECL [`cenv`,`mid.scopes`,`sf`,`mid.scopes`,
              `sarg`,`sbuf`,`name`,`b`,`len`] local_region_frame_fwd) >>
            rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
              (qpat_assum `wb_frame cenv mid mid sf sarg sbuf`
                (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE [wb_frame_def])), simp[]]) >>
         qpat_assum `!name b len. local_region cenv mid.scopes sbuf name b len ==> _`
           (fn th => MATCH_MP_TAC (Q.SPECL [`name`,`b`,`len`] th)) >>
         first_assum ACCEPT_TAC) >>
      `!off len. regions_disjoint off len (w2n wo) 32 ==>
         mem_bytes_at off len scall.vs_memory = mem_bytes_at off len sbuf.vs_memory` by
        (rpt gen_tac >> DISCH_TAC >>
         qpat_assum `scall.vs_memory = _`
           (fn th => pure_rewrite_tac [SIMP_RULE (srw_ss()) [wordsTheory.dimword_def] th]) >>
         MATCH_MP_TAC (Q.SPECL [`off`,`len`,`w2n (wo:256 word)`,`TAKE 32 data`,`sbuf`]
           mem_bytes_at_write_disjoint) >>
         `LENGTH (TAKE 32 data) <= 32` by simp[LENGTH_TAKE_EQ] >>
         qpat_assum `regions_disjoint off len (w2n wo) 32`
           (fn a => qpat_assum `LENGTH (TAKE 32 data) <= 32`
             (fn b => POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac [a,b])) >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      `pure_frame cenv func mid sf sarg scall` by
        (MATCH_MP_TAC (Q.SPECL [`cenv`,`func`,`mid`,`sf`,`sarg`,`sbuf`,`scall`,
           `mk_inst sp.cs_next_id ALLOCA [Lit 32w] [qo]`,`w2n (wo:256 word)`,`32`]
           pure_frame_buffer_tail) >>
         simp[NoAsms,mk_inst_def] >> rpt conj_tac >>
         FIRST [first_assum ACCEPT_TAC,
           (qpat_assum `MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w] [qo]) _`
              (ACCEPT_TAC o SIMP_RULE (srw_ss()) [mk_inst_def])),
           (qpat_assum `scall.vs_allocas = sbuf.vs_allocas`
              (fn eq => pure_rewrite_tac[eq]) >> simp[])]) >>
      `!aid entry. FLOOKUP sarg.vs_allocas aid = SOME entry ==>
         FLOOKUP scall.vs_allocas aid = SOME entry` by
        (qpat_assum `!aid entry. FLOOKUP sarg.vs_allocas aid = SOME entry ==> _`
           (fn frame => qpat_assum `scall.vs_allocas = sbuf.vs_allocas`
             (fn eq => POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac [frame,eq])) >>
         simp[]) >>
      `~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 scall` by
        (DISCH_TAC >> MATCH_MP_TAC (Q.SPECL [`cenv`,`func`,`es`,`mid`,`sa`,`sf`,
           `s0`,`sarg`,`scall`] pure_frame_trans) >>
         rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
           (qpat_assum `wb_frame cenv es mid sa s0 sarg`
             (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE [wb_frame_def])),
           (qpat_assum `~EXISTS expr_has_effect args ==> _` drule >> simp[])]) >>
      `~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 sfin` by
        (DISCH_TAC >> MATCH_MP_TAC (Q.SPECL [`cenv`,`func`,`es`,`sa`,`s0`,`scall`,
           `sfin`] pure_frame_mem_tail) >>
         rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
           (qpat_assum `~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 scall`
             drule >> simp[]),
           (qpat_assum `sfin.vs_allocas = scall.vs_allocas`
             (fn eq => pure_rewrite_tac[eq]) >> simp[])]) >>
      qabbrev_tac `retval = AddressV
        (case vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws) of
          NONE => 0w | SOME addr => addr)` >>
      (fn (asl,goal) => let
         val actualSource = List.nth (snd (strip_comb goal),4);
         val th = gas_outcome_full_intro;
         val sv = valOf (List.find (fn v => fst (dest_var v) = "source")
           (free_vars (concl th)));
         val typed = INST_TYPE (match_type (type_of sv) (type_of actualSource)) th;
         val sv = valOf (List.find (fn v => fst (dest_var v) = "source")
           (free_vars (concl typed)));
         val provider = INST [sv |-> actualSource] typed;
       in MATCH_MP_TAC (Q.INST [`marks` |-> `[F]`,`res` |-> `INL retval`,
         `ee` |-> `mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes)`,
         `r` |-> `OK sfin`,`G'` |-> `Gfin`,`tn'` |-> `tnfin`] provider) (asl,goal) end) >>
      conj_tac
      >- (gen_tac >> qunabbrev_tac `retval` >>
          qpat_assum `builtin_result cx mid.accounts _ _ _ vals = _`
            (fn result => qpat_assum `mid.outcomes = SOME sbuf.vs_outcomes`
              (fn outcomes => qpat_assum `sbuf.vs_outcomes = co::rest`
                (fn runtime => qpat_assum `co.co_success`
                  (fn success => POP_ASSUM_LIST (K all_tac) >>
                    MAP_EVERY assume_tac [result,outcomes,runtime,success])))) >>
          Cases_on `sarg.vs_gas_readings` >>
          simp[gas_explicit_def,
            SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`] gasOracleReplayTheory.gas_prefix_suc),
            ZIP,MAP,FILTER,
            ignore_bind_def,bind_def,return_def,ecrecover_source_outcome_step]) >>
      conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
      gen_tac >> simp[NoAsms] >> DISCH_TAC >>
      qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
        stmt_state_rel _ _ _ _ _ _ sfin /\ _`
        (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
          (strip_assume_tac o MATCH_MP th)) >>
      conj_tac
      >- (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
            gas_origin_ptr_path _ (sarg,G1,tn1) [F] (OK sfin,Gfin,tnfin)`
            (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
              (ACCEPT_TAC o MATCH_MP th))) >>
      `storage_well_formed_on cx mid (FST H)` by
        (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
           stmt_state_rel _ _ _ _ _ _ sbuf /\ _`
           (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
             (strip_assume_tac o MATCH_MP th)) >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (MATCH_MP_TAC (Q.INST [`tv` |-> `BaseTV AddressT`] expr_post_typed_stack_intro) >>
          simp[NoAsms,expr_type_def,is_word_type_def,evaluate_type_def] >>
          rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
            FIRST_PROVE [qpat_assum `stmt_state_rel H ctx func cenv cx _ sfin`
              (fn state => let
                val eq = PART_MATCH rhs (Q.INST [`gs` |-> `[]:256 word list`]
                  stmt_state_rel_gas_obs) (concl state);
                val lifted = EQ_MP (SYM eq) state;
              in ACCEPT_TAC (CONV_RULE (RATOR_CONV (RAND_CONV
                (SIMP_CONV (srw_ss()) []))) lifted) end)],
            FIRST_PROVE [qpat_assum `wb_frame cenv es _ sa s0 sfin`
              (fn frame => let
                val eq = PART_MATCH rhs (Q.INST [`gs` |-> `[]:256 word list`]
                  (SPEC_ALL wb_frame_gas_obs)) (concl frame);
                val lifted = EQ_MP (SYM eq) frame;
              in ACCEPT_TAC (CONV_RULE (RATOR_CONV (RATOR_CONV (RATOR_CONV
                (RAND_CONV (SIMP_CONV (srw_ss()) []))))) lifted) end)],
            (qunabbrev_tac `retval` >> first_assum ACCEPT_TAC),
            FIRST_PROVE [simp[NoAsms,expr_has_effect_thm] >>
              qpat_assum `~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 sfin`
                (ACCEPT_TAC o REWRITE_RULE [listTheory.NOT_EXISTS])],
            (pure_rewrite_tac [SIMP_RULE (srw_ss()) [] (Q.INST
              [`st` |-> `mid`,`st'` |-> `mid with <|outcomes := SOME (DROP 1 sbuf.vs_outcomes); gas_obs := []|>`]
              storage_well_formed_on_backends)] >> first_assum ACCEPT_TAC)]) >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
        FIRST_PROVE [simp[NoAsms,exprSimMemDefsTheory.expr_store_bound_def,
          expr_type_def,is_word_type_def,ptr_val_ok_def] >>
          rpt conj_tac >> first_assum ACCEPT_TAC],
        (qpat_assum `ghost_inv_at (DF H) lo d cenv cx _ Gfin tnfin sfin`
          (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
         simp[ghost_inv_at_def] >> strip_tac >> first_assum ACCEPT_TAC)]) >>
  `?failed. run_inst_seq [gi;ci;ai] sbuf = Abort Revert_abort failed` by
    (mp_tac (Q.INST [`target` |-> `1w`,`insz` |-> `128w`,
       `outsz` |-> `32w`,`ip` |-> `Var qi`,`op` |-> `Var qo`,
       `sm` |-> `cz`,`sb` |-> `cq`,`res` |-> `Var qo`,`s` |-> `sbuf`]
       computed_suffix_oracle_failure) >>
     (impl_tac >-
       (simp[] >>
        qpat_assum `~?co rest. sbuf.vs_outcomes = co::rest /\ co.co_success`
          (fn neg => POP_ASSUM_LIST (K all_tac) >> assume_tac neg) >>
        Cases_on `sbuf.vs_outcomes` >> gvs[] >> metis_tac[])) >> simp[]) >>
  `eval_operand (Var cv) vcall = SOME 0w` by
    (qpat_assum `run_inst_seq [gi;ci;ai] sbuf = Abort Revert_abort failed`
       (fn run => qpat_assum `step_inst_base gi sbuf = OK u`
         (fn gas => qpat_assum `step_inst_base ci u = OK vcall`
           (fn call => qpat_assum `Abbrev (ai = _)`
             (fn assertion => POP_ASSUM_LIST (K all_tac) >>
               MAP_EVERY assume_tac [run,gas,call,assertion])))) >>
     fs[run_inst_seq_def] >>
     qpat_assum `_ = Abort Revert_abort failed`
       (fn run => qpat_assum `Abbrev (ai = _)`
         (fn assertion => POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [run,assertion])) >>
     gvs[Abbr `ai`,step_inst_base_opcode_eqs,mk_inst_def,AllCaseEqs()]) >>
  qpat_assum `ghost_inv_at (DF (storage_trace_horizon _)) _ _ _ _ _ Gbuf tnbuf sbuf`
    (fn ghost => let
       val actualDF = rator (hd (snd (strip_comb (concl ghost))));
       val th = precompile_suffix_abort_full_family;
       val dv = valOf (List.find (fn v => fst (dest_var v) = "DF") (free_vars (concl th)));
       val typed = INST_TYPE (match_type (type_of dv) (type_of actualDF)) th;
       val dv = valOf (List.find (fn v => fst (dest_var v) = "DF") (free_vars (concl typed)));
       val provider = INST [dv |-> actualDF] typed;
     in mp_tac (Q.INST [`addr` |-> `1w`,`an` |-> `128w`,`rn` |-> `32w`,
       `src` |-> `qi`,`dst` |-> `qo`,`id` |-> `cz.cs_next_id`,
       `s` |-> `sbuf`,`v` |-> `vcall`,`G` |-> `Gbuf`,`tn` |-> `tnbuf`,
       `G2` |-> `Gcall`,`tn2` |-> `tncall`,`trace` |-> `mid.storage_trace`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] provider) end) >>
  (impl_tac >-
    (simp[Abbr `gi`,Abbr `ci`,Abbr `ai`,Abbr `Gcall`,Abbr `tncall`,
       wordsTheory.dimword_def] >> gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       ghost_inv_at _ _ _ _ _ _ Gbuf tnbuf sbuf /\ _`
       (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (strip_assume_tac o MATCH_MP th)) >> simp[])) >>
  disch_then (qx_choose_then `tabort` (qx_choose_then `Ga`
    (qx_choose_then `tna` strip_assume_tac))) >>
  `!H:(bool # 256 word # type_value) list # num list.
     valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (sarg,G1,tn1) [F] (Abort Revert_abort tabort,Ga,tna)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_origin_ptr_path _ (sbuf,Gbuf,tnbuf) [F] _`
       (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
         (assume_tac o MATCH_MP th)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (sarg,G1,tn1) [] _`
       (fn prefix => qpat_assum `gas_origin_ptr_path (DF H,_,_,_,_,_) (sbuf,Gbuf,tnbuf) [F] _`
         (fn call => let
            val args = snd (strip_comb (concl call));
            val actualD = fst (pairSyntax.dest_pair (hd args));
            val left = SPEC actualD prefix;
            val st = pairSyntax.strip_pair (List.nth (args,1));
            val out = pairSyntax.strip_pair (List.nth (args,3));
            val th = SPECL (st @ [List.nth (args,2)] @ out)
              (MATCH_MP gas_origin_ptr_path_append left);
            val endpoint = List.nth (snd (strip_comb (concl left)),3);
            val total = MATCH_MP th (CONJ (REFL endpoint) call);
          in ACCEPT_TAC (SIMP_RULE (srw_ss()) [APPEND] total) end))) >>
  (fn (asl,goal) => let
     val actualSource = List.nth (snd (strip_comb goal),4);
     val th = gas_outcome_full_intro;
     val sv = valOf (List.find (fn v => fst (dest_var v) = "source") (free_vars (concl th)));
     val typed = INST_TYPE (match_type (type_of sv) (type_of actualSource)) th;
     val sv = valOf (List.find (fn v => fst (dest_var v) = "source") (free_vars (concl typed)));
     val provider = INST [sv |-> actualSource] typed;
   in MATCH_MP_TAC (Q.INST [`marks` |-> `[F]`,
     `res` |-> `INR (Error (RuntimeError "precompile failed"))`,
     `ee` |-> `mid with outcomes := SOME (DROP 1 sbuf.vs_outcomes)`,
     `r` |-> `Abort Revert_abort tabort`,`G'` |-> `Ga`,`tn'` |-> `tna`]
     provider) (asl,goal) end) >>
  conj_tac
  >- (gen_tac >>
      qpat_assum `builtin_result cx mid.accounts _ _ _ vals = _`
        (fn result => qpat_assum `mid.outcomes = SOME sbuf.vs_outcomes`
          (fn outcomes => qpat_assum `~?co rest. sbuf.vs_outcomes = co::rest /\ co.co_success`
            (fn neg => POP_ASSUM_LIST (K all_tac) >>
              MAP_EVERY assume_tac [result,outcomes,neg]))) >>
      Cases_on `sbuf.vs_outcomes` >> gvs[] >> Cases_on `sarg.vs_gas_readings` >>
      simp[gas_explicit_def,
        SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`] gasOracleReplayTheory.gas_prefix_suc),
        ZIP,MAP,FILTER,ignore_bind_def,bind_def,return_def,ecrecover_source_outcome_step,
        evaluation_state_component_equality]) >>
  conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  gen_tac >> simp[NoAsms] >> DISCH_TAC >> conj_tac
  >- (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path _ (sarg,G1,tn1) [F] (Abort Revert_abort tabort,Ga,tna)`
        (fn th => qpat_assum `valid_horizon cx st0 H mid.storage_trace`
          (ACCEPT_TAC o MATCH_MP th))) >>
  simp[NoAsms,exit_result_def,expr_exit_def]
QED

Theorem ecrecover_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a args es.
    (builtin_args_length_ok ECRecover (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a ECRecover args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a ECRecover args) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a ECRecover args) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a ECRecover args) es` by
    (MATCH_MP_TAC (Q.SPECL [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`tops`,
       `func`,`shadow_func`,`cenv`,`env`,`cx`,`ty`,`a`,`args`,`es`]
       ecrecover_expr_sim_full) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule ecrecover_pre_types >> strip_tac >>
  irule expr_vv_sim_stack_full >>
  simp[vyperASTTheory.expr_type_def,is_word_type_def] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty (Builtin a ECRecover args) sa` >>
      drule_all compile_ecrecover_stack >> simp[] >> metis_tac[]) >>
  metis_tac[eval_expr_builtin_value]
QED
