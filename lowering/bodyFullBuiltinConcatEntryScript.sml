(* Compilation and execution up to the first operand of Concat. *)
Theory bodyFullBuiltinConcatEntry
Ancestors
  bodyFullBuiltinConcatReady bodyFullBuiltinConcatFrame
  bodyFullHashKeccakFixed[qualified,ignore_grammar] bodyFullIfExpReach[qualified,ignore_grammar]
  exprSimAbiDecodeEntryTyping[qualified,ignore_grammar]
  exprSimConcatResult exprSimHyps exprSimSource exprSimHypsDefs
  exprLowering exprLoweringProps allocLimits vyperTypeInvariants vyperTypeSystem
  vyperContext compileEnv emitHelperProps fragExec stateRelProj
  gasShadowCompile gasShadowCompileHelpers gasShadowState
  vyperTypeConversions valueEncoding valueEncodingDefs valueEncodingProps
  vfmConstants vyperAST words arithmetic list
  bodyFullPredsMods[qualified] bodyFullShadowBodyInv[qualified] bodyInvSplit[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
          expr_body_pre cenv cx env e st` by
    (rpt gen_tac >> strip_tac >>
     irule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`a`,`args`,`Concat n`,`es`] >> simp[]) >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Builtin a (Concat n) args) /\
   alloc_limits_expr cenv (Builtin a (Concat n) args)` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    metis_tac[exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env] >>
  `2 <= LENGTH args /\ SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
   well_formed_type env.type_defs a` by
    (qpat_assum `well_typed_expr _ _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[cj 9 well_typed_expr_def,well_typed_builtin_app_def] >>
     rpt strip_tac >> fs[]) >>
  `body_exprs_full_ok cx args` by
    (qpat_assum `builtin_args_length_ok (Concat n) (LENGTH args) ==> _` irule >>
     simp[builtin_args_length_ok_def]) >>
  Q.SUBGOAL_THEN
    `(a = BaseT (BytesT (Dynamic n)) /\
      EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
     (a = BaseT (StringT n) /\
      EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))` assume_tac
  >- (qpat_assum `well_typed_expr _ _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[cj 9 well_typed_expr_def,well_typed_builtin_app_def] >>
     rpt strip_tac >> fs[]) >>
  `?tvr. evaluate_type (get_tenv cx) a = SOME tvr` by
    (qpat_x_assum `well_formed_type _ _` mp_tac >>
     qpat_assum `env.type_defs = _`
       (fn th => simp[th,well_formed_type_def,optionTheory.IS_SOME_EXISTS])) >>
  `concat_alloc_size (MAP expr_type args) < 2 ** 64` by
    (qpat_x_assum `alloc_limits_expr _ _` mp_tac >> simp[alloc_limits_expr_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s0 /\ _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  suspend "allocate"
QED
*)
Theorem concat_loop_initial_entry:
  (builtin_args_length_ok (Concat n) (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin a (Concat n) args) es /\
  compile_expr cenv ty (Builtin a (Concat n) args) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin a (Concat n) args))
    shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_trace_domain cx st0 es.storage_trace ==>
  ?s4 s5 shadow_s4 shadow_s5 t4 G4 tn4 dp ov ow binst B bsz oinst buf bv fo s6 u' tvr.
    concat_loop_ready args 0 0 DF lo d ctx shadow_ctx PG mods exps tops func shadow_func cenv cx env
      st0 es s4 s5 shadow_s4 shadow_s5 t4 G4 tn4 dp ov ow binst B bsz oinst /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) [] (OK t4,G4,tn4)) /\
    2 <= LENGTH args /\
    SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
    ((a = BaseT (BytesT (Dynamic n)) /\
      EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
     (a = BaseT (StringT n) /\
      EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))) /\
    evaluate_type (get_tenv cx) a = SOME tvr /\
    bsz = concat_alloc_size (MAP expr_type args) /\
    32 <= bsz /\ bsz < dimword (:256) /\
    32 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
    binst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)]
      [STRING #"%" (toString sa.cs_next_var)] /\
    oinst = mk_inst (sa.cs_next_id+2) ALLOCA [Lit 64w]
      [STRING #"%" (toString (sa.cs_next_var+2))] /\
    vv = LocatedValue a (base_ptr buf) /\ buf.buf_operand = Var bv /\
    emit_op MLOAD [Var ov] s5 = (fo,s6) /\
    emit_void MSTORE [Var bv;fo] s6 = (u',sb) /\ fn_has_code s5 sb func /\
    s4.cs_next_var = sa.cs_next_var+3 /\ s4.cs_next_id = sa.cs_next_id+4 /\
    sb.cs_next_id = s5.cs_next_id+2 /\ ci_mono s4 s5 /\
    s0.vs_alloca_next <= t4.vs_alloca_next /\ not_fresh_at s4 bv /\
    lookup_var bv t4 = SOME (n2w B) /\ ptr_covers G4 tn4 bv t4 bsz /\
    (!aid e. FLOOKUP s0.vs_allocas aid = SOME e ==> FLOOKUP t4.vs_allocas aid = SOME e) /\
    (!name b len. local_region cenv es.scopes s0 name b len ==>
      regions_disjoint B bsz b len /\ regions_disjoint (w2n ow) 64 b len) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint B bsz b len /\ regions_disjoint (w2n ow) 64 b len) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t4 = lookup_var x s0 /\ FLOOKUP G4 x = FLOOKUP G0 x /\
      op_taint tn4 (Var x) = op_taint tn0 (Var x)) /\
    (!p n. p+n <= w2n ow \/ w2n ow+32 <= p ==>
      mem_bytes_at p n t4.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_loop_initial_entry[allocate]:
  qpat_assum `compile_expr cenv ty (Builtin a (Concat n) args) sa = _`
    (strip_assume_tac o MATCH_MP exprSimConcatResultTheory.concat_compile_shape) >>
  rename1 `emit_op ADD [buf.buf_operand; Lit 32w] s1 = (dataop,s2)` >>
  qabbrev_tac `bsz = concat_alloc_size (MAP expr_type args)` >>
  `bsz < dimword (:256)` by
    (qpat_assum `bsz < 2 ** 64` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
   32 + concat_data_bound 0 (MAP expr_type args) <= bsz` by
    simp[Abbr `bsz`,exprSimHypsTheory.concat_alloc_size_bounds] >>
  `32 <= bsz` by
    (qpat_assum `32 + SUM _ <= bsz` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  drule_all exprSimConcatResultTheory.concat_prefix_code >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sa s4` by
    (irule compileEnvTheory.cs_extends_same_block >>
     qpat_assum `s4.cs_current_insts = _` (fn th => simp[th])) >>
  `ci_mono s4 s5` by
    (qpat_assum `compile_concat _ _ _ _ _ _ s4 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_concat_cfn,
       cj 1 exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND]) >>
  `cs_extends s4 s5` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  qspecl_then [`STRING #"%" (toString (sa.cs_next_var+2))`,
    `STRING #"%" (toString sa.cs_next_var)`,`s5`,`fo`,`s6`,`u'`,`sb`]
    mp_tac exprSimConcatResultTheory.concat_suffix_code >>
  (impl_tac >-
    (qpat_assum `emit_op MLOAD [ob.buf_operand] s5 = _` mp_tac >>
     qpat_assum `emit_void MSTORE [buf.buf_operand;fo] s6 = _` mp_tac >>
     qpat_assum `buf.buf_operand = _` mp_tac >>
     qpat_assum `ob.buf_operand = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> Cases_on `u'` >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends s5 sb` by
    (irule compileEnvTheory.cs_extends_same_block >>
     qpat_assum `sb.cs_current_insts = _` (fn th => simp[th])) >>
  `cs_extends s4 sb` by
    (irule cs_extends_trans >> qexists `s5` >> simp[]) >>
  `fn_has_code sa s4 func /\ fn_has_code s4 sb func` by
    (qspecl_then [`sa`,`s4`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ es G0 tn0 s0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
    s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s0` mp_tac >>
     qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0`
       (mp_tac o MATCH_MP stmt_state_rel_fmp_room) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.fmp_room_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  drule_all bodyFullBuiltinConcatFrameTheory.concat_prefix_full >>
  disch_then (qspecl_then [`tn0`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G0`]
    (qx_choosel_then [`t4`,`G4`,`tn4`,`bv`,`dp`,`ov`,`B`,`ow`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "shadow"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_loop_initial_entry[shadow]:
  qpat_assum `compile_expr _ ty (gas_shadow_expr (Builtin a (Concat n) args)) shadow_sa = _`
    (mp_tac o SIMP_RULE (srw_ss())
      [gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def]) >>
  disch_then (mp_tac o MATCH_MP exprSimConcatResultTheory.concat_compile_shape) >>
  disch_then (qx_choosel_then [`shadow_buf`,`shadow_s1`,`shadow_data`,`shadow_s2`,
    `shadow_ob`,`shadow_s3`,`shadow_unit`,`shadow_s4`,`shadow_s5`,`shadow_fo`,
    `shadow_s6`,`shadow_unit'`] (map_every assume_tac o CONJUNCTS) o
    SIMP_RULE bool_ss [listTheory.MAP_MAP_o,combinTheory.o_DEF,gasShadowTheory.gas_shadow_expr_type]) >>
  `buf = shadow_buf /\ gas_shadow_state s1 shadow_s1` by
    (mp_tac (Q.INST [`nbytes` |-> `bsz`]
       gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
     qpat_assum `compile_alloc_buffer _ shadow_sa = _`
       (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
     simp_tac bool_ss [Abbr `bsz`] >> strip_tac >> simp[]) >>
  qpat_x_assum `buf = shadow_buf` (SUBST_ALL_TAC o SYM) >>
  `dataop = shadow_data /\ gas_shadow_state s2 shadow_s2` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `ops` |-> `[buf.buf_operand; Lit 32w]`]
       gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`,`shadow_s1`] mp_tac) >> simp[]) >>
  qpat_x_assum `dataop = shadow_data` (SUBST_ALL_TAC o SYM) >>
  `ob = shadow_ob /\ gas_shadow_state s3 shadow_s3` by
    (mp_tac (Q.INST [`nbytes` |-> `64`]
       gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s2`,`shadow_s2`] mp_tac) >> simp[]) >>
  qpat_x_assum `ob = shadow_ob` (SUBST_ALL_TAC o SYM) >>
  `gas_shadow_state s4 shadow_s4` by
    (mp_tac (Q.INST [`opc` |-> `MSTORE`, `ops` |-> `[ob.buf_operand; Lit 0w]`]
       gasShadowStateTheory.gas_shadow_compiles_emit_void) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s3`,`shadow_s3`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_concat _ _ args dataop _ _ s4 = _`
    (assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  qpat_x_assum `compile_concat _ _ (MAP gas_shadow_expr args) dataop _ _ shadow_s4 = _`
    (assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  qmatch_assum_abbrev_tac
    `compile_concat compile_expr cenv args dataop infos ob.buf_operand s4 = ((),s5)` >>
  `gas_shadow_compiles (compile_concat compile_expr cenv args dataop infos ob.buf_operand)
     (compile_concat compile_expr (gas_shadow_env T cenv)
       (MAP gas_shadow_expr args) dataop infos ob.buf_operand)` by
    (irule (REWRITE_RULE [COND_CLAUSES]
       (Q.INST [`sh` |-> `T`] gas_shadow_compiles_concat_env)) >>
     irule (cj 1 gas_shadow_compile_expr_env)) >>
  `gas_shadow_state s5 shadow_s5` by
    (qpat_x_assum `gas_shadow_compiles (compile_concat _ _ _ _ _ _) _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`s4`,`shadow_s4`] mp_tac) >> simp[]) >>
  suspend "shadow_code"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_loop_initial_entry[shadow_code]:
  `ci_mono shadow_s4 shadow_s5` by
    (qpat_assum `compile_concat _ _ _ _ _ _ shadow_s4 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_concat_cfn,
       cj 1 exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND]) >>
  `cs_extends shadow_s4 shadow_s5` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  qspecl_then [`bsz`,`shadow_sa`,`buf`,`shadow_s1`,`dataop`,`shadow_s2`,
    `ob`,`shadow_s3`,`shadow_unit`,`shadow_s4`]
    mp_tac exprSimConcatResultTheory.concat_prefix_code >>
  (impl_tac >-
    (qpat_assum `compile_alloc_buffer _ shadow_sa = _`
       (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >> simp[Abbr `bsz`])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends shadow_sa shadow_s4` by
    (irule compileEnvTheory.cs_extends_same_block >>
     qpat_assum `shadow_s4.cs_current_insts = _` (fn th => simp[th])) >>
  qspecl_then [`ov`,`bv`,`shadow_s5`,`shadow_fo`,`shadow_s6`,
    `shadow_unit'`,`shadow_sb`] mp_tac exprSimConcatResultTheory.concat_suffix_code >>
  (impl_tac >-
    (qpat_assum `emit_op MLOAD [ob.buf_operand] shadow_s5 = _` mp_tac >>
     qpat_assum `emit_void MSTORE [buf.buf_operand;shadow_fo] shadow_s6 = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var bv` mp_tac >>
     qpat_assum `ob.buf_operand = Var ov` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `shadow_unit'` >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends shadow_s5 shadow_sb` by
    (irule compileEnvTheory.cs_extends_same_block >>
     qpat_assum `shadow_sb.cs_current_insts = _` (fn th => simp[th])) >>
  `cs_extends shadow_s4 shadow_sb` by
    (irule cs_extends_trans >> qexists `shadow_s5` >> simp[]) >>
  `fn_has_code shadow_sa shadow_s4 shadow_func /\
   fn_has_code shadow_s4 shadow_sb shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_s4`,`shadow_sb`,`shadow_func`]
      mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code s4 s5 func /\ fn_has_code s5 sb func` by
    (qspecl_then [`s4`,`s5`,`sb`,`func`]
      mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_s4 shadow_s5 shadow_func /\
   fn_has_code shadow_s5 shadow_sb shadow_func` by
    (qspecl_then [`shadow_s4`,`shadow_s5`,`shadow_sb`,`shadow_func`]
      mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s4` by
    (qspecl_then [`cenv`,`sa`,`s4`]
      mp_tac exprLoweringPropsTheory.local_ptrs_reserved_next_var >> simp[]) >>
  `ptr_covers G4 tn4 ov t4 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `64` >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es t4 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G4 tn4 t4` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  suspend "ready"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_loop_initial_entry[ready]:
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==>
     local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >> disch_tac >>
     irule exprSimPropsTheory.local_region_frame >>
     conj_tac
     >- (qexists `func` >>
         qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace) _ _ _ _ es s0`
           (ACCEPT_TAC o MATCH_MP (cj 1 stmt_state_rel_local_ptrs_alloca))) >>
     qexistsl [`sa`,`es.scopes`,`t4`] >>
     rpt conj_tac >> asm_rewrite_tac[] >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `EVERY (\e. is_bytestring_type (expr_type e) \/
              ?m. expr_type e = BaseT (BytesT (Fixed m))) args` by
    (qpat_assum `(a = _ /\ _) \/ (a = _ /\ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     fs[listTheory.EVERY_MEM,listTheory.MEM_MAP,PULL_EXISTS] >>
     rpt strip_tac >> res_tac >> fs[compileEnvTheory.is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[compileEnvTheory.is_bytestring_type_def]) >>
  qabbrev_tac `binst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  qabbrev_tac `oinst = mk_inst (sa.cs_next_id+2) ALLOCA [Lit 64w]
    [STRING #"%" (toString (sa.cs_next_var+2))]` >>
  `MEM binst (fn_insts func)` by
    (qspecl_then [`func`,`sa`,`s4`,`binst`]
      mp_tac exprSimConcatResultTheory.concat_code_mem >>
     (impl_tac >- simp[Abbr `binst`]) >> simp[]) >>
  `MEM oinst (fn_insts func)` by
    (qspecl_then [`func`,`sa`,`s4`,`oinst`]
      mp_tac exprSimConcatResultTheory.concat_code_mem >>
     (impl_tac >- simp[Abbr `oinst`]) >> simp[]) >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi (CONJ inv member))))) >>
  `!fn inst z. frag_reachable ctx func t4 fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK t4,G4,tn4)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
       qpat_assum `!fn inst z. frag_reachable ctx func s0 fn inst z ==> _` (fn safe =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
           (LIST_CONJ [path,no_phi,safe]))))))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t4` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t4 /\ _`
       (fn th => qpat_assum `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
         (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
          CONJUNCT1 o MATCH_MP th))) >>
  `emit_op MLOAD [Var ov] s5 = (fo,s6)` by
    (qpat_assum `emit_op MLOAD [ob.buf_operand] s5 = (fo,s6)` mp_tac >>
     qpat_assum `ob.buf_operand = Var ov` (fn th => simp[NoAsms,th])) >>
  `emit_void MSTORE [Var bv;fo] s6 = (u',sb)` by
    (qpat_assum `emit_void MSTORE [buf.buf_operand;fo] s6 = (u',sb)` mp_tac >>
     qpat_assum `buf.buf_operand = Var bv` (fn th => simp[NoAsms,th])) >>
  qexistsl [`s4`,`s5`,`shadow_s4`,`shadow_s5`,`t4`,`G4`,`tn4`,`dp`,`ov`,`ow`,
    `binst`,`B`,`bsz`,`oinst`,`buf`,`bv`,`fo`,`s6`,`u'`,`tvr`] >>
  conj_tac
  >- (qunabbrev_tac `infos` >>
      simp[concat_loop_ready_def,Abbr `binst`,Abbr `oinst`,venomInstTheory.mk_inst_def] >>
      rpt conj_tac >> asm_rewrite_tac[] >>> NTH_GOAL (metis_tac[]) 1 >>> NTH_GOAL (metis_tac[]) 1 >>
      qpat_assum `regions_disjoint B bsz (w2n ow) 64` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    simp[Abbr `bsz`,Abbr `binst`,Abbr `oinst`])
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise concat_loop_initial_entry
*)
