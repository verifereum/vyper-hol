(* Continue the actual linked ECRecover run after its four strict operands. *)
Theory bodyECRecoverSuffixMods
Ancestors
  bodyECRecoverCodeCutsMods bodyECRecoverLaunchMods bodyECRecoverPayloadMods
  bodyECRecoverEmptyExitMods bodyECRecoverAssertExitMods
  bodyECRecoverSuccessfulCallMods bodyECRecoverWriteFrameMods bodyECRecoverLoadMods
  bodyFullPostsMods exprSimFullBundleProps generatedGasOrigin gasShadowCompileContext
  gasOutcomeFullZeroPrefixMods gasOutcomeFullPostMods wordArgsPtr exprSimWordArgs
  stateRelProj bodyForRangeScalarFrameMods vyperCallOutcomeProps gasSummaryCompose
  exprSimMemDefs freshWrites compileEnv gasShadowState exprLoweringProps builtinMisc fragExec
  exprSimPrecompiles vyperStorageFootprint venomState venomInst loweringStateRelDefs
  bodyFullHashKeccakFixed bodyFullShadowBodyInv bodyPtrDefs ptrDiscipline
  gasSummary loweringPosts valueEncodingDefs list rich_list pred_set words pair option exprSimProps
  gasOutcomeFullMods vyperInterpreter
Libs
  monadsyntax

val recovery_action = ``\vs ee.
  case builtin_result cx ee.accounts (BaseT AddressT) ECRecover (MAP expr_type args) vs of
    INR exc => (INR exc,ee)
  | INL w => (do precompile_call_success ECRecover vs; return w od) ee``;

Theorem ecrecover_suffix_mods:
  well_typed_builtin_app (BaseT AddressT) ECRecover (MAP expr_type args) /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                       value_has_type tv v) args vals /\
  compile_ecrecover h v r sig sf = (op,sb) /\
  compile_ecrecover h v r sig shadow_sf = (op,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sf,sb,shadow_sf,shadow_sb) /\
  ci_mono sa sf /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sf sarg /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  (!tail. eval_exprs cx args (es with gas_obs :=
      gas_explicit marks s0.vs_gas_readings ++ tail) = (INL vals,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    typed_args_post H ctx func cenv cx es sa s0 mid args [h;v;r;sig] vals sarg /\
    immutable_frame_mods func cenv cx mid sarg /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn sarg) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!q. x = Var q ==> not_fresh_at sf q)) [h;v;r;sig] /\
  alloca_history func sarg /\ s0.vs_alloca_next <= sarg.vs_alloca_next /\
  ~sarg.vs_halted /\ sarg.vs_current_bb = sf.cs_current_bb /\
  sarg.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 ((^recovery_action) vals) (mid,sarg,G,tn)
    (\H res ee G' tn' t. ?w. res = INL w /\
      expr_post_mods H ctx func cenv cx (Builtin (BaseT AddressT) ECRecover args)
        es sa sb s0 ee w op t /\
      expr_store_bound cx (post_value_type cenv (Builtin (BaseT AddressT) ECRecover args)) w op t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
      ptr_val_ok cx (post_value_type cenv (Builtin (BaseT AddressT) ECRecover args)) w op G' tn' t /\
      (~is_word_type (post_value_type cenv (Builtin (BaseT AddressT) ECRecover args)) ==>
       ptr_buf_ok cenv (Builtin (BaseT AddressT) ECRecover args) op G' t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee gt rr. expr_exit res rr /\ halt_exit H cx ee res rr /\
      (ctx_has_dalloca ctx ==> !u. rr = Halt u ==> allocas_below_fmp u))
Proof
  BETA_TAC >> strip_tac >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  drule_all_then (qx_choosel_then [`ib`,`bi`,`b0`,`b1`,`b2`,`bp`,`ob`,`bo`,`bz`] strip_assume_tac o cj 1)
    ecrecover_code_cuts_mods >>
  suspend "derive_code"
QED

Resume ecrecover_suffix_mods[derive_code]:
  qabbrev_tac `buf_code = do ib <- compile_alloc_buffer 128;
    emit_void MSTORE [ib.buf_operand;h];
    (do dst <- emit_op ADD [ib.buf_operand;Lit 32w]; emit_void MSTORE [dst;v] od);
    (do dst <- emit_op ADD [ib.buf_operand;Lit 64w]; emit_void MSTORE [dst;r] od);
    (do dst <- emit_op ADD [ib.buf_operand;Lit 96w]; emit_void MSTORE [dst;sig] od);
    ob <- compile_alloc_buffer 32;
    emit_void MSTORE [ob.buf_operand;Lit 0w];
    comp_return (ib.buf_operand,ob.buf_operand) od` >>
  `buf_code sf = ((ib.buf_operand,ob.buf_operand),bz)` by
    simp[Abbr `buf_code`,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  `gas_shadow_compiles buf_code buf_code` by
    (qunabbrev_tac `buf_code` >> POP_ASSUM_LIST (K all_tac) >>
     simp[comp_ignore_bind_def] >>
     rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
          >- simp[gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer,
              gas_shadow_compiles_emit_op,gas_shadow_compiles_emit_void,
              gas_shadow_compiles_bind] >> gen_tac >> BETA_TAC) >>
     simp[gas_shadow_compiles_return]) >>
  `?shz. buf_code shadow_sf = ((ib.buf_operand,ob.buf_operand),shz) /\ gas_shadow_state bz shz` by
    (qpat_assum `gas_shadow_compiles buf_code buf_code`
       (mp_tac o Q.SPECL [`sf`,`shadow_sf`] o REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `buf_code shadow_sf` >> simp[] >> metis_tac[]) >>
  `!st. ci_mono st (SND (buf_code st))` by
    (qunabbrev_tac `buf_code` >> POP_ASSUM_LIST (K all_tac) >>
     gen_tac >> simp[comp_ignore_bind_def] >>
     rpt (match_mp_tac ci_mono_bind >> conj_tac
          >- simp[ci_mono_compile_alloc_buffer,ci_mono_emit_op,ci_mono_emit_void,ci_mono_bind] >>
          rpt gen_tac >> BETA_TAC) >> simp[ci_mono_comp_return]) >>
  `ci_mono sf bz /\ ci_mono shadow_sf shz` by
    (conj_tac >-
       (qpat_assum `!st. ci_mono st (SND (buf_code st))` (qspec_then `sf` mp_tac) >>
        qpat_assum `buf_code sf = _` (fn th => pure_rewrite_tac[th,pairTheory.SND] >> simp[])) >>
     qpat_assum `!st. ci_mono st (SND (buf_code st))` (qspec_then `shadow_sf` mp_tac) >>
     qpat_assum `buf_code shadow_sf = _` (fn th => pure_rewrite_tac[th,pairTheory.SND] >> simp[])) >>
  `compile_ecrecover h v r sig =
    (do bufs <- buf_code; gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas;Lit 1w;FST bufs;Lit 128w;SND bufs;Lit 32w];
        emit_void ASSERT [success]; emit_op MLOAD [SND bufs] od)` by
    (simp[Abbr `buf_code`,compile_ecrecover_def,comp_ignore_bind_def,comp_bind_assoc] >>
     simp[comp_bind_def,comp_return_def,FUN_EQ_THM]) >>
  suspend "call_code"
QED

Resume ecrecover_suffix_mods[call_code]:
  qabbrev_tac `code = \gas. do
    success <- emit_op STATICCALL [gas;Lit 1w;ib.buf_operand;Lit 128w;ob.buf_operand;Lit 32w];
    emit_void ASSERT [success]; emit_op MLOAD [ob.buf_operand] od` >>
  Cases_on `emit_op GAS [] bz` >> rename1 `emit_op GAS [] bz = (g,bg)` >>
  `?shg. emit_op GAS [] shz = (g,shg) /\ gas_shadow_state bg shg` by
    (mp_tac (Q.SPECL [`bz`,`shz`] (REWRITE_RULE [gas_shadow_compiles_def]
       (Q.INST [`opc` |-> `GAS`,`opc'` |-> `GAS`,`ops` |-> `[]`] gas_shadow_compiles_emit_op))) >>
     Cases_on `emit_op GAS [] shz` >> simp[] >> metis_tac[]) >>
  `code g bg = (op,sb) /\ code g shg = (op,shadow_sb)` by
    (qpat_assum `compile_ecrecover _ _ _ _ sf = _` mp_tac >>
     qpat_assum `compile_ecrecover _ _ _ _ shadow_sf = _` mp_tac >>
     qpat_assum `compile_ecrecover _ _ _ _ = _` (fn th => pure_rewrite_tac[th,comp_bind_def]) >>
     qpat_assum `buf_code sf = _` (fn th => pure_rewrite_tac[th,pairTheory.FST,pairTheory.SND]) >>
     qpat_assum `buf_code shadow_sf = _` (fn th => pure_rewrite_tac[th,pairTheory.FST,pairTheory.SND]) >>
     simp[Abbr `code`,comp_bind_def]) >>
  `!g st. ci_mono st (SND (code g st))` by
    (qunabbrev_tac `code` >> POP_ASSUM_LIST (K all_tac) >>
     rpt gen_tac >> simp[comp_ignore_bind_def] >>
     rpt (match_mp_tac ci_mono_bind >> conj_tac
          >- simp[ci_mono_emit_op,ci_mono_emit_void] >> rpt gen_tac >> BETA_TAC) >>
     simp[ci_mono_emit_op]) >>
  `ci_mono bg sb /\ ci_mono shg shadow_sb` by
    (qpat_assum `!g st. ci_mono st (SND (code g st))`
       (fn th => mp_tac (Q.SPECL [`g`,`bg`] th) >> mp_tac (Q.SPECL [`g`,`shg`] th)) >>
     qpat_assum `code g bg = _` (fn th => pure_rewrite_tac[th,pairTheory.SND]) >>
     qpat_assum `code g shg = _` (fn th => pure_rewrite_tac[th,pairTheory.SND]) >> simp[]) >>
  `ci_mono bz bg /\ ci_mono shz shg` by
    (mp_tac (Q.SPECL [`GAS`,`[]`,`bz`] ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`GAS`,`[]`,`shz`] ci_mono_emit_op) >> simp[]) >>
  `fn_has_code sf bz func /\ fn_has_code bz bg func /\ fn_has_code shz shg shadow_func` by
    (fs[ci_mono_def] >> rpt conj_tac >> irule fn_has_code_mid >>
     metis_tac[cs_extends_refl,cs_extends_trans]) >>
  suspend "launch"
QED

Resume ecrecover_suffix_mods[launch]:
  `sa.cs_next_var <= sf.cs_next_var /\ sa.cs_next_id <= sf.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sf` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sf x` by metis_tac[not_fresh_at_mono] >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sf x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sf x)` by metis_tac[] >>
  qabbrev_tac `Hc = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 Hc mid.storage_trace` by fs[storage_trace_domain_def,Abbr `Hc`] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid sarg /\ immutable_frame_mods func cenv cx mid sarg /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G tn sarg` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ sarg /\ _`
       (drule_then strip_assume_tac) >> fs[typed_args_post_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ sarg /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `typed_args_post Hc _ _ _ _ _ _ _ _ _ _ _ sarg`
    (strip_assume_tac o PURE_REWRITE_RULE [typed_args_post_def]) >>
  `?wh wv wr ws. eval_operand h sarg = SOME wh /\ eval_operand v sarg = SOME wv /\
     eval_operand r sarg = SOME wr /\ eval_operand sig sarg = SOME ws` by
    (qpat_assum `LIST_REL _ [h;v;r;sig] _`
       (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
     simp[LIST_REL_THM] >> rpt strip_tac >> metis_tac[]) >>
  rename1 `eval_operand h sarg = SOME wh` >>
  rename1 `eval_operand v sarg = SOME wv` >>
  rename1 `eval_operand r sarg = SOME wr` >>
  rename1 `eval_operand sig sarg = SOME ws` >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`] ecrecover_launch_mods) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`sbuf`,`Gb`,`tb`,`qi`,`qo`,`wi`,`wo`] strip_assume_tac)) >>
  suspend "call_ready"
QED

Resume ecrecover_suffix_mods[call_ready]:
  qpat_assum `ib.buf_operand = Var qi` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qpat_assum `ob.buf_operand = Var qo` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qabbrev_tac `call_code = do gas <- emit_op GAS [];
    success <- emit_op STATICCALL [gas;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w];
    emit_void ASSERT [success]; comp_return (Var qo) od` >>
  Cases_on `call_code bz` >> rename1 `call_code bz = (out,cq)` >>
  `out = Var qo` by
    (qpat_assum `call_code bz = _` mp_tac >> qunabbrev_tac `call_code` >>
     disch_then (mp_tac o MATCH_MP computed_suffix_shape) >> simp[]) >>
  `emit_op MLOAD [Var qo] cq = (op,sb)` by
    (qpat_assum `comp_bind _ _ bz = (op,sb)` mp_tac >>
     qpat_assum `call_code bz = _` mp_tac >> qunabbrev_tac `call_code` >>
     disch_then (fn th => pure_rewrite_tac[comp_bind_def,th]) >>
     qpat_assum `out = Var qo` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  `same_blocks bz cq` by
    (qpat_assum `call_code bz = _` mp_tac >> qunabbrev_tac `call_code` >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     metis_tac[same_blocks_trans]) >>
  `sf.cs_next_id <= bz.cs_next_id /\ sf.cs_next_var <= bz.cs_next_var` by fs[ci_mono_def] >>
  `cq.cs_current_insts = bz.cs_current_insts ++ emitted_insts bz cq` by
    (qpat_assum `call_code bz = _`
       (fn th => mp_tac th >> qunabbrev_tac `call_code` >>
        disch_then (mp_tac o MATCH_MP computed_suffix_shape)) >> simp[]) >>
  `cs_extends bz cq` by fs[same_blocks_def,cs_extends_def] >>
  `cs_extends cq sb` by
    (qpat_assum `emit_op MLOAD _ cq = _` mp_tac >>
     mp_tac (Q.SPECL [`MLOAD`,`[Var qo]`,`cq`] ci_mono_emit_op) >>
     simp[ci_mono_def] >> strip_tac >> simp[]) >>
  `fn_has_code bz cq func /\ fn_has_code cq sb func` by
    (fs[ci_mono_def] >> rpt conj_tac >> irule fn_has_code_mid >>
     metis_tac[cs_extends_refl,cs_extends_trans]) >>
  suspend "call_facts"
QED

Resume ecrecover_suffix_mods[call_facts]:
  qpat_assum `call_code bz = _`
    (fn th => mp_tac th >> qunabbrev_tac `call_code` >> strip_tac) >>
  drule computed_suffix_shape >> strip_tac >>
  qabbrev_tac `gv = STRING #"%" (toString bz.cs_next_var)` >>
  qabbrev_tac `cv = STRING #"%" (toString (bz.cs_next_var+1))` >>
  qabbrev_tac `gi = mk_inst bz.cs_next_id GAS [] [gv]` >>
  qabbrev_tac `ci = mk_inst (bz.cs_next_id+1) STATICCALL
    [Var gv;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w] [cv]` >>
  qabbrev_tac `ai = mk_inst (bz.cs_next_id+2) ASSERT [Var cv] []` >>
  `emitted_insts bz cq = [gi;ci;ai]` by simp[Abbr `gi`,Abbr `ci`,Abbr `ai`,Abbr `gv`,Abbr `cv`] >>
  `~not_fresh_at bz gv` by simp[Abbr `gv`,not_fresh_at_def] >>
  `qi <> gv /\ qo <> gv` by metis_tac[] >>
  `cq.cs_current_bb = bz.cs_current_bb` by fs[same_blocks_def] >>
  `?bb. lookup_block sbuf.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts bz cq) (DROP sbuf.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code bz cq func`
       (mp_tac o CONJUNCT2 o PURE_REWRITE_RULE [fn_has_code_def]) >>
     disch_then (qx_choose_then `blx` strip_assume_tac) >>
     qexists_tac `blx` >> conj_tac
     >- (qpat_assum `lookup_block cq.cs_current_bb _ = SOME blx` mp_tac >>
         qpat_assum `cq.cs_current_bb = bz.cs_current_bb` (fn th => pure_rewrite_tac [th]) >> simp[]) >>
     qpat_assum `isPREFIX cq.cs_current_insts blx.bb_instructions`
       (mp_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     strip_tac >>
     qpat_assum `blx.bb_instructions = _ ++ _` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `cq.cs_current_insts = _ ++ _` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `sbuf.vs_inst_idx = LENGTH _` (fn th => pure_rewrite_tac [th]) >>
     pure_rewrite_tac [GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >>
     simp[]) >>
  `(func.fn_name,bz.cs_next_id) NOTIN gas_explicit_sites ctx shadow_ctx` by
    (drule_all compile_generated_gas_origin_path >>
     disch_then (qspec_then `ARB` strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var qi) sbuf = SOME wi /\ eval_operand (Var qo) sbuf = SOME wo` by simp[eval_operand_def] >>
  `stmt_state_rel Hc ctx func cenv cx mid sbuf` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sbuf /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `mid.outcomes = SOME sbuf.vs_outcomes` by
    (qpat_assum `stmt_state_rel Hc _ _ _ _ _ sbuf`
       (mp_then Any mp_tac stmt_state_rel_state_rel) >> simp[state_rel_def]) >>
  `alloca_inv sbuf /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sbuf)` by
    (qpat_assum `stmt_state_rel Hc _ _ _ _ _ sbuf`
       (fn th => strip_assume_tac (MATCH_MP stmt_state_rel_local_ptrs_alloca th) >>
                 assume_tac (MATCH_MP stmt_state_rel_allocas_below_fmp th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) 0 d cenv cx mid Gb tb sbuf /\
    stmt_state_rel H ctx func cenv cx mid sbuf /\ local_ptrs_rel func cenv mid.scopes sbuf /\
    allocas_from lo sbuf /\
    tb.t_stor SUBSET (DF H).d_stor sbuf.vs_call_ctx.cc_address
      (sbuf.vs_accounts sbuf.vs_call_ctx.cc_address).storage /\
    tb.t_trans SUBSET (DF H).d_trans sbuf.vs_call_ctx.cc_address
      (sbuf.vs_transient sbuf.vs_call_ctx.cc_address)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sbuf /\ _`
       (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     qpat_assum `ghost_inv_at_mods (DF H) lo _ _ _ _ Gb tb sbuf`
       (strip_assume_tac o PURE_REWRITE_RULE [ghost_inv_at_mods_def,stor_taint_ok_at_def]) >>
     pure_rewrite_tac[ghost_inv_at_def,stor_taint_ok_at_def] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[allocas_from_def])) >>
  suspend "branch"
QED

Resume ecrecover_suffix_mods[branch]:
  drule_all (SIMP_RULE pure_ss [LET_THM] ecrecover_payload_mods) >>
  disch_then (qspec_then `mid.accounts` strip_assume_tac) >>
  qpat_assum `!su wi. mem_bytes_at _ _ _ = _ ==> _`
    (qspecl_then [`sbuf`,`wi`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ParentQ ParentR` >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`Gb`,`sbuf`,`tb`] >>
  conj_tac
  >- (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ (sarg,G,tn) [] _`
        (qspec_then `DF H` ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ptr_covers Gb tb qi sbuf 128 /\ ptr_covers Gb tb qo sbuf 32 /\
    (!i. w2n wi <= i /\ i < w2n wi + 128 ==> i NOTIN tb.t_mem) /\
    allocas_from lo sbuf /\
    tb.t_stor SUBSET (DF H).d_stor sbuf.vs_call_ctx.cc_address
      (sbuf.vs_accounts sbuf.vs_call_ctx.cc_address).storage /\
    tb.t_trans SUBSET (DF H).d_trans sbuf.vs_call_ctx.cc_address
      (sbuf.vs_transient sbuf.vs_call_ctx.cc_address)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ sbuf /\ _`
        (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qmatch_asmsub_rename_tac `isPREFIX (emitted_insts bz cq) (DROP sbuf.vs_inst_idx bx.bb_instructions)` >>
  `isPREFIX [gi;ci;ai] (DROP sbuf.vs_inst_idx bx.bb_instructions)` by
    (qpat_assum `isPREFIX (emitted_insts bz cq) _` mp_tac >>
     qpat_assum `emitted_insts bz cq = _` (fn th => pure_rewrite_tac [th]) >> simp[]) >>
  `isPREFIX [gi;ci] (DROP sbuf.vs_inst_idx bx.bb_instructions)` by
    (irule IS_PREFIX_TRANS >> qexists_tac `[gi;ci;ai]` >> simp[]) >>
  Cases_on `sbuf.vs_outcomes`
  >- suspend "empty" >>
  rename1 `sbuf.vs_outcomes = co::rest` >>
  Cases_on `co.co_success`
  >- suspend "success" >>
  suspend "failed"
QED

Resume ecrecover_suffix_mods[empty]:
  `gi = mk_inst bz.cs_next_id GAS [] [gv]` by simp[Abbr `gi`] >>
  `ci = mk_inst (bz.cs_next_id+1) STATICCALL
    [Var gv;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w] [cv]` by simp[Abbr `ci`] >>
  `mid.outcomes = SOME sbuf.vs_outcomes` by simp[] >>
  drule_all (BETA_RULE (SIMP_RULE pure_ss [LET_THM] ecrecover_empty_exit_mods)) >>
  disch_then (qspecl_then [`cenv.ce_modules`,`ParentQ`,`PG`] strip_assume_tac) >>
  qunabbrev_tac `ParentR` >> first_assum ACCEPT_TAC
QED

Resume ecrecover_suffix_mods[failed]:
  `gi = mk_inst bz.cs_next_id GAS [] [gv]` by simp[Abbr `gi`] >>
  `ci = mk_inst (bz.cs_next_id+1) STATICCALL
    [Var gv;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w] [cv]` by simp[Abbr `ci`] >>
  `ai = mk_inst (bz.cs_next_id+2) ASSERT [Var cv] []` by simp[Abbr `ai`] >>
  `mid.outcomes = SOME sbuf.vs_outcomes` by simp[] >>
  drule_all (BETA_RULE (SIMP_RULE pure_ss [LET_THM] ecrecover_assert_exit_mods)) >>
  disch_then (qspecl_then [`cenv.ce_modules`,`ParentQ`,`PG`] strip_assume_tac) >>
  qunabbrev_tac `ParentR` >> first_assum ACCEPT_TAC
QED

Resume ecrecover_suffix_mods[success]:
  `read_memory (w2n wi) 128 sbuf = precompile_input ECRecover vals` by
    simp[read_memory_def,GSYM mem_bytes_at_def] >>
  `!x. not_fresh_at sf x ==> not_fresh_at bz x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sf` >> simp[]) >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at bz x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at bz x)` by
    (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `return_buf_frame d cenv sf sbuf` by
    (Cases_on `d`
     >- (qpat_assum `return_buf_frame NONE cenv bz sbuf` mp_tac >>
         pure_rewrite_tac [return_buf_frame_def] >> simp[]) >>
     rename1 `return_buf_frame (SOME dm) cenv sf sbuf` >> PairCases_on `dm` >>
     qpat_assum `return_buf_frame (SOME _) cenv bz sbuf`
       (mp_tac o REWRITE_RULE [return_buf_frame_def]) >>
     disch_then (qx_choosel_then [`rv`,`rs`] strip_assume_tac) >>
     pure_rewrite_tac [return_buf_frame_def] >>
     qexistsl_tac [`rv`,`rs`] >> simp[]) >>
  `immutable_alloca_sep func cenv cx mid sbuf` by
    (qpat_assum `stmt_state_rel Hc _ _ _ _ _ sbuf`
       (strip_assume_tac o PURE_REWRITE_RULE [stmt_state_rel_def]) >> first_assum ACCEPT_TAC) >>
  `(cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wo) 32 off (type_memory_size tv))` by
    (strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `immutable_alloca_sep _ _ _ _ sbuf`
       (strip_assume_tac o PURE_REWRITE_RULE [immutable_alloca_sep_def]) >>
     first_x_assum (drule_all_then strip_assume_tac) >>
     qpat_assum `!inst b sz. MEM inst _ /\ _ ==> regions_disjoint _ _ b sz`
       (qspec_then `mk_inst bp.cs_next_id ALLOCA [Lit 32w] [qo]` mp_tac) >>
     simp[mk_inst_def,regions_disjoint_def] >> disch_then drule >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    ghost_inv_at (DF H) 0 d cenv cx mid Gb tb sbuf /\
    stmt_state_rel H ctx func cenv cx mid sbuf /\ local_ptrs_rel func cenv mid.scopes sbuf /\
    tb.t_stor SUBSET (DF H).d_stor sbuf.vs_call_ctx.cc_address
      (sbuf.vs_accounts sbuf.vs_call_ctx.cc_address).storage /\
    tb.t_trans SUBSET (DF H).d_trans sbuf.vs_call_ctx.cc_address
      (sbuf.vs_transient sbuf.vs_call_ctx.cc_address)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ _ _ sbuf /\ _`
        (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from lo sbuf` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> ptr_covers _ _ _ sbuf _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `(do gas <- emit_op GAS [];
        success <- emit_op STATICCALL [gas;Lit 1w;Var qi;Lit 128w;Var qo;Lit 32w];
        emit_void ASSERT [success]; comp_return (Var qo) od) bz = (Var qo,cq)` by
    (qpat_assum `(do gas <- emit_op GAS []; _ od) bz = (out,cq)` mp_tac >> simp[]) >>
  drule_all (Q.INST [`s` |-> `sbuf`,`es` |-> `mid`,`sm` |-> `bz`,`sb` |-> `cq`]
    (SIMP_RULE pure_ss [LET_THM] ecrecover_successful_call_physical_mods)) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`scall`,`Gc`,`tc`] strip_assume_tac)) >>
  qabbrev_tac `after = SND (take_call_outcome NONE 1w (precompile_input ECRecover vals) NONE mid)` >>
  suspend "restore_write"
QED

Resume ecrecover_suffix_mods[restore_write]:
  `after.scopes = mid.scopes /\ after.immutables = mid.immutables` by simp[Abbr `after`] >>
  `!i. i < lo /\ i IN tc.t_mem ==> i IN tb.t_mem` by
    (qpat_assum `tc.t_mem SUBSET tb.t_mem` (strip_assume_tac o REWRITE_RULE [SUBSET_DEF]) >> simp[]) >>
  `(cenv.ce_is_ctor ==> !src tops name tv iv off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP (cenv with ce_module := src).ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP after.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wo) 32 off (type_memory_size tv))` by
    (simp[] >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H after.storage_trace ==>
       stmt_state_rel H ctx func cenv cx after scall /\
       immutable_frame_mods func cenv cx after scall /\
       ghost_inv_at_mods (DF H) lo d cenv cx after Gc tc scall` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by
        (qpat_assum `valid_horizon _ _ H after.storage_trace` mp_tac >>
         qunabbrev_tac `after` >> pure_rewrite_tac [take_call_outcome_storage_observations] >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ [F] _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ sbuf /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     drule_all (Q.INST [`sa` |-> `bz`] ecrecover_write_frame_mods) >> simp[]) >>
  suspend "load"
QED

Resume ecrecover_suffix_mods[load]:
  `!x. not_fresh_at bz x ==> not_fresh_at cq x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `bz` >> simp[]) >>
  `local_ptrs_reserved cenv cq` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `bz` >> simp[]) >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at cq x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at cq x)` by
    (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `lookup_var qo scall = SOME wo` by
    (qpat_assum `eval_operand (Var qo) scall = SOME wo`
       (ACCEPT_TAC o REWRITE_RULE [eval_operand_def])) >>
  `w2n wo + 32 <= scall.vs_alloca_next` by simp[] >>
  `valid_horizon cx st0 Hc after.storage_trace` by simp[Abbr `after`] >>
  qpat_assum `!H. valid_horizon _ _ H after.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `alloca_inv scall /\ (ctx_has_dalloca ctx ==> allocas_below_fmp scall)` by
    (qpat_assum `stmt_state_rel Hc _ _ _ _ _ scall`
       (fn th => strip_assume_tac (MATCH_MP stmt_state_rel_local_ptrs_alloca th) >>
                 assume_tac (MATCH_MP stmt_state_rel_allocas_below_fmp th)) >> simp[]) >>
  `!H. valid_horizon cx st0 H after.storage_trace ==>
    stmt_state_rel H ctx func cenv cx after scall /\
    ghost_inv_at_mods (DF H) lo d cenv cx after Gc tc scall` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H after.storage_trace ==> _`
       (drule_then strip_assume_tac) >> conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `recov = vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws)` >>
  qabbrev_tac `rdata = case recov of NONE => [] | SOME x => PAD_LEFT 0w 32 (word_to_bytes x T)` >>
  `rdata = (case recov of NONE => [] | SOME x => PAD_LEFT 0w 32 (word_to_bytes x T))` by simp[Abbr `rdata`] >>
  drule_all (Q.INST [`s` |-> `scall`, `before` |-> `sbuf`] ecrecover_load_mods) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`sfin`,`Gf`,`tf`] strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H after.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (qunabbrev_tac `after` >> pure_rewrite_tac[take_call_outcome_storage_observations] >> simp[]) >>
  `storage_trace_domain cx st0 after.storage_trace` by
    simp[Abbr `after`,storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H after.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (sbuf,Gb,tb) [F] (OK sfin,Gf,tf)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ [F] _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (scall,Gc,tc) [] _` (qspec_then `DF H` assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (sbuf,Gb,tb) [F] _`
       (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >> simp[]) >>
  suspend "join_wb"
QED

Resume ecrecover_suffix_mods[join_wb]:
  `valid_horizon cx st0 Hc es.storage_trace` by
    (qpat_assum `!tail. eval_exprs cx args _ = _` (qspec_then `[]` assume_tac) >>
     `storage_trace_frame (eval_exprs cx args)` by simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[] >>
     strip_tac >> qpat_assum `valid_horizon cx st0 Hc mid.storage_trace` mp_tac >>
     asm_rewrite_tac[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  `stmt_state_rel Hc ctx func cenv cx es s0` by metis_tac[] >>
  `wb_frame cenv mid after sf sbuf scall` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ [F] _ /\ _`
       (drule_then strip_assume_tac) >>
     simp[Abbr `after`] >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv mid after sf sarg scall` by
    (qpat_assum `stmt_state_rel Hc _ _ _ _ mid sarg` (mp_then Any irule wb_frame_trans) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`mid`,`sf`,`sbuf`] >> simp[]) >>
  `wb_frame cenv mid after sf sarg sfin` by
    (qpat_assum `wb_frame cenv mid after sf sarg scall`
       (mp_then Any irule wb_frame_readonly_tail) >>
     conj_tac >- (qpat_assum `sfin.vs_allocas = scall.vs_allocas` (fn th => PURE_REWRITE_TAC[th]) >> simp[]) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `cq` >> reverse conj_tac
     >- (qpat_assum `cq.cs_next_var = _` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `sf.cs_next_var <= bz.cs_next_var` mp_tac >> decide_tac) >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at cq x ==> lookup_var x sfin = _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `wb_frame cenv es after sa s0 sfin` by
    (qpat_assum `stmt_state_rel Hc _ _ _ _ es s0` (mp_then Any irule wb_frame_trans) >>
     conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`mid`,`sf`,`sarg`] >> simp[]) >>
  suspend "join_pure"
QED

Resume ecrecover_suffix_mods[join_pure]:
  `sf.cs_next_id <= bp.cs_next_id` by
    (`ci_mono sf bi` by (qspecl_then [`128`,`sf`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
     `ci_mono bi b0` by (qspecl_then [`MSTORE`,`[Var qi;h]`,`bi`] mp_tac ci_mono_emit_void >> simp[]) >>
     `!n x st. ci_mono st (SND ((do dst <- emit_op ADD [Var qi;Lit n]; emit_void MSTORE [dst;x] od) st))` by
       (rpt gen_tac >> irule ci_mono_bind >> simp[ci_mono_emit_op,ci_mono_emit_void]) >>
     `ci_mono b0 b1 /\ ci_mono b1 b2 /\ ci_mono b2 bp` by
       (qpat_assum `!n x st. ci_mono st _` (fn th =>
          qspecl_then [`32w`,`v`,`b0`] mp_tac th >>
          qspecl_then [`64w`,`r`,`b1`] mp_tac th >>
          qspecl_then [`96w`,`sig`,`b2`] mp_tac th) >>
        qpat_assum `(do dst <- emit_op ADD _; _ od) b0 = _` (fn th => PURE_REWRITE_TAC[th]) >>
        qpat_assum `(do dst <- emit_op ADD _; _ od) b1 = _` (fn th => PURE_REWRITE_TAC[th]) >>
        qpat_assum `(do dst <- emit_op ADD _; _ od) b2 = _` (fn th => PURE_REWRITE_TAC[th]) >> simp[]) >>
     `ci_mono sf bp` by metis_tac[ci_mono_trans] >>
     qpat_assum `ci_mono sf bp` (strip_assume_tac o PURE_REWRITE_RULE[ci_mono_def]) >>
     first_assum ACCEPT_TAC) >>
  `!name b len. local_region cenv mid.scopes sarg name b len ==> regions_disjoint (w2n wo) 32 b len` by
    (`!name entry p sz. lookup_scopes name mid.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> lookup_var p sbuf = lookup_var p sarg` by
       (rpt strip_tac >>
        `not_fresh_at sf p` by
          (irule exprOperandVarTheory.environment_var_not_fresh >> qexistsl_tac [`cenv`,`name`,`sz`] >> simp[]) >>
        qpat_assum `!x. not_fresh_at sf x ==> lookup_var x sbuf = _ /\ _`
          (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >> qpat_assum `!name b len. local_region cenv mid.scopes sbuf name b len ==> _` irule >>
     qexists_tac `name` >> drule local_region_lookup_cong >> disch_then (fn th => ASM_REWRITE_TAC[th])) >>
  `pure_frame cenv func mid sf sarg scall` by
    (irule (Q.INST [`s` |-> `sbuf`,`inst` |-> `mk_inst bp.cs_next_id ALLOCA [Lit 32w] [qo]`,
                    `bb` |-> `w2n (wo:bytes32)`,`bsz` |-> `32`] (SPEC_ALL pure_frame_buffer_tail)) >>
     qexistsl_tac [`bp`,`qo`,`sbuf`,`wo`] >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac
     >- (rpt strip_tac >> qpat_assum `!p n. regions_disjoint (w2n wo) 32 p n ==> _` irule >>
         qpat_assum `regions_disjoint off len (w2n wo) 32` mp_tac >>
         PURE_REWRITE_TAC[regions_disjoint_def] >> decide_tac) >>
     qpat_assum `scall.vs_allocas = sbuf.vs_allocas` (fn th => REWRITE_TAC[th]) >>
     qpat_assum `MEM (mk_inst bp.cs_next_id ALLOCA _ _) _` mp_tac >>
     simp[mk_inst_def]) >>
  `pure_frame cenv func mid sf sarg sfin` by
    (qpat_assum `pure_frame cenv func mid sf sarg scall` (mp_then Any irule pure_frame_mem_tail) >>
     conj_tac >- (qpat_assum `sfin.vs_allocas = scall.vs_allocas` (fn th => REWRITE_TAC[th])) >>
     first_assum ACCEPT_TAC) >>
  `~EXISTS expr_has_effect args ==> pure_frame cenv func es sa s0 sfin` by
    (strip_tac >> irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`mid`,`sf`,`sarg`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (rpt strip_tac >> qpat_assum `wb_frame cenv es mid sa s0 sarg` (mp_then Any irule wb_frame_vars) >> simp[])
     >- (rpt strip_tac >> qpat_assum `sfin.vs_allocas = scall.vs_allocas` (fn th => PURE_REWRITE_TAC[th]) >>
         qpat_assum `scall.vs_allocas = sbuf.vs_allocas` (fn th => PURE_REWRITE_TAC[th]) >>
         qpat_assum `!aid entry. FLOOKUP sarg.vs_allocas aid = SOME entry ==> _` (drule_then ACCEPT_TAC)) >>
     qpat_assum `~EXISTS expr_has_effect args ==> _` (drule_then ACCEPT_TAC)) >>
  suspend "join_kept"
QED

Resume ecrecover_suffix_mods[join_kept]:
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gb tb` by
    (qpat_assum `stmt_state_rel Hc _ _ _ _ es s0` (mp_then Any irule ghost_kept_at_wb_trans) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G`,`mid`,`mid`,`sarg`,`sf`,`tn`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gb tb`
       (mp_then Any irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix) >>
     reverse conj_tac
     >- (qpat_assum `tf.t_mem = tc.t_mem` (fn th => PURE_REWRITE_TAC[th]) >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     `not_fresh_at bz x` by
       (qpat_assum `!x. not_fresh_at sf x ==> not_fresh_at bz x` irule >>
        qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sf x` irule >> first_assum ACCEPT_TAC) >>
     `not_fresh_at cq x` by
       (qpat_assum `!x. not_fresh_at bz x ==> not_fresh_at cq x` irule >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at cq x ==> lookup_var x sfin = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at bz x ==> lookup_var x scall = _ /\ _` (drule_then strip_assume_tac) >>
     ASM_REWRITE_TAC[]) >>
  suspend "join_gas"
QED

Resume ecrecover_suffix_mods[join_gas]:
  qabbrev_tac `resv = AddressV (case recov of NONE => 0w | SOME x => x)` >>
  `builtin_result cx mid.accounts (BaseT AddressT) ECRecover (MAP expr_type args) vals = INL resv` by
    (qunabbrev_tac `resv` >> qunabbrev_tac `recov` >> first_assum ACCEPT_TAC) >>
  `gas_explicit [F] sbuf.vs_gas_readings = []` by
    (Cases_on `sbuf.vs_gas_readings` >> simp[gas_explicit_cons]) >>
  PURE_REWRITE_TAC[gas_outcome_full_mods_def] >>
  qexists_tac `[F]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL resv`,`after`,`OK sfin`,`Gf`,`tf`] >>
  conj_tac
  >- (gen_tac >> qpat_assum `gas_explicit [F] sbuf.vs_gas_readings = []` (fn th => PURE_REWRITE_TAC[th,APPEND]) >>
      qpat_assum `builtin_result cx mid.accounts _ _ _ vals = INL resv` (fn th => simp[th]) >>
      simp[vyperStateTheory.ignore_bind_def,vyperStateTheory.bind_def,vyperStateTheory.return_def,
           ecrecover_source_outcome_step,Abbr `after`]) >>
  conj_tac >- first_assum ACCEPT_TAC >> gen_tac >> strip_tac >>
  conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H after.storage_trace ==> gas_origin_ptr_path _ _ [F] _`
        (drule_then ACCEPT_TAC)) >>
  disj1_tac >> qexists_tac `sfin` >> REWRITE_TAC[] >>
  suspend "parent_post"
QED

Resume ecrecover_suffix_mods[parent_post]:
  qpat_assum `!H. valid_horizon _ _ H after.storage_trace ==> stmt_state_rel _ _ _ _ _ _ sfin /\ _`
    (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H after.storage_trace ==> valid_horizon _ _ H mid.storage_trace`
       (drule_then ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ sarg /\ _`
    (drule_then strip_assume_tac) >>
  `storage_well_formed_on cx (after with gas_obs := []) (FST H)` by
    (qpat_assum `storage_well_formed_on cx mid (FST H)` mp_tac >>
     POP_ASSUM_LIST (fn ls => MAP_EVERY assume_tac (List.filter (fn th => can (match_term ``Abbrev (after = _)``) (concl th)) ls)) >>
     simp[Abbr `after`,storage_well_formed_on_def,vyperStorageBackendTheory.get_storage_def,
       FORALL_BOOL]) >>
  `eval_operand op sfin = SOME (typed_val_to_w256 (BaseTV AddressT) resv)` by
    (qunabbrev_tac `resv` >>
     qpat_assum `expr_val_rel cx (BaseT AddressT) _ op sfin`
       (mp_tac o PURE_REWRITE_RULE[expr_val_rel_def]) >>
     simp[vyperValueTheory.evaluate_type_def,is_word_type_def]) >>
  `immutable_frame_mods func cenv cx (after with gas_obs := []) sfin` by
    (qpat_assum `immutable_frame_mods func cenv cx after sfin` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     PURE_REWRITE_TAC[immutable_frame_mods_def,bodyInvSplitTheory.immutables_rel_mods_def,
       bodyInvSplitTheory.immutable_alloca_sep_mods_def,immutables_rel_def,immutable_alloca_sep_def] >>
     pure_rewrite_tac[vyperStateTheory.evaluation_state_accfupds,LET_THM] >> disch_then ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (after with gas_obs := []) Gf tf sfin` by
    (qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx after Gf tf sfin` mp_tac >>
     PURE_REWRITE_TAC[ghost_inv_at_mods_def,vyperStateTheory.evaluation_state_accfupds] >>
     disch_then ACCEPT_TAC) >>
  qunabbrev_tac `ParentQ` >> BETA_TAC >> qexists_tac `resv` >> REWRITE_TAC[] >>
  conj_tac
  >- (rewrite_tac[expr_post_mods_def] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      irule expr_post_typed_stack_intro >>
      conj_tac >- REWRITE_TAC[vyperASTTheory.expr_type_def,is_word_type_def] >>
      conj_tac >- (qexists_tac `BaseTV AddressT` >>
        conj_tac >- first_assum ACCEPT_TAC >>
        POP_ASSUM_LIST (K all_tac) >> simp[vyperASTTheory.expr_type_def,vyperValueTheory.evaluate_type_def]) >>
      REWRITE_TAC[wb_frame_gas_obs,stmt_state_rel_gas_obs,expr_has_effect_thm] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `s0.vs_alloca_next <= sfin.vs_alloca_next` by
    (qpat_assum `sfin.vs_alloca_next = scall.vs_alloca_next` (fn th => PURE_REWRITE_TAC[th]) >>
     qpat_assum `scall.vs_alloca_next = sbuf.vs_alloca_next` (fn th => PURE_REWRITE_TAC[th]) >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `sarg.vs_alloca_next` >> ASM_REWRITE_TAC[]) >>
  qpat_assum `stmt_state_rel H _ _ _ _ after sfin`
    (mp_then Any assume_tac stmt_state_rel_allocas_below_fmp) >>
  simp[post_value_type_def,vyperASTTheory.expr_type_def,is_word_type_def,
    expr_store_bound_def,ptr_val_ok_def]
QED

Finalise ecrecover_suffix_mods
