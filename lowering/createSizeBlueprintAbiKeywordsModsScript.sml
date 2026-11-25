Theory createSizeBlueprintAbiKeywordsMods
Ancestors
  createSizeBlueprintAbiKeywords createExprSizeExitDefsMods
  bodySingletonCallSupport[qualified,ignore_grammar]
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr
  gasExplicitSites gasSummary venomExecSemantics venomInst venomState vyperCreate vyperState
  relation list words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering
  stmtLoweringMono vfmConstants compileEnv exprLoweringProps fragFuel exprBodyPreProps
  vyperStorageTrace freshWrites rich_list exprSimHypsDefs bodyPtrDefs loweringPosts context
  bodyInvCodeProps vyperAST vyperStorageFootprint vyperTypeCallGraph integer_word
  createCtorSegmentArrival bodyFullExtCallPosAggregate bodyFullHashKeccakFixed
  loweringStateRelDefs ptrDiscipline createCtorObservedSilence createCtorPayloadLengthMods
  bodyFullExtCallDirectState bodyPtrMakeArrayEmission bodySim loweringShapeDefs
  createExprSizeExitDefs createSizePrefixReplay createSizeBlueprintKeywordReplay
  createSizeRawReplay createSizeCtorValueRow createSizeObservedPrefix createSizeRawEncoderReplay
  createCtorRowCutsMods createSizeBlueprintAbiEmptyMods createSizeBlueprintAbiObservedCutsMods
  createSizeBlueprintAbiReplayCutsMods createCtorSnapshotTypingMods exprReasonOperand

Theorem create_blueprint_abi_keyword_entry_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order (CreateFromBlueprint F) hs args) /\
  (!i s vs s'. i < LENGTH ctors /\ ~exprs_can_mutate ce (DROP (SUC i) ctors) /\
    eval_exprs cx (DROP (SUC i) ctors) s = (INL vs,s') ==>
    s'.immutables = s.immutables /\
    !tr. get_storage cx s' tr = get_storage cx s tr) /\
  MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  eval_operand target_op (St 0) = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at (C 0) x) /\
  local_ptrs_reserved ce (C 0) /\ (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  return_buf_frame d ce (C 0) (St 0) /\ alloca_history func (St 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\
    immutable_frame_mods func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  expr_sim_inv_mods mods ce cx env p0 /\ ~(St 0).vs_halted /\
  (St 0).vs_current_bb = (C 0).cs_current_bb /\ (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  LENGTH svs = LENGTH ctors /\
  se = C (LENGTH ctors) /\ s = St (LENGTH ctors) /\
  compile_create_ctor_args compile_expr ce ctors (C 0) = (svs,se) /\
  compile_create_blueprint_args compile_expr ce F later ctors (C 0) = ((data,len),en) /\
  (!i. i < LENGTH ctors ==>
    compile_expr ce (expr_type (EL i ctors)) (EL i ctors) (C i) = (V i,M i) /\
    compile_expr (gas_shadow_env T ce) (expr_type (EL i ctors)) (gas_shadow_expr (EL i ctors)) (Sh i) = (V i,SM i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
      (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
    create_expr_prefix (C i) (M i) (gas_explicit_sites ctx shctx) ctx func
      (St i) (Chunk i) (Mid i) /\
    (Mid i).vs_current_bb = (M i).cs_current_bb /\
    (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
    create_expr_prefix (M i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
      (Mid i) (Snap i) (St (SUC i)) /\
    fn_has_code (M i) (C (SUC i)) func /\ ci_mono (C 0) (C i) /\
    (is_word_type (lowered_value_type ce (EL i ctors)) ==>
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
        (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (SM i) =
        (EL i svs,Sh (SUC i)) /\
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i ctors)) ==>
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i))) /\
  (ctors = [] ==> t = St 0 /\ R 0 = rest) /\
  (ctors <> [] ==>
    capacity = abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors)) /\
    capacity < dimword (:256) /\
    compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
    su.vs_current_bb = a.cs_current_bb /\ su.vs_inst_idx = LENGTH a.cs_current_insts /\
    create_expr_prefix se a (gas_explicit_sites ctx shctx) ctx func s am su /\
    compile_abi_encode_values_to_buf ce buf.buf_operand (ZIP (svs,MAP (lowered_value_type ce) ctors))
      a = (len,en) /\ fn_has_code a en func /\
    create_expr_prefix a en (gas_explicit_sites ctx shctx) ctx func su encmarks t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    R (LENGTH ctors) = am ++ encmarks ++ rest /\
    c 0 = en /\ r 0 = t /\ r n = bad /\
    (!k. k < n ==> (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
      create_expr_prefix (c k) (c (SUC k)) (gas_explicit_sites ctx shctx) ctx func
        (r k) (chunk k) (r (SUC k))) /\
    lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
    get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
    ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;offop;sz]) \/
     (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;offop;sz;salto])) /\
    eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) /\
  bind (eval_exprs cx (ctors ++ later))
    (\vs. eval_create_operands cx (CreateFromBlueprint F) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?cvs p G tn.
    LENGTH cvs = LENGTH ctors /\ eval_exprs cx ctors p0 = (INL cvs,p) /\
    bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) p = (res,out) /\
    valid_horizon cx st0 H p.storage_trace /\
    (?bs. encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs /\
      eval_operand len t = SOME (n2w (LENGTH bs))) /\
    (!x. len = Var x ==> not_fresh_at en x) /\
    eval_operand target_op t = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at en x) /\
    expr_sim_inv_mods mods ce cx env p /\ local_ptrs_reserved ce en /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    return_buf_frame d ce en t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    (!K. valid_horizon cx st0 K p.storage_trace ==>
      stmt_state_rel K ctx func ce cx p t /\
      immutable_frame_mods func ce cx p t /\ storage_well_formed_on cx p (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx p G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    p.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `ctors = []` >- suspend "empty" >>
  qpat_x_assum `ctors <> [] ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  mp_tac blueprint_abi_observed_ctor_cuts_mods >>
  (impl_tac >- (asm_rewrite_tac [] >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `k = \vs. bind (eval_exprs cx later)
    (\ws. eval_create_operands cx (CreateFromBlueprint F) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(vs ++ ws)))` >>
  `bind (eval_exprs cx ctors) k p0 = (res,out)` by
    (qpat_assum `bind (eval_exprs cx (ctors ++ later)) _ _ = _`
       (mp_tac o PURE_REWRITE_RULE[blueprint_abi_bind_append]) >>
     simp[Abbr `k`]) >>
  `!vs. storage_trace_frame (k vs)` by
    simp[Abbr `k`,evaluate_storage_trace_frame,storage_trace_frame_bind_all,
         storage_trace_frame_create_operands] >>
  mp_tac (INST_TYPE [alpha |-> ``:eval_result``] blueprint_abi_replay_ctor_cuts_mods) >>
  (impl_tac >- suspend "replay") >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`cvs`,`E`,`gf`,`tf`] (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  suspend "payload"
QED

Resume create_blueprint_abi_keyword_entry_mods[empty]:
  disj2_tac >>
  qpat_assum `ctors = [] ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `ctors = []` SUBST_ALL_TAC >>
  mp_tac create_blueprint_abi_empty_keyword_entry_mods >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac (srw_ss()) []
QED

Resume create_blueprint_abi_keyword_entry_mods[replay]:
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!i s vs s'. _ ==> s'.immutables = _ /\ _`
        (qspecl_then [`i`,`s'`,`vs`,`s''`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> ?j. _`
    (qspec_then `SUC i` mp_tac) >>
  impl_tac >- decide_tac >> simp[]
QED

Resume create_blueprint_abi_keyword_entry_mods[payload]:
  qabbrev_tac `ee = E (LENGTH ctors)` >>
  `EVERY (source_body_call_supported cx) (int_calls_exprs ctors)` by suspend "calls" >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ p0`
       (strip_assume_tac o REWRITE_RULE[expr_sim_inv_mods_def]) >> first_assum ACCEPT_TAC) >>
  `ci_mono (C 0) en` by metis_tac[ci_mono_trans] >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at se x /\ not_fresh_at en x` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  mp_tac (create_ctor_payload_length_mods |>
    Q.INST [`raw` |-> `F`] |>
    PURE_REWRITE_RULE[COND_CLAUSES,AND_CLAUSES,IMP_CLAUSES,NOT_CLAUSES,ADD_CLAUSES] |>
    Q.INST [`args` |-> `ctors`, `vs` |-> `cvs`,
            `module_src` |-> `src`, `alen` |-> `len`,
            `explicit` |-> `gas_explicit_sites ctx shctx`,
            `st` |-> `a`, `dst_op` |-> `buf.buf_operand`, `u` |-> `su`,
            `off` |-> `offop`, `salt` |-> `salto`]) >>
  (impl_tac >- suspend "producer_pre") >>
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >>
  disch_then strip_assume_tac >>
  suspend "finish"
QED

Resume create_blueprint_abi_keyword_entry_mods[calls]:
  qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) entry`
    (strip_assume_tac o REWRITE_RULE[expr_body_pre_mods_def]) >>
  qpat_x_assum `EVERY (source_body_call_supported cx) _` mp_tac >>
  Cases_on `hs` >> simp[int_calls_expr_def,EVERY_APPEND]
QED

Resume create_blueprint_abi_keyword_entry_mods[producer_pre]:
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >>
  pure_rewrite_tac[GSYM raw_encoder_prefix_rtc] >>
  `local_ptrs_reserved ce se` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by simp[] >>
  `compile_create_ctor_args compile_expr ce ctors (C 0) = (svs,C (LENGTH ctors))` by fs[] >>
  asm_rewrite_tac[PAIR_EQ,REFL_CLAUSE] >> conj_tac >- suspend "suffix_frame" >>
  conj_tac >- (qexists_tac `H` >> simp[Abbr `ee`]) >>
  conj_tac >- suspend "producer_row" >>
  conj_tac >- (rpt strip_tac >> qpat_assum `!K. valid_horizon _ _ K p0.storage_trace ==> _`
                (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "producer_callback" >>
  simp[Abbr `ee`]
QED

Resume create_blueprint_abi_keyword_entry_mods[suffix_frame]:
  `!i. i < LENGTH ctors ==>
     bind (eval_expr cx (EL i ctors)) (read_result cx) (E i) = (INL (EL i cvs),E (SUC i))` by
    (rpt strip_tac >> qpat_assum `!i. i < LENGTH ctors ==> monad_bind _ _ _ = _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`args` |-> `ctors`, `vs` |-> `cvs`] ctor_rows_source_mods) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  strip_tac >> qx_gen_tac `i` >> strip_tac >>
  `SUC i <= LENGTH ctors` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> eval_exprs _ _ _ = _`
    (qspec_then `SUC i` (drule_then assume_tac)) >>
  qpat_assum `!i s vs s'. _ ==> s'.immutables = _ /\ _`
    (qspecl_then [`i`,`E (SUC i)`,`DROP (SUC i) cvs`,`E (LENGTH ctors)`] mp_tac) >>
  simp[]
QED

Resume create_blueprint_abi_keyword_entry_mods[producer_row]:
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!i. i < LENGTH ctors ==> monad_bind _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at (C i) x` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `local_ptrs_reserved ce (C i)` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `i <= LENGTH ctors /\ SUC i <= LENGTH ctors` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `SUC i` (drule_then strip_assume_tac)) >>
  `(St (SUC i)).vs_labels = (St i).vs_labels` by
    (drule_then assume_tac create_prefix_labels >>
     qpat_assum `create_expr_prefix (C i) (M i) _ _ _ _ _ _`
       (mp_tac o MATCH_MP create_prefix_labels) >> simp[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (rpt strip_tac >> first_x_assum drule >> simp[] >> NO_TAC) >>
  disch_tac >> Cases_on `exprs_can_mutate ce (DROP (SUC i) ctors)` >> asm_rewrite_tac[]
  >- (conj_tac
      >- (irule raw_observed_prefix_live >>
          qexistsl_tac [`C i`,`M i`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`Chunk i`,`St i`] >>
          rpt conj_tac >> (simp[])) >>
      conj_tac
      >- (qpat_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _`
          (mp_tac o MATCH_MP blueprint_ctor_segment_rtc) >> simp[PAIR_EQ]) >>
      qpat_assum `!i. i <= LENGTH ctors ==> ?j. _`
        (qspec_then `SUC i` (drule_then ACCEPT_TAC))) >>
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)))` by
    suspend "snapshot_nonword" >>
  `C (SUC i) = M i` by
    (qpat_assum `compile_snapshot_vv _ _ _ (M i) = _`
       (mp_tac o PURE_REWRITE_RULE[compile_snapshot_vv_def]) >> simp[comp_return_def]) >>
  qpat_x_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _` mp_tac >>
  simp[] >> metis_tac[create_prefix_empty]
QED

Resume create_blueprint_abi_keyword_entry_mods[snapshot_nonword]:
  qabbrev_tac `e = EL i ctors` >>
  qpat_assum `expr_body_pre_mods _ _ _ _ e _`
    (strip_assume_tac o MATCH_MP ctor_snapshot_word_types_mods) >>
  `~is_word_type (expr_type e)` by
    (qpat_assum `is_word_type (lowered_value_type ce e) <=> _`
       (pure_once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ e _`
    (assume_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ p0`
    (strip_assume_tac o REWRITE_RULE[expr_sim_inv_mods_def]) >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `reason_uniform_shape _ _ _ _`
    (qx_choosel_then [`loc`,`ty`] (map_every assume_tac o CONJUNCTS) o
     REWRITE_RULE[reason_uniform_shape_def]) >>
  qpat_x_assum `!sa vv sb. compile_expr _ _ _ _ = _ ==> _`
    (drule_then (mk_asm "result_shape")) >>
  Cases_on `V i` >> asm_x "result_shape" mp_tac >>
  simp[reason_result_shape_def,ext_call_arg_value_def,vv_type_def] >>
  qpat_x_assum `ty = expr_type e \/ _` strip_assume_tac >> simp[]
QED

Resume create_blueprint_abi_keyword_entry_mods[producer_callback]:
  map_every qx_gen_tac [`i`,`g`,`h`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i. i < LENGTH ctors ==> monad_bind _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (mp_tac o List.last o CONJUNCTS))) >>
  disch_then (qspecl_then [`g`,`h`] (drule_then ACCEPT_TAC))
QED

Resume create_blueprint_abi_keyword_entry_mods[finish]:
  qhdtm_assum `abi_encode_saved_state_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_state_mods_def]) >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `ARB` (map_every assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (su,_,_) [] (OK t,geout,teout)` >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `LENGTH ctors` (strip_assume_tac o SIMP_RULE bool_ss [LESS_EQ_REFL])) >>
  `!f inst z. frag_reachable ctx func s f inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `s = St _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `!f inst z. frag_reachable ctx func su f inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s,_,_) [] (OK su,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >> asm_rewrite_tac[]) >>
  `!f inst z. frag_reachable ctx func t f inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (su,_,_) [] (OK t,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >> asm_rewrite_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `t.vs_labels = (St 0).vs_labels` by suspend "exit_labels" >>
  `eval_operand target_op t = SOME aw` by
    (irule blueprint_eval_operand_frame >> qexistsl_tac [`C 0`,`St 0`] >>
     asm_rewrite_tac[] >>
     qpat_assum `wb_frame ce (E 0) ee (C 0) (St 0) t`
       (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >> first_assum ACCEPT_TAC) >>
  `ee.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail` by suspend "exit_gas" >>
  `local_ptrs_reserved ce en` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  disj2_tac >> qexistsl_tac [`cvs`,`ee`,`geout`,`teout`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (qpat_x_assum `k cvs ee = _` mp_tac >> simp[Abbr `k`]) >>
  conj_tac >- (qexists_tac `bytes` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume create_blueprint_abi_keyword_entry_mods[exit_labels]:
  `!i. i <= LENGTH ctors ==> (St i).vs_labels = (St 0).vs_labels` by
    (Induct >> simp_tac (srw_ss()) [] >> disch_tac >>
     `i < LENGTH ctors` by
       (pure_rewrite_tac[LESS_EQ] >> first_assum ACCEPT_TAC) >>
     `i <= LENGTH ctors` by simp[LESS_IMP_LESS_OR_EQ] >>
     qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     qpat_assum `create_expr_prefix (C i) (M i) _ _ _ _ _ _`
       (assume_tac o MATCH_MP create_prefix_labels) >>
     qpat_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _`
       (assume_tac o MATCH_MP create_prefix_labels) >> simp[]) >>
  qpat_assum `create_expr_prefix se a _ _ _ s _ su`
    (assume_tac o MATCH_MP create_prefix_labels) >>
  qpat_assum `create_expr_prefix a en _ _ _ su _ t`
    (assume_tac o MATCH_MP create_prefix_labels) >> simp[]
QED

Resume create_blueprint_abi_keyword_entry_mods[exit_gas]:
  qpat_assum `gas_origin_ptr_path _ (s,_,_) [] (OK su,_,_)`
    (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  qpat_assum `gas_origin_ptr_path _ (su,_,_) [] (OK t,_,_)`
    (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  `am = [] /\ encmarks = []` by simp[] >>
  qpat_assum `create_expr_prefix se a _ _ _ s _ su`
    (assume_tac o MATCH_MP create_prefix_readings) >>
  qpat_assum `create_expr_prefix a en _ _ _ su _ t`
    (assume_tac o MATCH_MP create_prefix_readings) >>
  simp[Abbr `ee`]
QED

Finalise create_blueprint_abi_keyword_entry_mods
