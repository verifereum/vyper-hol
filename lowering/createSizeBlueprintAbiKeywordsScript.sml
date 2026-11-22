Theory createSizeBlueprintAbiKeywords
Ancestors
  bodySingletonCallSupport[qualified,ignore_grammar]
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr
  gasExplicitSites gasSummary venomExecSemantics venomInst venomState vyperCreate vyperState
  relation list words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering
  stmtLoweringMono vfmConstants compileEnv exprLoweringProps fragFuel exprBodyPreProps
  vyperStorageTrace freshWrites rich_list exprSimHypsDefs bodyPtrDefs loweringPosts context
  bodyInvCodeProps vyperAST vyperStorageFootprint vyperTypeCallGraph integer_word
  createCtorSegmentArrival bodyFullExtCallPosAggregate bodyFullHashKeccakFixed
  loweringStateRelDefs ptrDiscipline createCtorObservedSilence createCtorPayloadLength
  bodyFullExtCallDirectState bodyPtrMakeArrayEmission bodySim loweringShapeDefs
  createExprSizeExitDefs createSizePrefixReplay createSizeCopyReplay
  createSizeBlueprintKeywordReplay createSizeRawReplay createSizeBlueprintRawScalars
  createSizeCtorValueRow createSizeObservedPrefix createSizeRawObserved
  createSizeCtorRowsReplay createSizeRawEncoderReplay createSizeOperandPre

Theorem blueprint_abi_bind_append:
  !xs ys k.
    bind (eval_exprs cx (xs ++ ys)) k =
    bind (eval_exprs cx xs) (\vs. bind (eval_exprs cx ys) (\ws. k (vs ++ ws)))
Proof
  Induct >- simp[cj 49 vyperInterpreterTheory.evaluate_def,bind_return,ETA_AX] >>
  simp[create_copy_source_cons]
QED

Theorem blueprint_abi_fetch_back[local]:
  create_expr_prefix a b explicit ctx func s ms t /\
  a.cs_next_id <= b.cs_next_id /\
  (?j. ctor_segment_fetch func t = SOME j /\ b.cs_next_id <= j.inst_id) ==>
  ?j. ctor_segment_fetch func s = SOME j /\ a.cs_next_id <= j.inst_id
Proof
  simp[create_expr_prefix_marked] >> once_rewrite_tac[RTC_CASES1] >>
  simp[EXISTS_PROD,create_marked_edge_def,create_prefix_step_def,frag_ids_def] >>
  rpt strip_tac >> gvs[ctor_segment_fetch_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem blueprint_abi_rows_fetch[local]:
  !n i. i + n = N /\
    (?j. ctor_segment_fetch func (St N) = SOME j /\ (C N).cs_next_id <= j.inst_id) /\
    (!k. k < N ==> (C k).cs_next_id <= (M k).cs_next_id /\
      (M k).cs_next_id <= (C (SUC k)).cs_next_id /\
      create_expr_prefix (C k) (M k) explicit ctx func (St k) (Chunk k) (Mid k) /\
      create_expr_prefix (M k) (C (SUC k)) explicit ctx func (Mid k) (Snap k) (St (SUC k))) ==>
    ?j. ctor_segment_fetch func (St i) = SOME j /\ (C i).cs_next_id <= j.inst_id
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < N /\ SUC i + n = N` by decide_tac >>
  qpat_assum `!k. k < N ==> _` (qspec_then `i` (drule_then strip_assume_tac)) >>
  `?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ (C (SUC i)).cs_next_id <= j.inst_id`
    by (qpat_assum `!i. i + n = N /\ _ ==> _` (qspec_then `SUC i` mp_tac) >>
        simp_tac bool_ss [] >> metis_tac[]) >>
  metis_tac[blueprint_abi_fetch_back]
QED

Theorem blueprint_abi_silent_band[local]:
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_expr_prefix a b explicit ctx func s ms t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  gas_origin_path T explicit ctx func s [] (OK t) ==>
  ms = []
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  irule ctor_observed_cut_silent >>
  qexistsl [`ctx`,`(b.cs_current_bb,LENGTH b.cs_current_insts)`,`explicit`,`func`,`t`,`s`] >>
  simp[] >> qpat_x_assum `RTC _ _ _` mp_tac >> match_mp_tac RTC_MONOTONE >>
  simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,PULL_EXISTS]
QED

(* The nonraw payload's encoder is reached through the actual completed
   constructor rows. The final two prefixes are the allocation and encode
   bands, not part of any source operand. *)
Theorem create_blueprint_abi_keyword_entry:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint F) hs args) /\
  MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  eval_operand target_op (St 0) = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at (C 0) x) /\
  local_ptrs_reserved ce (C 0) /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  return_buf_frame d ce (C 0) (St 0) /\ alloca_history func (St 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  expr_sim_inv ce cx env p0 /\ ~(St 0).vs_halted /\
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
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
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
    expr_sim_inv ce cx env p /\ local_ptrs_reserved ce en /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    return_buf_frame d ce en t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    (!K. valid_horizon cx st0 K p.storage_trace ==>
      stmt_state_rel K ctx func ce cx p t /\ storage_well_formed_on cx p (FST K) /\
      ghost_inv_at (DF K) lo d ce cx p G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    p.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `k = \vs. bind (eval_exprs cx later)
    (\ws. eval_create_operands cx (CreateFromBlueprint F) hs rof
       (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(vs ++ ws)))` >>
  `bind (eval_exprs cx ctors) k p0 = (res,out)` by
    fs[Abbr `k`,blueprint_abi_bind_append] >>
  `!vs. storage_trace_frame (k vs)` by
    simp[Abbr `k`,blueprint_read_list_frame,evaluate_storage_trace_frame,
         storage_trace_frame_bind_all,storage_trace_frame_create_operands] >>
  Cases_on `ctors = []` >- suspend "empty" >>
  qpat_x_assum `ctors <> [] ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  suspend "nonempty"
QED

Resume create_blueprint_abi_keyword_entry[empty]:
  gvs[compile_create_blueprint_args_def,comp_return_def,cj 49 vyperInterpreterTheory.evaluate_def,bind_return] >>
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `k [] p0 = _` (mp_then Any irule vyperStorageFootprintTheory.valid_horizon_frame) >> simp[]) >>
  disj2_tac >> qexistsl [`p0`,`G0`,`tn0`] >>
  simp[encode_create_ctor_args_def,eval_operand_def,return_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_blueprint_abi_keyword_entry[nonempty]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!i. MEM i (fn_insts func) ==> i.inst_opcode <> PHI` by suspend "no_phi" >>
  `!i. i < LENGTH ctors ==> create_operand_completed_ok cx (EL i ctors)` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `hs` >> simp[create_operand_order_def,EVERY_APPEND] >>
     metis_tac[EVERY_MEM,EL_MEM]) >>
  `!i p. i < LENGTH ctors /\ expr_sim_inv ce cx env p ==>
         expr_body_pre ce cx env (EL i ctors) p` by
    (rpt strip_tac >> irule create_call_operand_body_pre >> simp[] >>
     qpat_assum `expr_body_pre ce cx env (Call _ _ _ _) entry` (irule_at Any) >>
     simp[MEM_APPEND,EL_MEM]) >>
  `ci_mono (C 0) se /\ ci_mono se a /\ ci_mono a en` by
    metis_tac[ci_mono_compile_create_ctor_args,ci_mono_compile_expr_sa,
      ci_mono_compile_alloc_buffer,ci_mono_compile_abi_encode_values_to_buf,SND] >>
  `!i. i < LENGTH ctors ==> (C i).cs_next_id <= (M i).cs_next_id /\
                          (M i).cs_next_id <= (C (SUC i)).cs_next_id` by
    (rpt strip_tac >> qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     metis_tac[ci_mono_compile_expr_sa,ci_mono_compile_snapshot_vv,ci_mono_def,SND]) >>
  `gas_origin_edge F (gas_explicit_sites ctx shctx) ctx func s am (OK su) /\
   (?j. ctor_segment_fetch func s = SOME j /\ se.cs_next_id <= j.inst_id)` by suspend "alloc_edge" >>
  `!i. i <= LENGTH ctors ==> ?j. ctor_segment_fetch func (St i) = SOME j /\
     j.inst_opcode <> PHI /\ (C i).cs_next_id <= j.inst_id` by suspend "fetch" >>
  mp_tac (Q.INST [`args` |-> `ctors`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:eval_result``] create_ctor_rows_at_cuts))) >>
  (impl_tac >- suspend "row_pre") >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choosel_then [`cvs`,`E`,`gf`,`tf`] (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "payload"
QED

Resume create_blueprint_abi_keyword_entry[no_phi]:
  rpt strip_tac >> drule bodySimTheory.body_inv_contract >>
  disch_then (strip_assume_tac o MATCH_MP contractInvContextPropsTheory.contract_inv_lowering_context) >>
  fs[vyperCompilerTheory.lowering_context_ok_def,vyperCompilerTheory.ptr_ok_check_def,EVERY_MEM] >>
  qpat_assum `!fn. MEM fn _ ==> fn_ptr_ok_check _ _ /\ _`
    (qspec_then `func` (drule_then strip_assume_tac)) >> metis_tac[]
QED

Resume create_blueprint_abi_keyword_entry[alloc_edge]:
  `?op. emit_op ALLOCA [Lit (n2w capacity)] se = (op,a)` by
    (Cases_on `emit_op ALLOCA [Lit (n2w capacity)] se` >>
     fs[compile_alloc_buffer_def,comp_bind_def,comp_return_def]) >>
  `s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts` by
    (Cases_on `LENGTH ctors` >> gvs[LENGTH_NIL] >>
     qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `n'` mp_tac) >> simp[]) >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  conj_tac
  >- (irule raw_observed_prefix_alloc >>
      qexistsl_tac [`se`,`a`,`buf`,`capacity`] >> gvs[]) >>
  qexists_tac `mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [tmp]` >>
  gvs[ctor_segment_fetch_def,mk_inst_def]
QED

Resume create_blueprint_abi_keyword_entry[fetch]:
  rpt strip_tac >>
  `?j. ctor_segment_fetch func (St i) = SOME j /\ (C i).cs_next_id <= j.inst_id` by
    (irule blueprint_abi_rows_fetch >>
     qexistsl [`Chunk`,`M`,`Mid`,`LENGTH ctors`,`Snap`,`ctx`,`gas_explicit_sites ctx shctx`,`LENGTH ctors - i`] >>
     rpt conj_tac >> TRY (decide_tac >> NO_TAC) >>
     TRY (qx_gen_tac `row` >> disch_tac >>
          qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
            (qspec_then `row` (drule_then (map_every assume_tac o CONJUNCTS))) >>
          simp[] >> NO_TAC) >>
     metis_tac[]) >>
  qpat_x_assum `ctor_segment_fetch func (St i) = SOME j'` (fn th =>
    qexists_tac `j'` >> conj_tac >- ACCEPT_TAC th >> simp[] >> mp_tac th) >>
  simp[ctor_segment_fetch_def,AllCaseEqs()] >>
  metis_tac[lookup_block_get_instruction_fn_insts]
QED

Resume create_blueprint_abi_keyword_entry[row_pre]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at (C i) x` by
     metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `local_ptrs_reserved ce (C i)` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `SUC i <= LENGTH ctors` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> ?j. _` (qspec_then `SUC i` (drule_then strip_assume_tac)) >>
  qmatch_asmsub_rename_tac `ctor_segment_fetch func (St (SUC i)) = SOME next` >>
  qpat_assum `!i. i < LENGTH ctors ==> (C i).cs_next_id <= _ /\ _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  simp[APPEND_ASSOC] >>
  conj_tac
  >- (disch_tac >> res_tac >> simp[] >>
      irule raw_observed_prefix_join >> simp[] >>
      qexistsl_tac [`M i`,`Mid i`] >> simp[]) >>
  disch_tac >> res_tac >> simp[] >> rpt disch_tac >>
  irule blueprint_abi_silent_band >>
  qexistsl_tac [`M i`,`C (SUC i)`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`Mid i`,`St (SUC i)`] >> simp[]
QED

Resume create_blueprint_abi_keyword_entry[payload]:
  qabbrev_tac `ee = E (LENGTH ctors)` >>
  `EVERY (\call. FST call = NONE /\ IS_SOME (supported_function_decl tops call Internal))
     (int_calls_exprs ctors)` by suspend "calls" >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by fs[expr_sim_inv_split_def,expr_sim_inv_mods_def] >>
  `((C 0):compile_state).cs_next_var <= se.cs_next_var /\ se.cs_next_var <= en.cs_next_var /\
   ((C 0):compile_state).cs_next_var <= en.cs_next_var` by
     (fs[ci_mono_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at se x /\ not_fresh_at en x` by
     metis_tac[not_fresh_at_mono] >>
  qmatch_asmsub_rename_tac `compile_abi_encode_values_to_buf _ _ _ _ = (alen,en)` >>
  mp_tac (Q.INST [`raw` |-> `F`, `args` |-> `ctors`, `vs` |-> `cvs`,
                  `explicit` |-> `gas_explicit_sites ctx shctx`,
                  `st` |-> `a`, `dst_op` |-> `buf.buf_operand`, `u` |-> `su`,
                  `off` |-> `offop`, `salt` |-> `salto`]
    create_ctor_payload_length |>
    PURE_REWRITE_RULE[COND_CLAUSES,AND_CLAUSES,IMP_CLAUSES,NOT_CLAUSES,ADD_CLAUSES,REFL_CLAUSE]) >>
  (impl_tac >- suspend "producer_pre") >>
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >>
  disch_then strip_assume_tac >>
  rename1 `encode_create_ctor_args _ _ _ = SOME bs` >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `ARB` (map_every assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (su,_,_) [] (OK t,geout,teout)` >>
  suspend "finish"
QED

Resume create_blueprint_abi_keyword_entry[calls]:
  drule_all_then assume_tac bodySingletonCallSupportTheory.body_inv_expr_pre_calls >>
  simp[EVERY_MEM] >> qx_gen_tac `call` >> disch_tac >>
  `MEM call (int_calls_expr (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks) args df))` by
    (Cases_on `hs` >> gvs[int_calls_expr_def]) >>
  qpat_assum `EVERY _ (int_calls_expr (Call _ _ _ _))`
    (qspec_then `call` mp_tac o SIMP_RULE bool_ss [EVERY_MEM]) >>
  simp[]
QED

Resume create_blueprint_abi_keyword_entry[producer_pre]:
  qpat_assum `ctors <> []` (simp_tac bool_ss o single) >>
  pure_rewrite_tac[GSYM raw_encoder_prefix_rtc] >>
  `local_ptrs_reserved ce se` by (irule local_ptrs_reserved_next_var >> qexists_tac `C 0` >> simp[]) >>
  `?K. valid_horizon cx st0 K (E (LENGTH ctors)).storage_trace` by (qexists_tac `H` >> fs[Abbr `ee`]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by simp[] >>
  `compile_create_ctor_args compile_expr ce ctors (C 0) = (svs,C (LENGTH ctors))` by gvs[] >>
  simp[PAIR_EQ] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (qexists_tac `H` >> first_assum ACCEPT_TAC >> NO_TAC)
  >- suspend "producer_row" >>
  suspend "producer_callback"
QED

Resume create_blueprint_abi_keyword_entry[producer_row]:
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `!x. not_fresh_at (C 0) x ==> not_fresh_at (C i) x` by
     metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `local_ptrs_reserved ce (C i)` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `i` mp_tac) >> simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(St (SUC i)).vs_labels = (St i).vs_labels` by
    (imp_res_tac create_prefix_labels >> metis_tac[]) >>
  simp[] >> disch_tac >> Cases_on `exprs_can_mutate ce (DROP (SUC i) ctors)` >> simp[]
  >- (conj_tac
      >- (irule raw_observed_prefix_live >>
          qexistsl_tac [`C i`,`M i`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`Chunk i`,`St i`] >> simp[]) >>
      simp[GSYM PAIR_EQ,GSYM IMP_DISJ_THM] >>
      drule blueprint_ctor_segment_rtc >> simp[PAIR_EQ]) >>
  `vv_type (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) =
     lowered_value_type ce (EL i ctors)` by metis_tac[extcall_operand_snapshot_type] >>
  `C (SUC i) = M i` by
    (qpat_assum `compile_snapshot_vv _ _ _ (M i) = _`
        (mp_tac o PURE_REWRITE_RULE[compile_snapshot_vv_def]) >>
     simp[comp_return_def] >> metis_tac[]) >>
  qpat_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _` mp_tac >>
  simp[] >> metis_tac[create_prefix_empty]
QED

Resume create_blueprint_abi_keyword_entry[producer_callback]:
  map_every qx_gen_tac [`i`,`g`,`h`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!i. i < LENGTH ctors ==> monad_bind _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (mp_tac o List.last o CONJUNCTS))) >>
  disch_then (qspecl_then [`g`,`h`] (drule_then ACCEPT_TAC))
QED

Resume create_blueprint_abi_keyword_entry[finish]:
  qhdtm_assum `abi_encode_saved_state`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_state_def]) >>
  qpat_assum `!i. i <= LENGTH ctors ==> (E i).gas_obs = _ /\ _`
    (qspec_then `LENGTH ctors` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
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
       (qspec_then `H` (drule_then
          (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o CONJUNCT1)))) >>
  `t.vs_labels = (St 0).vs_labels` by suspend "exit_labels" >>
  `eval_operand target_op t = SOME aw` by
    (irule blueprint_eval_operand_frame >>
     qexistsl_tac [`C 0`,`St 0`] >> simp[] >>
     qpat_assum `wb_frame ce (E 0) ee (C 0) (St 0) t`
       (mp_tac o cj 1 o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  `ee.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail` by suspend "exit_gas" >>
  `local_ptrs_reserved ce en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `C 0` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`cvs`,`ee`,`geout`,`teout`] >>
  gvs[Abbr `k`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexists_tac `bs` >> simp[]
QED

Resume create_blueprint_abi_keyword_entry[exit_labels]:
  `!i. i <= LENGTH ctors ==> (St i).vs_labels = (St 0).vs_labels` by
    (Induct >> simp[] >> disch_tac >>
     rename1 `SUC i <= LENGTH ctors` >>
     `i < LENGTH ctors` by
       (pure_rewrite_tac[LESS_EQ] >> qpat_assum `SUC i <= LENGTH ctors` ACCEPT_TAC) >>
     `i <= LENGTH ctors` by simp[LESS_IMP_LESS_OR_EQ] >>
     qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     imp_res_tac create_prefix_labels >> simp[]) >>
  imp_res_tac create_prefix_labels >> simp[]
QED

Resume create_blueprint_abi_keyword_entry[exit_gas]:
  `am = [] /\ encmarks = []` by
    (imp_res_tac gas_origin_ptr_path_projections >> conj_tac >>
     irule blueprint_abi_silent_band
     >- (qexistsl_tac [`se`,`a`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`s`,`su`] >> simp[]) >>
     qexistsl_tac [`a`,`en`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`su`,`t`] >> simp[]) >>
  imp_res_tac create_prefix_readings >> fs[Abbr `ee`]
QED

Finalise create_blueprint_abi_keyword_entry
