Theory createSizeBlueprintAbiObservedCutsMods
Ancestors
  createSizeObservedPrefix createCtorObservedSilence bodyPtrMakeArrayEmission
  bodyFullIfExpReach stmtLoweringMono fragFuel gasExplicitSites exprSimFullBundleProps
  createSizePrefixReplay relation pair createMarkedPath createExprSizeExitDefs
  createCtorSegmentArrival fragExec arithmetic list context compileEnv exprLoweringProps
  venomInst contractInvContextProps gasShadowCompileBase exprLowering venomState
  venomExecSemantics fragGasOrigin words abiEncoderProps

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

Theorem blueprint_abi_fetch_non_phi[local]:
  contract_inv mods exps ctx ce cx /\ MEM func ctx.ctx_functions /\
  ctor_segment_fetch func s = SOME j ==> j.inst_opcode <> PHI
Proof
  strip_tac >> drule contractInvContextPropsTheory.contract_inv_lowering_context >>
  simp[vyperCompilerTheory.lowering_context_ok_def,vyperCompilerTheory.ptr_ok_check_def,EVERY_MEM] >>
  strip_tac >>
  qpat_assum `!fn. MEM fn _ ==> fn_ptr_ok_check _ _ /\ _`
    (qspec_then `func` (drule_then strip_assume_tac)) >>
  qpat_x_assum `ctor_segment_fetch _ _ = _` mp_tac >>
  simp[ctor_segment_fetch_def,AllCaseEqs()] >>
  metis_tac[lookup_block_get_instruction_fn_insts]
QED

Theorem blueprint_abi_alloc_fetch[local]:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?j. ctor_segment_fetch func s = SOME j /\ se.cs_next_id <= j.inst_id
Proof
  strip_tac >>
  `?op. emit_op ALLOCA [Lit (n2w capacity)] se = (op,a)` by
    (Cases_on `emit_op ALLOCA [Lit (n2w capacity)] se` >>
     fs[compile_alloc_buffer_def,comp_bind_def,comp_return_def]) >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  qexists_tac `mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [tmp]` >>
  gvs[ctor_segment_fetch_def,mk_inst_def]
QED

Theorem blueprint_abi_observed_ctor_cuts_mods:
  ctors <> [] /\ contract_inv mods exps ctx ce cx /\
  MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
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
  capacity = abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors)) /\
  capacity < dimword (:256) /\
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  su.vs_current_bb = a.cs_current_bb /\ su.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix se a (gas_explicit_sites ctx shctx) ctx func s am su /\
  compile_abi_encode_values_to_buf ce buf.buf_operand (ZIP (svs,MAP (lowered_value_type ce) ctors))
    a = (len,en) /\ fn_has_code a en func /\
  create_expr_prefix a en (gas_explicit_sites ctx shctx) ctx func su encmarks t /\
  t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
  R (LENGTH ctors) = am ++ encmarks ++ rest ==>
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (ci_mono (C 0) se /\ ci_mono se a /\ ci_mono a en) /\
  gas_origin_edge F (gas_explicit_sites ctx shctx) ctx func s am (OK su) /\
  (!i. i <= LENGTH ctors ==> ?j. ctor_segment_fetch func (St i) = SOME j /\
    j.inst_opcode <> PHI /\ (C i).cs_next_id <= j.inst_id) /\
  (!i. i < LENGTH ctors ==>
    (is_word_type (lowered_value_type ce (EL i ctors)) ==>
      create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i ++ Snap i) (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i ctors)) /\
      exprs_can_mutate ce (DROP (SUC i) ctors) /\
      gas_origin_path T (gas_explicit_sites ctx shctx) ctx func (Mid i) [] (OK (St (SUC i))) ==>
      Snap i = [])) /\
  (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func s [] (OK su) ==> am = []) /\
  (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func su [] (OK t) ==> encmarks = [])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi_mods] >>
  `ci_mono (C 0) se /\ ci_mono se a /\ ci_mono a en` by
    metis_tac[ci_mono_compile_create_ctor_args,ci_mono_compile_expr_sa,
      ci_mono_compile_alloc_buffer,ci_mono_compile_abi_encode_values_to_buf,SND] >>
  `s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts` by
    (Cases_on `LENGTH ctors` >> gvs[LENGTH_NIL] >>
     qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `n'` mp_tac) >> simp[]) >>
  `gas_origin_edge F (gas_explicit_sites ctx shctx) ctx func s am (OK su)` by
    (irule raw_observed_prefix_alloc >> qexistsl_tac [`se`,`a`,`buf`,`capacity`] >> simp[]) >>
  `?j. ctor_segment_fetch func s = SOME j /\ se.cs_next_id <= j.inst_id` by
    (drule_all blueprint_abi_alloc_fetch >> simp[]) >>
  `!i. i < LENGTH ctors ==> (C i).cs_next_id <= (M i).cs_next_id /\
                          (M i).cs_next_id <= (C (SUC i)).cs_next_id` by
    (rpt strip_tac >> qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     metis_tac[ci_mono_compile_expr_sa,ci_mono_compile_snapshot_vv,ci_mono_def,SND]) >>
  `!i. i <= LENGTH ctors ==> ?j. ctor_segment_fetch func (St i) = SOME j /\
     j.inst_opcode <> PHI /\ (C i).cs_next_id <= j.inst_id` by suspend "fetch" >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "row" >>
  conj_tac >> strip_tac >> irule blueprint_abi_silent_band
  >- (qexistsl_tac [`se`,`a`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`s`,`su`] >> simp[]) >>
  qexistsl_tac [`a`,`en`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`su`,`t`] >> simp[]
QED

Resume blueprint_abi_observed_ctor_cuts_mods[fetch]:
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
  drule_all_then assume_tac blueprint_abi_fetch_non_phi >>
  qmatch_asmsub_rename_tac `ctor_segment_fetch func (St i) = SOME next` >>
  qexists_tac `next` >> simp[]
QED

Resume blueprint_abi_observed_ctor_cuts_mods[row]:
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH ctors ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `SUC i <= LENGTH ctors` by decide_tac >>
  qpat_assum `!i. i <= LENGTH ctors ==> ?j. _` (qspec_then `SUC i` (drule_then strip_assume_tac)) >>
  qpat_assum `!i. i < LENGTH ctors ==> (C i).cs_next_id <= _ /\ _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  conj_tac
  >- (disch_tac >> irule raw_observed_prefix_join >> simp[] >>
      qexistsl_tac [`M i`,`Mid i`] >> simp[]) >>
  strip_tac >> irule blueprint_abi_silent_band >>
  qexistsl_tac [`M i`,`C (SUC i)`,`ctx`,`gas_explicit_sites ctx shctx`,`func`,`Mid i`,`St (SUC i)`] >> simp[]
QED

Finalise blueprint_abi_observed_ctor_cuts_mods
