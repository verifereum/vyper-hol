(* Body-aware MakeArray integration over the counted widened-child loops. *)
Theory exprSimAggregateBodyCase
Ancestors
  exprSimAggregateBodyLoops exprSimAggregatesAllocCounted exprSimAggregateLoops exprSimAlloc
  exprSimAggregateBodySource exprSimAggregateBodyAlloc stmtSimDeclCompose
  exprSimAggregateLayout exprSimAggregateSource exprSimAggregateChildren
  exprSimHyps exprSimHypsDefs exprSimDefs exprSimSource exprSimProps
  loweringPosts exprLoweringProps exprLowering compileEnv
  gasOutcome gasSummary gasContext fragGasMode fragGasPath fragGasSeq fragExec
  vyperInterpreter vyperState vyperTypeSystem valueEncoding valueEncodingDefs
  loweringStateRelDefs gasStorage vyperStorageTrace vyperStorageFootprint

(* buffer_alloc_counted with one endpoint for every valid horizon: the
   ALLOCA run is a function of the start state, so the endpoint found at H0
   is the one literal_alloc_buffer_run gives at every other horizon. *)
Theorem buffer_alloc_counted_horizons[local]:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  valid_horizon cx st0 H0 es.storage_trace /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?inst x t b. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    gas_marked_path F ctx func s0 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es t) /\
    lookup_var x t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    b + sz < dimword (:256) /\ t.vs_memory = s0.vs_memory /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
      FLOOKUP t.vs_allocas aid = SOME a) /\
    (!aid p n. aid < sa.cs_next_id /\
      FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
      regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n ==>
      regions_disjoint b sz p n) /\
    (!name p n. local_region ce es.scopes t name p n <=>
      local_region ce es.scopes s0 name p n)
Proof
  strip_tac >>
  `stmt_state_rel H0 ctx func ce cx es s0` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then (ACCEPT_TAC o cj 1))) >>
  drule_all buffer_alloc_provenance >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    literal_alloc_buffer_run) >> strip_tac >>
  rename1 `run_inst_seq _ s0 = OK u` >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es u` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then (assume_tac o cj 1)) >>
     drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)
       (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
          literal_alloc_buffer_run) >>
     disch_then (qpat_assum `compile_alloc_buffer _ _ = _` o mp_then Any mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ u` kall_tac >>
  qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ s0` kall_tac >>
  `emitted_insts sa sm =
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]] /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `?bb. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sm)
          (DROP s0.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `gas_path ctx func s0 0
     (OK (u with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (drule_all tuple_run_inst_seq_gas_path >>
     simp[venomInstTheory.mk_inst_def]) >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb` by
    (qmatch_asmsub_abbrev_tac `emitted_insts sa sm = [ai]` >>
     `step_inst 0 ctx ai s0 = OK u` by
       (fs[run_inst_seq_def, venomExecSemanticsTheory.step_inst_non_invoke,
           Abbr `ai`, venomInstTheory.mk_inst_def, AllCaseEqs()]) >>
     `~is_terminator ai.inst_opcode` by
       simp[Abbr `ai`, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def] >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >>
     drule_all venomInstProofsTheory.step_preserves_halted >> simp[]) >>
  `!name p n. local_region ce es.scopes u name p n <=>
               local_region ce es.scopes s0 name p n` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`inst`, `x`, `u with vs_inst_idx := LENGTH sm.cs_current_insts`,
                `w2n w`] >>
  gvs[gas_marked_path_def, stmt_state_rel_inst_idx,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def, local_region_def,
      wordsTheory.n2w_w2n] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. aid < _ /\ _ ==> _` irule >>
      qexists_tac `aid` >> simp[]) >>
  rpt gen_tac >>
  qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _`
    (qspecl_then [`name`, `p'`, `n`] mp_tac) >> simp[]
QED

Theorem compile_make_array_body_vv_case:
  !ctx func cenv cx ann topt bnd args.
    exprs_case F ctx func cenv cx args /\
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    expr_vv_case F ctx func cenv cx (Builtin ann (MakeArray topt bnd) args)
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_case_def, expr_vv_sim_def] >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >>
     fs[storage_trace_domain_def]) >>
  Cases_on `topt`
  >- (drule compile_tuple_literal_inv >> strip_tac >>
      drule make_tuple_evaluated_layout >> strip_tac >>
      qpat_assum `ann = _` (fn th =>
        qpat_x_assum `compile_alloc_buffer _ _ = _`
          (assume_tac o SIMP_RULE (srw_ss()) [th, tuple_literal_types_def]) >>
        qpat_x_assum `compile_make_tuple _ _ _ _ _ _ _ = _`
          (assume_tac o SIMP_RULE (srw_ss()) [th, tuple_literal_types_def])) >>
      `ci_mono sa sm /\ ci_mono sm sb` by
        metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_make_tuple_cfn,
                  compile_expr_ci_mono, pairTheory.SND] >>
      `fn_has_code sa sm func /\ fn_has_code sm sb func` by
        metis_tac[fn_has_code_split, ci_mono_def] >>
      `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
      `type_memory_size_list tvs < dimword (:256)` by
        (drule expr_body_pre_copy_ok >>
         simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
         disch_then (qspec_then `TupleTV tvs` mp_tac) >>
         gvs[valueEncodingTheory.type_memory_size_def,
             wordsTheory.dimword_def]) >>
      drule buffer_alloc_counted_horizons >>
      disch_then (drule_at (Pat `fn_has_code sa sm func`)) >>
      disch_then (drule_at (Pat `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ storage_well_formed_on _ _ (FST H)`)) >>
      disch_then (drule_at (Pat `valid_horizon _ _ H0 _`)) >>
      simp[] >> strip_tac >>
      `!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es t /\ storage_well_formed_on cx es (FST H)` by
        (gen_tac >> strip_tac >> conj_tac
         >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t`
               (drule_then ACCEPT_TAC)) >>
         qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s0 /\ storage_well_formed_on _ _ (FST H)`
           (drule_then (ACCEPT_TAC o cj 2))) >>
      `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
         expr_body_pre cenv cx env e st /\ (F ==> int_calls_expr e = [])` by
        (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
         conj_tac >- simp[] >> qexistsl_tac [`ann`, `args`, `MakeArray NONE bnd`, `es`] >> simp[]) >>
      `cenv.ce_is_ctor ==> !name itv iv io.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
        FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
        regions_disjoint io (type_memory_size itv) b (type_memory_size_list tvs)` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t /\ storage_well_formed_on _ _ (FST H)`
           (qspec_then `H0` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         drule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
           aggregate_body_alloc_immutable_prefix) >>
         disch_then (drule_at (Pat `fn_has_code sa sm func`)) >>
         disch_then (drule_at (Pat `stmt_state_rel H0 _ _ _ _ _ t`)) >>
         disch_then (qspec_then `type_memory_size_list tvs` mp_tac) >>
         gvs[] >> metis_tac[]) >>
      qpat_x_assum `compile_make_tuple _ _ _ _ _ _ _ = _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      drule aggregate_body_make_tuple_fits_sim >>
      disch_then (drule_at (Pat `LIST_REL _ _ _`)) >>
      disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
      disch_then (drule_at (Pat `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t /\ storage_well_formed_on _ _ (FST H)`)) >>
      disch_then (qspec_then `env` mp_tac) >> simp[] >>
      disch_then (qspecl_then [`inst`, `b`, `type_memory_size_list tvs`] mp_tac) >>
      simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
      `compatible_bound bnd (LENGTH args)` by
        fs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
      `eval_expr cx (Builtin ann (MakeArray NONE bnd) args) =
       bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (TupleV vs))))` by
        (simp[FUN_EQ_THM] >> gen_tac >>
         Cases_on `eval_exprs cx args x'` >>
         drule aggregate_eval_make_tuple >> simp[bind_def, return_def] >>
         disch_then drule >> Cases_on `q` >> simp[]) >>
      irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
      gvs[] >>
      irule gas_outcome_map_source_run >> goal_assum (drule_at Any) >>
      conj_tac >- (simp[] >> rpt strip_tac >> gvs[]) >>
      simp[] >> rpt strip_tac >> gvs[] >> suspend "tuple_post")
  >> suspend "array_case"
QED

Resume compile_make_array_body_vv_case[tuple_post]:
  qmatch_goalsub_abbrev_tac `vv_post H _ _ _ _ e` >>
  `TupleT tys = expr_type e` by
    simp[Abbr `e`, vyperASTTheory.expr_type_def] >>
  pop_assum SUBST1_TAC >> irule buffer_loop_memory_vv_post >>
  simp[Abbr `e`, vyperASTTheory.expr_type_def, post_value_type_def, is_word_type_def,
       contextTheory.mk_ptr_def] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `EVERY _ args ==> _` drule >> strip_tac >>
      drule_all buffer_alloc_code >> strip_tac >>
      `FLOOKUP t'.vs_allocas sa.cs_next_id = SOME (b,type_memory_size_list tvs)` by metis_tac[] >>
      irule aggregate_pure_frame_buffer >>
      qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
      qpat_assum `FLOOKUP t'.vs_allocas _ = SOME (b,_)` (irule_at Any) >>
      qexistsl_tac [`t`, `sm`] >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!name lo sz. local_region _ _ s0 _ _ _ ==> _` irule >>
          qexists_tac `n` >> simp[]) >>
      gvs[]) >>
  qexistsl_tac [`b`, `sm`, `type_memory_size_list tvs`, `t`] >>
  simp[venomStateTheory.eval_operand_def, valueEncodingDefsTheory.val_in_memory_def] >>
  conj_tac >- (rpt strip_tac >>
    `FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,type_memory_size_list tvs)` by metis_tac[] >>
    drule_at (Pat `local_region _ _ _ _ _ _`)
      (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] aggregate_alloca_slice_excludes_local) >>
    disch_then (qspecl_then [`x`, `0`, `type_memory_size_list tvs`] mp_tac) >>
    disch_then (drule_at (Pat `MEM _ _`)) >> simp[] >>
    disch_then (drule_at (Pat `stmt_state_rel H _ _ _ _ _ _`)) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` suffices_by
    (strip_tac >> simp[] >> drule val_footprint_le >>
     simp[valueEncodingTheory.type_memory_size_def]) >>
  `eval_expr cx (Builtin (TupleT tys) (MakeArray NONE bnd) args)
    (es with gas_obs := gs) = (INL (Value (ArrayV (TupleV vs))),ee)` by
    simp[bind_def, return_def] >>
  irule aggregate_materialised_child_wf >>
  goal_assum (drule_at Any) >>
  simp[expr_body_pre_gas_obs, vyperASTTheory.expr_type_def, read_result_def, return_def] >>
  goal_assum (drule_at Any)
QED

Resume compile_make_array_body_vv_case[array_case]:
  rename1 `MakeArray (SOME et) bnd` >>
  drule compile_array_literal_inv >> strip_tac >>
  drule make_array_evaluated_layout >> strip_tac >> gvs[] >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_make_array_cfn,
              compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes cenv (ArrayT et bnd) < dimword (:256)` by
    (drule expr_body_pre_copy_ok >>
     simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
     gvs[wordsTheory.dimword_def]) >>
  drule buffer_alloc_counted_horizons >>
  disch_then (drule_at (Pat `fn_has_code sa sm func`)) >>
  disch_then (drule_at (Pat `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ storage_well_formed_on _ _ (FST H)`)) >>
  disch_then (drule_at (Pat `valid_horizon _ _ H0 _`)) >>
  simp[] >> strip_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es t /\ storage_well_formed_on cx es (FST H)` by
    (gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t`
           (drule_then ACCEPT_TAC)) >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s0 /\ storage_well_formed_on _ _ (FST H)`
       (drule_then (ACCEPT_TAC o cj 2))) >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     conj_tac >- simp[] >>
     qexistsl_tac [`ArrayT et bnd`, `args`, `MakeArray (SOME et) bnd`, `es`] >> simp[]) >>
  `cenv.ce_is_ctor ==> !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b
      ((if (case bnd of Fixed _ => F | Dynamic _ => T) then 32 else 0) +
       LENGTH args * type_memory_size tv)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t /\ storage_well_formed_on _ _ (FST H)`
       (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
       aggregate_body_alloc_immutable_prefix) >>
     disch_then (drule_at (Pat `fn_has_code sa sm func`)) >>
     disch_then (drule_at (Pat `stmt_state_rel H0 _ _ _ _ _ t`)) >>
     disch_then (qspec_then
       `((if (case bnd of Fixed _ => F | Dynamic _ => T) then 32 else 0) +
         LENGTH args * type_memory_size tv)` mp_tac) >>
     gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `compile_make_array _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule aggregate_body_make_array_sim >>
  disch_then (drule_at (Pat `evaluate_type _ et = _`)) >>
  disch_then (drule_at (Pat `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t /\ storage_well_formed_on _ _ (FST H)`)) >>
  disch_then (qspec_then `env` mp_tac) >> simp[] >>
  disch_then (drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`inst`, `b`, `type_memory_bytes cenv (ArrayT et bnd)`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[arithmeticTheory.ADD_COMM]) >> strip_tac >>
  `compatible_bound bnd (LENGTH args)` by
    fs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `eval_expr cx (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args) =
    bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (make_array_value tv bnd vs))))` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `eval_exprs cx args x'` >>
     qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` kall_tac >>
     drule_at (Pat `eval_exprs _ _ _ = _`) aggregate_eval_make_array >>
     disch_then (drule_at (Pat `evaluate_type _ et = _`)) >>
     simp[bind_def, return_def] >> Cases_on `q` >> simp[]) >>
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >> gvs[] >>
  irule gas_outcome_map_source_run >> goal_assum (drule_at Any) >>
  conj_tac >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[] >> rpt strip_tac >> gvs[] >> suspend "array_post"
QED

Resume compile_make_array_body_vv_case[array_post]:
  qmatch_goalsub_abbrev_tac `vv_post H _ _ _ _ e` >>
  `ArrayT et bnd = expr_type e` by
    simp[Abbr `e`, vyperASTTheory.expr_type_def] >>
  pop_assum SUBST1_TAC >> irule buffer_loop_memory_vv_post >>
  simp[Abbr `e`, vyperASTTheory.expr_type_def, post_value_type_def, is_word_type_def,
       contextTheory.mk_ptr_def] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `EVERY _ args ==> _` drule >> strip_tac >>
      drule_all buffer_alloc_code >> strip_tac >>
      `FLOOKUP t'.vs_allocas sa.cs_next_id = SOME (b,type_memory_bytes cenv (ArrayT et bnd))` by metis_tac[] >>
      irule aggregate_pure_frame_buffer >>
      qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
      qpat_assum `FLOOKUP t'.vs_allocas _ = SOME (b,_)` (irule_at Any) >>
      qexistsl_tac [`t`, `sm`] >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!name lo sz. local_region _ _ s0 _ _ _ ==> _` irule >>
          qexists_tac `n` >> simp[]) >>
      gvs[]) >>
  qexistsl_tac [`b`, `sm`, `type_memory_bytes cenv (ArrayT et bnd)`, `t`] >>
  simp[venomStateTheory.eval_operand_def] >>
  conj_tac >- (rpt strip_tac >>
    `FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,type_memory_bytes cenv (ArrayT et bnd))` by metis_tac[] >>
    drule_at (Pat `local_region _ _ _ _ _ _`)
      (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] aggregate_alloca_slice_excludes_local) >>
    disch_then (qspecl_then [`x`, `0`, `type_memory_bytes cenv (ArrayT et bnd)`] mp_tac) >>
    disch_then (drule_at (Pat `MEM _ _`)) >> simp[] >>
    disch_then (drule_at (Pat `stmt_state_rel H _ _ _ _ _ _`)) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_wf (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs))` by
    (`eval_expr cx (Builtin (ArrayT et bnd) (MakeArray (SOME et) bnd) args)
      (es with gas_obs := gs) = (INL (Value (ArrayV (make_array_value tv bnd vs))),ee)` by
       simp[bind_def, return_def] >>
     irule aggregate_materialised_child_wf >> goal_assum (drule_at Any) >>
     simp[expr_body_pre_gas_obs, vyperASTTheory.expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any)) >>
  conj_tac >- (drule val_footprint_le >>
    `type_memory_bytes cenv (ArrayT et bnd) = type_memory_size (ArrayTV tv bnd)` by
       metis_tac[expr_sim_inv_memory_size] >> simp[]) >>
  simp[] >>
  `LENGTH vs = LENGTH args` by (drule eval_exprs_length >> simp[]) >>
  Cases_on `bnd` >> gvs[vyperValueTheory.compatible_bound_def]
  >- (irule exprSimAggregateEncodingTheory.fixed_array_from_dense >> simp[]) >>
  simp[vyperValueTheory.make_array_value_def, val_in_memory_def]
QED

Finalise compile_make_array_body_vv_case
