(* A field of a target on the joint line: the base target's run, then
   one ADD of the field's offset with no gas mark. *)
Theory bodyFullTargetAttribute
Ancestors
  bodyFullTargetDefs bodyFullTargetRoots gasOutcomeFullCompose gasOutcomeFull
  fragGasOriginPtr bodyFullUnwrapRun targetPtrFacts
  exprSimAttributeFields exprSimFieldLayout exprSimSubscriptArrayLiveImmutableView exprSimProps
  bodySimAugPlaceLoad gasShadowCompileStmtHelpers vyperTypeEnv
  bodyFullSubscriptArrayCodeOps bodyFullGhostFrame bodyFullPathHistory
  vyperFixedShapePath allocLimits freshWrites typedStructMetadata
  bodyPtrAttributeAdd typedCopyPtr decoderGhostFramePtr
  targetPlaceSimCasesBase targetPlaceSimCases targetPlaceSim targetPlaceSimDefs
  gasShadowCompile gasShadowCompileHelpers gasShadow gasShadowState gasExemptCert
  stmtLoweringMono exprLoweringProps emitHelperProps
  exprPtrUnwrapScalarEdges fragGasSeqPtr fragExecMem fragExec
  bodyPtrDefs loweringPosts exprSimHypsDefs
  compileEnv exprLowering ptrDiscipline vyperStorageTrace loweringStateRelDefs
  exprSimDefs emitHelper gasContext bodyFullShared vyperTypeSystem
  vyperTypeInvariants
  vyperStorageFootprint vyperTyping vyperInterpreter vyperState venomState
  venomInst unitTransformDefs memSafeRun contextCodegenRel codegenRel
  list finite_map pair

(* A write to a variable no local pointer, return buffer or return pc
   uses keeps the ghost invariant. *)
Theorem ghost_inv_at_fresh_write:
  ghost_inv_at D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t' = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t'.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
  t'.vs_call_ctx = s.vs_call_ctx /\ t'.vs_accounts = s.vs_accounts /\
  t'.vs_transient = s.vs_transient /\ t'.vs_immutables = s.vs_immutables /\
  t'.vs_allocas = s.vs_allocas /\ t'.vs_alloca_next = s.vs_alloca_next /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  tn'.t_imm = tn.t_imm ==>
  ghost_inv_at D lo d cenv cx ee G' tn' t'
Proof
  simp[ghost_inv_at_def, local_ptrs_reserved_def, stor_taint_ok_at_def,
       allocas_from_def] >> rpt strip_tac
  >- (gvs[ptr_covers_def] >> metis_tac[])
  >- metis_tac[]
  >- (Cases_on `d` >- gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >>
      metis_tac[])
  >> metis_tac[]
QED

(* The ADD of a field offset, from the base target's endpoint, on a
   zero-mark path at every horizon. *)
Theorem target_add_suffix_endpoint:
  !rb off sm dst sb func ctx cenv sa t s0 w0 cx st0 trace es pv vt DF lo d ee
   G tn pv' G0 tn0 vt' explicit PG.
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  eval_operand (FST rb) t = SOME w0 /\
  (!H. valid_horizon cx st0 H trace ==>
     target_post H ctx func cenv cx es sa sm s0 ee pv vt rb t /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
     target_ptr_ok cenv pv' rb G tn t /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
  place_ptr_rel cenv cx t pv' (w0 + n2w off) (FST (SND rb)) vt' /\
  place_readable cx ee pv' ==>
  ?u G' tn'.
    (?out. dst = Var out /\
      u = (update_var out (w0 + n2w off) t with vs_inst_idx := SUC t.vs_inst_idx)) /\
    !H. valid_horizon cx st0 H trace ==>
      gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
        (t, G, tn) [] (OK u, G', tn') /\
      target_post H ctx func cenv cx es sa sb s0 ee pv' vt'
        (dst, FST (SND rb), SOME (value_type_place vt')) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' u /\
      target_ptr_ok cenv pv' (dst, FST (SND rb), SOME (value_type_place vt'))
        G' tn' u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexistsl_tac [
    `update_var (STRING #"%" (toString sm.cs_next_var)) (w0 + n2w off) t with
       vs_inst_idx := LENGTH sb.cs_current_insts`,
    `step_prov PG G
       (mk_inst sm.cs_next_id ADD [FST rb; Lit (n2w off)]
          [STRING #"%" (toString sm.cs_next_var)])
       (update_var (STRING #"%" (toString sm.cs_next_var)) (w0 + n2w off) t)`,
    `step_taint
       (mk_inst sm.cs_next_id ADD [FST rb; Lit (n2w off)]
          [STRING #"%" (toString sm.cs_next_var)]) t
       (update_var (STRING #"%" (toString sm.cs_next_var)) (w0 + n2w off) t)
       tn`] >>
  conj_tac >- (qexists_tac `STRING #"%" (toString sm.cs_next_var)` >>
              simp[arithmeticTheory.ADD1]) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  `op_taint tn (FST rb) = {}` by fs[target_ptr_ok_def] >>
  `allocas_from lo t` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_at_def]) >>
  `alloca_inv t` by
    (qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[target_post_def, stmt_state_rel_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (fs[target_post_def, stmt_state_rel_def, fmp_room_def,
        allocas_below_fmp_def, venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id ADD [FST rb; Lit (n2w off)] [out]` >>
  qabbrev_tac `u0 = update_var out (w0 + n2w off) t` >>
  `step_inst_base inst t = OK u0` by
    (simp[Abbr `inst`, Abbr `u0`] >> irule step_ADD >>
     simp[eval_operand_def]) >>
  `run_inst_seq [inst] t = OK u0` by simp[run_inst_seq_def] >>
  `dst = Var out /\ sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ [inst]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, Abbr `inst`, Abbr `out`] >>
     strip_tac >> gvs[]) >>
  `op_taint (step_taint inst t u0 tn) (Var out) = {} /\
   (step_taint inst t u0 tn).t_mem = tn.t_mem /\
   (step_taint inst t u0 tn).t_stor = tn.t_stor /\
   (step_taint inst t u0 tn).t_trans = tn.t_trans /\
   (!p. p <> out ==>
      FLOOKUP (step_prov PG G inst u0) p = FLOOKUP G p /\
      op_taint (step_taint inst t u0 tn) (Var p) = op_taint tn (Var p))` by
    simp[Abbr `inst`, Abbr `u0`, copy_len_binop_ghost_frame] >>
  `(step_taint inst t u0 tn).t_imm = tn.t_imm` by
    (irule (cj 3 step_taint_nonmemory_frame) >>
     simp[Abbr `inst`, mk_inst_def]) >>
  gvs[] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[Abbr `out`, not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  suspend "parts"
QED

Resume target_add_suffix_endpoint[parts]:
  `inst_seq_ptr (DF H) lo ctx func PG G tn [inst] t
     (step_prov PG G inst u0) (step_taint inst t u0 tn)` by
    (simp[inst_seq_ptr_def] >> simp[Abbr `inst`] >>
     irule ptr_inst_ok_copy_arith >> simp[op_taint_def]) >>
  `run_inst_seq_mem_ok [inst] t` by
    (simp[run_inst_seq_mem_ok_def] >>
     simp[Abbr `inst`, mk_inst_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
              ~is_terminator i.inst_opcode) [inst]` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  qspecl_then [`DF H`, `[inst]`, `sm`, `sb`, `t`, `u0`, `G`, `tn`,
               `step_prov PG G inst u0`, `step_taint inst t u0 tn`]
    mp_tac (Q.GEN `D` emitted_origin_ptr_path) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      `MEM i [inst]` by metis_tac[MEM_APPEND, MEM] >>
      gvs[Abbr `inst`, mk_inst_def, dalloca_no_wrap_non_dalloca]) >>
  strip_tac >>
  qspecl_then [`[inst]`, `sm`, `sb`, `t`, `u0`] mp_tac emitted_alloca_history >>
  (impl_tac >- fs[EVERY_DEF]) >> strip_tac >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) target_post_add >>
  disch_then (qspecl_then [`sb`, `Var out`, `w0`, `off`, `pv'`, `vt'`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `q = u0` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `HG = step_prov PG G inst u0` >>
  qabbrev_tac `tm = step_taint inst t u0 tn` >>
  `!x. not_fresh_at sa x ==>
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)`
    by metis_tac[] >>
  `ghost_inv_at (DF H) lo d cenv cx ee HG tm
     (u0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule ghost_inv_at_fresh_write >> disch_then irule >>
     simp[Abbr `u0`, update_var_def, lookup_var_def] >>
     qexists_tac `sa` >> simp[] >>
     rpt strip_tac >> res_tac >> gvs[FLOOKUP_UPDATE]) >>
  `target_ptr_ok cenv pv' (Var out, FST (SND rb), SOME (value_type_place vt'))
     HG tm (u0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule target_ptr_ok_operand_transport >> disch_then irule >>
     simp[op_prov_def, Abbr `HG`, Abbr `inst`, attribute_add_provenance] >>
     metis_tac[local_ptrs_reserved_def]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`, `tn`] >>
     simp[]) >>
  `u0.vs_current_bb = t.vs_current_bb /\
   u0.vs_alloca_next = t.vs_alloca_next` by
    simp[Abbr `u0`, update_var_def] >>
  `LENGTH sb.cs_current_insts = LENGTH sm.cs_current_insts + 1` by simp[] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >> simp[]
QED

Finalise target_add_suffix_endpoint

Theorem target_add_suffix_full:
  !rb off sm dst sb func ctx cenv sa t s0 w0 cx st0 trace es pv vt DF lo d ee
   G tn pv' G0 tn0 vt' explicit PG.
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  eval_operand (FST rb) t = SOME w0 /\
  (!H. valid_horizon cx st0 H trace ==>
     target_post H ctx func cenv cx es sa sm s0 ee pv vt rb t /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
     target_ptr_ok cenv pv' rb G tn t /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
  place_ptr_rel cenv cx t pv' (w0 + n2w off) (FST (SND rb)) vt' /\
  place_readable cx ee pv' ==>
  ?u G' tn'.
    !H. valid_horizon cx st0 H trace ==>
      gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
        (t, G, tn) [] (OK u, G', tn') /\
      target_post H ctx func cenv cx es sa sb s0 ee pv' vt'
        (dst, FST (SND rb), SOME (value_type_place vt')) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' u /\
      target_ptr_ok cenv pv' (dst, FST (SND rb), SOME (value_type_place vt'))
        G' tn' u /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  rpt gen_tac >>
  disch_then (mp_tac o MATCH_MP (SPEC_ALL target_add_suffix_endpoint)) >>
  disch_then (qx_choosel_then [`u`,`G'`,`tn'`]
    (CONJUNCTS_THEN2 (K ALL_TAC) assume_tac)) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >> first_assum ACCEPT_TAC
QED

Theorem target_attribute_sim_full:
  target_pre cenv cx env (AttributeTarget bt fld) es /\
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es ==>
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env (AttributeTarget bt fld) es
Proof
  strip_tac >> simp[target_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ bty fld = SOME fty` >>
  drule compile_get_target_ptr_attr >> strip_tac >> gvs[] >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
     (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt))` by irule gas_shadow_stmt_get_target_ptr_env >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o MATCH_MP compile_get_target_ptr_attr o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa =
             (srb, shadow_sm)` >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    metis_tac[ci_mono_emit_op, SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_next_var <= sm.cs_next_var /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `eval_base_place cx (AttributeTarget bt fld) =
     bind (eval_base_place cx bt) (\pv. extend_place cx pv (AttrSubscript fld))`
    by simp[FUN_EQ_THM, Once evaluate_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]) >>
  qpat_x_assum `target_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `Type bty`, `sa`, `sm`, `shadow_sa`,
                           `shadow_sm`, `rb`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_base_place cx bt) _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_base_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_extend_place] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\
                                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def]
QED

Resume target_attribute_sim_full[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `pv` >> simp[] >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL pv, mid)`
    by (qpat_assum `!tail. eval_base_place _ _ _ = _`
          (qspec_then `[]` mp_tac) >> REWRITE_TAC [APPEND_NIL] >>
        qpat_assum `mid with gas_obs := [] = mid` (fn th => REWRITE_TAC [th])) >>
  `expr_sim_inv cenv cx env mid` by
    (irule eval_base_place_sim_inv >>
     qexistsl_tac [`bt`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                   `INL pv`] >> fs[target_pre_def] >>
     metis_tac[target_pre_sub, target_pre_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?sid. bty = StructT sid` by
    (Cases_on `bty` >> gvs[attribute_type_def]) >> gvs[] >>
  Cases_on `extend_place cx pv (AttrSubscript fld) mid` >>
  rename1 `extend_place _ _ _ _ = (res1, es2)` >>
  `!m. res1 <> INR (Error (TypeError m))` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def] >> rpt strip_tac >> gvs[target_res_ok_def]) >>
  `?w0. eval_operand (FST rb) t = SOME w0 /\
        place_ptr_rel cenv cx t pv w0 (FST (SND rb)) (Type (StructT sid)) /\
        SND (SND rb) = SOME (ValPT (StructT sid)) /\
        place_readable cx mid pv` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> rpt strip_tac >>
     qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE std_ss [target_post_def,
                                             value_type_place_def]) >>
     qexists_tac `w` >> fs[]) >>
  drule_all target_field_source_ptr >> strip_tac >> gvs[] >>
  suspend "tail"
QED

Resume target_attribute_sim_full[tail]:
  qspecl_then [`rb`, `target_field_offset cenv (FST (SND rb)) (SND (SND rb)) fld`,
               `sm`, `dst`, `sb`, `func`, `ctx`, `cenv`, `sa`, `t`, `s0`, `w0`,
               `cx`, `st0`, `es2.storage_trace`, `es`, `pv`,
               `Type (StructT sid)`, `DF`, `lo`, `d`, `es2`, `G1`, `tn1`,
               `pv'`, `G0`, `tn0`, `Type fty`,
               `gas_explicit_sites ctx shadow_ctx`, `PG`]
    mp_tac target_add_suffix_full >>
  impl_tac
  >- (simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      gen_tac >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H es2.storage_trace ==> _` drule >>
      strip_tac >> simp[]) >>
  strip_tac >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `es2`, `INL pv'`, `u`, `tn'`] >>
  conj_tac >- simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H es2.storage_trace ==>
                    gas_origin_ptr_path _ _ _ _ /\ _` drule >>
  simp[] >> strip_tac >>
  fs[target_post_def, stmt_state_rel_def, fmp_room_def,
     allocas_below_fmp_def, venomMemDefsTheory.alloca_inv_def,
     venomMemDefsTheory.alloca_next_valid_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

Finalise target_attribute_sim_full

Theorem immutable_target_field_source[local]:
  expr_sim_inv cenv cx env ee /\
  attribute_type (get_tenv cx) (StructT sid) fld = SOME fty /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables NONE imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ptv) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME ptv /\
  evaluate_subscripts itv iv path = INL v ==>
  ?ftv fv off fsz.
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      SOME (fty,fsz) /\
    off = struct_field_offset (get_struct_fields cenv.ce_struct_fields
      (nsid_to_string sid)) fld /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\
    mem_path_offset itv (path ++ [AttrSubscript fld]) = SOME (k+off,ftv) /\
    evaluate_subscripts itv iv (path ++ [AttrSubscript fld]) = INL fv /\
    !gs. bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
                 (AttrSubscript fld)) get_place (ee with gas_obs := gs) =
         (INL (ImmutablePlace NONE id (path ++ [AttrSubscript fld])),
          ee with gas_obs := gs)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac stmtSimAssignAttrTheory.attribute_type_struct_field >>
  drule_all_then strip_assume_tac struct_fields_layout >> gvs[] >>
  drule_all_then strip_assume_tac struct_field_type >>
  drule_all_then assume_tac mem_field_offset_layout >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) =
     SOME (struct_field_offset (get_struct_fields cenv.ce_struct_fields
             (nsid_to_string sid)) fld,ftv)` by simp[mem_step_offset_def] >>
  drule_all_then strip_assume_tac exprSimPropsTheory.mem_path_offset_snoc >>
  drule_all_then strip_assume_tac imm_place_at_value_type >>
  drule_then strip_assume_tac exprSimPropsTheory.mem_path_offset_sound >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `evaluate_subscripts itv iv path = INL (StructV vals)` >>
  `?fv. ALOOKUP vals fld = SOME fv` by
    (Cases_on `ALOOKUP vals fld` >> simp[] >>
     drule_all_then mp_tac
       vyperTypeStatePreservationTheory.struct_has_type_alookup_none >> simp[]) >>
  drule_all_then assume_tac evaluate_subscripts_snoc_attr >>
  simp[] >> gen_tac >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  `evaluate_subscripts (StructTV fs) (StructV vals) [AttrSubscript fld] =
    INL fv` by simp[evaluate_subscripts_def] >>
  `subscripts_type itv path = SOME (StructTV fs)` by
    metis_tac[exprSimPropsTheory.mem_path_offset_sound] >>
  mp_tac (Q.INST [`es` |-> `ee with gas_obs := gs`, `path` |-> `path`,
    `sb` |-> `AttrSubscript fld`, `src` |-> `NONE`, `imms` |-> `x`,
    `ptv` |-> `StructTV fs`, `value` |-> `StructV vals`]
    immutable_target_extend) >> simp[]
QED

Theorem immutable_target_field_add[local]:
  emit_op ADD [FST rb; Lit (n2w field_off)] sm = (dst,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  eval_operand (FST rb) t = SOME (n2w (off+k)) /\ op_taint tn (FST rb) = {} /\
  op_prov G (FST rb) = NONE /\
  FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables NONE imms) id = SOME (itv,iv) /\
  mem_path_offset itv path' = SOME (k+field_off,ftv) /\
  evaluate_type (get_tenv cx) fty = SOME ftv /\
  evaluate_subscripts itv iv path' = INL fv /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    imm_target_post H ctx func cenv cx es sa sm s0 ee id path bty rb t /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  ?u G' tn'.
    (?out. dst = Var out /\ u = (update_var out
       ((n2w (off+k):bytes32) + n2w field_off) t with vs_inst_idx := SUC t.vs_inst_idx)) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,G',tn') /\
      imm_target_post H ctx func cenv cx es sa sb s0 ee id path' fty
        (dst,SOME LocCode,SOME (ValPT fty)) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' u /\
      target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id path'))
        (dst,SOME LocCode,SOME (ValPT fty)) G' tn' u /\
      op_prov G' dst = NONE /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >> drule_then strip_assume_tac emitted_insts_emit_op >>
  qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `eval_operand (Lit (n2w field_off)) t = SOME (n2w field_off) /\
    op_taint tn (Lit (n2w field_off)) = {} /\ op_prov G (Lit (n2w field_off)) = NONE` by
    simp[eval_operand_def,op_taint_def,op_prov_def] >>
  mp_tac (Q.INST [`opc` |-> `ADD`,`w` |-> `n2w (off+k) + n2w field_off : bytes32`,
     `a` |-> `n2w (off+k):bytes32`,`b` |-> `n2w field_off:bytes32`,
     `left` |-> `FST (rb : operand # data_location option # place_ty option)`,`right` |-> `Lit (n2w field_off)`,`sa` |-> `sm`,
     `s` |-> `t`,`out` |-> `out`,`PG` |-> `PG`]
     (INST_TYPE [``:'a`` |-> ``:256``] scalar_binop_joint_frame_endpoint)) >>
  impl_tac >- simp[Abbr `out`] >> strip_tac >>
  rename1 `lookup_var out u = SOME _` >>
  rename1 `op_taint tn' (Var out) = _` >>
  rename1 `op_prov G' (Var out) = _` >>
  qexistsl [`u`,`G'`,`tn'`] >>
  conj_tac >- (qexists_tac `out` >> simp[Abbr `out`]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,G',tn')` by simp[] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `ghost_inv_at (DF H) lo d cenv cx ee G' tn' u` by
    (irule ghost_inv_at_exterior_frame >> qexistsl [`G`,`ee`,`t`,`sm`,`tn`] >>
     simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[]) >>
  fs[imm_target_post_def] >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  drule_all_then assume_tac body_full_path_alloca_history >>
  `stmt_state_rel H ctx func cenv cx ee u` by
    (first_assum (qspecl_then [`H`,`cenv`,`cx`,`ee`] irule) >> simp[]) >>
  `locals_kept cenv es ee s0 u` by
    (irule locals_kept_mem_tail >> qexists_tac `t` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `?o' root curr delta leaf selected.
     FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc o') /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables NONE imms) id = SOME (root,curr) /\
     mem_path_offset root path' = SOME (delta,leaf) /\
     evaluate_type (get_tenv cx) fty = SOME leaf /\
     evaluate_subscripts root curr path' = INL selected /\
     eval_operand (Var out) u = SOME (n2w (o'+delta))` by
    (qexistsl [`off`,`itv`,`iv`,`k+field_off`,`ftv`,`fv`] >>
     gvs[eval_operand_def,GSYM wordsTheory.word_add_n2w,
         AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM,
         AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  rewrite_tac[imm_target_post_def,target_ptr_ok_def,pairTheory.FST,pairTheory.SND] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Abbr `out`,not_fresh_at_def,ASCIInumbersTheory.toString_11] >>
  gvs[]
QED

Theorem immutable_target_attribute_sim_full:
  expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env bt /\
  immutable_root cx bt /\
  imm_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es ==>
  imm_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (AttributeTarget bt fld) es
Proof
  strip_tac >> simp[imm_target_place_sim_full_def] >> rpt gen_tac >> strip_tac >>
  fs[type_place_target_AttributeTarget] >>
  rename1 `type_place_target env bt = SOME (Type bty)` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `?sid. bty = StructT sid` by (Cases_on `bty` >> fs[attribute_type_def]) >>
  gvs[] >>
  drule_then strip_assume_tac compile_get_target_ptr_attr >> gvs[] >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o MATCH_MP compile_get_target_ptr_attr o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa =
             (srb,shadow_sm)` >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
     (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt))` by irule gas_shadow_stmt_get_target_ptr_env >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    metis_tac[ci_mono_emit_op,SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_next_var <= sm.cs_next_var /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func` by metis_tac[fn_has_code_split] >>
  drule_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE[th]) >> REWRITE_TAC[th])
    immutable_target_attribute_source >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _` mp_tac >>
     simp[gas_admissible_def,bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_place_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_place_res_ok_def]) >>
  qpat_x_assum `imm_target_place_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[imm_target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`StructT sid`,`sa`,`sm`,`shadow_sa`,
    `shadow_sm`,`rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_target_place cx bt) _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> simp[])
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_bind,storage_trace_frame_extend_place,
          storage_trace_frame_get_place] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\
                  ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[Abbr `childR`] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]
QED

Resume immutable_target_attribute_sim_full[selected]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx bt (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL (ImmutablePlace NONE id path),mid)` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th]) >> simp[]) >>
  `expr_sim_inv cenv cx env mid` by
    (mp_tac (Q.INST [`s` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `s'` |-> `mid`,`t` |-> `bt`,`r` |-> `INL (ImmutablePlace NONE id path)`]
       aug_place_target_inv) >> simp[expr_sim_inv_gas_obs]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> imm_target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `imm_target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [imm_target_post_def]) >>
  drule_all_then strip_assume_tac immutable_target_field_source >>
  qpat_x_assum `target_ptr_ok _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_ptr_ok_def]) >>
  gvs[target_field_type_def,target_field_offset_def] >>
  rename1 `mem_path_offset itv (path ++ [AttrSubscript fld]) = SOME (_,ftv)` >>
  rename1 `evaluate_subscripts itv iv (path ++ [AttrSubscript fld]) = INL fv` >>
  qmatch_asmsub_abbrev_tac `emit_op ADD [FST rb; Lit (n2w field_off)] sm` >>
  mp_tac (Q.INST [`ee` |-> `mid`, `G` |-> `G1`, `tn` |-> `tn1`,
     `bty` |-> `StructT sid`, `fty` |-> `ty`, `path'` |-> `path ++ [AttrSubscript fld]`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] immutable_target_field_add) >>
  (impl_tac >- (simp[Abbr `field_off`] >> rpt strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (drule_then strip_assume_tac) >> simp[])) >>
  strip_tac >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`,`mid`,`INL (ImmutablePlace NONE id (path ++ [AttrSubscript fld]))`,
    `u`,`tn'`] >> simp[target_root_def] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
      gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  simp[target_through_dynarray_def] >> rpt strip_tac >> gvs[] >>
  irule immutable_target_fixed_snoc >> rpt conj_tac
  >- (qexistsl [`k`,`ptv`] >> simp[] >>
      qpat_assum `evaluate_type _ (StructT sid) = SOME ptv`
        (strip_assume_tac o MATCH_MP evaluate_type_struct_fields) >> simp[])
  >- (qexistsl [`field_off+k`,`ftv`] >> simp[]) >>
  fs[target_through_dynarray_def]
QED

Finalise immutable_target_attribute_sim_full
