(* A field of a target on the joint line: the base target's run, then
   one ADD of the field's offset with no gas mark. *)
Theory bodyFullTargetAttribute
Ancestors
  bodyFullTargetDefs gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr
  bodyFullUnwrapRun targetPtrFacts
  bodyPtrAttributeAdd
  targetPlaceSimCasesBase targetPlaceSim targetPlaceSimDefs
  gasShadowCompile gasShadowCompileHelpers gasShadow gasExemptCert
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
Theorem target_add_suffix_full:
  !rb off sm dst sb func ctx cenv sa t s0 w0 cx st0 trace es pv vt DF lo d ee
   G tn pv' G0 tn0 vt' explicit PG.
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\
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
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  `op_taint tn (FST rb) = {}` by fs[target_ptr_ok_def] >>
  `allocas_from lo t` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_at_def]) >>
  `alloca_inv t` by
    (qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[target_post_def, stmt_state_rel_def]) >>
  qspecl_then [`ADD`, `word_add`, `FST rb`, `Lit (n2w off)`, `sm`, `dst`,
               `sb`, `func`, `ctx`, `t`, `w0`, `n2w off`, `tn`, `DF H`, `PG`,
               `G`] mp_tac
    (Q.GENL [`opc`, `f`, `left`, `right`, `sa`, `dst`, `sb`, `func`, `ctx`,
             `s`, `a`, `b`, `tn`, `D`, `PG`, `G`] attribute_emit_binop_path_ptr) >>
  impl_tac >- simp[eval_operand_def, op_taint_def] >>
  strip_tac >> gvs[] >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id ADD [FST rb; Lit (n2w off)] [out]` >>
  qabbrev_tac `u0 = update_var out (w0 + n2w off) t` >>
  `step_inst_base inst t = OK u0` by
    (simp[Abbr `inst`, Abbr `u0`] >> irule step_ADD >>
     simp[eval_operand_def]) >>
  `run_inst_seq [inst] t = OK u0` by simp[run_inst_seq_def] >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ [inst]` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, Abbr `inst`, Abbr `out`] >>
     strip_tac >> gvs[]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[Abbr `out`, not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  suspend "parts"
QED

Resume target_add_suffix_full[parts]:
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
  (impl_tac >- simp[]) >> strip_tac >>
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

Finalise target_add_suffix_full

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
     (compile_get_target_ptr compile_expr cenv (gas_shadow_target bt))` by
    (mp_tac (MATCH_MP gas_shadow_compiles_get_target_ptr
               (CONJUNCT1 gas_shadow_compile_expr)) >>
     disch_then (qspecl_then [`bt`, `cenv`, `T`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o MATCH_MP compile_get_target_ptr_attr o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa =
             (srb, shadow_sm)` >>
  qspecl_then [`compile_get_target_ptr compile_expr cenv bt`,
               `compile_get_target_ptr compile_expr cenv (gas_shadow_target bt)`,
               `sa`, `shadow_sa`, `rb`, `sm`, `srb`, `shadow_sm`] mp_tac
    (Q.GENL [`f`, `g`, `s`, `t`, `x`, `s'`, `y`, `t'`] gas_shadow_step) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
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
  (impl_tac >- simp[]) >> strip_tac >>
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
  simp[]
QED

Finalise target_attribute_sim_full
