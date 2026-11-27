Theory bodyFullSubscriptTuple
Ancestors exprSimAttributeProps[qualified,ignore_grammar] context[qualified,ignore_grammar]
  bodyFullSubscriptTupleSource bodyFullAttributeAdd bodyPtrAttributeCase
  exprSimTuple exprSimSource exprSimUnwrap exprSimHyps bodySimFull gasOutcomeFullCompose
  gasShadowCompilePure gasShadowCompileStmtHelpers
  gasShadow gasShadowState gasShadowCompile gasExemptCert vyperStorageTrace
  vyperStorageFootprint emitHelperProps exprLoweringProps fragExec
  loweringPosts compileEnv valueEncoding vyperTyping vyperInterpreter
  vyperState vyperAST stateRelProj tupleMemoryLayout typedCopyLayoutPtr
  exprSimHypsDefs[qualified]

Theorem subscript_tuple_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj idx es tys.
    expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = TupleT tys /\ place_type cenv obj = ValPT (TupleT tys) /\
    post_value_type cenv obj = expr_type obj /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >> drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_tuple_subscript >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  `cs_extends sm sb` by
    (drule emit_op_extends >> simp[same_blocks_def, cs_extends_def] >>
     strip_tac >> qexists_tac `[]` >> simp[]) >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
      (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty obj)
         (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
       irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa` >>
     simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    suspend "shadow_extends" >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  `eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) =
   bind (eval_expr cx obj)
     (\r. select_result cx (TupleT tys) r (ValueSubscript (IntV (&k))))` by
    simp[tuple_source] >>
  asm_rewrite_tac[] >>
  irule gas_outcome_full_bind_all >>
  `!res : eval_result + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[exprSimDefsTheory.expr_exit_def]) >> simp[] >>
  rpt conj_tac
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`] >>
  rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume subscript_tuple_vv_sim_full[shadow_extends]:
  drule compile_expr_extends >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
  simp[gas_shadow_expr_def] >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr obj) _) _ = _`
    (mp_then Any mp_tac compile_expr_tuple_subscript) >>
  simp[gas_shadow_place_type] >> strip_tac >>
  drule emit_op_extends >> simp[same_blocks_def, cs_extends_def] >>
  strip_tac >> qexists_tac `[]` >> simp[]
QED

Resume subscript_tuple_vv_sim_full[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `s`] >>
  strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >>
  disch_then strip_assume_tac >> gvs[] >>
  `~s.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[] >>
     `mid with gas_obs := [] = mid` by
       (qpat_x_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `expr_body_pre cenv cx env (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx obj es sa sm s0 mid tv bvv s` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `?w. eval_operand (vv_operand bvv) s = SOME w` by
    (qhdtm_assum `vv_post` (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
     drule bodyPtrAttributeSourceTheory.attribute_vv_holds_read_operand >>
     disch_then (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac)) >>
     qexists_tac `w` >> first_assum ACCEPT_TAC) >>
  drule_all tuple_selected_marked_source >> strip_tac >> gvs[] >>
  rename1 `select_result _ _ _ _ _ = (INL tv',mid)` >>
  `op_taint tn1 (vv_operand bvv) = {}` by
    (Cases_on `bvv` >> gvs[bodyPtrDefsTheory.ptr_vv_ok_def,
       bodyPtrDefsTheory.ptr_val_ok_def, contextTheory.vv_operand_def]) >>
  qabbrev_tac `off = tuple_offset cenv tys (vv_loc bvv) k` >>
  `emit_op ADD [vv_operand bvv; Lit (n2w off)] sm = (p,sb)` by
    gvs[Abbr `off`, exprLoweringTheory.literal_int_index_def] >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD [vv_operand bvv; Lit (n2w off)] [out]` >>
  qabbrev_tac `u = update_var out (w + n2w off) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G2 = step_prov PG G1 i u` >>
  qabbrev_tac `tn2 = step_taint i s u tn1` >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all attribute_add_full_frame >> strip_tac >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G2`, `mid`, `INL tv'`, `t`, `tn2`] >>
  simp[NoAsms] >>
  conj_tac >- metis_tac[tuple_select_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  `vv_post H ctx func cenv cx obj es sa sm s0 mid tv bvv s /\
   ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_x_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  conj_tac >- gvs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  suspend "endpoint_posts"
QED

Resume subscript_tuple_vv_sim_full[endpoint_posts]:
  (* Transport the base post across the very same ADD used in the path. *)
  `vv_post H ctx func cenv cx obj es sa sb s0 mid tv bvv t /\
   eval_operand (vv_operand bvv) t = SOME w` by
    (drule_all attribute_add_vv_post >>
     disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
     `t = update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s
          with vs_inst_idx := SUC s.vs_inst_idx` by simp[] >>
     pop_assum (fn th => rewrite_tac[GSYM th]) >>
     disch_then ACCEPT_TAC) >>
  `eval_operand p t = SOME (w + n2w off)` by
    simp[venomStateTheory.eval_operand_def, venomStateTheory.update_var_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `expr_sim_inv cenv cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_sim_inv cenv cx env mid /\
   eval_result_typed (env,cx,mid) tv (Type (TupleT tys))` by
    (`expr_body_pre cenv cx env obj
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[]) >>
  `!t' op. bvv = StackValue t' op ==> !pl. tv <> PlaceR pl` by
    (rpt strip_tac >>
     gvs[vv_post_def, loweringPostsTheory.vv_at_def, is_word_type_def]) >>
  `vv_place_ptr cenv cx mid t tv bvv` by fs[vv_post_def] >>
  `vv_place_ptr cenv cx mid t tv' (LocatedValue (EL k tys) (mk_ptr p (vv_loc bvv)))` by
    (match_mp_tac tuple_place_ptr >>
     qexistsl_tac [`env`, `mid`, `tv`, `tys`, `tvs`, `k`, `mid`, `w`] >>
     simp[]) >>
  drule exprSimPropsTheory.select_result_memory_place >> strip_tac >>
  conj_asm1_tac
  >- (match_mp_tac tuple_vv_post >> qexistsl_tac [`env`, `tv`, `w`, `tvs`, `vs`] >>
      simp[IgnAsm `t = _`]) >>
  suspend "remaining_posts"
QED

Resume subscript_tuple_vv_sim_full[remaining_posts]:
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule exprSimAttributeFieldsTheory.opt_mmap_el >> simp[]) >>
  `vv_loc bvv = LocMemory ==>
     off = SUM (MAP type_memory_size (TAKE k tvs)) /\
     off + type_memory_size (EL k tvs) <= type_memory_size (TupleTV tvs) /\
     w2n (w + n2w off) = w2n w + off /\
     (type_memory_size (EL k tvs) = 0 \/
      w2n (w + n2w off) + type_memory_size (EL k tvs) <= t.vs_alloca_next)` by
    suspend "memory_geometry" >>
  `type_memory_bytes cenv
     (lowered_value_type cenv (Subscript (EL k tys) obj (Literal ity (IntL (&k))))) =
   type_memory_size (EL k tvs)` by
    (simp[exprLoweringTheory.lowered_value_type_def, expr_type_def] >>
     drule_all expr_sim_inv_memory_size >> simp[]) >>
  `vv_loc bvv = LocMemory ==>
   ptr_mem_ok cx (TupleT tys) (ArrayV (TupleV vs)) (vv_operand bvv) G1 tn1 s` by
    suspend "base_mem_ptr" >>
  `vv_loc bvv = LocMemory ==>
   ptr_buf_ok cenv (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) p G2 t` by
    suspend "ptr_buffer" >>
  conj_tac >- suspend "store_bound" >>
  conj_tac >- (drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >>
               simp[venomStateTheory.update_var_def]) >>
  conj_tac >- (drule emitted_insts_emit_op >> strip_tac >>
               drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >> simp[]) >>
  conj_tac >- suspend "alloca_history" >>
  conj_tac >- (strip_tac >> fs[ptrDisciplineTheory.allocas_below_fmp_def,
                              venomStateTheory.update_var_def] >>
               first_assum ACCEPT_TAC) >>
  conj_tac >- simp[venomStateTheory.update_var_def] >>
  conj_tac >- (qpat_x_assum `out = STRING _ _` SUBST_ALL_TAC >>
               drule_all attribute_fresh_full_ghost_update >> strip_tac >> gvs[]) >>
  conj_tac >- suspend "selected_ptr" >>
  conj_tac >- suspend "owned_value" >>
  conj_tac >- suspend "code_robust" >>
  conj_tac >- (simp[contextTheory.mk_ptr_def, NoAsms] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `out = STRING _ _` SUBST_ALL_TAC >>
  drule_all attribute_fresh_full_ghost_update >> strip_tac >> gvs[]
QED

Resume subscript_tuple_vv_sim_full[alloca_history]:
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (drule emit_op_extends >> simp[same_blocks_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sm.cs_current_insts) = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base i s = OK u` by
    simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def,
         venomStateTheory.eval_operand_def] >>
  `alloca_inv s` by
    (qpat_assum `vv_post H _ _ _ _ obj _ sa sm _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME i` by simp[] >>
  drule_all allocaHistoryTheory.alloca_history_base_step >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Resume subscript_tuple_vv_sim_full[code_robust]:
  simp[contextTheory.vv_location_def, contextTheory.mk_ptr_def, NoAsms] >>
  strip_tac >>
  `vv_location bvv = SOME LocCode` by fs[exprSimAttributePropsTheory.vv_loc_def, AllCaseEqs()] >>
  `off = SUM (MAP type_memory_size (TAKE k tvs))` by
    (`elem_size_in_location cenv LocCode = elem_size_in_location cenv LocMemory` by
       simp[FUN_EQ_THM, compileEnvTheory.elem_size_in_location_def,
            compileEnvTheory.is_slot_addressed_def] >>
     drule_all tuple_offset_memory >> disch_then (qspec_then `k` mp_tac) >>
     simp[tuple_offset_def, listTheory.MAP_TAKE]) >>
  `k < LENGTH tvs` by simp[] >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule exprSimAttributeFieldsTheory.opt_mmap_el >> simp[]) >>
  `off + type_memory_size (EL k tvs) <= type_memory_size (TupleTV tvs)` by
    (drule tuple_element_interval >>
     simp[valueEncodingTheory.type_memory_size_def,
          valueEncodingProofsTheory.type_memory_size_list_sum]) >>
  `vv_holds cenv cx (TupleT tys) tv bvv mid s` by
    (qpat_assum `vv_post H _ _ _ _ obj es sa sm s0 mid tv bvv s`
       (mp_tac o cj 3 o REWRITE_RULE [vv_post_def]) >>
     qpat_assum `post_value_type cenv obj = TupleT tys` (fn th => rewrite_tac[th])) >>
  `immutable_holds cenv cx (TupleT tys) tv w mid s` by
    (Cases_on `bvv` >>
     gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def, vv_holds_def]) >>
  `immutable_holds cenv cx (TupleT tys) (Value (ArrayV (TupleV vs))) w mid s` by
    metis_tac[reasonEndpointResourcesPtrTheory.immutable_holds_read_value] >>
  drule_all exprSimCopyTheory.immutable_holds_bounds >> strip_tac >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule exprSimAttributePropsTheory.field_ptr_w2n >>
     qexistsl_tac [`type_memory_size (EL k tvs)`, `type_memory_size (TupleTV tvs)`] >> simp[]) >>
  qpat_assum `cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==> _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `EL k vs` >>
  simp[expr_type_def, contextTheory.vv_operand_def, contextTheory.mk_ptr_def,
       IgnAsm `t = _`, IgnAsm `p = _`, IgnAsm `out = _`, IgnAsm `off = _`] >>
  `t.vs_memory = s.vs_memory` by simp[venomStateTheory.update_var_def] >>
  `!m. mem_agree_outside tn1.t_mem s.vs_memory m ==>
       tuple_in_memory vs tvs (w2n w) m` by
    fs[valueEncodingDefsTheory.val_in_memory_def] >>
  qx_gen_tac `mem` >> strip_tac >>
  `tuple_in_memory vs tvs (w2n w) mem` by
    (qpat_assum `!m. _ ==> tuple_in_memory _ _ _ m`
       (qspec_then `mem` irule) >>
     qpat_assum `mem_agree_outside _ t.vs_memory mem` mp_tac >>
     qpat_assum `t.vs_memory = s.vs_memory` (fn th => rewrite_tac[th])) >>
  qpat_assum `off = SUM _` SUBST1_TAC >>
  rewrite_tac[Once arithmeticTheory.ADD_COMM] >>
  irule tuple_in_memory_element >> simp[]
QED

Resume subscript_tuple_vv_sim_full[memory_geometry]:
  strip_tac >>
  `off = SUM (MAP type_memory_size (TAKE k tvs))` by
    (drule_all tuple_offset_memory >> disch_then (qspec_then `k` mp_tac) >>
     simp[listTheory.MAP_TAKE]) >>
  `k < LENGTH tvs` by simp[] >>
  `off + type_memory_size (EL k tvs) <= type_memory_size (TupleTV tvs)` by
    (drule tuple_element_interval >>
     simp[valueEncodingTheory.type_memory_size_def,
          valueEncodingProofsTheory.type_memory_size_list_sum]) >>
  `stmt_state_rel H ctx func cenv cx mid t /\
   vv_at cenv cx (TupleT tys) sa sb mid tv bvv t` by
    (qpat_assum `vv_post H _ _ _ _ obj es sa sb s0 mid tv bvv t`
       (mp_tac o REWRITE_RULE [vv_post_def]) >> simp[]) >>
  `type_memory_size (TupleTV tvs) = 0 \/
   (?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
                w2n w + type_memory_size (TupleTV tvs) <= b + sz) \/
   (?n b sz. local_region cenv mid.scopes t n b sz /\
             w2n w + type_memory_size (TupleTV tvs) <= b + sz)` by
    (qpat_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `eval_operand (vv_operand bvv) t = SOME w` mp_tac >>
     qpat_assum `vv_loc bvv = LocMemory` mp_tac >>
     qpat_assum `evaluate_type _ (TupleT tys) = SOME _` mp_tac >>
     qpat_assum `read_result cx tv mid = (INL _,mid)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bvv` >>
     simp[vv_at_def, expr_val_at_def, exprSimAttributePropsTheory.vv_loc_def,
          contextTheory.vv_location_def, contextTheory.vv_operand_def,
          is_word_type_def] >> rpt strip_tac >>
     gs[val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
     metis_tac[]) >>
  `type_memory_size (TupleTV tvs) <> 0 ==>
   w2n w + type_memory_size (TupleTV tvs) < dimword (:256) /\
   w2n w + type_memory_size (TupleTV tvs) <= t.vs_alloca_next` by
    (simp[] >> strip_tac >>
     drule exprSimPropsTheory.stmt_state_rel_region_lt >> strip_tac >>
     (conj_tac
      >- ((qpat_assum `!a b sz. FLOOKUP t.vs_allocas a = SOME (b,sz) ==> _` drule ORELSE
           qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz ==> _` drule) >>
          decide_tac) >>
      (FIRST [
        drule_all bodyMemoryDefsTheory.body_local_region_frontier,
        drule stmt_state_rel_local_ptrs_alloca >>
        pure_rewrite_tac[venomMemDefsTheory.alloca_inv_def,
                         venomMemDefsTheory.alloca_next_valid_def] >>
        strip_tac >> qpat_assum `!a b sz. FLOOKUP t.vs_allocas a = SOME (b,sz) ==> _ <= _` drule
       ] >> simp[venomStateTheory.update_var_def] >> decide_tac))) >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule exprSimAttributePropsTheory.field_ptr_w2n >>
     qexistsl_tac [`type_memory_size (EL k tvs)`, `type_memory_size (TupleTV tvs)`] >>
     simp[] >> decide_tac) >>
  Cases_on `type_memory_size (TupleTV tvs) = 0` >> gvs[]
QED

Resume subscript_tuple_vv_sim_full[store_bound]:
  Cases_on `vv_loc bvv = LocMemory`
  >- (simp[exprLoweringTheory.lowered_value_type_def, expr_type_def, NoAsms] >>
      qpat_assum `vv_post H _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ _`
        (mp_then Any mp_tac exprSimMemDefsTheory.vv_store_bound_capacity) >>
      disch_then (qspecl_then [`w + n2w off`, `EL k tvs`] mp_tac) >>
      simp[contextTheory.mk_ptr_def, post_value_type_def, expr_type_def,
           IgnAsm `t = _`, IgnAsm `p = _`, IgnAsm `off = _`,
           IgnAsm `vv_loc bvv = LocMemory`] >>
      disch_then irule >>
      qpat_assum `vv_loc bvv = LocMemory ==> _ /\ _`
        (drule_then (mp_tac o cj 4)) >> decide_tac) >>
  irule exprSimMemDefsTheory.vv_store_bound_nonmem >> simp[contextTheory.mk_ptr_def]
QED

Resume subscript_tuple_vv_sim_full[owned_value]:
  simp[post_value_type_def, expr_type_def, contextTheory.mk_ptr_def, NoAsms] >>
  rpt strip_tac >>
  `?bv. tv = Value bv` by
    (qpat_x_assum `select_result _ _ tv _ _ = _` mp_tac >>
     Cases_on `tv` >> simp[select_result_def] >>
     strip_tac >> drule vyperPlaceResultTypingTheory.extend_place_result_shape >> simp[]) >>
  rename1 `tv = Value bv` >>
  `vv_own cenv cx (TupleT tys) sa sm mid tv bvv s /\ vv_loc bvv = LocMemory` by
    (qpat_assum `!v. tv = Value v /\ _ ==> _` (qspec_then `bv` mp_tac) >>
     Cases_on `bvv` >> simp[is_word_type_def, is_bytestring_type_def,
       exprSimAttributePropsTheory.vv_loc_def, contextTheory.vv_location_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
                    finite_mapTheory.FLOOKUP_UPDATE, loweringStateRelDefsTheory.not_fresh_at_def] >>
     qpat_assum `sa.cs_next_var <= sm.cs_next_var` (mp_tac) >>
     metis_tac[]) >>
  `vv_own cenv cx (TupleT tys) sa sb mid tv bvv t` by
    (irule exprSimVVFrameTheory.vv_own_vars_frame >> qexistsl_tac [`s`, `sm`] >>
     simp[venomStateTheory.update_var_def, IgnAsm `t = _`] >>
     conj_tac >- (drule emitted_insts_emit_op >> simp[]) >>
     rpt strip_tac >>
     drule_all exprSimCopyTheory.copy_buffer_local_region_frame >>
     disch_then (once_rewrite_tac o single o GSYM) >> simp[]) >>
  `vv_own cenv cx (TupleT tys) sa sb mid tv
     (LocatedValue (TupleT tys) (mk_ptr (vv_operand bvv) LocMemory)) t` by
    (qpat_assum `vv_own _ _ _ sa sb mid tv bvv t` mp_tac >>
     qpat_assum `vv_loc bvv = LocMemory` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bvv` >>
     simp[vv_own_def, expr_val_own_def, contextTheory.vv_operand_def,
          contextTheory.mk_ptr_def, exprSimAttributePropsTheory.vv_loc_def,
          contextTheory.vv_location_def, is_word_type_def] >> metis_tac[]) >>
  `off + val_footprint (EL k tvs) (EL k vs) <=
    val_footprint (TupleTV tvs) (ArrayV (TupleV vs))` by
    ((drule typedCopyLayoutPtrTheory.tuple_child_footprint_contained >>
     disch_then (qspec_then `k` mp_tac) >>
     simp[val_footprint_def, valueEncodingTheory.type_memory_size_def,
       valueEncodingProofsTheory.type_memory_size_list_sum,
       IgnAsm `off = _`, IgnAsm `vv_loc bvv = LocMemory`] >> (simp[]))) >>
  `vv_own cenv cx (EL k tys) sa sb mid tv'
     (LocatedValue (EL k tys) (mk_ptr p LocMemory)) t` by
    (irule exprSimVVFrameTheory.vv_own_memory_slice >>
     goal_assum (drule_at (Pat `vv_own _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `read_result cx tv mid = _`)) >>
     goal_assum (drule_at (Pat `read_result cx tv' mid = _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ (TupleT tys) = _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ (EL k tys) = _`)) >>
     goal_assum (drule_at (Pat `eval_operand (vv_operand bvv) t = _`)) >>
     goal_assum (drule_at (Pat `eval_operand p t = _`)) >>
     qexists_tac `off` >>
     simp[IgnAsm `off = _`, IgnAsm `t = _`, IgnAsm `p = _`]) >>
  pop_assum mp_tac >>
  simp[contextTheory.mk_ptr_def, IgnAsm `t = _`, IgnAsm `p = _`]
QED

Resume subscript_tuple_vv_sim_full[base_mem_ptr]:
  qpat_assum `ptr_vv_ok cx (TupleT tys) tv bvv mid G1 tn1 s` mp_tac >>
  qpat_assum `read_result cx tv mid = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bvv` >>
  simp[bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_val_ok_def,
       exprSimAttributePropsTheory.vv_loc_def, contextTheory.vv_location_def,
       contextTheory.vv_operand_def, is_word_type_def]
QED

Resume subscript_tuple_vv_sim_full[ptr_buffer]:
  strip_tac >>
  qpat_assum `vv_loc bvv = LocMemory ==> _ /\ _`
    (fn th => drule_then strip_assume_tac th) >>
  pure_rewrite_tac[bodyPtrDefsTheory.ptr_buf_ok_def] >>
  qx_gen_tac `wp` >> strip_tac >>
  `wp = w + n2w off` by
    (qpat_assum `eval_operand p t = SOME (w + n2w off)` mp_tac >>
     qpat_assum `eval_operand p t = SOME wp` (fn th => rewrite_tac[th]) >> simp[NoAsms]) >>
  `type_memory_size (EL k tvs) <> 0` by
    (qpat_assum `type_memory_bytes cenv (lowered_value_type cenv (Subscript _ _ _)) = _`
       (fn th => qpat_assum `type_memory_bytes cenv _ <> 0`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `type_memory_size (TupleTV tvs) <> 0` by decide_tac >>
  qpat_assum `vv_loc bvv = LocMemory ==> ptr_mem_ok _ _ _ _ _ _ _`
    (drule_then (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_mem_ok_def])) >>
  disch_then (qspecl_then [`TupleTV tvs`, `w`] mp_tac) >>
  simp[val_footprint_def, exprSimPropsTheory.val_store_size_def, NoAsms] >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mp_tac o cj 2) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `x` (qx_choose_then `b` (qx_choose_then `sz` strip_assume_tac))) >>
  qexistsl_tac [`out`, `b`, `sz`] >>
  `FLOOKUP G2 out = SOME (b,sz)` by
    (qpat_assum `FLOOKUP G2 out = _` SUBST1_TAC >>
     qpat_assum `vv_operand bvv = Var x` SUBST1_TAC >>
     simp[ptrDisciplineTheory.op_prov_def, NoAsms] >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  qpat_assum `wp = _` SUBST1_TAC >>
  qpat_assum `w2n (w + n2w off) = _` SUBST1_TAC >>
  qpat_assum `type_memory_bytes cenv (lowered_value_type cenv (Subscript _ _ _)) = _` SUBST1_TAC >>
  decide_tac
QED

Resume subscript_tuple_vv_sim_full[selected_ptr]:
  Cases_on `vv_loc bvv = LocMemory`
  >- suspend "selected_ptr_memory" >>
  suspend "selected_ptr_nonmemory"
QED

Resume subscript_tuple_vv_sim_full[selected_ptr_memory]:
  irule bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
  simp[contextTheory.mk_ptr_def, expr_type_def, NoAsms] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `EL k vs` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule bodyPtrAttributeFieldsTheory.ptr_mem_ok_of_buffer >>
  goal_assum (drule_at (Pat `type_memory_bytes _ _ = _`)) >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >~ [`val_wf _ _`]
  >- (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
      qpat_assum `values_have_types tvs vs` mp_tac >>
      rewrite_tac[vyperTypeDefaultsTheory.values_have_types_LIST_REL,
                  listTheory.LIST_REL_EL_EQN] >> strip_tac >> simp[]) >>
  `t.vs_memory = s.vs_memory` by simp[venomStateTheory.update_var_def] >>
  qpat_assum `vv_loc bvv = LocMemory ==> _ /\ _`
    (drule_then (fn th => assume_tac (cj 1 th) >> assume_tac (cj 3 th))) >>
  `!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
         tuple_in_memory vs tvs (w2n w) mem` by
    (qpat_assum `vv_loc bvv = LocMemory ==> ptr_mem_ok _ _ _ _ _ _ _`
       (drule_then (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_mem_ok_def])) >>
     disch_then (qspecl_then [`TupleTV tvs`, `w`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[valueEncodingDefsTheory.val_in_memory_def, NoAsms]) >>> NTH_GOAL (simp[]) 2 >>
  qx_genl_tac [`wp`, `mem`] >> strip_tac >>
  `wp = w + n2w off` by
    (qpat_assum `eval_operand p t = SOME (w + n2w off)` mp_tac >>
     qpat_assum `eval_operand p t = SOME wp` (fn th => rewrite_tac[th]) >> simp[NoAsms]) >>
  `tuple_in_memory vs tvs (w2n w) mem` by
    (qpat_assum `!m. _ ==> tuple_in_memory _ _ _ m` (qspec_then `mem` irule) >>
     qpat_assum `t.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     qpat_assum `tn2.t_mem = tn1.t_mem` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `wp = _` SUBST1_TAC >>
  qpat_assum `w2n (w + n2w off) = _` SUBST1_TAC >>
  qpat_assum `off = SUM _` SUBST1_TAC >>
  irule tuple_in_memory_element >> simp[]
QED

Resume subscript_tuple_vv_sim_full[selected_ptr_nonmemory]:
  irule bodyPtrAttributeFieldsTheory.ptr_vv_ok_nonmemory >>
  simp[contextTheory.mk_ptr_def, expr_type_def, NoAsms] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (strip_tac >>
      `op_prov G1 (vv_operand bvv) = NONE` by
        (qpat_assum `ptr_vv_ok cx (TupleT tys) tv bvv mid G1 tn1 s` mp_tac >>
         qpat_assum `vv_loc bvv = LocCode` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bvv` >>
         simp[bodyPtrDefsTheory.ptr_vv_ok_def, exprSimAttributePropsTheory.vv_loc_def,
              contextTheory.vv_location_def, contextTheory.vv_operand_def]) >>
      qpat_assum `p = Var out` SUBST1_TAC >>
      simp[ptrDisciplineTheory.op_prov_def, IgnAsm `G2 = _`, IgnAsm `out = _`]) >>
  qexists_tac `EL k tvs` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`wp`, `j`, `b`] >> strip_tac >>
  `wp = w + n2w off` by
    (qpat_assum `eval_operand p t = SOME (w + n2w off)` mp_tac >>
     qpat_assum `eval_operand p t = SOME wp` (fn th => rewrite_tac[th]) >> simp[NoAsms]) >>
  `type_slot_size (EL k tvs) <> 0` by decide_tac >>
  `k < LENGTH tvs` by simp[] >>
  `vv_loc bvv = LocStorage \/ vv_loc bvv = LocTransient ==>
   off = tuple_prefix_slot_size k tvs` by
    (strip_tac >>
     `MAP (elem_size_in_location cenv (vv_loc bvv)) tys = MAP type_slot_size tvs` by
       (irule listTheory.LIST_EQ >> simp[listTheory.EL_MAP] >>
        qx_gen_tac `j'` >> strip_tac >>
        `evaluate_type (get_tenv cx) (EL j' tys) = SOME (EL j' tvs)` by
          (drule exprSimAttributeFieldsTheory.opt_mmap_el >> simp[]) >>
        `type_memory_bytes cenv (EL j' tys) = type_memory_size (EL j' tvs)` by
          (drule_all expr_sim_inv_memory_size >> simp[]) >>
        simp[compileEnvTheory.elem_size_in_location_def, compileEnvTheory.is_slot_addressed_def,
             exprSimFieldLayoutTheory.slot_count_of_memory_size]) >>
     simp[tuple_offset_def, tuple_prefix_slot_size_sum, listTheory.MAP_TAKE,
          IgnAsm `off = _`] >>
     qpat_assum `off = _` SUBST1_TAC >>
     simp[tuple_offset_def, tuple_prefix_slot_size_sum, listTheory.MAP_TAKE]) >>
  `tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <=
   type_slot_size (TupleTV tvs)` by
    (qspecl_then [`MAP type_slot_size tvs`, `k`] mp_tac sum_take_el_le >>
     simp[listTheory.EL_MAP, listTheory.MAP_TAKE, tuple_prefix_slot_size_sum,
          vyperValueTheory.type_slot_size_def, vyperStorageRegionWriteTheory.type_slot_size_list_sum]) >>
  `vv_holds cenv cx (TupleT tys) tv bvv mid s` by
    (qpat_assum `vv_post H _ _ _ _ obj es sa sm s0 mid tv bvv s`
       (mp_tac o cj 3 o REWRITE_RULE [vv_post_def]) >>
     qpat_assum `post_value_type cenv obj = TupleT tys` (fn th => rewrite_tac[th])) >>
  `vv_loc bvv = LocStorage \/ vv_loc bvv = LocTransient ==>
   w2n w + type_slot_size (TupleTV tvs) <= dimword (:256)` by
    (qpat_assum `vv_holds cenv cx (TupleT tys) tv bvv mid s` mp_tac >>
     qpat_assum `eval_operand (vv_operand bvv) s = SOME w` mp_tac >>
     qpat_assum `evaluate_type _ (TupleT tys) = SOME (TupleTV tvs)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bvv` >>
     simp[vv_holds_def, exprSimAttributePropsTheory.vv_loc_def,
          contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
     rpt strip_tac >>
     gvs[storage_holds_def, accountsRelPropsTheory.storage_range_agree_def]) >>
  `vv_loc bvv = LocStorage \/ vv_loc bvv = LocTransient ==>
   w2n wp = w2n w + tuple_prefix_slot_size k tvs` by
    (disch_tac >>
     `off = tuple_prefix_slot_size k tvs /\
      w2n w + type_slot_size (TupleTV tvs) <= dimword (:256)` by
       (conj_tac >> first_assum (drule_then ACCEPT_TAC)) >>
     qpat_assum `off = tuple_prefix_slot_size k tvs` (SUBST1_TAC o SYM) >>
     qpat_assum `wp = _` SUBST1_TAC >>
     irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  (* The ADD changes neither storage nor the storage taint sets. *)
  `t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_transient = s.vs_transient` by simp[venomStateTheory.update_var_def] >>
  conj_tac >> strip_tac >>
  `w2n wp = w2n w + tuple_prefix_slot_size k tvs` by simp[] >>
  `w2n w <= w2n j /\ w2n j < w2n w + type_slot_size (TupleTV tvs)` by decide_tac >>
  `((vv_loc bvv = LocStorage /\ (j,b) IN tn1.t_stor) ==>
      dead_bytes_list (s.vs_accounts s.vs_call_ctx.cc_address).storage (w2n w) tvs (w2n j) b) /\
   ((vv_loc bvv = LocTransient /\ (j,b) IN tn1.t_trans) ==>
      dead_bytes_list (s.vs_transient s.vs_call_ctx.cc_address) (w2n w) tvs (w2n j) b)` by
    (qpat_assum `ptr_vv_ok cx (TupleT tys) tv bvv mid G1 tn1 s` mp_tac >>
     qpat_assum `eval_operand (vv_operand bvv) s = SOME w` mp_tac >>
     qpat_assum `evaluate_type _ (TupleT tys) = SOME (TupleTV tvs)` mp_tac >>
     qpat_assum `w2n w <= w2n j` mp_tac >>
     qpat_assum `w2n j < w2n w + type_slot_size (TupleTV tvs)` mp_tac >>
     qpat_assum `b < 32` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bvv` >>
     simp[bodyPtrDefsTheory.ptr_vv_ok_def, exprSimAttributePropsTheory.vv_loc_def,
          contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
     rpt strip_tac >>
     first_x_assum (qspecl_then [`j`, `b`] mp_tac) >>
     simp[loweringStateRelDefsTheory.dead_bytes_def]) >>
  qpat_assum `tn2.t_stor = tn1.t_stor` (fn th => rule_assum_tac (ONCE_REWRITE_RULE [th])) >>
  qpat_assum `tn2.t_trans = tn1.t_trans` (fn th => rule_assum_tac (ONCE_REWRITE_RULE [th])) >>
  qpat_assum `t.vs_accounts = s.vs_accounts` SUBST1_TAC >>
  qpat_assum `t.vs_call_ctx = s.vs_call_ctx` SUBST1_TAC >>
  qpat_assum `t.vs_transient = s.vs_transient` SUBST1_TAC >>
  qpat_assum `w2n wp = _` SUBST1_TAC >>
  irule accountsRelPropsTheory.dead_bytes_list_el >>
  rpt conj_tac >> simp[] >> decide_tac
QED

Finalise subscript_tuple_vv_sim_full
