(* The attribute read over the finite-horizon joint judgments: the base's
   value judgment, then one ADD of the field offset, with the source GAS
   marks, memory posts and pointer ghosts on one witness at (DF H, lo).
   The value judgment comes from the vv one by bodyFullOfVV.
 *
 * TOP-LEVEL:
 *   attribute_vv_sim_full -- the vv judgment of e.fld from that of e
 *   attribute_expr_full_ok -- body_expr_full_ok of e.fld from that of e
 *)
Theory bodyFullAttribute
Ancestors
  bodyFullAttributeAdd bodyFullAttributeFields bodyPtrAttributeSelection
  bodyAttributeMemory gasOutcomeFullCompose exprSimHyps exprLoweringProps
  bodyFullOfVV bodyFullPreds bodyFullSimProjection bodySimFull
  exprSimAttribute exprSimHypsDefs gasShadow
  gasShadowState gasShadowCompile gasExemptCert vyperStorageTrace vyperStorageFootprint
  emitHelperProps fragExec exprSimUnwrap
  loweringPosts compileEnv valueEncoding vyperTyping
  vyperInterpreter vyperState vyperAST

val _ = Parse.hide "body";

Theorem attribute_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj fld es.
    expr_body_pre cenv cx env (Attribute ann obj fld) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty obj es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Attribute ann obj fld) es
Proof
  rpt gen_tac >> strip_tac >> drule attr_pre_base >> strip_tac >>
  `post_value_type cenv obj = expr_type obj` by
    (drule_all attr_post_value_type >> simp[]) >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_shadow_compiles (compile_expr cenv ty obj)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
      (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`, `shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa` >>
     simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (drule compile_expr_extends >> strip_tac >>
     qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Attribute _ _ _)) _ = _`
       mp_tac >> simp[gas_shadow_expr_def] >>
     disch_then (strip_assume_tac o MATCH_MP compile_expr_attribute) >>
     gvs[] >> drule attr_extends >> simp[]) >>
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
  `eval_expr cx (Attribute ann obj fld) =
   bind (eval_expr cx obj) (\r. select_result cx (expr_type obj) r (AttrSubscript fld))` by
    simp[FUN_EQ_THM, eval_expr_attribute] >>
  asm_rewrite_tac[] >>
  irule gas_outcome_full_bind_all >>
  `!res : eval_result + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[]) >>
  simp[] >>
  rpt conj_tac
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`] >>
  rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume attribute_vv_sim_full[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `s`] >>
  strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >>
  disch_then strip_assume_tac >> gvs[] >>
  `vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx obj es sa sm s0 mid tv bvv s` by metis_tac[] >>
  `~s.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[] >>
     `mid with gas_obs := [] = mid` by
       (qpat_x_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `expr_body_pre cenv cx env (Attribute ann obj fld)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all bodyPtrAttributeSourceTheory.attribute_typed_selection >> strip_tac >>
  `op_taint tn1 (vv_operand bvv) = {}` by
    (Cases_on `bvv` >> gvs[bodyPtrDefsTheory.ptr_vv_ok_def,
       bodyPtrDefsTheory.ptr_val_ok_def, contextTheory.vv_operand_def]) >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id ADD
    [vv_operand bvv; Lit (n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld))] [out]` >>
  qabbrev_tac `u = update_var out (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G2 = step_prov PG G1 i u` >>
  qabbrev_tac `tn2 = step_taint i s u tn1` >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all attribute_add_full_frame >> strip_tac >>
  `sid' = sid` by metis_tac[vyperASTTheory.type_11] >>
  qpat_x_assum `sid' = sid` SUBST_ALL_TAC >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G2`, `mid`, `INL tv'`, `t`, `tn2`] >>
  simp[NoAsms] >>
  conj_tac
  >- simp[bodyPtrAttributeObservationTheory.select_attr_gas_update] >>
  qx_gen_tac `H` >> strip_tac >>
  `vv_post H ctx func cenv cx obj es sa sm s0 mid tv bvv s /\
   ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  conj_tac
  >- gvs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  suspend "endpoint_posts"
QED

Resume attribute_vv_sim_full[endpoint_posts]:
  drule_all bodyPtrAttributeCaseTheory.attribute_add_vv_post >>
  disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  `t = update_var (STRING #"%" (toString sm.cs_next_var))
      (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) s
      with vs_inst_idx := SUC s.vs_inst_idx` by simp[] >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >> strip_tac >>
  `eval_operand p t = SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld))` by
    simp[venomStateTheory.eval_operand_def, venomStateTheory.update_var_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `?v. select_result cx (expr_type obj) tv (AttrSubscript fld) mid = (INL v,mid) /\
       vv_post H ctx func cenv cx (Attribute ann obj fld) es sa sb s0 mid v
         (LocatedValue ann (mk_ptr p (vv_loc bvv))) t` by
    (irule attribute_selected_vv_post >>
     metis_tac[]) >>
  `v = tv'` by gvs[vyperASTTheory.type_11] >>
  qpat_x_assum `v = tv'` SUBST_ALL_TAC >>
  `?pv. select_result cx (expr_type obj) tv (AttrSubscript fld) mid = (INL pv,mid) /\
    ptr_vv_ok cx ann pv (LocatedValue ann (mk_ptr p (vv_loc bvv))) mid G2 tn2 t /\
    (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv (Attribute ann obj fld) p G2 t)` by
    suspend "pointer_posts" >>
  `pv = tv'` by gvs[vyperASTTheory.type_11] >>
  qpat_x_assum `pv = tv'` SUBST_ALL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "store_bound" >>
  conj_tac >- suspend "current_bb" >>
  conj_tac >- suspend "inst_idx" >>
  conj_tac >- suspend "alloca_history" >>
  conj_tac >- (strip_tac >>
               fs[ptrDisciplineTheory.allocas_below_fmp_def,
                  venomStateTheory.update_var_def] >>
               first_assum ACCEPT_TAC) >>
  conj_tac >- simp[venomStateTheory.update_var_def] >>
  conj_tac >- suspend "ghost_inv" >>
  conj_tac >- suspend "selected_ptr" >>
  conj_tac >- suspend "owned_value" >>
  conj_tac >- suspend "code_field" >>
  conj_tac >- suspend "ptr_buf" >>
  suspend "ghost_kept"
QED

Resume attribute_vv_sim_full[current_bb]:
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
      compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
      compileEnvTheory.emit_def, venomStateTheory.update_var_def]
QED

Resume attribute_vv_sim_full[inst_idx]:
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
      compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
      compileEnvTheory.emit_def]
QED

Resume attribute_vv_sim_full[store_bound]:
  `expr_body_pre cenv cx env obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `!v. read_result cx tv mid = (INL v,mid) ==> value_has_type (StructTV fs) v` by
    (gvs[] >> metis_tac[]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by simp[venomStateTheory.update_var_def] >>
  drule_all attr_field_store_bound >>
  simp[vyperASTTheory.expr_type_def, exprLoweringTheory.lowered_value_type_def]
QED

Resume attribute_vv_sim_full[ghost_inv]:
  qpat_x_assum `out = STRING _ _` SUBST_ALL_TAC >>
  drule_all attribute_fresh_full_ghost_update >> strip_tac >>
  gvs[]
QED

Resume attribute_vv_sim_full[ghost_kept]:
  qpat_x_assum `out = STRING _ _` SUBST_ALL_TAC >>
  drule_all attribute_fresh_full_ghost_update >> strip_tac >>
  qpat_x_assum `!w s'' n. _` (qspecl_then [`w`, `s`, `0`] mp_tac) >>
  simp[]
QED

Resume attribute_vv_sim_full[owned_value]:
  qx_gen_tac `child` >> strip_tac >>
  `?sv. tv = Value sv` by
    (Cases_on `tv` >> simp[] >>
     qpat_x_assum `select_result _ _ _ _ _ = (INL tv',_)`
       (mp_tac o MATCH_MP vyperPlaceResultTypingTheory.extend_place_result_shape o
        REWRITE_RULE [select_result_def]) >> simp[]) >>
  `vv_own cenv cx (StructT sid) sa sm mid tv bvv s /\
   vv_loc bvv = LocMemory` by
    (qpat_x_assum `!v. tv = Value v /\ _ ==> _` mp_tac >>
     simp[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
     strip_tac >> Cases_on `bvv` >>
     gvs[exprSimAttributePropsTheory.vv_loc_def, contextTheory.vv_location_def]) >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (rpt strip_tac >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  `!n lb sz. local_region cenv mid.scopes t n lb sz ==>
             local_region cenv mid.scopes s n lb sz` by
    (rpt strip_tac >>
     qpat_x_assum `local_region _ _ t _ _ _` mp_tac >>
     simp[loweringStateRelDefsTheory.local_region_def,
          venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >>
     qmatch_asmsub_rename_tac `PtrVar (Var local_ptr) sz` >>
     `not_fresh_at sa local_ptr` by
       (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
     gvs[] >> metis_tac[]) >>
  `vv_own cenv cx (StructT sid) sa sb mid tv bvv t` by
    (irule exprSimVVFrameTheory.vv_own_vars_frame >>
     qexistsl_tac [`s`, `sm`] >>
     simp[venomStateTheory.update_var_def] >>
     drule emitted_insts_emit_op >> simp[]) >>
  `vv_own cenv cx (StructT sid) sa sb mid tv
     (LocatedValue (StructT sid) (mk_ptr (vv_operand bvv) LocMemory)) t` by
    (qpat_x_assum `vv_own _ _ _ sa sb _ _ _ t` mp_tac >>
     qpat_x_assum `vv_loc bvv = LocMemory` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bvv` >>
     simp[vv_own_def, expr_val_own_def, contextTheory.mk_ptr_def,
         contextTheory.vv_operand_def, exprSimAttributePropsTheory.vv_loc_def,
         contextTheory.vv_location_def, compileEnvTheory.is_word_type_def] >>
     metis_tac[]) >>
  `w2n (w + n2w (struct_field_offset
       (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)) =
     w2n w + struct_field_offset
       (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld` by
    (drule_all bodyPtrAttributeSourceTheory.attribute_memory_field_address >> simp[]) >>
  `struct_field_offset
       (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld +
     val_footprint ftv fv <= val_footprint (StructTV fs) (StructV vals)` by
    (`val_footprint ftv fv <= type_memory_size ftv` by
       simp[exprSimPropsTheory.val_footprint_le] >>
     drule_all exprSimFieldLayoutTheory.struct_field_offset_le >>
     strip_tac >>
     CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss())
       [val_footprint_def, valueEncodingTheory.type_memory_size_def])) >>
     decide_tac) >>
  qpat_assum `vv_loc bvv = LocMemory`
    (fn th => rewrite_tac[th, vyperASTTheory.expr_type_def]) >>
  reverse conj_tac >- simp[contextTheory.mk_ptr_def] >>
  irule exprSimVVFrameTheory.vv_own_memory_slice >>
  qexistsl_tac [`StructT sid`, `ftv`, `fv`,
                `w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)`,
                `struct_field_offset
                  (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld`,
                `vv_operand bvv`, `tv`, `StructTV fs`, `StructT sid`,
                `StructV vals`, `w`] >>
  simp[exprSimAttributePropsTheory.attr_offset_def, contextTheory.mk_ptr_def] >>
  qpat_assum `tv' = Value child` (fn eq =>
    qpat_assum `read_result cx tv' mid = (INL fv,mid)`
      (ACCEPT_TAC o REWRITE_RULE [eq]))
QED

Resume attribute_vv_sim_full[code_field]:
  `t.vs_memory = s.vs_memory` by simp[venomStateTheory.update_var_def] >>
  qpat_assum `vv_post H ctx func cenv cx obj es sa sm s0 mid tv bvv s`
    (mp_then (Pos (el 3)) mp_tac attribute_code_field_full) >>
  disch_then assume_tac >>
  strip_tac >>
  simp[NoAsms, arithmeticTheory.ADD_COMM, vyperASTTheory.expr_type_def] >>
  qpat_assum `t.vs_memory = s.vs_memory` (fn th => rewrite_tac[th]) >>
  qpat_assum `tn2.t_mem = tn1.t_mem` (fn th => rewrite_tac[th]) >>
  qpat_assum `!w tv' tn' tn t lo fld es0 env dst ann. _`
    (irule o SRULE [arithmeticTheory.ADD_COMM, vyperASTTheory.expr_type_def]) >>
  simp[] >>
  conj_tac >- (qexists_tac `tn1` >> simp[]) >>
  reverse conj_tac
  >- (qexistsl_tac [`env`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`, `fld`] >> simp[]) >>
  strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==> _` mp_tac >>
  simp[]
QED

Resume attribute_vv_sim_full[alloca_history]:
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
        compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
        compileEnvTheory.emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sm.cs_current_insts) = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base i s = OK u` by
    simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomInstTheory.mk_inst_def, venomExecSemanticsTheory.exec_pure2_def,
         venomStateTheory.eval_operand_def] >>
  `alloca_inv s` by gvs[loweringPostsTheory.vv_post_def,
      exprLoweringPropsTheory.stmt_state_rel_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME i` by simp[] >>
  drule_all allocaHistoryTheory.alloca_history_base_step >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Resume attribute_vv_sim_full[selected_ptr]:
  gvs[vyperASTTheory.expr_type_def]
QED

Resume attribute_vv_sim_full[ptr_buf]:
  gvs[contextTheory.mk_ptr_def]
QED

Resume attribute_vv_sim_full[pointer_posts]:
  `vv_loc bvv = LocCode ==> op_prov G2 p = NONE` by
    (strip_tac >>
     `op_prov G1 (vv_operand bvv) = NONE` by
       (Cases_on `bvv` >>
        gvs[bodyPtrDefsTheory.ptr_vv_ok_def, exprSimAttributePropsTheory.vv_loc_def,
            contextTheory.vv_location_def, contextTheory.vv_operand_def]) >>
     gvs[ptrDisciplineTheory.op_prov_def]) >>
  `!x b sz. vv_operand bvv = Var x /\ FLOOKUP G1 x = SOME (b,sz) ==>
     ?y. p = Var y /\ FLOOKUP G2 y = SOME (b,sz)` by
    (rpt strip_tac >> qexists_tac `out` >>
     gvs[ptrDisciplineTheory.op_prov_def]) >>
  `ptr_vv_ok cx (expr_type obj) tv bvv mid G1 tn1 s` by gvs[] >>
  qpat_assum `vv_post H ctx func cenv cx obj es sa sm s0 mid tv bvv s`
    (mp_then (Pos (el 3)) mp_tac attribute_selected_ptr) >>
  disch_then assume_tac >>
  first_x_assum irule >>
  simp[venomStateTheory.update_var_def] >>
  conj_tac
  >- (qexistsl_tac [`env`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >> simp[]) >>
  qexistsl_tac [`G1`, `tn1`] >>
  gvs[ptrDisciplineTheory.op_prov_def, venomStateTheory.update_var_def]
QED

Finalise attribute_vv_sim_full


Theorem attribute_expr_full_ok:
  !cx v9 e id. body_expr_full_ok cx e ==> body_expr_full_ok cx (Attribute v9 e id)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  drule attr_pre_base >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e es` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Attribute v9 e id) es` by
    (irule attribute_vv_sim_full >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Attribute _ _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Attribute v9 e id)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
