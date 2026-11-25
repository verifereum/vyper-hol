(* Linked execution of the fixed, read-only memory selector. *)
Theory bodySubscriptArrayFramedMemoryMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodyFullPredsMods bodyFullPostsMods exprBodyPreProps
  exprSimSubscriptArraySource exprSimTopLevelProps supportedExprTraverse
  exprSimHypsDefs allocLimits vyperTypeSystem vyperTypeInvariants
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperAST pair list
  exprSimSubscriptArrayFramed exprLoweringProps gasShadowCompileStmtHelpers
  context compileEnv compilerInstructionSuffix exprSimUnwrap
  bodyArrayNoCopySourceMods bodyArrayNoCopyCodeMods bodyArrayNoCopyBindMods bodyArrayNoCopyCutsMods
  bodyArraySubscriptReadMods bodyFullIfExpReach bodyArrayFramedMemoryViewMods
  bodyArrayFramedMemoryChildMods bodyArrayFramedMemoryRejectMods
  bodyArrayFramedMemoryAddressMods bodyAssignNameLinkedSetup overflowElimHelpers
  exprSimArrayIndex loweringShapeRules exprSimWordArgs words venomInst
  vyperTyping vyperPlaceTyping vyperArray loweringPosts bodyPtrDefs exprBodyPreTypingProps
Libs
  monadsyntax

Theorem framed_memory_base_pre[local]:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocMemory ==>
  expr_body_pre_mods mods cenv cx env obj es
Proof
  strip_tac >>
  `~array_slot_base cenv obj` by metis_tac[array_slot_base_compile_location] >>
  `well_typed_expr env obj` by
    (`env_context_consistent env cx` by
       (drule_then assume_tac expr_body_pre_mods_inv >>
        drule_then mp_tac expr_sim_inv_mods_env >> simp[env_consistent_def]) >>
     drule_then mp_tac expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def] >> strip_tac >>
     drule type_place_expr_vtype_annotation >> simp[] >>
     Cases_on `vt` >> gvs[vtype_annotation_ok_def] >>
     strip_tac >> gvs[] >>
     irule type_place_expr_context_value_typed >>
     conj_tac >- (qexists_tac `ArrayT et bd` >> simp[]) >>
     qexists_tac `cx` >> simp[]) >>
  gvs[expr_body_pre_mods_def, alloc_limits_expr_def, byte_widths_expr_def, int_calls_expr_def,
      expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem framed_memory_cuts[local]:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type cenv obj = ValPT (ArrayT et (vyperAST$Fixed n)) /\
  ~copies_subscript_base cenv obj idx /\
  (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory) ==>
  ?bvv sm iop si dst.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv ty idx sm = (iop,si) /\
    vv_location bvv = SOME LocMemory /\
    compile_array_subscript (vv_operand bvv) iop F n (word_scale LocMemory)
      (elem_size_in_location cenv LocMemory et) (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) si = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst LocMemory) /\
    cs_extends sa sm /\ cs_extends sm si /\ cs_extends si sb
Proof
  strip_tac >> drule_all_then strip_assume_tac compile_expr_array_subscript >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  `vv_location bvv = SOME LocMemory` by
    (qpat_assum `compile_expr cenv ty obj sa = (bvv,sm)` (fn cut =>
       qpat_assum `!ty st. vv_location _ = _`
         (qspecl_then [`ty`,`sa`] (ACCEPT_TAC o PURE_REWRITE_RULE [cut,SND,FST])))) >>
  gvs[] >>
  conj_tac >- (drule compile_expr_extends >> simp[]) >>
  conj_tac >- (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (SUBST1_TAC o SYM o PURE_REWRITE_RULE [FST,SND] o Q.AP_TERM `SND`) >>
  irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]
QED

Theorem framed_memory_child_sims[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx sh fn sf ce env ty es.
                _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (irule o SPEC_ALL) >>
  simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
  qexists_tac `env` >> simp[]
QED

Theorem subscript_array_framed_memory_full_mods:
  !mods exps cx ann obj idx DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd.
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  subscript_array_framed_memory_case_mods cenv cx obj idx et bd ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Subscript ann obj idx) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >>
  `~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
   (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory)` by
    fs[subscript_array_framed_memory_case_mods_def] >>
  conj_asm2_tac
  >- (drule_all array_subscript_value_of_located_mods >> simp[]) >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac array_nocopy_paired_parts_mods >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  `vv_location bvv = SOME LocMemory` by
    (qpat_assum `compile_expr cenv ty obj sa = (bvv,sm)` (fn cut =>
       qpat_assum `!ty st. vv_location _ = _`
         (qspecl_then [`ty`,`sa`] (ACCEPT_TAC o PURE_REWRITE_RULE [cut,FST])))) >>
  `expr_body_pre_mods mods cenv cx env obj es` by
    (`vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocMemory` by
       (qpat_assum `compile_expr cenv ty obj sa = (bvv,sm)` (fn th => pure_rewrite_tac[th,FST]) >>
        first_assum ACCEPT_TAC) >>
     drule_all_then ACCEPT_TAC framed_memory_base_pre) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty obj es` by
    (irule (framed_memory_child_sims |> CONV_RULE (REWR_CONV IMP_CONJ_THM) |> cj 2) >>
     qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `!obs raw mid. eval_expr cx obj (es with gas_obs := obs) = (INL raw,mid) ==>
     expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty idx mid` by
    (rpt gen_tac >> strip_tac >> drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
     irule (framed_memory_child_sims |> CONV_RULE (REWR_CONV IMP_CONJ_THM) |> cj 1) >>
     qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >> simp[] >>
     qexistsl_tac [`cenv`,`ctx`,`cx`,`exps`,`func`,`mods`] >> simp[]) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  irule (PURE_REWRITE_RULE [LET_THM] array_nocopy_children_bind_mods |> BETA_RULE) >>
  suspend "bind"
QED

Resume subscript_array_framed_memory_full_mods[bind]:
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bd`,`bvv`,`et`,`iop`,`shadow_func`,`shadow_sa`,`shadow_sb`,
                `shadow_sm`,`shadow_st2`,`sm`,`st2`,`ty`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid)` by
    (qhdtm_assum `array_nocopy_cut_mods`
      (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  `expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs1) /\
   expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  drule_all_then strip_assume_tac framed_memory_reached_view_mods >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `bd = Fixed _` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV _` SUBST_ALL_TAC >>
  rename1 `read_result cx raw fin = (INL (ArrayV av),fin)` >>
  rename1 `evaluate_type (get_tenv cx) et = SOME etv` >>
  rename1 `eval_operand iop it = SOME iw` >>
  rename1 `valid_index (ArrayTV etv (Fixed n)) av i <=> _` >>
  Cases_on `valid_index (ArrayTV etv (Fixed n)) av i`
  >- suspend "in_bounds" >>
  drule_all_then ACCEPT_TAC framed_memory_select_oob_mods
QED

Resume subscript_array_framed_memory_full_mods[in_bounds]:
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  `is_word_type (expr_type idx)` by
    (`is_int_type (expr_type idx)` by
       (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
          (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
        simp[Once well_typed_expr_def] >> strip_tac >> gvs[subscript_type_ok_def] >>
        drule type_place_expr_vtype_annotation >> strip_tac >> Cases_on `vt` >>
        gvs[vtype_annotation_ok_def, subscript_vtype_def, AllCaseEqs()]) >>
     `!t. is_int_type t ==> is_word_type t` by
       (POP_ASSUM_LIST (K ALL_TAC) >> gen_tac >> Cases_on `t` >>
        simp[is_int_type_def] >> rename1 `is_int_type (BaseT bt) ==> _` >>
        Cases_on `bt` >> simp[is_int_type_def,is_word_type_def]) >>
     first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `op_taint tni p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> qpat_assum `!x. p.ptr_operand = Var x ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (drule_all_then ACCEPT_TAC assign_name_memory_bytes_mods) >>
  `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)` by fs[] >>
  `w2n iw = Num i` by
    (`0 <= i` by fs[valid_index_def] >>
     Cases_on `is_signed_type (expr_type idx)` >> gvs[] >>
     drule_then ACCEPT_TAC nonneg_w2i_eq_w2n) >>
  suspend "fixed_run"
QED

Resume subscript_array_framed_memory_full_mods[fixed_run]:
  `?sc smul off out.
     array_bounds_check iop (Lit (n2w n)) (is_signed_type (expr_type idx)) st2 = ((),sc) /\
     emit_op MUL [iop;Lit (n2w (type_memory_size etv))] sc = (Var off,smul) /\
     emit_op ADD [p.ptr_operand;Var off] smul = (Var out,sb) /\ dst = Var out` by
    (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _` mp_tac >>
     simp[NoAsms,vv_operand_def,elem_size_in_location_def,is_slot_addressed_def,
          compile_array_subscript_split,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     simp[NoAsms,array_elem_ptr_def,comp_bind_def,comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     qpat_assum `emit_op MUL _ _ = _` (mp_then Any (qx_choose_then `off` (assume_tac o cj 1)) emit_op_facts) >>
     qpat_assum `emit_op ADD _ _ = _` (mp_then Any (qx_choose_then `out` (assume_tac o cj 1)) emit_op_facts) >>
     qpat_x_assum `_ = Var off` SUBST_ALL_TAC >>
     qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
     qexistsl_tac [`off`,`out`] >> simp[]) >>
  qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp it)` by simp[] >>
  drule_all (framed_memory_fixed_address_run
    |> INST_TYPE [Type.alpha |-> ``:256``]
    |> Q.INST [`i` |-> `w2n (iw:bytes32)`] |> SRULE []) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     vv_post_mods H ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx)
       es sa st2 s0 fin raw (LocatedValue (ArrayT et (Fixed n)) p) it` by
    (rpt strip_tac >> qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o cj 1))) >>
  `lookup_var out sf = SOME (w + n2w (Num i * type_memory_size etv))` by
    (qpat_assum `w2n iw = Num i` (fn eq =>
       qpat_assum `lookup_var out sf = SOME _` (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  irule framed_memory_select_in_bounds_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`,`Gf`,`av`,`env`,`etv`,`exps`,`gs1`,`gs2`,`iop`,`mid`,
    `mods`,`p`,`s`,`sf`,`shadow_func`,`shadow_sa`,`shadow_sb`,`shadow_sm`,
    `shadow_st2`,`sm`,`src`,`st2`,`tn1`,`tnf`,`tops`,`ty`,`w`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise subscript_array_framed_memory_full_mods
