(* Capture the lowered RHS layout before evaluating an effectful target. *)
Theory bodyMemAssignPlaceCapture
Ancestors
  bodyMemAssignSnapshot bodyMemLoweredSnapshot bodyMemSnapshotStages
  bodyMemSnapshotCapturedFrame bodyMemSnapshotSourceLocation bodySim
  exprSimIfExpWidenedOwnedProvenance
  exprSimHypsDefs exprSimHyps exprSimMemDefs exprSimProps exprSimSource loweringPosts
  exprLowering exprLoweringProps exprOperandVar exprSafeOperand exprWordOperand freshWrites
  incompatibleReturnLayout internalReturnMetadata intCallStep externalNormalizePremises
  memoryLocalRhsProps supportedExprs supportedProgram supportedDecls allocLimits
  typedMemoryCopy valueCopyBytes valueTypingMemoryProps valueEncoding
  vyperTypeArgFits vyperTypeSystem vyperTypeInvariants vyperValue vyperState vyperAST
  compileEnv context venomState venomInst fragGasMode fragGasPathMem
  stmtSimAugAssignPlaceMemory words pair list rich_list finite_map

Theorem capture_lower_widens[local]:
  expr_sim_inv ce cx env es /\ well_typed_expr env e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv ==>
  type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)
Proof
  strip_tac >>
  Cases_on `lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)`
  >- gvs[type_widens_to_def, well_formed_type_def] >>
  drule_all incompatible_return_layout_intcall >> strip_tac >>
  gvs[expr_type_def]
QED

Theorem capture_incompatible_located[local]:
  body_inv tops ctx ce cx /\ supported_expr tops e /\
  expr_sim_inv ce cx env es /\ well_typed_expr env e /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  compile_expr ce (expr_type e) e sa = (vv,sr) ==>
  post_value_type ce e = lowered_value_type ce e /\
  ~is_word_type (lowered_value_type ce e) /\
  ?declared p. vv = LocatedValue declared p /\ p.ptr_location = LocMemory
Proof
  strip_tac >> drule_all incompatible_return_layout_intcall >> strip_tac >>
  gvs[expr_type_def] >>
  `lowered_value_type ce (Call ann (IntCall fid) xs drv) <> ann` by metis_tac[] >>
  `~is_word_type (lowered_value_type ce (Call ann (IntCall fid) xs drv))` by
    metis_tac[return_source_word_widens_eq] >>
  `0 < type_memory_size ltv` by
    (drule_all normalize_return_source_positive >> simp[]) >>
  `type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) xs drv)) = type_memory_size ltv` by
    metis_tac[expr_sim_inv_memory_size] >>
  gvs[expr_type_def] >> simp[post_value_type_def] >>
  `drv = NONE /\ ?mut nr rr args dflts ret body.
    supported_function_decl tops fid Internal =
      SOME (mut,nr,rr,args,dflts,ret,body)` by
    (Cases_on `drv` >>
     fs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
        optionTheory.IS_SOME_EXISTS] >>
     rename1 `supported_function_decl tops fid Internal = SOME finfo` >>
     PairCases_on `finfo` >> metis_tac[]) >>
  `supported_program tops /\
   ce.ce_func_return_type = build_func_return_type tops /\
   ce.ce_func_info = build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
   ce.ce_struct_fields = make_struct_fields_map tops` by fs[body_inv_def] >>
  `ce.ce_func_return_type (nsid_to_string fid) = ret` by
    (drule_all supported_internal_return_type >> simp[]) >>
  `ret <> NoneT` by
    (strip_tac >> gvs[lowered_value_type_def, evaluate_type_def,
                     type_memory_size_def]) >>
  `ce.ce_func_info (nsid_to_string fid) =
    compute_func_info (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n))
      ret (type_memory_bytes ce ret) (MAP SND args)` by
    (drule_all supported_internal_call_info >> simp[]) >>
  namedCases_on `ce.ce_func_info (nsid_to_string fid)` ["ret_count rbs pvs"] >>
  `0 < ret_count \/ 0 < rbs` by
    (mp_tac (Q.INST [`ats` |-> `MAP SND (args : (string # type) list)`, `declared` |-> `ret`,
       `sft` |-> `\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)`,
       `sz` |-> `type_memory_bytes ce ret`] positive_compute_func_info) >>
     gvs[lowered_value_type_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule_all compile_call_intcall_shape >> strip_tac >>
  Cases_on `ret_count = 0` >> gvs[base_ptr_def]
QED

Theorem assign_place_capture_mem:
  body_inv tops ctx ce cx /\ supported_expr tops e /\
  expr_body_pre ce cx env e es /\
  type_alloc_ok ce (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv0,sr) /\
  compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv0) sr =
    (saved,ss) /\
  vv_post ctx func ce cx e es sa sr s0 ee raw vv0 s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv0 s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\ value_has_type etv v /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  value_has_type ltv v /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ci_mono sa sr /\ fn_has_code sr ss func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sr.cs_current_bb /\
  s.vs_inst_idx = LENGTH sr.cs_current_insts ==>
  ?z. gas_marked_path T ctx func s 0 (OK z) /\
    vv_post ctx func ce cx e es sa ss s0 ee raw saved z /\
    stmt_state_rel ctx func ce cx ee z /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
    vv_type saved = lowered_value_type ce e /\
    (!x. vv_operand saved = Var x ==> not_fresh_at ss x) /\
    (!l. vv_operand saved <> Label l) /\
    alloca_history func z /\ ~z.vs_halted /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = ss.cs_current_bb /\
    z.vs_inst_idx = LENGTH ss.cs_current_insts /\
    (if is_word_type (lowered_value_type ce e) then
       expr_val_rel cx (lowered_value_type ce e) v (vv_operand saved) z
     else
       vv_own ce cx (lowered_value_type ce e) sr ss ee (Value v) saved z /\
       vv_at ce cx (lowered_value_type ce e) sr ss ee (Value v) saved z /\
       ?w. eval_operand (vv_operand saved) z = SOME w /\ val_wf ltv v /\
         val_in_memory ltv v (w2n w) z.vs_memory /\
         (type_memory_size ltv = 0 \/
          w2n w + type_memory_size ltv <= z.vs_alloca_next))
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    fs[expr_body_pre_def] >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    metis_tac[capture_lower_widens] >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv /\
   type_memory_bytes ce (expr_type e) = type_memory_size etv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `sa.cs_next_var <= sr.cs_next_var /\ sa.cs_next_id <= sr.cs_next_id` by
    fs[ci_mono_def] >>
  `!x. vv_operand vv0 = Var x ==> not_fresh_at sr x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `?z. gas_marked_path T ctx func s 0 (OK z) /\
    vv_post ctx func ce cx e es sa ss s0 ee raw saved z /\
    vv_own ce cx (post_value_type ce e) sr ss ee raw saved z /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
      ee raw saved z /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = ss.cs_current_bb /\
    z.vs_inst_idx = LENGTH ss.cs_current_insts` by
    (Cases_on `lowered_value_type ce e = expr_type e \/
       is_bytestring_type (expr_type e) /\
       is_bytestring_type (lowered_value_type ce e) /\
       arg_type_fits (lowered_value_type ce e) (expr_type e)`
     >- suspend "compatible" >> suspend "widened") >>
  suspend "result"
QED

Resume assign_place_capture_mem[compatible]:
  `post_value_type ce e = expr_type e` by
    metis_tac[post_value_type_lowered, post_value_type_bytestring] >>
  `!t p. vv0 = LocatedValue t p /\ p.ptr_location <> LocMemory ==>
    lowered_value_type ce e = expr_type e` by
    (rpt strip_tac >> Cases_on `lowered_value_type ce e = expr_type e` >>
     simp[] >>
     `lowered_value_type ce e <> post_value_type ce e` by metis_tac[] >>
     drule_all snapshot_changed_type_location >>
     simp[vv_location_def] >> metis_tac[]) >>
  `~is_word_type (expr_type e) ==> type_memory_size etv < 2**64` by
    (strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  `~is_word_type (lowered_value_type ce e) ==> type_memory_size ltv < 2**64` by
    fs[type_alloc_ok_def] >>
  `!t tv. (t = expr_type e \/ t = lowered_value_type ce e) /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t ==>
    type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2**64` by
    (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `!tvt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvt ==>
    value_has_type tvt v` by (rpt strip_tac >> gvs[]) >>
  mp_tac (Q.SPECL [`ctx`,`func`,`ce`,`cx`,`e`,`es`,`sa`,`sr`,`ss`,
    `s0`,`ee`,`raw`,`v`,`vv0`,`saved`,`s`] snapshot_vv_counted_mem) >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `u` >> simp[]
QED

Resume assign_place_capture_mem[widened]:
  `lowered_value_type ce e <> expr_type e` by metis_tac[] >>
  drule_all capture_incompatible_located >> strip_tac >> gvs[vv_operand_def] >>
  `0 < type_memory_size ltv` by
    (drule_all normalize_return_source_positive >> simp[]) >>
  `type_memory_size ltv < dimword (:256)` by
    (fs[type_alloc_ok_def] >>
     CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> decide_tac) >>
  `!w. eval_operand p.ptr_operand s = SOME w ==>
    w2n w + type_memory_size ltv <= s.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_x_assum `vv_store_bound _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT2 o REWRITE_RULE [vv_store_bound_def]) >>
     disch_then (qspecl_then [`declared`,`p.ptr_operand`,`ltv`,`w`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  drule_all snapshot_lowered_located_mem >> strip_tac >>
  qexists_tac `z` >> simp[gas_marked_path_def]
QED

Resume assign_place_capture_mem[result]:
  `~z.vs_halted` by metis_tac[aug_place_marked_path_not_halted] >>
  `vv_type saved = lowered_value_type ce e` by
    metis_tac[snapshot_saved_representation] >>
  `?w. eval_operand (vv_operand saved) z = SOME w` by
    (Cases_on `saved` >> fs[vv_post_def, vv_holds_def, expr_val_rel_def,
                          vv_operand_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  Cases_on `is_word_type (lowered_value_type ce e)`
  >- suspend "word" >>
  drule_all snapshot_nonword_slices >> strip_tac >> gvs[] >>
  `eval_operand buf.buf_operand z = SOME w` by fs[vv_operand_def, mk_ptr_def] >>
  `!l. buf.buf_operand <> Label l` by metis_tac[alloc_buffer_not_label] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at ss x` by
    (drule compiler_alloc_buffer_var >> strip_tac >>
     metis_tac[compiler_ci_mono_not_fresh, ci_mono_trans]) >>
  `val_wf ltv v /\ val_in_memory ltv v (w2n w) z.vs_memory /\
   vv_own ce cx (lowered_value_type ce e) sr ss ee (Value v)
     (LocatedValue (lowered_value_type ce e) (mk_ptr buf.buf_operand LocMemory)) z` by
    suspend "retag" >>
  `vv_at ce cx (lowered_value_type ce e) sr ss ee (Value v)
    (LocatedValue (lowered_value_type ce e) (mk_ptr buf.buf_operand LocMemory)) z` by
    (mp_tac (Q.INST [`sty` |-> `lowered_value_type ce e`,
       `dty` |-> `lowered_value_type ce e`, `stv` |-> `ltv`, `dtv` |-> `ltv`,
       `sa` |-> `sr`, `sb` |-> `ss`, `es` |-> `ee`, `s` |-> `z`,
       `raw` |-> `Value v`, `t` |-> `lowered_value_type ce e`,
       `t'` |-> `lowered_value_type ce e`, `op` |-> `buf.buf_operand`]
       vv_own_memory_transport) >> simp[read_result_def, return_def]) >>
  `type_memory_size ltv = 0 \/ w2n w + type_memory_size ltv <= z.vs_alloca_next` by
    (fs[vv_store_bound_def, mk_ptr_def, vv_operand_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `z` >> gvs[vv_operand_def, mk_ptr_def, vv_post_def] >>
  first_assum ACCEPT_TAC
QED

Resume assign_place_capture_mem[word]:
  `lowered_value_type ce e = expr_type e` by
    metis_tac[return_source_word_widens_eq] >>
  `is_word_type (expr_type e)` by metis_tac[] >>
  `expr_val_rel cx (lowered_value_type ce e) v (vv_operand saved) z` by
    (drule_all snapshot_saved_representation >> strip_tac >>
     Cases_on `saved` >> gvs[vv_type_def, vv_location_def, vv_post_def,
       vv_holds_def, vv_operand_def] >> metis_tac[]) >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
    well_formed_type env.type_defs t` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `word_result_ok sr vv0` by metis_tac[cj 1 compile_expr_word_result] >>
  `word_result_ok sr (vv_with_type (lowered_value_type ce e) vv0)` by
    (Cases_on `vv0` >> fs[word_result_ok_def, vv_with_type_def]) >>
  `safe_operand ss (vv_operand saved)` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     `vv_type (vv_with_type (lowered_value_type ce e) vv0) = lowered_value_type ce e` by
       (Cases_on `vv0` >> simp[vv_type_def, vv_with_type_def]) >>
     simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[vv_operand_def] >>
     metis_tac[unwrap_value_safe_operand]) >>
  qexists_tac `z` >> simp[] >> fs[vv_post_def, safe_operand_def] >>
  first_assum ACCEPT_TAC
QED

Resume assign_place_capture_mem[retag]:
  `vv_holds ce cx (post_value_type ce e) raw
    (LocatedValue (lowered_value_type ce e) (mk_ptr buf.buf_operand LocMemory)) ee z` by
    fs[vv_post_def] >>
  Cases_on `post_value_type ce e = lowered_value_type ce e`
  >- (gvs[] >>
      mp_tac (Q.INST [`sty` |-> `lowered_value_type ce e`,
        `lty` |-> `lowered_value_type ce e`, `stv` |-> `ltv`,
        `sa` |-> `sr`, `sb` |-> `ss`, `es` |-> `ee`, `s` |-> `z`,
        `op` |-> `buf.buf_operand`] snapshot_captured_memory_retag) >>
      simp[vv_operand_def, mk_ptr_def] >> metis_tac[]) >>
  `post_value_type ce e = expr_type e /\
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type ce e)` by
    (Cases_on `lowered_value_type ce e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e)`
     >- metis_tac[post_value_type_lowered, post_value_type_bytestring] >>
     drule_all capture_incompatible_located >> simp[]) >>
  gvs[] >>
  mp_tac (Q.INST [`sty` |-> `expr_type e`,
    `lty` |-> `lowered_value_type ce e`, `stv` |-> `etv`,
    `sa` |-> `sr`, `sb` |-> `ss`, `es` |-> `ee`, `s` |-> `z`,
    `op` |-> `buf.buf_operand`] snapshot_captured_memory_retag) >>
  simp[vv_operand_def, mk_ptr_def] >> metis_tac[]
QED

Finalise assign_place_capture_mem
