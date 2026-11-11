(* Counted memory simulation of a struct field on a local Name. *)
Theory bodyFieldValueMemory
Ancestors
  bodyFieldMemoryProps bodyNameValueMemory bodyNameMemoryFacts exprSimNameValue
  exprSimFieldLayout exprSimAttributeProps exprSimVVFrame exprSimProps
  exprSimSource exprSimHypsDefs exprSimMemDefs exprSimDefs loweringPosts
  exprSimMemoryStack exprSimMemoryValues exprSimMemoryPath exprSimUnwrapProps
  gasNormalPrefix gasSummary gasSummaryCompose gasContext gasCount fragGasMode gasOutcome
  fragGasPathMem fragGasSeqMem gasExemptCert
  bodyMemoryDefs emitHelperProps fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list finite_map
  compileEnv fragExec valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState vyperExprNoControl
  freshWrites varsExt vyperTyping vyperTypeSystem vyperTypeInvariants
  allocLimits context vyperInterpreter vyperTypeExprSoundness

Theorem body_attribute_name_counted_prefix:
  expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es /\
  compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?tv v t ftv p fw.
    vv = LocatedValue ann (mk_ptr p LocMemory) /\
    (!tail. read_result cx tv (es with gas_obs := tail) =
      (INL v, es with gas_obs := tail)) /\
    gas_marked_exec T (ctx,func)
      (eval_expr cx (Attribute ann (Name (StructT sid) id) fld))
      (es,s0) [] (INL tv) es (OK t) /\
    vv_post ctx func cenv cx (Attribute ann (Name (StructT sid) id) fld)
      es sa sb s0 (es with gas_obs := []) tv vv t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    evaluate_type (get_tenv cx) ann = SOME ftv /\
    eval_operand p t = SOME fw /\ w2n fw + type_memory_size ftv <= t.vs_alloca_next /\
    vv_store_bound cx ann ann (es with gas_obs := []) tv vv t
Proof
  strip_tac >> drule body_attribute_name_pre >> strip_tac >>
  `expr_sim_pre cenv cx env (Name (StructT sid) id) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule_all body_attribute_name_source >> strip_tac >>
  drule_all body_name_source_region >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule body_attribute_name_compile >> strip_tac >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `StructT sid`] assume_tac) >> gvs[] >>
  `vv_post ctx func cenv cx (Name (StructT sid) id) es sa sa s0
     (es with gas_obs := []) (PlaceR (MemoryPlace id []))
     (LocatedValue (StructT sid) (mk_ptr (Var p) LocMemory)) s0` by
    (irule name_value_post >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand (vv_operand (LocatedValue (StructT sid)
      (mk_ptr (Var p) LocMemory))) s0 = SOME w` by
    simp[vv_operand_def, mk_ptr_def, eval_operand_def] >>
  `sa.cs_next_var <= sa.cs_next_var` by simp[] >>
  drule_all attr_add_counted_post >> strip_tac >>
  qpat_x_assum `expr_body_pre _ _ _ (Attribute _ _ _) _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Attribute _ _ _) _ = _` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ (Name _ _) _` kall_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ s0` kall_tac >>
  qpat_x_assum `val_in_memory _ _ _ _` kall_tac >>
  qpat_x_assum `local_region _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `val_wf _ _` kall_tac >>
  `read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
      (INL (StructV vals), es with gas_obs := [])` by
    simp[read_result_def, read_place_def, read_memory_path_def,
         evaluate_subscripts_def, bind_def, get_scopes_def,
         lift_option_type_def, lift_sum_def, return_def] >>
  `vv_post ctx func cenv cx (Attribute ann (Name (StructT sid) id) fld)
      es sa sb s0 (es with gas_obs := [])
      (PlaceR (MemoryPlace id [AttrSubscript fld]))
      (LocatedValue ann (mk_ptr p' LocMemory)) t` by
    (`vv_loc (LocatedValue (StructT sid) (mk_ptr (Var p) LocMemory)) = LocMemory`
       by simp[vv_loc_def, vv_location_def, mk_ptr_def] >>
     pop_assum (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule body_attr_memory_vv_post >>
     simp[expr_type_def, vv_loc_def, vv_location_def, mk_ptr_def] >>
     qexists_tac `PlaceR (MemoryPlace id [])` >> simp[] >>
     fs[mk_ptr_def]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (`stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by
       fs[vv_post_def] >>
     drule msg_gas_state_frame >>
     disch_then (qspecl_then [`t.vs_gas_readings`, `t.vs_inst_idx`, `es.gas_obs`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  `?fw. eval_operand p' t = SOME fw /\
      w2n fw + type_memory_size ftv <= t.vs_alloca_next` by
    (`eval_operand p' t = SOME (w + n2w (struct_field_offset
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))` by
       fs[attr_offset_def, vv_loc_def, vv_location_def, mk_ptr_def] >>
     drule_all body_attribute_name_capacity >> simp[]) >>
  qexistsl_tac [`PlaceR (MemoryPlace id [AttrSubscript fld])`, `fv`, `t`, `p'`, `fw`] >>
  `vv_store_bound cx ann ann (es with gas_obs := [])
     (PlaceR (MemoryPlace id [AttrSubscript fld]))
     (LocatedValue ann (mk_ptr p' LocMemory)) t` by
    (`ann = expr_type (Attribute ann (Name (StructT sid) id) fld)` by
       simp[expr_type_def] >>
     pop_assum (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th]))) >>
     irule vv_store_bound_capacity >> simp[expr_type_def, mk_ptr_def] >>
     fs[mk_ptr_def] >> metis_tac[]) >>
  simp[vv_loc_def, vv_location_def, mk_ptr_def, gas_marked_exec_def,
       gas_marked_path_def] >> fs[mk_ptr_def]
QED

Theorem compile_attribute_name_body_vv_sim_mem:
  !ctx func cenv cx env ty ann sid id fld es.
    expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es ==>
    expr_vv_sim_mem ctx func cenv cx ty
      (Attribute ann (Name (StructT sid) id) fld) es
Proof
  rpt gen_tac >> strip_tac >> simp[expr_vv_sim_mem_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all body_attribute_name_counted_prefix >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL tv`, `es`, `OK t`] >>
  gvs[expr_type_def, exprLoweringTheory.lowered_value_type_def]
QED
