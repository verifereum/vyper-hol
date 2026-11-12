(* Storage/transient struct fields specialize the pure-place pipeline. *)
Theory augAssignPtrStorageFieldCase
Ancestors
  augAssignPtrStoragePipeline augAssignPtrStorageFieldInputs
  augAssignPtrStorageFieldLoad augAssignPtrStorageFieldLive
  stmtSimAugAssignAttrStorage stmtSimAssignStorage stmtSimAssignAttrStorage
  exprSimFieldLayout exprSimAttributeFields exprSimTopLevelProps
  exprSimProps exprSimSource exprSimHypsDefs bodyPtrDefs
  vyperPlaceTyping vyperStorageLayoutSafety vyperTypeValues
  vyperTypeInvariants vyperValue vyperTypeStatePreservation vyperTypeBuiltins vyperTypeSystem vyperState vyperInterpreter vyperStorageBackend
  loweringPosts codegenRel compileEnv loweringStateRelDefs emitHelperProps exprLoweringProps
  accountsRelProps exprSimUnwrap fragExec loweringSlice stmtFragPtr bodyPtrPreds stmtSimDefs stmtSimAugAssign gasSummary gasContext

Theorem compile_augassign_attr_storage_case_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld = SOME (ty,fsz) /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty0
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e))
    (eval_stmt cx (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `contract_storage_well_formed cx es /\ storage_layout_safe cx /\
   storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[expr_sim_inv_def, stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all augassign_attr_storage_code_parts_ptr >> strip_tac >> gvs[] >>
  `?fs off ftv.
     evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
     struct_field_slot fs fld = SOME (off,ftv)` by
    (Cases_on `eval_stmt cx (AugAssign ty
       (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e) es` >>
     rename1 `_ = (res,es')` >>
     `es with gas_obs := es.gas_obs = es` by simp[evaluation_state_component_equality] >>
     `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
     `!m. res <> INR (Error (TypeError m))` by
       (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
     drule_all augassign_storage_field_place_ptr >> metis_tac[]) >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  drule_all struct_field_type >> strip_tac >>
  `ALOOKUP fs fld = SOME ftv` by metis_tac[struct_field_slot_type] >>
  gvs[] >> suspend "load"
QED

Resume compile_augassign_attr_storage_case_ptr[load]:
  qabbrev_tac `off = struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld` >>
  drule_all augassign_storage_field_read_ptr >> strip_tac >>
  `!st. storage_read_live cx tr st (n2w slot + n2w off) ftv` by
    (irule declared_storage_field_live_ptr >> metis_tac[]) >>
  `type_slot_size ftv = 1` by metis_tac[word_type_slot_size] >>
  `!w st. storage_dead cx tr (update_storage (n2w slot + n2w off) w st) =
      storage_dead cx tr st` by
    (rpt gen_tac >> irule storage_dead_update_struct_word_field >>
     qexistsl [`fld`,`fs`,`ftv`,`src`,`id`] >>
     simp[declared_storage_region_def]) >>
  `?z. dst = Var z` by metis_tac[emitted_insts_emit_op_local] >>
  `?z. cur = Var z` by metis_tac[emitted_insts_emit_op_local] >> gvs[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends sa sn /\ cs_extends sn s1 /\ cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sa s1 /\ cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends sa s2` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `storage_holds cx tr ty (Value cur') (n2w slot + n2w off) es s0` by metis_tac[] >>
  `0 < type_slot_size ftv` by simp[] >>
  drule_all augassign_storage_field_load_clean_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  suspend "pipeline"
QED

Resume compile_augassign_attr_storage_case_ptr[pipeline]:
  `sn.cs_next_var = sa.cs_next_var + 1 /\ s1.cs_next_var = sn.cs_next_var + 1` by
    metis_tac[emitted_insts_emit_op_local] >>
  `sa.cs_next_var <= s1.cs_next_var` by decide_tac >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ret_pc_ok_def]) >>
  `!gs. eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld)
      (es with gas_obs := gs) =
      (INL (StoragePlace tr (n2w slot + n2w off) ftv),es with gas_obs := gs)` by
    (gen_tac >> irule (cj 1 eval_target_place_attr_toplevel_field) >> metis_tac[]) >>
  `well_formed_type env.type_defs ty` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def, well_formed_type_def] >>
  `well_formed_type_value ftv` by metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type ftv cur'` by metis_tac[read_storage_slot_success_type] >>
  `word_value cur'` by metis_tac[word_value_type_typed] >>
  `eval_operand (Var z') t = SOME (val_to_w256 cur')` by
    simp[typed_val_to_w256_word_value] >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) augassign_storage_place_pipeline_ptr >>
  disch_then irule >> simp[SF SFY_ss] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`H`,`Var z'`,`Var z`,`res_op`,`s3`,`t`,`tm`] >> simp[]
QED

Finalise compile_augassign_attr_storage_case_ptr
