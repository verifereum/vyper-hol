(* Field-target compilation boundary, independent of execution and ghost state. *)
Theory augAssignPtrStorageFieldInputs
Ancestors
  stmtSimAssignStorage stmtSimAugAssignAttrStorage stmtLowering
  exprLowering emitHelper compileEnv stmtSimDefs loweringPosts
  vyperInterpreter stmtSimAssignAttrStorage exprSimTopLevelProps
  accountsRelProps vyperStorageLayoutSafety vyperLookupStorage
  vyperStorageBackend vfmState codegenRel vyperState
  exprLoweringProps exprSimAttributeFields

Theorem augassign_attr_storage_code_parts_ptr:
  !cenv lctx ty0 ty src id fld sid fty fsz bop e sa c sf tr slot.
    stmt_env cenv lctx ty0
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    c = cenv /\
    ?dst sn cur s1 rhs s2 res_op s3.
      emit_op ADD
        [Lit slot; Lit (n2w (struct_field_offset_slots
          (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
        sa = (dst, sn) /\
      emit_op (if tr then TLOAD else SLOAD) [dst] sn = (cur, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
      compile_binop bop cur rhs ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [dst; res_op] s3 = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  asm_simp_tac (srw_ss())
    [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
     Once compile_get_target_ptr_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `emit_op ADD [Lit slot; Lit (n2w off)] sa` >>
  Cases_on `emit_op ADD [Lit slot; Lit (n2w off)] sa` >>
  rename1 `_ = (dst, sn)` >>
  asm_simp_tac (srw_ss())
    [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `emit_op load [dst] sn` >>
  Cases_on `emit_op load [dst] sn` >> rename1 `_ = (cur, s1)` >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs, s2)` >>
  Cases_on `compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2` >>
  rename1 `_ = (res_op, s3)` >>
  qmatch_goalsub_abbrev_tac `emit_void store [dst; res_op] s3` >>
  Cases_on `emit_void store [dst; res_op] s3` >>
  asm_simp_tac (srw_ss())
    [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
     oneTheory.one] >>
  strip_tac >> gvs[oneTheory.one]
QED

(* Recover the field type from the admissible source outcome, without
   requiring the entire struct type to have been evaluated by the caller. *)
Theorem augassign_storage_field_place_ptr:
  !cx ty src id fld bop e es res es' ts tr sid id_str slot.
    eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src, id)) fld) bop e)
      es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?fs off ftv.
      evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM] >>
  Cases_on `eval_target_place cx
    (AttributeTarget (TopLevelNameTarget (src, id)) fld) es` >>
  rename1 `_ = (r0, es0)` >> Cases_on `r0` >> simp[]
  >- (strip_tac >> drule eval_target_place_attr_toplevel >>
      rpt (disch_then drule) >> simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  drule eval_target_place_attr_toplevel >>
  rpt (disch_then drule) >> simp[] >> metis_tac[]
QED

Theorem augassign_storage_field_read_ptr:
  !cx es src id ts tr sid id_str slot fs fld off ftv ty.
    contract_storage_well_formed cx es /\ storage_layout_safe cx /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts =
      SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\
    evaluate_type (get_tenv cx) ty = SOME ftv ==>
    ?cur. read_storage_slot cx tr (n2w slot + n2w off) ftv es =
            (INL cur, es) /\
          !ctx func cenv s.
            stmt_state_rel ctx func cenv cx es s ==>
            storage_holds cx tr ty (Value cur) (n2w slot + n2w off) es s
Proof
  rpt strip_tac >>
  drule_all toplevel_storage_read_decodes >> strip_tac >>
  drule_all read_storage_slot_field >> strip_tac >>
  `declared_storage_region cx src id [] =
     SOME (tr, n2w slot, StructTV fs)` by
    simp[declared_storage_region_def] >>
  `get_storage_backend cx tr es = (INL (get_storage cx es tr), es)` by
    simp[get_storage_backend_eq] >>
  drule_all contract_storage_well_formed_region >> strip_tac >>
  drule_all storage_field_slots_in_range >> strip_tac >>
  qexists_tac `fv` >> simp[storage_holds_def, read_result_def, return_def] >>
  rpt strip_tac >>
  irule storage_range_agree_field >> goal_assum (drule_at Any) >>
  irule storage_range_agree_of_live >> conj_tac
  >- (drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  qexistsl [`cx`, `tr`] >> conj_tac
  >~ [`storage_read_live`]
  >- (irule declared_storage_region_read_live >> goal_assum (drule_at Any)) >>
  Cases_on `tr` >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
      get_storage_def, lookup_account_def]
QED
