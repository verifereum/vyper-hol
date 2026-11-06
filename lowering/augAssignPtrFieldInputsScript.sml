(* Typed source and covered field-address inputs, before running any code. *)
Theory augAssignPtrFieldInputs
Ancestors
  augAssignPtrFieldLoad augAssignPtrFieldSource exprSimFieldLayout
  exprSimAttributeFields stmtSimAugAssignAttr exprSimHyps exprSimHypsDefs
  exprSimDefs exprSimProps bodyPtrDefs vyperTypeSystem vyperValue
  stmtSimAssignStore stmtSimAugAssign exprSimSource valueEncoding
  vyperTypeStatePreservation vyperTyping exprLoweringProps compileEnv

Theorem augassign_attr_field_inputs_ptr:
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (ty,fsz) /\ word_value_type ty /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s ==>
  ?p sz a entry fs vals ftv fv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (StructT sid) /\
    lookup_scopes id es.scopes = SOME entry /\ lookup_var p s = SOME a /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
    ALOOKUP vals fld = SOME fv /\ value_has_type ftv fv /\ word_value fv /\
    evaluate_type (get_tenv cx) ty = SOME ftv /\ type_memory_size ftv = 32 /\
    ptr_covers G tn p s sz /\
    struct_field_offset (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld < sz /\
    struct_field_offset (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld + 32 <= sz /\
    w2n a + struct_field_offset (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld < dimword (:256) /\
    (!i. w2n (a + n2w (struct_field_offset
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)) <= i /\
      i < w2n (a + n2w (struct_field_offset
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)) + 32 ==>
      i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by fs[expr_sim_inv_def] >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by metis_tac[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  `value_has_type entry.type entry.value` by
    metis_tac[expr_sim_inv_def, lookup_scopes_state_well_typed_value_has_type] >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  drule_all struct_has_type_field >> strip_tac >>
  `word_value fv` by metis_tac[word_value_type_typed] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `type_memory_size ftv = 32` by metis_tac[word_value_type_memory_size] >>
  `?a. lookup_var p s = SOME a` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all ghost_inv_struct_field_inputs >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
