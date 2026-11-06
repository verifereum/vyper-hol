(* Counted field store with ordinary and robust ghost posts at one endpoint. *)
Theory augAssignPtrFieldStoreCase
Ancestors
  augAssignPtrFieldStorePost augAssignPtrStore stmtSimAssignAttr
  exprLoweringProps exprSimProps bodyPtrDefs compileEnv valueEncoding
  valueEncodingProps stmtFragPtr venomState

Theorem augassign_field_store_case_ptr:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME da /\ eval_operand value s = SOME (val_to_w256 v) /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  find_containing_scope name es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME a /\
  w2n da = w2n a + struct_field_offset flds fld /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\ fields_val_wf vals fs /\
  ALOOKUP fs fld = SOME ftv /\ type_memory_size ftv = 32 /\ word_value v /\
  store_lays_out ftv ftv v /\ struct_field_offset flds fld + 32 <= sz ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    stmt_state_rel ctx fn cenv cx
      (es with scopes := pre ++ (env |+ (name,entry with
        <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) sf /\
    ghost_inv d cenv cx
      (es with scopes := pre ++ (env |+ (name,entry with
        <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) G tnf sf /\
    ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!q. lookup_var q sf = lookup_var q s) /\
    tnf.t_var = tn.t_var
Proof
  strip_tac >>
  qabbrev_tac `fin = es with scopes := pre ++ (env |+ (name,entry with
    <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest` >>
  drule_all emit_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `local_ptrs_rel fn cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `ghost_inv d cenv cx fin G tnf sf` by
    (drule_all ghost_inv_write_local_field_word >>
     disch_then (qspecl_then [`LENGTH sb.cs_current_insts`, `sa.cs_next_id`] mp_tac) >>
     gvs[Abbr `fin`]) >>
  `stmt_state_rel ctx fn cenv cx fin (mstore (w2n da) (val_to_w256 v) s)` by
    (`typed_val_to_w256 ftv v = val_to_w256 v` by
       simp[typed_val_to_w256_word_value] >>
     drule_all stmt_state_rel_write_field >> simp[Abbr `fin`]) >>
  qexistsl [`tnf`, `sf`] >> simp[] >>
  qpat_x_assum `sf = _` SUBST1_TAC >>
  metis_tac[stmt_state_rel_inst_idx]
QED
