(* Semantic packaging of the covered field load; invariants stay opaque to callers. *)
Theory augAssignPtrFieldLoadClean
Ancestors
  augAssignPtrFieldInputs augAssignPtrFieldLoad stmtSimAugAssignAttr
  exprSimSource exprLoweringProps valueEncodingProps valueEncoding
  bodyPtrDefs emitHelperProps emitHelper compileEnv loweringSlice
  stmtFragPtr exprSimProps

Theorem augassign_field_load_clean_ptr:
  emit_op ADD [Var p; Lit (n2w (struct_field_offset flds fld))] sa = (Var dst,sn) /\
  emit_op MLOAD [Var dst] sn = (Var out,s1) /\
  fn_has_code sa sn func /\ fn_has_code sn s1 func /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME a /\ lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  word_value_type ty /\ evaluate_type (get_tenv cx) ty = SOME ftv /\
  value_has_type ftv fv /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ ghost_inv d cenv cx es H tm t /\
    ghost_kept cenv es sa G tn s H tm /\
    lookup_var dst t = SOME (a + n2w (struct_field_offset flds fld)) /\
    ptr_covers H tm dst t 32 /\ lookup_var out t = SOME (val_to_w256 fv) /\
    op_taint tm (Var out) = {} /\ op_prov H (Var out) = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    local_ptrs_reserved cenv s1 /\ not_fresh_at s1 dst /\ not_fresh_at s1 out /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s)
Proof
  strip_tac >>
  `word_value fv` by metis_tac[word_value_type_typed] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `type_memory_size ftv = 32` by metis_tac[word_value_type_memory_size] >>
  drule_all ghost_inv_struct_field_inputs >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `mload (w2n (a + n2w (struct_field_offset flds fld))) s = val_to_w256 fv` by
    (drule_all stmt_state_rel_field_word >>
     simp[typed_val_to_w256_word_value]) >>
  drule_all augassign_field_load_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`, `sf`] >> simp[]
QED
