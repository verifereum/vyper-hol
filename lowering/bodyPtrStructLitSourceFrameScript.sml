(* Source postconditions ignore the execution cursor. *)
Theory bodyPtrStructLitSourceFrame
Ancestors
  exprSimVVFrame exprLoweringProps loweringPosts compileEnv venomState venomMemDefs

Theorem stmt_state_rel_pc:
  stmt_state_rel ctx func cenv cx es
    (s with <|vs_current_bb := lbl; vs_inst_idx := idx|>) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  `fmp_room ctx func (s with <|vs_current_bb := lbl; vs_inst_idx := idx|>) <=>
   fmp_room ctx func s` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       accounts_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def,
       immutable_base_zero_alt]
QED

Theorem eval_operand_pc:
  eval_operand op (s with <|vs_current_bb := lbl; vs_inst_idx := idx|>) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem vv_post_pc:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv
    (s with <|vs_current_bb := lbl; vs_inst_idx := idx|>) <=>
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s
Proof
  Cases_on `vv` >>
  simp[vv_post_def, stmt_state_rel_pc, eval_operand_pc, vv_holds_def, vv_at_def,
       expr_val_rel_def, expr_val_at_def, eval_operand_def, lookup_var_def,
       local_region_def, locals_kept_def, storage_holds_def,
       immutable_holds_def, contract_storage_def, contract_transient_def]
QED

Theorem expr_post_pc:
  expr_post ctx func cenv cx e es sa sb s0 es' v op
    (s with <|vs_current_bb := lbl; vs_inst_idx := idx|>) <=>
  expr_post ctx func cenv cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, stmt_state_rel_pc, eval_operand_pc, expr_val_rel_def, expr_val_at_def,
       eval_operand_def, lookup_var_def, local_region_def, locals_kept_def]
QED

Theorem vv_post_update_var_pc:
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_id <= sn.cs_next_id /\ ~not_fresh_at sm x /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) ==>
  vv_post ctx func cenv cx e es sa sn s0 es' tv vv
    (update_var x w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all vv_post_update_var >>
  disch_then (qspec_then `w` assume_tac) >>
  qspec_then `(update_var x w s).vs_current_bb` mp_tac
    (Q.GEN `lbl` vv_post_pc) >> simp[]
QED
