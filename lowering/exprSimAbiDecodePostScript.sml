(* Postcondition closure used by the relabeled counted decoder bridge. *)
Theory exprSimAbiDecodePost
Ancestors
  loweringPosts exprLoweringProps venomState compileEnv venomMemDefs

Definition abi_decode_post_closure_def:
  abi_decode_post_closure post t <=>
    ?u rd p. post u /\
      t = u with <|vs_returndata := rd; vs_prev_bb := p|>
End

Theorem abi_decode_post_closure_intro:
  post t ==> abi_decode_post_closure post t
Proof
  strip_tac >> simp[abi_decode_post_closure_def] >>
  qexistsl [`t`, `t.vs_returndata`, `t.vs_prev_bb`] >> simp[]
QED

Theorem abi_decode_post_closure_returndata:
  abi_decode_post_closure post t ==>
  abi_decode_post_closure post (t with vs_returndata := rd)
Proof
  rw[abi_decode_post_closure_def] >>
  qexistsl [`u`, `rd`, `p`] >> simp[]
QED

Theorem abi_decode_post_closure_prev_bb:
  abi_decode_post_closure post t ==>
  abi_decode_post_closure post (t with vs_prev_bb := p)
Proof
  rw[abi_decode_post_closure_def] >>
  qexistsl [`u`, `rd`, `p`] >> simp[]
QED

Theorem abi_decode_stmt_state_rel_control:
  stmt_state_rel ctx func ce cx es
    (s with <|vs_returndata := rd; vs_prev_bb := p|>) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       fmp_room_def, pending_alloca_size_def, immutable_alloca_sep_def,
       immutable_base_zero_alt, accounts_rel_def]
QED

Theorem abi_decode_eval_operand_control:
  eval_operand op (s with <|vs_returndata := rd; vs_prev_bb := p|>) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_vv_post_control:
  vv_post ctx func ce cx e es sa sb s0 es' tv vv
    (s with <|vs_returndata := rd; vs_prev_bb := p|>) <=>
  vv_post ctx func ce cx e es sa sb s0 es' tv vv s
Proof
  Cases_on `vv` >>
  simp[vv_post_def, abi_decode_stmt_state_rel_control, vv_holds_def,
       vv_at_def, expr_val_rel_def, expr_val_at_def, abi_decode_eval_operand_control,
       lookup_var_def, local_region_def, locals_kept_def,
       dynarray_free_def, storage_holds_def, immutable_holds_def,
       contract_storage_def, contract_transient_def]
QED

Theorem abi_decode_post_closure_vv_post:
  abi_decode_post_closure
    (vv_post ctx func ce cx e es sa sb s0 es' tv vv) s ==>
  vv_post ctx func ce cx e es sa sb s0 es' tv vv s
Proof
  rw[abi_decode_post_closure_def] >>
  simp[SRULE [] abi_decode_vv_post_control]
QED
