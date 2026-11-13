Theory extRetRecursiveResourceEntryPtr
Ancestors
  extRetRecursiveResourcePtr extRetScratchResourcePtr extRetEncoderScratchSitesPtr
  extRetBufferStatePtr exprLoweringProps loweringHalt abiEncoderWindowContract
  abiEncoderProps compileEnv venomState finite_map pred_set arithmetic words

Theorem scratch_resource_live_bound:
  scratch_resource ctx fn sites q len s /\ len <> 0 ==>
  q+len < dimword(:256)
Proof
  simp[scratch_resource_def] >> strip_tac >>
  drule alloca_room_next_lt >> decide_tac
QED

Theorem encoder_return_buffer_resource:
  lower_value compile_expr cenv ret e sa = (op,sb) /\
  compile_alloc_buffer cenv.ce_max_return_size sb = (buf,st) /\
  compile_abi_encode_to_buf buf.buf_operand op ei st = (result,en) /\
  fn_has_code st en fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\
  FLOOKUP s.vs_allocas sb.cs_next_id = SOME (b,cenv.ce_max_return_size) ==>
  encoder_resource ctx fn (window_alloca_sites fn (frag_ids st en))
    (w2n w) (val_footprint tv v) [(sb.cs_next_id,b,cenv.ce_max_return_size)] s
Proof
  strip_tac >> drule_all encoder_return_buffer_scratch_resource >> strip_tac >>
  irule encoder_resource_registered_intro >> simp[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  simp[window_alloca_sites_def, frag_ids_def]
QED

Theorem encoder_normalized_window_resource:
  compile_abi_encode_to_buf dst src ei st = (result,en) /\
  fn_has_code st en fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv st /\ sb.cs_next_id <= st.cs_next_id /\
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ did < st.cs_next_id /\
  FLOOKUP s.vs_allocas did = SOME (b,cap) ==>
  encoder_resource ctx fn (window_alloca_sites fn (frag_ids st en))
    (w2n w) (val_footprint tv v) [(did,b,cap)] s
Proof
  strip_tac >> drule_all encoder_window_scratch_resource >> strip_tac >>
  irule encoder_resource_registered_intro >> simp[] >>
  simp[window_alloca_sites_def, frag_ids_def]
QED

(* The destination registration in encoder_return_buffer_resource is produced
   by the counted allocation, not assumed at the source endpoint. *)
Theorem encoder_return_buffer_resource_counted:
  lower_value compile_expr cenv ret e sa = (Var src,sb) /\
  compile_alloc_buffer cenv.ce_max_return_size sb = (buf,st) /\
  compile_abi_encode_to_buf buf.buf_operand (Var src) ei st = (result,en) /\
  fn_has_code sb st fn /\ fn_has_code st en fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v (Var src) s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  lookup_var src s = SOME w /\ not_fresh_at sb src /\
  not_local_ptr cenv es.scopes (STRING #"%" (toString sb.cs_next_var)) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ cenv.ce_max_return_size < dimword(:256) ==>
  ?ip b Gf tnf sf.
    buf.buf_operand = Var ip /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = st.cs_current_bb /\
    sf.vs_inst_idx = LENGTH st.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var ip sf = SOME (n2w b) /\
    ptr_covers Gf tnf ip sf cenv.ce_max_return_size /\
    lookup_var src sf = SOME w /\
    encoder_resource ctx fn (window_alloca_sites fn (frag_ids st en))
      (w2n w) (val_footprint tv v) [(sb.cs_next_id,b,cenv.ce_max_return_size)] sf
Proof
  strip_tac >> drule_all compile_alloc_buffer_state_counted_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `lookup_var src sf = SOME w` by metis_tac[] >>
  `expr_val_at cenv cx ty sa sb es v (Var src) sf` by
    (first_x_assum irule >> simp[eval_operand_def]) >>
  qexistsl_tac [`ip`,`addr`,`Gf`,`tnf`,`sf`] >> simp[] >>
  irule encoder_return_buffer_resource >> simp[] >>
  metis_tac[eval_operand_def]
QED
