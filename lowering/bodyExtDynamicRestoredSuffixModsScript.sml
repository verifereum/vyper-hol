(* Run the encoder and offset/cursor suffix at the actual restored cut.
   Only the encoder interval owns encoder scratch sites. *)
Theory bodyExtDynamicRestoredSuffixMods
Ancestors
  bodyAbiEncodeRestoredInputMods abiEncodeValuesDynamicPrefix
  abiEncoderAdmissible abiEncoderWindowPhase
  abiEncoderWindowContract exprSimAbiEncodeExecFrame exprLoweringProps
  exprLowering compileEnv loweringPosts loweringStateRelDefs bodyPtrDefs
  fragGasOriginPtr fragExec context vyperABI vyperValue vyperTyping
  contractABI venomState venomInst venomMemDefs finite_map words list pair

Theorem ext_dynamic_restored_suffix_mods:
  abi_encode_values_prefix_at ats avs hl d (Var cursor) loc slot i ready z Gz tz /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ is_dynamic at /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\
  at = vyper_to_abi_type (get_tenv cx) ty /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ bytes = enc at av /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!typ rt. evaluate_type (get_tenv cx) typ = SOME rt ==>
    type_memory_bytes ce typ = type_memory_size rt) /\
  stmt_state_rel H ctx func ce cx ee z /\ expr_val_at ce cx ty first last ee v src z /\
  expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\
  expr_store_bound cx ty v src z /\ last.cs_next_id <= ready.cs_next_id /\
  local_ptrs_reserved ce ready /\
  MEM inst (fn_insts func) /\ inst.inst_id = owner /\ inst.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  (owner < first.cs_next_id \/ last.cs_next_id <= owner) /\
  FLOOKUP z.vs_allocas owner = SOME (b,capacity) /\
  owner < ready.cs_next_id /\ owner <> loc /\ b <= d /\
  d+off+LENGTH bytes <= b+capacity /\
  unwrap_value ce saved prepared = (src,ready) /\
  compile_abi_encode_to_buf (Var tail) src
    (type_to_abi_enc_info ce.ce_struct_fields ce ty) ready = (len,encoded) /\
  abi_encode_child_suffix (Var head) (Var cursor) offset len encoded = (len,en) /\
  fn_has_code ready encoded func /\ fn_has_code encoded en func /\
  fn_inst_ids_distinct func /\ ci_mono ready en /\
  eval_operand (Var tail) z = SOME (n2w (d+off)) /\
  eval_operand (Var head) z = SOME (n2w (d+h)) /\
  eval_operand offset z = SOME (n2w off) /\ op_taint tz offset = {} /\
  (!x. src = Var x \/ Var tail = Var x \/ Var head = Var x \/ offset = Var x ==>
    not_fresh_at ready x) /\
  ptr_covers Gz tz head z 32 /\ ptr_covers Gz tz tail z (LENGTH bytes) /\
  alloca_inv z /\ alloca_room ctx func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z /\
    z.vs_alloca_next + pending_alloca_size func z <= w2n z.vs_initial_fmp) /\
  ~z.vs_halted /\ z.vs_current_bb = ready.cs_current_bb /\
  z.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?t Gt tt.
    abi_encode_values_prefix_at ats avs hl d (Var cursor) loc slot (SUC i) en t Gt tt /\
    window_phase ctx func ready en (loc INSERT window_alloca_sites func (frag_ids ready encoded))
      [(d+h,32);(d+off,LENGTH bytes)] z t /\
    abi_encode_exec_frame func z t /\
    (!x. not_fresh_at ready x ==>
      FLOOKUP Gt x = FLOOKUP Gz x /\ op_taint tt (Var x) = op_taint tz (Var x)) /\
    (!j. (j < d+h \/ d+h+32 <= j) /\
      (j < d+off \/ d+off+LENGTH bytes <= j) /\
      (!aid p sz. aid IN (loc INSERT window_alloca_sites func (frag_ids ready encoded)) /\
        FLOOKUP t.vs_allocas aid = SOME (p,sz) ==> j < p \/ p+sz <= j) ==>
      (j IN tt.t_mem <=> j IN tz.t_mem)) /\
    tt.t_stor = tz.t_stor /\ tt.t_trans = tz.t_trans /\ tt.t_imm = tz.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,Gt,tt)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_abi_encode_payload ce T [saved] [ty] (Var tail) prepared = (len,encoded)` by
    asm_simp_tac (srw_ss()) [compile_abi_encode_payload_def,comp_bind_def,LET_THM] >>
  `get_tenv cx SUBMAP get_tenv cx` by simp[] >>
  `bytes = enc (vyper_to_abi_type (get_tenv cx) ty) av` by
    (qpat_assum `at = vyper_to_abi_type _ _` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  `b <= d+off` by decide_tac >>
  qpat_x_assum `inst.inst_id = owner` (SUBST_ALL_TAC o SYM) >>
  drule_all (Q.INST [`d` |-> `d + off`, `E0` |-> `get_tenv cx`]
    abi_encode_restored_window_input_mods) >>
  disch_then (qx_choosel_then [`w`,`ct`,`rv`] (map_every assume_tac o CONJUNCTS)) >>
  `abi_encoder_admissible (type_to_abi_enc_info ce.ce_struct_fields ce ty)` by
    simp[abi_encoder_translation_admissible] >>
  `op_taint tz (Var tail) = {}` by
    (qpat_assum `ptr_covers Gz tz tail z _` (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [ptr_covers_def])) >>
  `eval_operand src z = SOME (n2w (w2n w))` by simp[] >>
  irule abi_encode_values_dynamic_prefix_input >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (qexistsl [`b`,`capacity`,`inst.inst_id`] >> asm_rewrite_tac[])
  >- (qexistsl [`at`,`av`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `compile_abi_encode_to_buf _ _ _ ready = _` (irule_at Any) >>
  qpat_assum `abi_encode_child_suffix _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl [`w2n w`,`rv`,`ct`,`val_footprint tv v`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
