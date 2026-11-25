Theory createCtorEncoderWordRowMods
Ancestors
  createExprSizeExitDefsMods bodyFullPostsMods bodyFullShadowBodyInv bodyFullExtCallDirectWord
  abiEncodeValuesWordRow exprSimAbiEncodePlanMetadata entryDecodeStaticProps
  stateRelProj allocaSiteResource exprLoweringProps
  fragGasOriginPtr fragExec abiEncoderWindowPhase exprSimAbiEncodeExecFrame
  exprLowering compileEnv context contractABI loweringStateRelDefs bodyPtrDefs
  venomState venomInst finite_map pred_set list arithmetic pair words
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

(* A word row writes exactly one 32-byte head. The phase callback lifts
   that machine effect to the linked saved state. *)
Theorem ctor_encoder_word_row_mods:
  ty = lowered_value_type ce e /\ is_word_type ty /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op. saved = StackValue tag op) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  local_ptrs_reserved ce si /\ ss.cs_next_var <= se.cs_next_var /\
  (!l. vv_operand saved <> Label l) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ read_result cx raw ee = (INL v,ee) /\
  value_has_type rt v /\ type_memory_bytes ce ty = type_memory_size rt /\
  vv_holds_mods ce cx ty raw saved ee s /\ ptr_vv_ok cx ty raw saved ee G tn s /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\ shared <> loc /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] a = ((),c) /\
  fn_has_code a c func /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  (!a c ids outs u Gu tu z Gz tz.
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix a u Gu tu /\
    ci_mono a c /\ window_phase ctx func a c ids outs u z /\ abi_encode_exec_frame func u z /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    (!x. not_fresh_at a x ==>
      FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
    tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
    shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
    EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
    (!aid. aid IN shared INSERT ids ==>
      ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
    (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
      (!aid p n. aid IN ids /\ FLOOKUP z.vs_allocas aid = SOME (p,n) ==>
        i < p \/ p+n <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem) ==>
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz) ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?tag src. saved = StackValue tag src` by
    (qpat_x_assum `(?tag op. saved = StackValue tag op) \/ _` mp_tac >> simp[]) >>
  qpat_x_assum `saved = StackValue tag src` SUBST_ALL_TAC >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  `stmt_state_rel hz ctx func ce cx ee u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
      (qspec_then `hz` (drule_then (ACCEPT_TAC o cj 1)))) >>
  drule_then (assume_tac o cj 2) stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `allocas_from lo u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
      (qspec_then `hz` (drule_then
        (ACCEPT_TAC o cj 7 o REWRITE_RULE [ghost_inv_at_mods_def] o cj 4)))) >>
  `eval_operand src u = SOME (typed_val_to_w256 rt v) /\ op_taint tu src = {} /\
   (!x. src = Var x ==> not_fresh_at a x)` by
    (mp_tac (Q.INST [`tv` |-> `rt`, `saved` |-> `StackValue tag src`] extcall_direct_word_source) >>
     impl_tac >-
       (qpat_assum `vv_holds_mods _ _ _ _ _ _ _`
          (assume_tac o SIMP_RULE (srw_ss()) [vv_holds_mods_def]) >>
        asm_rewrite_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `abi_member_head_size at = 32` by
    metis_tac[abi_encode_translated_head, entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
  `pbase+capacity <= u.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `ci_mono a c` by metis_tac[ci_mono_compile_abi_encode_value_rows, SND] >>
  drule_then (drule_then (mp_tac o Q.INST
    [`env` |-> `get_tenv cx`, `b` |-> `pbase`, `cap` |-> `capacity-dst_offset`,
     `owner` |-> `shared`, `tv` |-> `rt`] o SPEC_ALL))
    abi_encode_values_word_prefix >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  qpat_assum `!a c ids outs u Gu tu z Gz tz. _` irule >>
  qpat_assum `window_phase ctx func a c {} _ u z` (irule_at Any) >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a u Gu tu`
    (irule_at Any) >>
  `pbase+dst_offset+h+32 <= pbase+capacity` by decide_tac >>
  asm_simp_tac (srw_ss()) [] >>
  conj_tac
  >- (qpat_assum `tz.t_mem SUBSET tu.t_mem` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
      simp[]) >>
  qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[]
QED
