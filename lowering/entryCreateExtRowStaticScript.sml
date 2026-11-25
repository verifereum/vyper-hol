Theory entryCreateExtRowStatic
Ancestors
  bodyFullExtCallDirectRow bodyFullExtCallDirectState abiEncodeValuesStatic
  entryCreatePathScope entryCreateCompletedCut entryCreateFocusSpec
  exprLoweringProps fragExec fragGasOriginPtr compileEnv venomState venomInst
  abiEncoderProps pred_set list arithmetic words

(* Work backwards from the final cut. The two lifts need only exclude
   its fetch from the earlier row band, not from the installed function. *)
Theorem static_row_scope_compose[local]:
  ci_mono su a /\ ci_mono a b /\ ci_mono b en /\
  (!bb i. lookup_block en.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids su en) /\
  create_operand_full_scope su a E C fn x [] (OK y) /\
  create_operand_full_scope a b E C fn y [] (OK z) /\
  create_operand_full_scope b en E C fn z [] (OK t) ==>
  create_operand_full_scope su en E C fn x [] (OK t)
Proof
  simp[ci_mono_def] >> strip_tac >>
  `a.cs_next_id <= en.cs_next_id` by decide_tac >>
  `create_operand_full_scope a en E C fn y [] (OK t)` by
    (irule (SIMP_RULE bool_ss [APPEND]
       (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_operand_full_scope_prepend)) >>
     qexistsl_tac [`b`,`z`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!bb i. _ ==> _ NOTIN frag_ids su en`
       (qspecl_then [`bb`,`i`] mp_tac) >> fs[frag_ids_def] >> decide_tac) >>
  irule (SIMP_RULE bool_ss [APPEND]
    (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_operand_full_scope_prepend)) >>
  qexistsl_tac [`a`,`y`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!bb i. _ ==> _ NOTIN frag_ids su en`
    (qspecl_then [`bb`,`i`] mp_tac) >> fs[frag_ids_def] >> decide_tac
QED

Theorem extcall_static_pack_row_from_scoped_phases:
  abi_static_row_restore (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
    ctx func ce cx st0 ee DF lo explicit PG d se s G tn
    shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i /\
  abi_values_source_phase ctx func lo explicit PG
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)) /\
  (!a b p u. emit_op ADD [Var dst; Lit (n2w h)] a = (Var p,b) /\
    fn_has_code a b func /\ ~u.vs_halted /\ create_operand_at a u /\
    lookup_var dst u = SOME (n2w (pbase+dst_offset)) ==>
    create_operand_full_scope a b explicit ctx func u []
      (OK ((update_var p (n2w (pbase+dst_offset) + n2w h) u) with
              vs_inst_idx := SUC u.vs_inst_idx))) /\
  (!bb i. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids su en) /\
  ~is_word_type ty /\ ~is_dynamic at /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  fn_has_code su en func /\ compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\ shared < loc /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  value_has_type tv v /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    create_operand_full_scope su en explicit ctx func u [] (OK z)
Proof
  simp_tac bool_ss [create_operand_at_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`R` |-> `\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)`]
    abi_encode_saved_static_row_phase) >>
  simp_tac bool_ss [] >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (rpt strip_tac >> simp[create_operand_full_scope_def])
     >- (rpt strip_tac >> first_assum irule >> simp[]) >>
     map_every qx_gen_tac [`a`,`b`,`x`,`y`,`w`,`t`] >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     irule static_row_scope_compose >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`a`,`b`,`y`,`w`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
