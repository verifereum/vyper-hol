(* Physical input and setup resources at the linked decoder operand cut. *)
Theory bodyAbiDecodeOpenMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyTypeBuiltinAbiMods
  exprBodyPreProps exprSimHypsDefs exprSimHyps exprSimWordArgs
  exprSimAbiDecodeEntryTyping exprSimAbiDecodeEntryMetadata
  exprSimAbiDecodeEntryCoherence abiDecoderCoherence
  exprSimAbiDecodeResources exprSimAbiDecodeFootprint exprSimAbiDecodeBuiltin
  bodyPtrEnvBuiltinsHashInput exprOpenFirstOperand exprOperandVar
  abiBuiltinDecodeCorrect abiBuiltinDecodeSetup abiDecoderAppend abiDecoderReentry
  abiBuiltinAllocation abiDecodePtrMemberFrame abiDecoderLayoutBounds abiArgsLabelBoundary
  representationCleanPtr loweringPosts loweringStateRelDefs
  stateRelProj exprLoweringProps compileEnv allocLimits vyperTypeInvariants
  vyperValue vyperAST abiDecoderFrame bodyPtrDefs ptrDiscipline venomMemDefs venomState
  actualDecoderSites fragExec finite_map list words arithmetic

Theorem abi_decode_static_mods[local]:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  wty = (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n))) /\
  abi_size_bound ce.ce_struct_fields wty < dimword (:256) /\
  type_memory_bytes ce wty < dimword (:256) /\
  assignable_type (get_tenv cx) wty /\
  abi_decode_bytes_widths (get_tenv cx) wty /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields wty
    (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv) /\
  type_memory_bytes ce wty = type_memory_size
    (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)
Proof
  strip_tac >>
  `alloc_limits_expr ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])` by
    fs[expr_body_pre_mods_def] >>
  drule_then assume_tac alloc_limits_abi_decode_output >>
  drule_all_then assume_tac alloc_limits_abi_decode_bound >>
  `type_alloc_ok ce (expr_type e)` by
    (irule alloc_limits_expr_type_alloc_ok >>
     qpat_assum `alloc_limits_expr _ (TypeBuiltin _ _ _ _)`
       (mp_tac o PURE_REWRITE_RULE [Once alloc_limits_expr_def]) >>
     simp[Once alloc_limits_expr_def]) >>
  `n < 2 ** 64` by
    (qpat_x_assum `type_alloc_ok _ _` mp_tac >>
     simp[type_alloc_ok_def, is_word_type_def, type_memory_bytes_def] >>
     qspec_then `n` mp_tac abi_builtin_word_size_capacity >> simp[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `abi_size_bound ce.ce_struct_fields wty < dimword (:256) /\
   type_memory_bytes ce wty < dimword (:256)` by (gvs[dimword_def] >> decide_tac) >>
  conj_tac
  >- (simp[Once evaluate_type_def, type_slot_size_def,
           vfmConstantsTheory.word_size_def, dimword_def] >>
      qspec_then `32` mp_tac DIV_LESS_EQ >> simp[] >>
      disch_then (qspec_then `n + 31` assume_tac) >>
      qpat_assum `n < 2 ** 64` (assume_tac o SIMP_RULE (srw_ss()) []) >>
      qabbrev_tac `slots = (n + 31) DIV 32` >> decide_tac) >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule abi_decode_parent_type >> strip_tac >>
  `env.type_defs = get_tenv cx /\ abi_decode_root_metadata ce (get_tenv cx)` by
    (drule_then assume_tac expr_body_pre_mods_inv >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def,
          env_consistent_def, env_context_consistent_def]) >>
     simp[abi_decode_root_metadata_def] >> rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP ce.ce_struct_fields _ = _ ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `assignable_type (get_tenv cx) wty /\ abi_decode_bytes_widths (get_tenv cx) wty` by
    (conj_tac
     >- (gvs[] >> irule abi_decode_wrapped_assignable >> simp[]) >>
     gvs[] >> irule abi_decode_wrapped_widths >> simp[]) >>
  `evaluate_type (get_tenv cx) wty =
     SOME (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)` by
    gvs[abi_decode_wrapped_type] >>
  drule_all_then assume_tac abi_decode_root_coherent >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def]
QED

Theorem abi_decode_input_window_mods[local]:
  expr_post (H:(bool # bytes32 # type_value) list # num list)
    ctx fn ce cx e es0 origin st s0 es (BytesV bs) data s /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n))) /\
  ptr_val_ok cx (post_value_type ce e) (BytesV bs) data G tn s /\
  eval_operand data s = SOME (n2w b) /\ b + 32 + LENGTH bs < dimword (:256) ==>
  (?p. data = Var p /\ op_taint tn data = {} /\
       abi_decode_ptr_window G tn s p (n2w b) (32 + LENGTH bs)) /\
  ((?aid ib isz. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
       ib <= b + 32 /\ b + 32 + LENGTH bs <= ib + isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
       ib <= b + 32 /\ b + 32 + LENGTH bs <= ib + isz))
Proof
  strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  conj_tac
  >- (`post_value_type ce e = expr_type e` by
        simp[post_value_type_bytestring, is_bytestring_type_def] >>
      `ptr_val_ok cx (expr_type e) (BytesV bs) data G tn s` by metis_tac[] >>
      `?p. data = Var p /\ ptr_covers G tn p s (32 + LENGTH bs)` by
        (irule ptr_val_ok_read_covers >> conj_tac >- (qexists `n2w b` >> simp[]) >>
         qexistsl_tac [`cx`, `BaseTV (BytesT (Dynamic n))`, `expr_type e`, `BytesV bs`] >>
         asm_rewrite_tac[] >> simp[val_footprint_def]) >>
      `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
         SOME (BaseTV (BytesT (Dynamic n)))` by metis_tac[] >>
      `ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) data G tn s` by
        metis_tac[] >>
      drule_all_then strip_assume_tac ptr_val_ok_bytes_read_clean >>
      gvs[ptr_covers_def, abi_decode_ptr_window_def, eval_operand_def] >>
      rpt strip_tac >> Cases_on `i < b + 32` >> gvs[] >>
      qpat_x_assum `!i. b + 32 <= i /\ _ ==> _` (qspec_then `i` mp_tac) >>
      simp[] >> decide_tac) >>
  drule_all abi_decode_bytes_post_footprint >>
  disch_then (qx_choose_then `p` strip_assume_tac) >>
  `b = p` by
    (`(n2w b : bytes32) = n2w p` by metis_tac[optionTheory.SOME_11] >>
     pop_assum mp_tac >> simp[n2w_11]) >>
  gvs[] >> metis_tac[LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]
QED

(* Nothing is executed here. The same setup witnesses identify the input
   window and the guarded decoder interval; the frame is kept at the cut. *)
Theorem abi_decode_open_entry_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es0 /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  wty = (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  wtv = (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv) /\
  lower_value compile_expr ce (expr_type e) e origin = (data,st) /\
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
    (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
    (type_memory_bytes ce wty) st = (out,final) /\
  fn_has_code st final fn /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved ce origin /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_history fn s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (?H:(bool # bytes32 # type_value) list # num list. V H) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es0 s0) /\
  (!H. V H ==>
    expr_post_mods H ctx fn ce cx e es0 origin st s0 es (BytesV bs) data s /\
    ghost_inv_at_mods (DF H) lo delta ce cx es G tn s /\
    ptr_val_ok cx (post_value_type ce e) (BytesV bs) data G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) ==>
  assignable_type (get_tenv cx) wty /\ abi_decode_bytes_widths (get_tenv cx) wty /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields wty wtv /\
  type_memory_bytes ce wty = type_memory_size wtv /\
  EXISTS (occurs_abi_decode_target ty o SND) mods /\
  (?b p d ops ready.
    abi_builtin_decode_setup data (abi_static_size ce.ce_struct_fields wty)
      (abi_size_bound ce.ce_struct_fields wty) (type_memory_bytes ce wty) st = (ops,ready) /\
    compile_abi_decode_to_buf (FST ops) (Lit 0w) MLOAD (FST (SND ops)) (SND (SND ops))
      (type_to_abi_dec_info ce.ce_struct_fields ce wty) ready = ((),final) /\
    out = FST ops /\ fn_has_code st ready fn /\ fn_has_code ready final fn /\
    fn_inst_ids_distinct fn /\ local_ptrs_reserved ce st /\
    origin.cs_next_var <= st.cs_next_var /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    alloca_history fn s /\ lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    (?H. V H) /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off + sz <= s.vs_alloca_next) /\
    (!name a sz. local_region ce es0.scopes s0 name a sz ==> a + sz <= s.vs_alloca_next) /\
    (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
      immutable_frame_mods fn ce cx es s /\
      ghost_inv_at_mods (DF H) lo delta ce cx es G tn s /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
    data = Var p /\ eval_operand data s = SOME (n2w b) /\ op_taint tn data = {} /\
    abi_decoder_operand_live st.cs_next_var data /\
    abi_decode_ptr_window G tn s p (n2w b) (32 + LENGTH bs) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) b s.vs_memory /\
    mload b s = n2w (LENGTH bs) /\ mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 + LENGTH bs < dimword (:256) /\
    abi_static_size ce.ce_struct_fields wty <= abi_size_bound ce.ce_struct_fields wty /\
    abi_size_bound ce.ce_struct_fields wty < dimword (:256) /\
    type_memory_bytes ce wty < dimword (:256) /\
    abi_builtin_decode_site_resources ctx fn st final.cs_next_id
      (abi_static_size ce.ce_struct_fields wty) (abi_size_bound ce.ce_struct_fields wty)
      (type_memory_bytes ce wty) (LENGTH bs) b d s /\
    ((?aid ib isz.
        aid < abi_builtin_decode_output_site st (abi_static_size ce.ce_struct_fields wty)
          (abi_size_bound ce.ce_struct_fields wty) /\
        FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
        ib <= b + 32 /\ b + 32 + LENGTH bs <= ib + isz) \/
     (?name ib isz. local_region ce es.scopes s name ib isz /\
        ib <= b + 32 /\ b + 32 + LENGTH bs <= ib + isz)))
Proof
  strip_tac >> drule_all abi_decode_static_mods >> strip_tac >>
  drule abi_decode_entry_inputs_mods >> strip_tac >>
  `?ops ready. abi_builtin_decode_setup data (abi_static_size ce.ce_struct_fields wty)
      (abi_size_bound ce.ce_struct_fields wty) (type_memory_bytes ce wty) st = (ops,ready) /\
    compile_abi_decode_to_buf (FST ops) (Lit 0w) MLOAD (FST (SND ops)) (SND (SND ops))
      (type_to_abi_dec_info ce.ce_struct_fields ce wty) ready = ((),final) /\
    out = FST ops` by (drule lower_abi_decode_setup_trace >> simp[]) >>
  pop_assum strip_assume_tac >>
  `cs_extends st ready` by
    (drule abi_builtin_decode_setup_shape >> strip_tac >>
     simp[cs_extends_def] >> qexists `[]` >> simp[]) >>
  drule_then assume_tac cs_extends_abi_decode >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  `origin.cs_next_var <= st.cs_next_var` by metis_tac[compile_expr_grows] >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists `origin` >> simp[]) >>
  rename1 `V h` >>
  qpat_assum `!H. V H ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `h` mp_tac) >>
  pure_rewrite_tac[expr_post_mods_def] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all abi_decode_caller_resources >>
  disch_then (qx_choose_then `b` (qx_choose_then `d` strip_assume_tac)) >>
  `b + 32 + LENGTH bs < dimword (:256)` by
    (qpat_assum `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_builtin_decode_site_resources_def, decode_site_resources_def]) >>
     drule alloca_room_next_lt >> decide_tac) >>
  drule_all abi_decode_input_window_mods >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac) >>
  `abi_decoder_operand_live st.cs_next_var data` by
    (drule_all compile_lower_value_var >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `stmt_state_rel h ctx fn ce cx es0 s0` by metis_tac[] >>
  `alloca_inv s0` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- (qpat_assum `wtv = _` SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`b`,`p`,`d`,`ops`,`ready`] >>
  (* Most fields are exact hypotheses from the reached cut. *)
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac)
  >- (qexists `h` >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> fs[alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac)
  >- (rpt strip_tac >> drule_all abi_args_local_region_frontier >> decide_tac)
  >- (rpt strip_tac >>
      qpat_assum `!H. V H ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
      drule expr_post_state >> simp[])
  >- (drule val_in_memory_bytes_word >> simp[valueEncodingPropsTheory.mem_word_at_eq_mload])
  >- (irule val_in_memory_bytes_payload >> qexists `BaseTV (BytesT (Dynamic n))` >> simp[])
  >- simp[abi_static_size_le_size_bound] >>
  `st.cs_next_id < abi_builtin_decode_output_site st (abi_static_size ce.ce_struct_fields wty)
    (abi_size_bound ce.ce_struct_fields wty)` by simp[abi_builtin_decode_output_site_def] >>
  metis_tac[LESS_TRANS]
QED
