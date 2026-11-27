(* Actual-site resources at one physical successful child endpoint. *)
Theory bodyFullAbiDecodeCallerSetupEntry
Ancestors
  bodyFullAbiDecodeCallerEntry exprSimAbiDecodeResources
  exprSimAbiDecodeInputBound exprSimAbiDecodeBodyEntry
  bodyPtrEnvBuiltinsHashInput abiArgsLabelBoundary abiBuiltinDecodeSetup
  exprLoweringProps representationCleanPtr exprSimAbiDecodeEntryTyping
  exprSimHyps vyperValue compileEnv exprOperandVar exprSimAbiDecodeLiveFrame
  exprSafeOperand exprSimHypsDefs exprOpenFirstOperand
  bodyInvSplit[qualified]

val caller_setup_pre = ``\data min_size max_size outsz st ready ops s G tn b data_var d.
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (?H : (bool # bytes32 # type_value) list # num list. V H) /\
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name a sz. local_region ce es0.scopes s0 name a sz ==>
    a+sz <= s.vs_alloca_next) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  data = Var data_var /\ eval_operand data s = SOME (n2w b) /\
  op_taint tn data = {} /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_decode_ptr_window G tn s data_var (n2w b) (32+LENGTH input_bytes) /\
  mload b s = n2w (LENGTH input_bytes) /\
  mem_bytes_at (b+32) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  b+32+LENGTH input_bytes <= s.vs_alloca_next /\
  b+32+LENGTH input_bytes < dimword (:256) /\
  min_size <= max_size /\ max_size < dimword (:256) /\
  outsz < dimword (:256) /\ d+outsz < dimword (:256) /\
  (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
     SOME (d,outsz))``;

Theorem abi_decode_body_setup_entry:
  !mods exps.
  (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es0 /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  wty = (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) /\
  min_size = abi_static_size ce.ce_struct_fields wty /\
  max_size = abi_size_bound ce.ce_struct_fields wty /\
  outsz = type_memory_bytes ce wty /\
  lower_value compile_expr ce (expr_type e) e origin = (data,st) /\
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
    min_size max_size outsz st = (out,final) /\
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st final fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce origin /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (?H : (bool # bytes32 # type_value) list # num list. V H) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es0 s0) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_history fn s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!H. V H ==>
    expr_post H ctx fn ce cx e es0 origin st s0 es (BytesV input_bytes) data s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ptr_val_ok cx (post_value_type ce e) (BytesV input_bytes) data G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) ==>
  ?b data_var d.
    (^caller_setup_pre) data min_size max_size outsz st ready ops s G tn b data_var d
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `cs_extends origin st /\ origin.cs_next_var <= st.cs_next_var` by
    metis_tac[compile_expr_grows] >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `origin` >> simp[]) >>
  `max_size < dimword (:256)` by
    (drule_all abi_decode_body_input_word_bound >> simp[]) >>
  `outsz < dimword (:256)` by
    (drule abi_decode_body_output_bound >> simp[wordsTheory.dimword_def]) >>
  qpat_assum `?H. V H` (qx_choose_then `H` assume_tac) >>
  qpat_assum `!H. V H ==> _ /\ _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic n)))` by
    (`IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
       metis_tac[expr_body_pre_type_builtin_head, expr_body_pre_type_evaluates] >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `~is_word_type (expr_type e)` by simp[compileEnvTheory.is_word_type_def] >>
  qpat_x_assum `min_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `max_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  drule_all abi_decode_caller_resources >>
  disch_then (qx_choose_then `b` (qx_choose_then `d`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `post_value_type ce e = expr_type e` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     simp[compileEnvTheory.is_bytestring_type_def]) >>
  `ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV input_bytes) data G tn s` by
    metis_tac[] >>
  `?p. data = Var p /\ ptr_covers G tn p s (32+LENGTH input_bytes)` by
    (irule ptr_val_ok_read_covers >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`cx`, `BaseTV (BytesT (Dynamic n))`, `expr_type e`,
       `BytesV input_bytes`] >>
     simp[loweringPostsTheory.val_footprint_def]) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
     SOME (BaseTV (BytesT (Dynamic n)))` by metis_tac[] >>
  drule_all ptr_val_ok_bytes_read_clean >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `data = Var p` SUBST_ALL_TAC >>
  `op_taint tn (Var p) = {}` by fs[bodyPtrDefsTheory.ptr_covers_def] >>
  `abi_decode_ptr_window G tn s p (n2w b) (32+LENGTH input_bytes)` by
    (simp[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >>
     conj_tac >- fs[venomStateTheory.eval_operand_def] >>
     rpt strip_tac >> Cases_on `i < w2n (n2w b : bytes32) + 32`
     >- (gvs[]) >>
     qpat_x_assum `!i. w2n (n2w b) + 32 <= i /\ _ ==> _`
       (qspec_then `i` mp_tac) >> gs[] >> decide_tac) >>
  `fn_has_code st ready fn` by
    (`cs_extends st ready` by
       (drule abi_builtin_decode_setup_shape >> strip_tac >>
        simp[compileEnvTheory.cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
     `cs_extends ready final` by
       (drule abiBuiltinDecodeCorrectTheory.lower_abi_decode_setup_trace >>
        disch_then (qx_choose_then `other_ops` (qx_choose_then `other_ready`
          (CONJUNCTS_THEN2 mp_tac (CONJUNCTS_THEN assume_tac)))) >>
        asm_rewrite_tac[] >> simp[] >> strip_tac >>
        mp_tac (cj 1 abiDecoderAppendTheory.cs_appends_abi_decode_mutual) >>
        simp[fragExecTheory.cs_appends_def] >> metis_tac[]) >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  `stmt_state_rel H ctx fn ce cx es0 s0` by metis_tac[] >>
  `alloca_inv s0` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  qpat_assum `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [exprSimAbiDecodeBuiltinTheory.abi_builtin_decode_site_resources_def]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >>
     metis_tac[actualDecoderSitesTheory.decode_site_resources_def]) >>
  `b+32+LENGTH input_bytes < dimword (:256)` by
    metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS] >>
  qpat_x_assum `wty = _` kall_tac >>
  qexistsl_tac [`b`, `p`, `d`] >> BETA_TAC >> asm_rewrite_tac[] >>
  conj_tac >- fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  conj_tac >-
    (rpt strip_tac >>
     `off+sz <= s0.vs_alloca_next` by
       metis_tac[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     simp[]) >>
  conj_tac >-
    (rpt strip_tac >> drule_all abi_args_local_region_frontier >> simp[]) >>
  conj_tac >-
    (qx_gen_tac `hhorizon` >> strip_tac >>
     qpat_assum `!H. V H ==> expr_post H ctx fn ce cx e es0 origin st s0 es _ _ s /\ _`
       (qspec_then `hhorizon` mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[exprSimWordArgsTheory.expr_post_state]) >>
  conj_tac >-
    (`not_fresh_at st p` by metis_tac[compile_lower_value_var] >>
     fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
        abiDecoderReentryTheory.abi_decoder_older_vars_def,
        loweringStateRelDefsTheory.not_fresh_at_def]) >>
  conj_tac >-
    (drule representationCleanPtrTheory.val_in_memory_bytes_word >>
     simp[valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  conj_tac >-
    (irule representationCleanPtrTheory.val_in_memory_bytes_payload >>
     qexists_tac `BaseTV (BytesT (Dynamic n))` >> simp[]) >>
  simp[abiDecoderLayoutBoundsTheory.abi_static_size_le_size_bound] >>
  fs[abiDecoderFrameTheory.abi_footprint_disjoint_def]
QED
