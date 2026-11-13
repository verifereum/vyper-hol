(* Selected-shape scalar tuple encoding; static tuples need no cursor. *)
Theory stmtSimLogScalarEncode
Ancestors
  abiDecoderRange
  stmtSimLogMembersRun stmtSimLogScalarPrefix stmtSimLogScalarMembers
  stmtSimLogEncodeLayout abiEncoderReentryLeaves abiEncoderInputFrame abiEncoderInput
  abiEncoderComplexCode abiEncoderComplexPrefix abiEncoderMemberCode abiBuiltinPrefix
  abiEncoderComplexDynamic abiEncoderMembersInput abiEncoderTuple abiEncoderOpenInput
  abiBuiltinAllocation abiDecoderReentry abiDecoderFrame abiDecoderFrameCompose abiDecoderDynamicLoopSetup
  abiDecoderGuards exprLoweringProps emitHelperProps compileEnv emitHelper abiEncoder
  abiCanonicalWindows valueEncoding contractABI venomState venomInst words list arithmetic finite_map

Theorem log_scalar_tuple_copy_run[local]:
  compile_abi_encode_to_buf dst src (AbiCopy n) st = (out,end_st) /\
  abi_encoder_input (AbiCopy n) (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  n < dimword (:256) /\ LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    abi_decode_footprint_frame [(db,outcap)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  strip_tac >>
  `sb < dimword (:256) /\ db < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_copy_input_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st end_st) initial = OK actual` >>
  `abi_decode_footprint_frame [(db,LENGTH (enc (Tuple ats) (ListV avs)))] initial actual` by
    (irule (iffLR abi_decode_frame_footprint) >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(db,LENGTH (enc (Tuple ats) (ListV avs)))]` >>
  simp[Excl "enc_def"]
QED

Theorem log_scalar_tuple_members_run[local]:
  compile_abi_encode_complex_elems dst src infos 0 0 dp st = (out,end_st) /\
  log_members_run_pre infos ats avs [] [] sb 0 0 db hl outcap st limit_st src dst dp p initial /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. log_members_run_post st end_st limit_st db outcap p initial actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    mload p actual = n2w (LENGTH (enc (Tuple ats) (ListV avs)))
Proof
  strip_tac >> drule_all log_members_run_list >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  qpat_x_assum `log_members_run_pre [] [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [log_members_run_pre_def, APPEND, ADD] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule log_members_layout_complete >> strip_tac >>
  drule log_members_layout_final_length >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem log_scalar_tuple_load[local]:
  emit_op MLOAD [dp] st = (out,end_st) /\
  eval_operand dp initial = SOME (n2w p) /\ p < dimword (:256) /\
  mload p initial = n2w len /\ fresh_vars_wrt limit_st initial /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. log_members_run_post st end_st limit_st db outcap p initial actual /\
    eval_operand out actual = SOME (n2w len) /\ actual.vs_memory = initial.vs_memory
Proof
  strip_tac >> drule_all abi_builtin_emit_load >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `log_members_run_post st end_st limit_st db outcap p initial actual` by
    (irule log_members_run_post_prefix >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >>
  fs[abi_builtin_prefix_def, abi_decoder_address_frame_def, w2n_n2w]
QED

Theorem log_scalar_tuple_layout_frame[local]:
  abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  abi_decode_frame p 32 initial ready /\ (sb+cap <= p \/ p+32 <= sb) ==>
  log_members_layout infos ats avs [] [] sb 0 0 db (head_lengths ats 0) outcap ready.vs_memory /\
  abi_encoder_member_span infos <= cap /\
  SUM (MAP (\(_,asz,_,_). asz) infos) = head_lengths ats 0
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_footprint_frame [(p,32)] initial ready` by
    (irule (iffLR abi_decode_frame_footprint) >> first_assum ACCEPT_TAC) >>
  `abi_footprint_disjoint sb cap [(p,32)]` by
    simp[abi_footprint_disjoint_def] >>
  `abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) sb cap ready.vs_memory` by
    (drule_all abi_encoder_input_frame >> simp[]) >>
  conj_tac >- (irule log_members_layout_initial >> asm_simp_tac bool_ss [] >>
    qexists_tac `cap` >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `abi_encoder_input _ _ _ _ _ initial.vs_memory` mp_tac >>
      simp_tac bool_ss [abi_encoder_complex_input_iff] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  drule abi_encoder_complex_input_metadata >> simp[]
QED

Theorem log_scalar_tuple_dynamic_run[local]:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos /\
  abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  (sb+cap <= db \/ db+outcap <= sb) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
  p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
  (db+outcap <= p \/ p+32 <= db) /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    abi_decode_footprint_frame [(db,outcap);(p,32)] initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_scalar_cursor_prefix_run >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  `log_members_run_pre infos ats avs [] [] sb 0 0 db (head_lengths ats 0) outcap
     prepared limit_st src dst dyn_ptr p ready` by suspend "prepare" >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_scalar_tuple_members_run >>
  disch_then (qx_choose_then `encoded` strip_assume_tac) >>
  `eval_operand dyn_ptr encoded = SOME (n2w p)` by suspend "cursor" >>
  `fresh_vars_wrt limit_st encoded` by fs[log_members_run_post_def] >>
  drule_all log_scalar_tuple_load >>
  disch_then (qspecl_then [`outcap`,`db`] (qx_choose_then `actual` strip_assume_tac)) >>
  qexists_tac `actual` >> suspend "compose"
QED

Resume log_scalar_tuple_dynamic_run[prepare]:
  drule_all log_scalar_tuple_layout_frame >>
  disch_then (qspec_then `db` strip_assume_tac) >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `eval_operand src ready = SOME (n2w sb)` by (first_x_assum irule >> simp[]) >>
  `eval_operand dst ready = SOME (n2w db)` by (first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  simp_tac bool_ss [log_members_run_pre_def] >>
  asm_simp_tac (srw_ss()) [abi_tuple_tails_def, Excl "enc_def"] >>
  rpt conj_tac >> decide_tac
QED

Resume log_scalar_tuple_dynamic_run[cursor]:
  qpat_x_assum `log_members_run_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `log_members_run_post _ _ _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [log_members_run_pre_def, log_members_run_post_def] >>
  metis_tac[]
QED

Resume log_scalar_tuple_dynamic_run[compose]:
  drule_all log_members_run_post_trans >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  MAP_EVERY (fn q => qpat_x_assum q mp_tac)
    [`log_members_run_post prepared end_st _ _ _ _ _ _`,
     `run_inst_seq (emitted_insts st prepared) initial = OK ready`,
     `inst_extends st prepared`, `abi_decode_frame p 32 initial ready`,
     `ready.vs_allocas = _`, `ready.vs_alloca_next = _`,
     `ready.vs_halted = _`,
     `!op w. abi_decoder_operand_live st.cs_next_var op /\ _ ==> _`,
     `prepared.cs_next_var = _`,
     `mem_bytes_at db _ encoded.vs_memory = _`,
     `eval_operand out actual = _`, `actual.vs_memory = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `abi_decode_footprint_frame [(p,32)] initial ready` by
    (irule (iffLR abi_decode_frame_footprint) >> first_assum ACCEPT_TAC) >>
  `abi_decode_footprint_frame [(db,outcap);(p,32)] initial ready` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(p,32)]` >>
     simp[] >> qexistsl_tac [`p`,`32`] >> simp[]) >>
  qpat_x_assum `log_members_run_post _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [log_members_run_post_def] >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_footprint_frame_trans >> strip_tac >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_operand_live prepared.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand op ready = SOME w` by (first_x_assum irule >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Finalise log_scalar_tuple_dynamic_run


Theorem log_scalar_tuple_run:
  compile_abi_encode_to_buf dst src ei st = (out,end_st) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  (sb+cap <= db \/ db+outcap <= sb) /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  ((?infos. ei = AbiComplex infos) ==>
    ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
      FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db)) ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    abi_decode_footprint_frame
      ((db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else [])) initial actual /\
    actual.vs_allocas =
      (if (?infos. ei = AbiComplex infos) then abi_builtin_allocate_state st.cs_next_id 32 initial
       else initial).vs_allocas /\
    actual.vs_alloca_next =
      (if (?infos. ei = AbiComplex infos) then abi_builtin_allocate_state st.cs_next_id 32 initial
       else initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?n. _ /\ _) \/ (?infos. _ /\ _ /\ _)`
    (DISJ_CASES_THEN strip_assume_tac)
  >- (qpat_x_assum `ei = _` SUBST_ALL_TAC >>
      full_simp_tac (srw_ss()) [Excl "enc_def"] >> drule_all log_scalar_tuple_copy_run >> simp[]) >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  qpat_x_assum `(?infos'. _ = AbiComplex infos') ==> _` mp_tac >>
  simp_tac (srw_ss()) [Excl "enc_def"] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_scalar_tuple_dynamic_run >> simp[Excl "enc_def"]
QED
