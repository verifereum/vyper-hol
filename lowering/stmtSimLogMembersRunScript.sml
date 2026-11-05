(* Compact proof-only interfaces for the allocation-free scalar tuple loop. *)
Theory stmtSimLogMembersRun
Ancestors
  abiDecoderRange
  stmtSimLogScalarMembers abiEncoderInput abiDecoderGuards exprLoweringProps
  abiEncoderMemberCode abiEncoderCounters abiBuiltinPrefix abiEncoderAddressReach
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderFrame abiDecoderLoop
  emitHelperProps compileEnv emitHelper abiEncoder venomState venomInst
  stmtSimLogEncodeLayout contractABI words list arithmetic

Definition log_members_run_pre_def:
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s <=>
    log_members_layout infos tys avs pre pvs sb so ho d hl outcap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w p) /\
    mload p s = n2w (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
    sb+so+abi_encoder_member_span infos < dimword (:256) /\
    d+outcap < dimword (:256) /\ p < dimword (:256) /\
    (sb+so+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so) /\
    (sb+so+abi_encoder_member_span infos <= p \/ p+32 <= sb+so) /\
    (d+outcap <= p \/ p+32 <= d) /\ fresh_vars_wrt limit_st s
End

Definition log_members_run_post_def:
  log_members_run_post st end_st limit_st d outcap p initial actual <=>
    run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    abi_decode_footprint_frame [(d,outcap);(p,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
End

Theorem log_members_span_cons[local]:
  abi_encoder_member_span ((ei,asz,mz,dyn)::infos) = mz+abi_encoder_member_span infos
Proof
  simp[abi_encoder_member_span_def]
QED

Theorem log_members_run_post_refl:
  fresh_vars_wrt limit_st s ==> log_members_run_post st st limit_st d outcap p s s
Proof
  simp[log_members_run_post_def, emitted_insts_def, run_inst_seq_def,
    inst_extends_def, abi_decode_footprint_frame_refl]
QED

Theorem log_members_run_post_trans:
  log_members_run_post st middle limit_st d outcap p s t /\
  log_members_run_post middle final limit_st d outcap p t u /\
  st.cs_next_var <= middle.cs_next_var ==>
  log_members_run_post st final limit_st d outcap p s u
Proof
  simp_tac bool_ss [log_members_run_post_def] >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_footprint_frame_trans >> strip_tac >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_operand_live middle.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand op t = SOME w` by (first_x_assum irule >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem log_members_run_pre_address:
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  abi_decoder_address_frame st.cs_next_var s t /\ fresh_vars_wrt limit_st t /\
  st.cs_next_var <= next.cs_next_var ==>
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap next limit_st src dst dp p t
Proof
  simp_tac bool_ss [log_members_run_pre_def, abi_decoder_address_frame_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `mload p t = mload p s` by (simp_tac bool_ss [mload_def] >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem log_members_run_post_prefix:
  abi_builtin_prefix st next limit_st s t ==>
  log_members_run_post st next limit_st d outcap p s t
Proof
  simp[abi_builtin_prefix_def, log_members_run_post_def,
    abi_decoder_address_frame_def, abi_decode_footprint_frame_def]
QED

Theorem log_members_run_source_add:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,next) /\
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap
    st limit_st src dst dp p s /\
  next.cs_next_var <= limit_st.cs_next_var ==>
  ?t. log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap
        next limit_st src dst dp p t /\
    eval_operand elem_src t = SOME (n2w (sb+so)) /\
    abi_decoder_operand_live next.cs_next_var elem_src /\
    log_members_run_post st next limit_st d outcap p s t
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w sb) /\ fresh_vars_wrt limit_st s` by
    fs[log_members_run_pre_def] >>
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all abi_builtin_emit_add >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `st.cs_next_var <= next.cs_next_var` by decide_tac >>
  `log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap
      next limit_st src dst dp p t` by
    (irule log_members_run_pre_address >>
     conj_tac >- fs[abi_builtin_prefix_def] >>
     qexistsl_tac [`s`,`st`] >> fs[abi_builtin_prefix_def]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [GSYM word_add_n2w] >>
  conj_tac >- (drule abi_decoder_operand_live_emit >> simp[]) >>
  irule log_members_run_post_prefix >> first_assum ACCEPT_TAC
QED

Theorem log_members_run_child:
  compile_abi_encode_child dst elem_src ei dyn ho dp st = (out,end_st) /\
  log_members_run_pre ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  eval_operand elem_src s = SOME (n2w (sb+so)) /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. log_members_run_pre infos tys avs (pre++[ty]) (pvs++[av])
        sb (so+mz) (ho+asz) d hl outcap end_st limit_st src dst dp p t /\
    log_members_run_post st end_st limit_st d outcap p s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `log_members_run_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [log_members_run_pre_def, log_members_span_cons, ADD_ASSOC] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb+so < dimword (:256)` by decide_tac >>
  drule_all log_scalar_member_child_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st end_st) s = OK t` >>
  drule abi_encoder_child_bounds >> strip_tac >>
  qexists_tac `t` >> reverse conj_tac
  >- (simp_tac bool_ss [log_members_run_post_def] >> asm_simp_tac bool_ss []) >>
  simp_tac bool_ss [log_members_run_pre_def] >>
  `eval_operand src t = SOME (n2w sb)` by (first_x_assum irule >> simp[]) >>
  `eval_operand dst t = SOME (n2w d)` by (first_x_assum irule >> simp[]) >>
  `eval_operand dp t = SOME (n2w p)` by (first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live end_st.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live end_st.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live end_st.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> decide_tac
QED

Theorem log_members_run_cons:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\
  compile_abi_encode_child dst elem_src ei dyn ho dp prepared = (out,child_end) /\
  log_members_run_pre ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  child_end.cs_next_var <= limit_st.cs_next_var ==>
  ?t. log_members_run_pre infos tys avs (pre++[ty]) (pvs++[av])
        sb (so+mz) (ho+asz) d hl outcap child_end limit_st src dst dp p t /\
    log_members_run_post st child_end limit_st d outcap p s t
Proof
  strip_tac >> drule abi_encoder_child_bounds >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_members_run_source_add >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  drule_all log_members_run_child >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule log_members_run_post_trans >> qexists_tac `prepared` >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `ready` >> asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem log_members_run_pre_lengths:
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s ==>
  LENGTH infos = LENGTH tys /\ LENGTH tys = LENGTH avs
Proof
  simp_tac bool_ss [log_members_run_pre_def] >> strip_tac >>
  drule log_members_layout_lengths >> simp[]
QED

Theorem log_members_run_pre_fresh:
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s ==>
  fresh_vars_wrt limit_st s
Proof
  simp[log_members_run_pre_def]
QED

Theorem log_members_run_list:
  !infos dst src so ho dp st out final tys avs pre pvs sb d hl outcap limit_st p s.
  compile_abi_encode_complex_elems dst src infos so ho dp st = (out,final) /\
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?t. log_members_run_pre [] [] [] (pre++tys) (pvs++avs)
        sb (so+abi_encoder_member_span infos)
        (ho+SUM (MAP (\(_,asz,_,_). asz) infos)) d hl outcap
        final limit_st src dst dp p t /\
    log_members_run_post st final limit_st d outcap p s t
Proof
  Induct >- suspend "nil" >>
  qx_gen_tac `info` >> PairCases_on `info` >> rpt gen_tac >> strip_tac >>
  drule log_members_run_pre_lengths >> strip_tac >>
  Cases_on `tys` >- fs[] >> Cases_on `avs` >- fs[] >>
  rename1 `log_members_run_pre _ (ty::tys) (av::avs) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` >>
  drule abi_encoder_member_cons_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `child_end.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_members_run_cons >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  first_x_assum drule >> disch_then drule >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  qexists_tac `actual` >> conj_tac
  >- (qpat_x_assum `log_members_run_pre [] [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual` mp_tac >>
      pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
      simp_tac (srw_ss()) [log_members_span_cons, ADD_ASSOC]) >>
  irule log_members_run_post_trans >> qexistsl_tac [`child_end`,`ready`] >>
  asm_simp_tac bool_ss [] >> drule emitted_insts_emit_op >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >> decide_tac
QED

Resume log_members_run_list[nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >> gvs[] >>
  drule log_members_run_pre_lengths >> strip_tac >>
  `tys = [] /\ avs = []` by (Cases_on `tys` >> Cases_on `avs` >> fs[]) >>
  gvs[abi_encoder_member_span_def] >> qexists_tac `s` >> simp[] >>
  irule log_members_run_post_refl >> drule log_members_run_pre_fresh >> simp[]
QED

Finalise log_members_run_list

(* Public unbundled endpoint; no interval allocation budget is required. *)
Theorem log_scalar_members_run:
  compile_abi_encode_complex_elems dst src infos so ho dp st = (out,final) /\
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w p) /\
  mload p initial = n2w (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  sb+so+abi_encoder_member_span infos < dimword (:256) /\
  d+outcap < dimword (:256) /\ p < dimword (:256) /\
  (sb+so+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so) /\
  (sb+so+abi_encoder_member_span infos <= p \/ p+32 <= sb+so) /\
  (d+outcap <= p \/ p+32 <= d) /\ fresh_vars_wrt limit_st initial /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    inst_extends st final /\ fresh_vars_wrt limit_st actual /\
    log_members_layout [] [] [] (pre++tys) (pvs++avs)
      sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,asz,_,_). asz) infos)) d hl outcap actual.vs_memory /\
    mload p actual = n2w (hl+LENGTH (FLAT (abi_tuple_tails (pre++tys) (pvs++avs)))) /\
    abi_decode_footprint_frame [(d,outcap);(p,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap
    st limit_st src dst dp p initial` by
    (simp_tac bool_ss [log_members_run_pre_def] >> asm_simp_tac bool_ss []) >>
  drule_all log_members_run_list >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  qexists_tac `actual` >>
  qpat_x_assum `log_members_run_post _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `log_members_run_pre [] [] [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [log_members_run_pre_def, log_members_run_post_def] >>
  rpt strip_tac >> asm_simp_tac bool_ss []
QED
