(* Structural boundary for zero-output encoder fragments. *)
Theory abiEncoderEmptyCode
Ancestors
  abiEncoderWindow abiEncoderOpenInput abiEncoderInput abiDecodeRanges
  abiEncoder contractABI valueEncoding valueEncodingProofs list rich_list words byte arithmetic
  venomExecSemantics venomState venomInst emitHelperProps exprLoweringProps
  compileEnv emitHelper

Definition abi_encoder_empty_def:
  abi_encoder_empty AbiPrimWord = F /\
  abi_encoder_empty (AbiCopy sz) = (sz = 0) /\
  abi_encoder_empty (AbiBytestring n) = F /\
  abi_encoder_empty (AbiDynArray ei asz msz dyn) = F /\
  abi_encoder_empty (AbiComplex infos) = abi_encoder_empty_members infos /\
  abi_encoder_empty_members [] = T /\
  abi_encoder_empty_members ((ei,asz,msz,dyn)::infos) =
    (abi_encoder_empty ei /\ asz = 0 /\ ~dyn /\ abi_encoder_empty_members infos)
End

Theorem abi_encoder_empty_members_every:
  !infos. abi_encoder_empty_members infos <=>
    EVERY (\(ei,asz,msz,dyn). abi_encoder_empty ei /\ asz = 0 /\ ~dyn) infos
Proof
  Induct >> simp[abi_encoder_empty_def] >>
  qx_gen_tac `info` >> PairCases_on `info` >> simp[abi_encoder_empty_def] >> metis_tac[]
QED

Theorem abi_encoder_window_empty:
  !ei at av sb cap mem. abi_encoder_window_input ei at av sb cap mem ==>
  LENGTH (enc at av) = 0 ==> abi_encoder_empty ei
Proof
  ho_match_mp_tac abi_encoder_window_input_strongind >> rpt conj_tac
  >- (rpt strip_tac >> drule (cj 1 enc_has_static_length) >> simp[])
  >- (rpt strip_tac >> drule (cj 1 enc_has_static_length) >>
      gvs[abi_encoder_empty_def])
  >- (rpt strip_tac >> gvs[enc_def] >>
      qpat_x_assum `word_to_bytes _ _ = []`
        (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_word_to_bytes])
  >- (rpt gen_tac >> strip_tac >> rename1 `abi_sz = abi_member_head_size ct` >>
      `LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ct) avs` by
        (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
         first_x_assum (qspec_then `n` mp_tac) >> simp[EL_REPLICATE] >>
         metis_tac[abi_encoder_window_input_valid, abi_encoder_structural_valid_layout]) >>
      drule abi_encoder_open_enc_tuple_length >>
      disch_then (qspecl_then [`head_lengths (REPLICATE (LENGTH avs) ct) 0`,
        `0`, `[word_to_bytes (n2w (LENGTH avs):bytes32) T]`, `[]`] mp_tac) >>
      simp[Once enc_def, LENGTH_word_to_bytes] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `LIST_REL abi_encoder_layout_valid ats avs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     `n < LENGTH infos` by decide_tac >>
     Cases_on `EL n infos` >> rename1 `EL n infos = (child,rest)` >> PairCases_on `rest` >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
     metis_tac[abi_encoder_window_input_valid, abi_encoder_structural_valid_layout]) >>
  `LENGTH (enc at (ListV avs)) = LENGTH (enc (Tuple ats) (ListV avs))` by
    (gvs[abi_encoder_tuple_type_def, enc_def]) >>
  `SUM (MAP abi_member_head_size ats) = 0` by
    (drule abi_encoder_open_tuple_length >> decide_tac) >>
  simp[abi_encoder_empty_def, abi_encoder_empty_members_every, EVERY_EL] >>
  qx_gen_tac `i` >> strip_tac >>
  Cases_on `EL i infos` >> rename1 `EL i infos = (child,rest)` >> PairCases_on `rest` >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `abi_member_head_size (EL i ats) = 0` by
    (gvs[SUM_eq_0, MEM_MAP] >> first_x_assum irule >>
     qexists_tac `EL i ats` >> simp[MEM_EL] >> metis_tac[]) >>
  Cases_on `is_dynamic (EL i ats)` >> gvs[abi_member_head_size_def] >>
  `LENGTH (enc (EL i ats) (EL i avs)) = 0` by
    (gvs[LIST_REL_EL_EQN, abi_encoder_layout_valid_def] >>
     metis_tac[LENGTH_NIL]) >>
  metis_tac[LENGTH_NIL]
QED

Theorem abi_encoder_empty_copy_observation:
  !s d b a n. mem_bytes_at a n (mcopy d b 0 s).vs_memory =
    mem_bytes_at a n s.vs_memory
Proof
  rpt gen_tac >> simp[mcopy_def, write_memory_with_expansion_def,
    TAKE_DROP, mem_bytes_at_append_zero] >>
  IF_CASES_TAC >> simp[mem_bytes_at_append_zero]
QED

Theorem abi_encoder_empty_copy_sequence:
  compile_abi_encode_to_buf dst src (AbiCopy 0) st = (out,st') /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME b ==>
  run_inst_seq (emitted_insts st st') s = OK (mcopy (w2n d) (w2n b) 0 s) /\
  out = Lit 0w /\ inst_extends st st' /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >> gvs[same_blocks_def] >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
    eval_operand_def, is_terminator_def, same_blocks_def]
QED

(* Empty execution may change temporaries and append zero memory only. *)
Definition abi_encoder_empty_effect_def:
  abi_encoder_empty_effect s t <=>
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|> /\
    (!a n. mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
End

Theorem abi_encoder_empty_effect_refl[simp]:
  !s. abi_encoder_empty_effect s s
Proof
  simp[abi_encoder_empty_effect_def]
QED

Theorem abi_encoder_empty_effect_trans:
  !s t u. abi_encoder_empty_effect s t /\ abi_encoder_empty_effect t u ==>
    abi_encoder_empty_effect s u
Proof
  rpt gen_tac >> simp[abi_encoder_empty_effect_def] >> strip_tac >>
  qpat_x_assum `u = _` SUBST1_TAC >> simp[] >>
  qpat_x_assum `t = _` SUBST1_TAC >> simp[]
QED

Theorem abi_encoder_empty_effect_mcopy:
  !d b s. abi_encoder_empty_effect s (mcopy d b 0 s)
Proof
  simp[abi_encoder_empty_effect_def, abi_encoder_empty_copy_observation] >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_empty_add_sequence:
  emit_op ADD [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (a+b) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_encoder_empty_effect s t /\ inst_extends st st' /\ same_blocks st st' /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st')
Proof
  strip_tac >> drule_all emit_op_ADD_correct >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `t = update_var (STRING #"%" (toString st.cs_next_var)) (a+b) s` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       eval_operand_def, exec_pure2_def]) >>
  qexists_tac `t` >> simp[] >>
  simp[abi_encoder_empty_effect_def, update_var_def, mk_inst_def, is_terminator_def,
    venom_state_component_equality]
QED

Definition abi_encoder_empty_seq_def:
  abi_encoder_empty_seq st st' s t <=>
    run_inst_seq (emitted_insts st st') s = OK t /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_encoder_empty_effect s t /\ inst_extends st st' /\ same_blocks st st' /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st')
End

Theorem abi_encoder_empty_seq_refl:
  !st s. fresh_vars_wrt st s ==> abi_encoder_empty_seq st st s s
Proof
  simp[abi_encoder_empty_seq_def, emitted_insts_def, run_inst_seq_def,
    inst_extends_refl, same_blocks_def]
QED

Theorem abi_encoder_empty_seq_trans:
  !st mid fin s t u.
    abi_encoder_empty_seq st mid s t /\ abi_encoder_empty_seq mid fin t u ==>
    abi_encoder_empty_seq st fin s u
Proof
  rpt gen_tac >> simp[abi_encoder_empty_seq_def] >> strip_tac >>
  `emitted_insts st fin = emitted_insts st mid ++ emitted_insts mid fin` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  `run_inst_seq (emitted_insts st fin) s = OK u` by
    (simp[] >> qpat_x_assum `run_inst_seq (emitted_insts st mid) s = OK t`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  `abi_encoder_empty_effect s u` by (irule abi_encoder_empty_effect_trans >> metis_tac[]) >>
  `inst_extends st fin` by (irule inst_extends_trans >> metis_tac[]) >>
  `same_blocks st fin` by (irule same_blocks_trans >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem abi_encoder_empty_seq_add:
  emit_op ADD [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fresh_vars_wrt st s ==>
  ?t. abi_encoder_empty_seq st st' s t /\ eval_operand out t = SOME (a+b)
Proof
  strip_tac >> drule_all abi_encoder_empty_add_sequence >>
  simp[abi_encoder_empty_seq_def] >> metis_tac[]
QED

Theorem abi_encoder_empty_seq_copy:
  compile_abi_encode_to_buf dst src (AbiCopy 0) st = (out,st') /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME b /\
  fresh_vars_wrt st s ==>
  ?t. abi_encoder_empty_seq st st' s t /\ out = Lit 0w
Proof
  strip_tac >> drule_all abi_encoder_empty_copy_sequence >> strip_tac >>
  `st'.cs_next_var = st.cs_next_var` by
    (qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     simp[compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_void >> simp[]) >>
  qexists_tac `mcopy (w2n d) (w2n b) 0 s` >>
  simp[abi_encoder_empty_seq_def, abi_encoder_empty_effect_mcopy, same_blocks_def] >>
  conj_tac >- gvs[fresh_vars_wrt_def, mcopy_def, write_memory_with_expansion_def,
    lookup_var_def] >>
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_empty_members_metadata:
  !infos. abi_encoder_empty_members infos ==>
    ~EXISTS (\(_,_,_,dyn). dyn) infos /\
    SUM (MAP (\(_,asz,_,_). asz) infos) = 0
Proof
  Induct >> simp[abi_encoder_empty_def] >>
  qx_gen_tac `info` >> PairCases_on `info` >> simp[abi_encoder_empty_def] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem abi_encoder_empty_seq_fresh:
  !st st' s t. abi_encoder_empty_seq st st' s t ==> fresh_vars_wrt st' t
Proof
  simp[abi_encoder_empty_seq_def]
QED

Theorem abi_encoder_empty_seq_eval:
  !st st' s t op w. abi_encoder_empty_seq st st' s t /\
    eval_operand op s = SOME w ==> eval_operand op t = SOME w
Proof
  simp[abi_encoder_empty_seq_def]
QED

Theorem abi_encoder_empty_execution:
  (!ei. abi_encoder_empty ei ==>
    !dst src st out st' s d b.
      compile_abi_encode_to_buf dst src ei st = (out,st') /\
      eval_operand dst s = SOME d /\ eval_operand src s = SOME b /\
      fresh_vars_wrt st s ==>
      ?t. abi_encoder_empty_seq st st' s t /\ out = Lit 0w) /\
  (!infos. abi_encoder_empty_members infos ==>
    !dst src so ho dp st out st' s d b.
      compile_abi_encode_complex_elems dst src infos so ho dp st = (out,st') /\
      eval_operand dst s = SOME d /\ eval_operand src s = SOME b /\
      fresh_vars_wrt st s ==>
      ?t. abi_encoder_empty_seq st st' s t /\ out = Lit 0w)
Proof
  ho_match_mp_tac abi_encoder_empty_ind >>
  simp[abi_encoder_empty_def] >> conj_tac
  >- metis_tac[abi_encoder_empty_seq_copy] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      drule abi_encoder_empty_members_metadata >> strip_tac >>
      Cases_on `infos`
      >- (gvs[compile_abi_encode_child_def, comp_return_def] >>
          metis_tac[abi_encoder_empty_seq_refl]) >>
      qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
      simp[Once compile_abi_encode_child_def] >>
      simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> metis_tac[]) >>
  conj_tac
  >- (simp[compile_abi_encode_child_def, comp_return_def] >>
      metis_tac[abi_encoder_empty_seq_refl]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD [src; Lit (n2w so)] st = (elem_src,src_st)` >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD [dst; Lit (n2w ho)] src_st = (static_loc,dst_st)` >>
  rename1 `compile_abi_encode_to_buf static_loc elem_src ei dst_st = (child_out,child_st)` >>
  `?t1. abi_encoder_empty_seq st src_st s t1 /\
        eval_operand elem_src t1 = SOME (b + n2w so)` by
    (irule abi_encoder_empty_seq_add >> simp[] >>
     qexistsl_tac [`src`, `Lit (n2w so)`] >> simp[eval_operand_def]) >>
  `fresh_vars_wrt src_st t1 /\ eval_operand dst t1 = SOME d` by
    metis_tac[abi_encoder_empty_seq_fresh, abi_encoder_empty_seq_eval] >>
  `?t2. abi_encoder_empty_seq src_st dst_st t1 t2 /\
        eval_operand static_loc t2 = SOME (d + n2w ho)` by
    (irule abi_encoder_empty_seq_add >> simp[] >>
     qexistsl_tac [`dst`, `Lit (n2w ho)`] >> simp[eval_operand_def]) >>
  `fresh_vars_wrt dst_st t2 /\
   eval_operand elem_src t2 = SOME (b + n2w so)` by
    metis_tac[abi_encoder_empty_seq_fresh, abi_encoder_empty_seq_eval] >>
  qpat_x_assum `abi_encoder_empty ei ==> _` drule >>
  disch_then drule_all >> strip_tac >>
  rename1 `abi_encoder_empty_seq dst_st child_st t2 t3` >>
  `abi_encoder_empty_seq st child_st s t3` by
    metis_tac[abi_encoder_empty_seq_trans] >>
  `fresh_vars_wrt child_st t3 /\ eval_operand dst t3 = SOME d /\
   eval_operand src t3 = SOME b` by
    metis_tac[abi_encoder_empty_seq_fresh, abi_encoder_empty_seq_eval] >>
  qpat_x_assum `abi_encoder_empty_members infos ==> _` drule >>
  disch_then drule_all >> strip_tac >>
  metis_tac[abi_encoder_empty_seq_trans]
QED
