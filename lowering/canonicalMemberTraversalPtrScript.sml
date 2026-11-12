(* Canonical member navigation from facts at the parent's entry state. *)
Theory canonicalMemberTraversalPtr
Ancestors sourcePrimitiveMemberPtr abiDecoderMemberSetup abiDecoderMemberCode
  abiDecoderDynamicLoopSetup decoderMemberPrefixPtr abiDecoderContract
  abiDecoderReentry compileEnv loweringStateRelDefs ghostPcTransportPtr ptrDiscipline bodyPtrDefs
  venomState venomExecSemantics exprLoweringProps fragExec words arithmetic
  finite_map list abiEncoder emitHelperProps entrySinkExtraction
  sourceEncodingWindows sourceEncodingLayout abiCanonicalHeadSize abiDecodeRanges
  contractABI byte abiDecoderMemberSlice rich_list vyperABIRoundtrip

(* The calldata instance of the position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`] th);

Theorem straight_sequence_inst_idx[local]:
  !is s t. EVERY (\i. ~is_terminator i.inst_opcode) is /\
    run_inst_seq is s = OK t ==> t.vs_inst_idx = s.vs_inst_idx
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  drule_all step_inst_base_preserves_inst_idx >> strip_tac >>
  first_x_assum drule >> metis_tac[]
QED

Theorem calldata_member_setup_source_ptr:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\ not_fresh_at sa root /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var root) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  eval_operand src s = SOME (n2w srcpos) /\
  (dyn ==> abi_decode_load CALLDATALOAD (n2w (srcpos + ao) : bytes32) s = n2w off /\
    srcpos + off < dimword (:256)) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + C <= cap /\ d + vo < dimword (:256) /\ fresh_vars_wrt mid s /\
  fn_has_code sa mid fn /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r H u q.
    run_inst_seq (emitted_insts sa mid) s = OK (r with vs_inst_idx := s.vs_inst_idx) /\
    r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
    abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt mid r /\
    SND ops = Var q /\ eval_operand (SND ops) r = SOME (n2w (d + vo)) /\
    eval_operand (FST ops) r = SOME (n2w (srcpos + if dyn then off else ao)) /\
    ptr_covers H u q r C /\ op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u r) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME (n2w d)` by simp[eval_operand_def] >>
  drule_all (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `CALLDATALOAD`, `limit_st` |-> `st'`]
      (calldata_pos abi_decode_member_setup_reentry))) >> strip_tac >>
  drule_all (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `CALLDATALOAD`] abi_decode_member_setup_shape)) >> strip_tac >>
  `w2n (n2w d : bytes32) + vo < dimword (:256)` by simp[w2n_n2w, LESS_MOD] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa mid) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa mid)` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `t.vs_inst_idx = s.vs_inst_idx /\ t.vs_current_bb = s.vs_current_bb` by
    metis_tac[straight_sequence_inst_idx, run_inst_seq_preserves_entry_control] >>
  drule_all calldata_member_setup_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `H`, `u`, `q`] >>
  gvs[w2n_n2w, LESS_MOD, lookup_var_def, fresh_vars_wrt_def,
    abi_decoder_address_frame_def] >>
  conj_tac >- simp[venom_state_component_equality] >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => fs[GSYM th]) >> simp[]
QED

Theorem structural_member_offset_load:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty)
    (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  mem_bytes_at cdsbase (LENGTH (enc (Tuple (pre ++ ty::post))
    (ListV (pvs ++ v::rest)))) (abi_decode_source opc s) =
      enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) /\
  cdsbase + LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))) <
    dimword (:256) ==>
  abi_decode_load opc
    (n2w (cdsbase + SUM (MAP abi_member_head_size pre)) : bytes32) s =
    n2w (head_lengths (pre ++ ty::post) 0 +
      SUM (MAP2 abi_member_tail_size pre pvs))
Proof
  strip_tac >> drule_all structural_tuple_child_ranges >> strip_tac >>
  drule_all structural_member_head_window >>
  asm_simp_tac bool_ss [abi_member_head_size_def, enc_number_def] >> strip_tac >>
  `cdsbase + SUM (MAP abi_member_head_size pre) < dimword (:256)` by decide_tac >>
  irule EQ_TRANS >>
  qexists_tac `word_of_bytes T (0w:256 word)
    (TAKE 32 (DROP (SUM (MAP abi_member_head_size pre))
      (mem_bytes_at cdsbase (LENGTH (enc (Tuple (pre ++ ty::post))
        (ListV (pvs ++ v::rest)))) (abi_decode_source opc s))))` >>
  conj_tac
  >- (irule abi_decode_load_window >> gvs[abi_member_head_size_def]) >>
  asm_rewrite_tac[] >> irule word_of_bytes_word_to_bytes >>
  simp[dividesTheory.divides_def]
QED

Theorem structural_tuple_indexed_offset_load:
  LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty) ats avs /\
  i < LENGTH ats /\ is_dynamic (EL i ats) /\
  mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs)))
    (abi_decode_source opc s) = enc (Tuple ats) (ListV avs) /\
  cdsbase + LENGTH (enc (Tuple ats) (ListV avs)) < dimword (:256) ==>
  abi_decode_load opc
    (n2w (cdsbase + SUM (MAP abi_member_head_size (TAKE i ats))) : bytes32) s =
    n2w (abi_tuple_child_offset ats avs i)
Proof
  strip_tac >>
  `LENGTH ats = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  `i < LENGTH avs` by decide_tac >>
  `ats = TAKE i ats ++ EL i ats::DROP (SUC i) ats /\
   avs = TAKE i avs ++ EL i avs::DROP (SUC i) avs` by
    metis_tac[TAKE_DROP_SUC, APPEND, APPEND_ASSOC] >>
  `LENGTH (TAKE i ats) = LENGTH (TAKE i avs)` by simp[] >>
  `LIST_REL (\ty av. ~is_dynamic ty ==>
      LENGTH (enc ty av) = abi_member_head_size ty)
    (TAKE i ats ++ EL i ats::DROP (SUC i) ats)
    (TAKE i avs ++ EL i avs::DROP (SUC i) avs)` by metis_tac[] >>
  `mem_bytes_at cdsbase
    (LENGTH (enc (Tuple (TAKE i ats ++ EL i ats::DROP (SUC i) ats))
      (ListV (TAKE i avs ++ EL i avs::DROP (SUC i) avs))))
    (abi_decode_source opc s) =
    enc (Tuple (TAKE i ats ++ EL i ats::DROP (SUC i) ats))
      (ListV (TAKE i avs ++ EL i avs::DROP (SUC i) avs))` by metis_tac[] >>
  `cdsbase + LENGTH (enc (Tuple (TAKE i ats ++ EL i ats::DROP (SUC i) ats))
    (ListV (TAKE i avs ++ EL i avs::DROP (SUC i) avs))) < dimword (:256)` by metis_tac[] >>
  drule_all structural_member_offset_load >>
  asm_simp_tac bool_ss [abi_tuple_child_offset_def] >> metis_tac[]
QED

Theorem canonical_tuple_primitive_traversal_ptr:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\ vyper_to_abi_list env tys vs = SOME avs /\
  ats = MAP (vyper_to_abi_type env) tys /\ i < LENGTH tys /\
  mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) s.vs_call_ctx.cc_calldata =
    enc (Tuple ats) (ListV avs) /\
  cdsbase + LENGTH (enc (Tuple ats) (ListV avs)) < dimword (:256) /\
  cdsbase + abi_tuple_child_offset ats avs i < dimword (:256) /\
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (is_dynamic (EL i ats)) (SUM (MAP abi_member_head_size (TAKE i ats))) vo sa = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    ei mid = ((),sb) /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\ not_fresh_at sa root /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var root) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  eval_operand src s = SOME (n2w cdsbase) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + C <= cap /\ d + vo < dimword (:256) /\ C < dimword (:256) /\
  fresh_vars_wrt mid s /\ type_to_abi_dec_info sf ce (EL i tys) = ei /\
  ((?clamp. ei = DecPrimWord clamp /\ is_word_type (EL i tys) /\ C = 32) \/
   (?m. ei = DecBytestring m /\ C = abi_decode_bytes_copy_size m /\ m < dimword (:256))) /\
  fn_has_code sa mid fn /\ fn_has_code mid sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u q.
    SND ops = Var q /\
    run_inst_seq (emitted_insts sa mid ++ emitted_insts mid sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ptr_covers H u q t C /\
    val_in_memory (EL i tvs) (EL i vs) (d + vo) t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs) (d + vo) mem) /\
    abi_decode_frame (d + vo) C s t /\ fresh_vars_wrt sb t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `i < LENGTH ats` by simp[] >>
  `is_dynamic (EL i ats) ==>
    abi_decode_load CALLDATALOAD
      (n2w (cdsbase + SUM (MAP abi_member_head_size (TAKE i ats))) : bytes32) s =
      n2w (abi_tuple_child_offset ats avs i) /\
    cdsbase + abi_tuple_child_offset ats avs i < dimword (:256)` by
    (strip_tac >> conj_tac >- (irule structural_tuple_indexed_offset_load >>
      simp[abi_decode_source_def, Excl "enc_def"] >> gvs[]) >> simp[]) >>
  drule_all calldata_member_setup_source_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `eval_operand (FST ops) r = SOME (n2w (cdsbase + abi_tuple_child_offset ats avs i))` by
    (Cases_on `is_dynamic (EL i ats)` >> gvs[abi_tuple_child_offset_def]) >>
  `mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) r.vs_call_ctx.cc_calldata =
    enc (Tuple ats) (ListV avs)` by gvs[abi_decoder_address_frame_def] >>
  `LIST_REL (\ty av. ~is_dynamic ty ==>
    LENGTH (enc ty av) = abi_member_head_size ty) ats avs` by metis_tac[] >>
  drule_all structural_tuple_indexed_source >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  `abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
   value_has_type (EL i tvs) (EL i vs) /\
   vyper_to_abi env (EL i tys) (EL i vs) = SOME (EL i avs)` by
    (gvs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  qpat_x_assum `ats = _` SUBST_ALL_TAC >>
  qpat_x_assum `type_to_abi_dec_info sf ce (EL i tys) = ei` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `mem_bytes_at (_ + abi_tuple_child_offset _ _ _) _ _ = _` mp_tac >>
  simp[EL_MAP, Excl "enc_def"] >> strip_tac >>
  `vo + C <= cap /\ w2n (n2w d : bytes32) + vo < dimword (:256)` by simp[w2n_n2w, LESS_MOD] >>
  drule_all (SRULE [] (Q.INST [`ty` |-> `EL i tys`,
    `ei` |-> `type_to_abi_dec_info sf ce (EL i tys)`] source_primitive_member_ptr)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`, `H'`, `u'`] >> gvs[w2n_n2w, LESS_MOD]
QED
