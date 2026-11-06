(* Heterogeneous calldata member traversal with original-state scratch ghosts. *)
Theory calldataScratchTuplePtr
Ancestors calldataScratchBytesPtr decoderMemberPrefixPtr abiScratchDecoderTuple
  abiScratchDecoderMemberCons abiScratchDecoderMembersContract
  abiDecoderMemberInfos abiScratchLeafEffect abiDecoderLoop abiDecoderFrame
  abiDecoderMemberCode fragExec abiValidMember abiValidDecodedMetadata
  abiDecoderDynamicLoopSetup abiScratchDecoderSubwindow abiDecoderValidMemberCons
  abiDecoderArraySetupInputs abiScratchDecoderContract abiDecoderReentry abiDecodeRanges
  abiDecoderFootprint abiDecoderMemberSetup abiDecoderCoherence abiDecoderDynamic instIdxIndep
  abiScratchEncoderContract abiEncoder abiDecoderContract exprLowering compileEnv valueEncoding
  venomState venomExecSemantics bodyPtrDefs ptrDiscipline list arithmetic

(* The empty suffix executes no instructions, even after an arbitrary prefix.
   Keep the entire root allocation and arbitrary protected memory in the interface. *)
Theorem calldata_scratch_members_nil_ptr:
  compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w) []
    ao vo start = ((),end_st) /\
  abi_decoder_budget first last b cap initial /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial outsz /\ allocas_from lower initial /\
  DISJOINT P tn.t_mem ==>
  ?actual H u.
    tuple_in_memory [] [] (d + vo) actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      tuple_in_memory [] [] (d + vo) mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st (d + vo) 0 b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual outsz /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  simp_tac (srw_ss()) [Once compile_abi_decode_to_buf_def, comp_return_def] >>
  rpt strip_tac >>
  qexistsl_tac [`initial`, `G`, `tn`] >>
  simp[val_in_memory_def, abi_decode_sim_refl] >>
  irule abi_scratch_leaf_effect >> simp[abi_decode_frame_def]
QED

(* Keep the physical sequence witness when passing to continuation semantics. *)
Theorem calldata_member_setup_run_sim[local]:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) dyn ao vo st = (ops,ready) /\
  fn_has_code st ready func /\
  run_inst_seq (emitted_insts st ready) initial = OK prepared /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_decode_sim ctx func initial
    (prepared with vs_inst_idx := LENGTH ready.cs_current_insts) /\
  prepared.vs_current_bb = ready.cs_current_bb /\ ~prepared.vs_halted
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `frag_exec ctx st ready (\s. s = initial)
     (\t. t = prepared with vs_inst_idx := LENGTH ready.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >>
     fs[EVERY_CONJ] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

(* Physical input at a supplied address-only endpoint, rather than at an
   unrelated existential execution. Empty dynamic members are handled separately. *)
Theorem calldata_member_input_at_endpoint[local]:
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ vyper_to_abi_type env ty::ats) bs bs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs))) = SOME v /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d outsz first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_address_frame st.cs_next_var initial prepared /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  eval_operand childsrc prepared = SOME (n2w (sb +
    abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre)))) /\
  eval_operand childdst prepared = SOME (n2w (d + vo)) /\
  abi_decoder_operand_live ready.cs_next_var childsrc /\
  abi_decoder_operand_live ready.cs_next_var childdst ==>
  abi_scratch_decoder_input ce env sf ty tv
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs)) v ready childsrc childdst
    CALLDATALOAD (Lit 0w)
    (sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre))) (d + vo) first last b cap prepared
Proof
  strip_tac >>
  `sb + LENGTH bs < dimword (:256)` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all (SRULE [LET_THM] abi_valid_member_window) >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  `abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
     d outsz first last b cap prepared` by
    (qpat_x_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `abi_decoder_address_frame _ _ _` mp_tac >>
     qpat_x_assum `abi_decoder_operand_live _ src` mp_tac >>
     qpat_x_assum `abi_decoder_operand_live _ dst` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_scratch_decoder_ranges_def, abi_decoder_address_frame_def] >>
     rpt strip_tac >> gvs[abi_decoder_child_scratch_def] >> metis_tac[]) >>
  `abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) childsrc childdst
     (sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
       (SUM (MAP abi_member_head_size pre)))
     (LENGTH (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
       (DROP (SUM (MAP abi_member_head_size pre)) bs)))
     (d + vo) (type_memory_bytes ce ty) first last b cap prepared` by
    (irule abi_scratch_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`d`, `dst`, `LENGTH (bs:word8 list)`, `outsz`, `sb`, `src`] >>
     asm_simp_tac arith_ss []) >>
  `abi_decode_source CALLDATALOAD prepared = abi_decode_source CALLDATALOAD initial` by
    (drule abi_decoder_address_frame_source >> simp[]) >>
  drule_all abi_decoder_valid_member_readable >> strip_tac >>
  simp[abi_scratch_decoder_input_def, abi_decoder_operand_live_def] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  fs[abi_member_head_size_def]
QED

Theorem calldata_member_input_pc[local]:
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc hi sb d first last b cap
    (s with vs_inst_idx := idx) =
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc hi sb d first last b cap s
Proof
  simp[abi_scratch_decoder_input_def, abi_scratch_decoder_ranges_def,
    abi_decoder_child_scratch_def, abi_decode_source_def, eval_op_inst_idx]
QED

Theorem calldata_member_address_frame_pc[local]:
  abi_decoder_address_frame next s (t with vs_inst_idx := idx) =
  abi_decoder_address_frame next s t
Proof
  simp[abi_decoder_address_frame_def, eval_op_inst_idx]
QED

Theorem calldata_scratch_member_setup_ptr[local]:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w)
    (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size pre)) vo st = (ops,ready) /\
  fn_has_code st ready func /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ vyper_to_abi_type env ty::ats) bs bs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs))) = SOME v /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
    d outsz first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ptr_covers G tn root initial outsz /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx ==>
  ?prepared H u q.
    SND ops = Var q /\
    abi_scratch_decoder_input ce env sf ty tv
      (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
        (DROP (SUM (MAP abi_member_head_size pre)) bs)) v ready (FST ops) (Var q)
      CALLDATALOAD (Lit 0w)
      (sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
        (SUM (MAP abi_member_head_size pre))) (d + vo) first last b cap prepared /\
    ptr_covers H u q prepared (type_memory_bytes ce ty) /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    fresh_vars_wrt limit_st prepared /\
    abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared /\ allocas_from lower prepared /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u prepared) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  strip_tac >>
  `eval_operand src initial = SOME (n2w sb) /\
   lookup_var root initial = SOME (n2w d) /\
   sb + LENGTH bs < dimword (:256) /\ d + outsz < dimword (:256)` by
    fs[abi_scratch_decoder_ranges_def, eval_operand_def] >>
  `not_fresh_at st root /\ (!q. src = Var q ==> not_fresh_at st q)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> fs[]) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  drule_all (SRULE [LET_THM] abi_valid_member_window) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_decode_load CALLDATALOAD (n2w (sb + ao)) initial = n2w off` >>
  qmatch_goalsub_abbrev_tac `abi_scratch_decoder_input ce env sf ty tv childbs` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `eval_operand (Var root) initial = SOME (n2w d)` by simp[eval_operand_def] >>
  `abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) ==>
     abi_decode_load CALLDATALOAD (n2w (sb + ao):bytes32) initial = n2w off /\
     sb + off < dimword (:256)` by simp[] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK t` >>
  `w2n (n2w d:bytes32) + vo < dimword (:256)` by
    (simp[] >> decide_tac) >>
  drule_all calldata_member_setup_endpoint_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `eval_operand (FST ops) t = SOME (n2w (sb + off))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     fs[Abbr `off`, abi_decode_member_offset_def]) >>
  drule_all calldata_member_setup_run_sim >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  unabbrev_all_tac >>
  drule_all calldata_member_input_at_endpoint >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH ready.cs_current_insts`, `H`, `u`, `q`] >>
  simp[calldata_member_input_pc, calldata_member_address_frame_pc,
    ptr_covers_def, fresh_vars_wrt_def, allocas_from_def, lookup_var_def] >>
  `initial with vs_inst_idx := LENGTH st.cs_current_insts = initial` by
    simp[venom_state_component_equality] >>
  qpat_x_assum `abi_scratch_decoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `fresh_vars_wrt limit_st t` mp_tac >>
  qpat_x_assum `allocas_from lower initial` mp_tac >>
  qpat_x_assum `!x. not_fresh_at st x ==> _` mp_tac >>
  qpat_x_assum `(!fuel. _) ==> _` mp_tac >>
  simp[fresh_vars_wrt_def, allocas_from_def, lookup_var_def] >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `!aid b sz. _` drule >> simp[]
QED
