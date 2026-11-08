(* Heterogeneous calldata member traversal with original-state scratch ghosts. *)
Theory calldataScratchTuplePtr
Ancestors calldataScratchBytesPtr decoderMemberPrefixPtr abiScratchDecoderTuple abiDecoderComplexGuard
  abiScratchDecoderMemberCons abiScratchDecoderMembersContract
  abiDecoderMemberInfos abiScratchLeafEffect abiDecoderLoop abiDecoderFrame
  abiDecoderMemberCode fragExec abiValidMember abiValidDecodedMetadata
  abiDecoderDynamicLoopSetup abiScratchDecoderSubwindow abiDecoderValidMemberCons
  abiDecoderArraySetupInputs abiScratchDecoderContract abiDecoderReentry abiDecodeRanges
  abiDecoderOffsetHead abiDecoderOffset abiDecoderMemberBody abiScratchAfterAddress
  abiScratchAddress abiDecoderEmpty abiDecoderComplexHead decoderGhostFramePtr abiDecoderAllocation
  abiDecoderFootprint abiDecoderMemberSetup abiDecoderCoherence abiDecoderDynamic instIdxIndep
  abiScratchEncoderContract abiEncoder abiDecoderContract exprLowering compileEnv valueEncoding
  robustCopyTransportPtr valueEncodingProps valueEncodingTyping exprSim freshWrites vyperTyping abiScratchEffect abiScratchFootprint pred_set abiDecoderMembers
  abiDecoderValidMemberCursor abiDecoderMembersCode abiScratchDecoderMemberFrames
  venomState venomExecSemantics bodyPtrDefs ptrDiscipline list arithmetic
  abiScratchDecoderRecursive abiDecoderFixedMemory rich_list abiStaticDynarrayLayout

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

Theorem calldata_scratch_member_body_guarded_ptr:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
    G tn P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
    ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size pre)) vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),end_st) /\
  fn_has_code st end_st func /\ fn_inst_ids_distinct func /\
  (ready.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ vyper_to_abi_type env ty::ats) bs bs /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs))) = SOME v /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
    d outsz first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ptr_covers G tn root initial outsz /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
  ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory tv v (d + vo) actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory tv v (d + vo) mem) /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\ ptr_covers H u root actual outsz /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids st.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- suspend "empty" >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  `(is_dynamic (vyper_to_abi_type env ty) ==>
      !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)` by
    (strip_tac >> drule_all abi_decoder_nonempty_readable_head >> simp[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
     abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
    simp[abi_decoder_needs_offset_iff] >>
  qpat_x_assum `dec_info_needs_offset _ = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `first <= ready.cs_next_id /\ ready.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all calldata_scratch_member_setup_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `abi_decoder_budget first last b cap prepared` by
    (drule_all abi_scratch_address >> simp[]) >>
  `(bounded ==> lower <= prepared.vs_alloca_next)` by
    fs[abi_decoder_address_frame_def] >>
  `DISJOINT P u.t_mem` by simp[] >>
  qpat_x_assum `SND ops = Var q` (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn P D PG. _`
    (fn child => drule_all child) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d + vo`, `end_st.cs_next_id`, `ready.cs_next_id`,
       `ready.cs_next_var`, `type_memory_bytes ce ty`, `prepared`] >> simp[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at ready x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
    FLOOKUP H' x = FLOOKUP G x /\ op_taint u' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at ready x` by metis_tac[] >>
     qpat_x_assum `!x. not_fresh_at ready x ==> _` drule >>
     qpat_x_assum `!x. not_fresh_at st x ==> lookup_var x prepared = _ /\ _` drule >>
     simp[]) >>
  `not_fresh_at st root` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  `ptr_covers H' u' root actual outsz` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`initial`,`tn`] >> simp[]) >>
  `!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids st.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial` by
    (rpt strip_tac >>
     `~(site IN abi_decoder_ids ready.cs_next_id end_st.cs_next_id)` by
       (fs[abi_decoder_ids_def] >> decide_tac) >>
     `FLOOKUP prepared.vs_allocas site = SOME (slot,32) /\
       mload slot prepared = mload slot initial` by
       fs[abi_decoder_address_frame_def, mload_def] >>
     qpat_x_assum `!site slot. _ ==> FLOOKUP actual.vs_allocas site = _ /\ _` drule_all >> simp[]) >>
  qexistsl_tac [`actual`,`H'`,`u'`] >> asm_simp_tac bool_ss [] >>
  rpt conj_tac
  >- (irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[])
  >> metis_tac[]
QED

Resume calldata_scratch_member_body_guarded_ptr[empty]:
  qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn P D PG. _` kall_tac >>
  drule_all abi_decoder_empty_descriptor_value >> strip_tac >>
  `end_st = ready` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_empty_complex_phases, abi_decode_complex_head_guard_def,
       comp_return_def]) >>
  gvs[] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `eval_operand src initial = SOME (n2w sb) /\
   eval_operand (Var root) initial = SOME (n2w d) /\
   lookup_var root initial = SOME (n2w d) /\
   d + outsz < dimword (:256)` by
    fs[abi_scratch_decoder_ranges_def, eval_operand_def] >>
  `not_fresh_at st root /\ (!q. src = Var q ==> not_fresh_at st q)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> fs[]) >>
  fs[dec_info_needs_offset_def] >>
  drule_all (SRULE [] (Q.INST [`dyn` |-> `F`] abi_decode_member_setup_reentry)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK t` >>
  `w2n (n2w d:bytes32) + vo < dimword (:256)` by
    (simp[] >> decide_tac) >>
  `vo + 0 <= outsz` by simp[] >>
  drule_all calldata_member_setup_endpoint_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all calldata_member_setup_run_sim >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `ptr_covers H u root t outsz` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`initial`,`tn`] >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var initial
     (t with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    simp[calldata_member_address_frame_pc] >>
  `fresh_vars_wrt limit_st (t with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    fs[fresh_vars_wrt_def] >>
  `abi_scratch_effect first last st.cs_next_id ready.cs_next_id st.cs_next_var
     limit_st (d + vo) 0 b cap initial
     (t with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule abi_scratch_address_effect >> simp[]) >>
  `initial with vs_inst_idx := LENGTH st.cs_current_insts = initial` by
    simp[venom_state_component_equality] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH ready.cs_current_insts`,`H`,`u`] >>
  simp[ptr_covers_def, lookup_var_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at st x ==> _` drule >> simp[lookup_var_def])
  >- (qpat_x_assum `allocas_from lower initial` mp_tac >>
      fs[abi_decoder_address_frame_def, allocas_from_def])
  >> rpt strip_tac >> fs[abi_decoder_address_frame_def, mload_def]
QED

Finalise calldata_scratch_member_body_guarded_ptr

Theorem calldata_scratch_member_body_ptr:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
    G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size pre)) vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),end_st) /\
  fn_has_code st end_st func /\ fn_inst_ids_distinct func /\
  (ready.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ vyper_to_abi_type env ty::ats) bs bs /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs))) = SOME v /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
    d outsz first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ptr_covers G tn root initial outsz /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory tv v (d + vo) actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory tv v (d + vo) mem) /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\ ptr_covers H u root actual outsz /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids st.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL (SIMP_RULE bool_ss []
    (Q.INST [`bounded` |-> `F`] calldata_scratch_member_body_guarded_ptr))) >>
  (impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      (rpt gen_tac >> disch_tac >>
       qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn lower P D PG. _`
         irule >> metis_tac[])])) >>
  disch_then ACCEPT_TAC
QED

Theorem calldata_scratch_members_guarded_ptr:
  !tys tvs pretys st final func ctx src root bs vs sb d first last b cap limit_st
    initial G tn lower P D PG.
  LENGTH tys = LENGTH tvs /\
  (!ty tv. MEM (ty,tv) (ZIP (tys,tvs)) ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
    ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs
      (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)) vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (pretys ++ tys)) bs bs /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ptr_covers G tn root initial (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
  ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) mem) /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys))
      (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids st.cs_next_id final.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  Induct_on `tys`
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      `vs = []` by (drule abi_decoder_members_lengths >> simp[]) >>
      gvs[abi_decoder_member_infos_def] >>
      drule_all calldata_scratch_members_nil_ptr >>
      disch_then (qspecl_then [`func`,`d`,`ctx`,`PG`,`D`] strip_assume_tac) >>
      qexistsl_tac [`actual`,`H`,`u`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `LENGTH (ty::tys) = LENGTH tvs` >>
  Cases_on `tvs` >- fs[] >> rename1 `tv::tvs` >>
  `LENGTH (ty::tys) = LENGTH vs` by
    (drule abi_decoder_members_lengths >> simp[]) >>
  Cases_on `vs` >- fs[] >> rename1 `v::vs` >>
  drule abi_decoder_valid_member_cursor >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD /\
   abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decode_source_opcode_def, abi_decoder_operand_live_def] >>
  drule_all abi_decoder_members_cons_code >>
  disch_then (qx_choose_then `ops` (qx_choose_then `middle` (qx_choose_then `end_st`
    (map_every assume_tac o CONJUNCTS)))) >>
  `end_st.cs_next_id <= last /\ first <= end_st.cs_next_id /\
   end_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= end_st.cs_next_var`
    by decide_tac >>
  qpat_assum `!ty' tv'. _` (qspecl_then [`ty`,`tv`] mp_tac) >>
  simp_tac bool_ss [ZIP, MEM, pairTheory.PAIR_EQ, boolTheory.OR_CLAUSES] >>
  disch_tac >>
  mp_tac (Q.INST [`ready` |-> `middle`,
    `pre` |-> `MAP (vyper_to_abi_type env) pretys`,
    `ats` |-> `MAP (vyper_to_abi_type env) tys`,
    `vo` |-> `SUM (MAP (type_memory_bytes ce) pretys)`,
    `outsz` |-> `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`]
      calldata_scratch_member_body_guarded_ptr) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    simp[MAP_APPEND, SUM_APPEND, MAP, SUM] >>
    qpat_x_assum `vyper_decode_valid_enc_tuple _ bs bs` mp_tac >>
    simp[MAP_APPEND])) >>
  strip_tac >>
  rename1 `abi_decode_sim ctx func initial after_head` >>
  `(bounded ==> lower <= after_head.vs_alloca_next)` by
    (drule_all abi_scratch_effect_alloca_next_mono >>
     strip_tac >> strip_tac >> fs[]) >>
  drule_all abi_scratch_decoder_member_after_head >> strip_tac >>
  `not_fresh_at st root /\
   (!q. src = Var q ==> not_fresh_at st q)` by
    (qpat_assum `abi_decoder_operand_live st.cs_next_var src` mp_tac >>
     qpat_assum `abi_decoder_operand_live st.cs_next_var (Var root)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> simp[]) >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (Cases_on `src` >> fs[op_taint_def, op_prov_def] >>
     first_x_assum (drule_then strip_assume_tac) >> fs[op_taint_def, op_prov_def]) >>
  qpat_assum `abi_embedded_static_size ce.ce_struct_fields ty = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [MAP_APPEND, MAP, SUM_APPEND, SUM, APPEND_ASSOC, ADD_CLAUSES]) >>
  qpat_x_assum `!tvs pretys st final func ctx src root bs vs sb d first last b cap limit_st initial G tn lower P D PG. _`
    (fn ih => mp_tac (SRULE [MAP_APPEND, MAP, SUM_APPEND, SUM, APPEND_ASSOC]
      (Q.INST [`st` |-> `end_st`, `initial` |-> `after_head:venom_state`,
        `G` |-> `H`, `tn` |-> `u`]
        (SPEC_ALL (Q.SPECL [`tvs`, `pretys ++ [ty]`] ih))))) >>
  (impl_tac >- (asm_simp_tac bool_ss [LENGTH, GSYM ADD_ASSOC, APPEND] >>
    conj_tac
    >- (qpat_assum `LENGTH (ty::tys) = LENGTH (tv::tvs)` mp_tac >> simp_tac bool_ss [LENGTH, prim_recTheory.INV_SUC_EQ]) >>
    conj_tac
    >- (rpt gen_tac >> disch_tac >>
        qpat_x_assum `!ty' tv'. _` (qspecl_then [`ty'`,`tv'`] mp_tac) >>
        asm_simp_tac bool_ss [ZIP, MEM]) >>
    qpat_assum `vyper_decode_valid_enc_tuple _ bs bs` mp_tac >>
    simp_tac bool_ss [APPEND, GSYM APPEND_ASSOC])) >>
  strip_tac >>
  `value_has_type tv v /\ type_memory_size tv = type_memory_bytes ce ty` by
    (drule abi_decoder_members_relations >> simp[LIST_REL_def]) >>
  `val_wf tv v /\ val_footprint tv v <= type_memory_size tv` by
    (conj_asm1_tac >- (drule (cj 1 value_has_type_val_wf) >> simp[]) >>
     irule val_footprint_le >> simp[]) >>
  `abi_decode_footprint_frame
     ((d + (SUM (MAP (type_memory_bytes ce) pretys) + type_memory_bytes ce ty),
       SUM (MAP (type_memory_bytes ce) tys))::
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap after_head)
     after_head actual` by
    (qpat_assum `abi_scratch_effect _ _ end_st.cs_next_id _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac abi_scratch_effect_frame) >>
     asm_simp_tac bool_ss []) >>
  `mem_bytes_at (d + SUM (MAP (type_memory_bytes ce) pretys))
     (val_footprint tv v) actual.vs_memory =
   mem_bytes_at (d + SUM (MAP (type_memory_bytes ce) pretys))
     (val_footprint tv v) after_head.vs_memory` by
    (irule abi_decode_footprint_frame_slice >>
     goal_assum (drule_at Any) >>
     simp_tac bool_ss [abi_scratch_disjoint_cons] >>
     conj_tac >- (disj1_tac >> decide_tac) >>
     qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ after_head` mp_tac >>
     qpat_assum `val_footprint tv v <= _` mp_tac >>
     qpat_assum `type_memory_size tv = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_scratch_decoder_ranges_def, abi_footprint_disjoint_def] >>
     rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `!mem. mem_agree_outside u'.t_mem actual.vs_memory mem ==>
     val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) mem` by
    (match_mp_tac (Q.INST [`oldmem` |-> `after_head.vs_memory`,
       `oldtaint` |-> `u.t_mem`] calldata_member_robust_window_frame) >>
     asm_simp_tac bool_ss []) >>
  `val_in_memory tv v (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  qexistsl_tac [`actual`, `H'`, `u'`] >>
  simp_tac bool_ss [MAP_APPEND, MAP, SUM_APPEND, SUM, GSYM ADD_ASSOC] >>
  asm_simp_tac bool_ss [] >>
  conj_tac
  >- (simp_tac (srw_ss()) [Once val_in_memory_def] >>
      asm_simp_tac (srw_ss()) [LET_THM, GSYM ADD_ASSOC]) >>
  conj_tac
  >- (rpt strip_tac >> simp_tac (srw_ss()) [Once val_in_memory_def] >>
      asm_simp_tac (srw_ss()) [LET_THM, GSYM ADD_ASSOC]) >>
  conj_tac
  >- (irule abi_scratch_decoder_member_effects_compose >>
      asm_simp_tac bool_ss [] >>
      qexistsl_tac [`end_st.cs_next_id`, `after_head`, `end_st.cs_next_var`] >>
      asm_simp_tac bool_ss [GSYM ADD_ASSOC]) >>
  conj_tac
  >- (irule abi_decode_sim_trans >> qexists_tac `after_head` >> asm_simp_tac bool_ss []) >>
  conj_tac >- (asm_simp_tac bool_ss [ADD_ASSOC]) >>
  conj_tac >- (irule SUBSET_TRANS >> qexists_tac `u.t_mem` >> asm_simp_tac bool_ss []) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at end_st x` by
        (irule not_fresh_at_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
      qpat_x_assum `!x. not_fresh_at end_st x ==> _` drule >> strip_tac >>
      qpat_x_assum `!x. not_fresh_at st x ==> _` drule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `~(site IN abi_decoder_ids st.cs_next_id end_st.cs_next_id) /\
   ~(site IN abi_decoder_ids end_st.cs_next_id final.cs_next_id)` by
    (qpat_x_assum `~(site IN abi_decoder_ids st.cs_next_id final.cs_next_id)` mp_tac >>
     simp[abi_decoder_ids_def] >> decide_tac) >>
  qpat_x_assum `!site slot. _ ==> FLOOKUP after_head.vs_allocas site = _ /\ _` drule_all >>
  strip_tac >>
  qpat_x_assum `!site slot. _ ==> FLOOKUP actual.vs_allocas site = _ /\ _` drule_all >> simp[]

QED

Theorem calldata_scratch_members_ptr:
  !tys tvs pretys st final func ctx src root bs vs sb d first last b cap limit_st
    initial G tn lower P D PG.
  LENGTH tys = LENGTH tvs /\
  (!ty tv. MEM (ty,tv) (ZIP (tys,tvs)) ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos sf ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs
      (DROP (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))) bs)) vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (pretys ++ tys)) bs bs /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ptr_covers G tn root initial (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      tuple_in_memory vs tvs (d + SUM (MAP (type_memory_bytes ce) pretys)) mem) /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      (d + SUM (MAP (type_memory_bytes ce) pretys))
      (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (SUM (MAP (type_memory_bytes ce) (pretys ++ tys))) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids st.cs_next_id final.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL (SIMP_RULE bool_ss []
    (Q.INST [`bounded` |-> `F`] calldata_scratch_members_guarded_ptr))) >>
  (impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      (rpt gen_tac >> disch_tac >>
       qpat_x_assum `!ty tv. _` drule >>
       disch_then assume_tac >>
       rpt gen_tac >> disch_tac >>
       qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn lower P D PG. _`
         irule >> metis_tac[])])) >>
  disch_then ACCEPT_TAC
QED

(* Constructor-independent closure of the complex member decoder. *)
Theorem calldata_scratch_complex_decoder_guarded_ptr:
  LENGTH tys = LENGTH tvs /\
  (!ty tv. MEM (ty,tv) (ZIP (tys,tvs)) ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
    ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (DecComplex dyn (abi_decoder_member_infos sf ce tys)) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var (Var root) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (SUM (MAP (type_memory_bytes ce) tys)) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
  ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    tuple_in_memory vs tvs d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      tuple_in_memory vs tvs d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (SUM (MAP (type_memory_bytes ce) tys)) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decode_complex_phases,
      abi_decode_complex_head_guard_def, comp_ignore_bind_def,
      comp_bind_def, comp_return_def]) >>
  gnvs[LET_THM, comp_return_def] >>
  mp_tac (SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES, DROP_0]
    (Q.INST [`pretys` |-> `[]`, `st` |-> `start`, `final` |-> `end_st`]
      (SPEC_ALL calldata_scratch_members_guarded_ptr))) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexistsl_tac [`actual`,`H`,`u`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem calldata_scratch_complex_decoder_ptr:
  LENGTH tys = LENGTH tvs /\
  (!ty tv. MEM (ty,tv) (ZIP (tys,tvs)) ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (DecComplex dyn (abi_decoder_member_infos sf ce tys)) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var (Var root) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (SUM (MAP (type_memory_bytes ce) tys)) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    tuple_in_memory vs tvs d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      tuple_in_memory vs tvs d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (SUM (MAP (type_memory_bytes ce) tys)) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL (SIMP_RULE bool_ss []
    (Q.INST [`bounded` |-> `F`] calldata_scratch_complex_decoder_guarded_ptr))) >>
  (impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      (rpt gen_tac >> disch_tac >>
       qpat_x_assum `!ty tv. _` drule >> disch_then assume_tac >>
       rpt gen_tac >> disch_tac >>
       qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn lower P D PG. _`
         irule >> metis_tac[])])) >>
  disch_then ACCEPT_TAC
QED

(* Tuple closure is a specialization of the constructor-independent boundary. *)
Theorem calldata_scratch_tuple_decoder_ptr:
  LENGTH tys = LENGTH tvs /\
  (!ty tv. MEM (ty,tv) (ZIP (tys,tvs)) ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (TupleT tys)) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (TupleT tys) (TupleTV tvs) bs v start src (Var root)
    CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (TupleT tys)) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory (TupleTV tvs) v d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory (TupleTV tvs) v d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (type_memory_bytes ce (TupleT tys)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (type_memory_bytes ce (TupleT tys)) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_tuple_inputs >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  drule_all calldata_scratch_complex_decoder_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`actual`,`H`,`u`] >>
  asm_simp_tac bool_ss [val_in_memory_tuple] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* Fixed arrays share complex traversal, including the empty member list. *)
Theorem calldata_scratch_fixed_array_decoder_ptr:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  (0 < n /\ is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Fixed n))) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
    bs v start src (Var root) CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Fixed n))) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory (ArrayTV tv (Fixed n)) v d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Fixed n)) v d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (type_memory_bytes ce (ArrayT ty (Fixed n)))
      b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (type_memory_bytes ce (ArrayT ty (Fixed n))) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_fixed_array_inputs >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  mp_tac (Q.INST [`tys` |-> `REPLICATE (LENGTH vs) ty`,
    `tvs` |-> `REPLICATE (LENGTH vs) tv`,
    `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
    calldata_scratch_complex_decoder_ptr) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [map_replicate, SUM_REPLICATE,
    MEM_ZIP, EL_REPLICATE] >> rpt gen_tac >> strip_tac >>
    gvs[EL_REPLICATE] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [map_replicate, SUM_REPLICATE]) >>
  qexistsl_tac [`actual`,`H`,`u`] >>
  asm_simp_tac bool_ss [] >>
  rpt conj_tac
  >- (irule abi_decoder_fixed_array_memory >> simp[])
  >- (rpt strip_tac >> irule abi_decoder_fixed_array_memory >>
      simp[] >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* Struct members descend in the source maps, keeping the compiler environment. *)
Theorem calldata_scratch_struct_decoder_ptr:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  (!ty tv. MEM (ty,tv) (ZIP (MAP SND args,tvs)) ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info (sf \\ nsid_to_string nsid) ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv
      bs v start src (Var root) CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (StructT nsid)) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    bs v start src (Var root) CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (StructT nsid)) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory (StructTV (ZIP (MAP FST args,tvs))) v d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory (StructTV (ZIP (MAP FST args,tvs))) v d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (type_memory_bytes ce (StructT nsid)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (type_memory_bytes ce (StructT nsid)) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_struct_inputs >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  drule abi_decoder_struct_infos >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`env` |-> `env \\ nsid`,
    `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`]
    calldata_scratch_complex_decoder_ptr) >>
  impl_tac >- (asm_simp_tac bool_ss [LENGTH_MAP] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qexistsl_tac [`actual`,`H`,`u`] >> asm_simp_tac bool_ss [val_in_memory_struct] >>
  conj_tac
  >- (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule static_fields_memory_zip >>
      fs[Once value_has_type_def] >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* Guard-parametric tuple closure: recursive children share the parent's lower. *)
Theorem calldata_scratch_tuple_decoder_guarded_ptr:
  LENGTH tys = LENGTH tvs /\
  (!ty tv. MEM (ty,tv) (ZIP (tys,tvs)) ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
    ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (TupleT tys)) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (TupleT tys) (TupleTV tvs) bs v start src (Var root)
    CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (TupleT tys)) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
  ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory (TupleTV tvs) v d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory (TupleTV tvs) v d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (type_memory_bytes ce (TupleT tys)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (type_memory_bytes ce (TupleT tys)) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_tuple_inputs >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  drule_all calldata_scratch_complex_decoder_guarded_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`actual`,`H`,`u`] >>
  asm_simp_tac bool_ss [val_in_memory_tuple] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem calldata_scratch_fixed_array_decoder_guarded_ptr:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
    ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  (0 < n /\ is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Fixed n))) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
    bs v start src (Var root) CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Fixed n))) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
  ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory (ArrayTV tv (Fixed n)) v d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Fixed n)) v d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (type_memory_bytes ce (ArrayT ty (Fixed n)))
      b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (type_memory_bytes ce (ArrayT ty (Fixed n))) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_fixed_array_inputs >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  mp_tac (Q.INST [`tys` |-> `REPLICATE (LENGTH vs) ty`,
    `tvs` |-> `REPLICATE (LENGTH vs) tv`,
    `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
    calldata_scratch_complex_decoder_guarded_ptr) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [map_replicate, SUM_REPLICATE,
    MEM_ZIP, EL_REPLICATE] >> rpt gen_tac >> strip_tac >>
    gvs[EL_REPLICATE] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [map_replicate, SUM_REPLICATE]) >>
  qexistsl_tac [`actual`,`H`,`u`] >>
  asm_simp_tac bool_ss [] >>
  rpt conj_tac
  >- (irule abi_decoder_fixed_array_memory >> simp[])
  >- (rpt strip_tac >> irule abi_decoder_fixed_array_memory >>
      simp[] >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem calldata_scratch_struct_decoder_guarded_ptr:
  FLOOKUP env nsid = SOME (StructArgs args) /\ LENGTH tvs = LENGTH args /\
  (!ty tv. MEM (ty,tv) (ZIP (MAP SND args,tvs)) ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info (sf \\ nsid_to_string nsid) ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv
      bs v start src (Var root) CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
    ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (StructT nsid)) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
    bs v start src (Var root) CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (StructT nsid)) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ (bounded ==> lower <= initial.vs_alloca_next) /\
  ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory (StructTV (ZIP (MAP FST args,tvs))) v d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory (StructTV (ZIP (MAP FST args,tvs))) v d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (type_memory_bytes ce (StructT nsid)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (type_memory_bytes ce (StructT nsid)) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_struct_inputs >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  drule abi_decoder_struct_infos >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`env` |-> `env \\ nsid`,
    `sf` |-> `sf \\ nsid_to_string nsid`,
    `tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
    `vs` |-> `MAP SND (fields:(string # value) list)`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields)
      (MAP SND (args:(string # vyperAST$type) list))`]
    calldata_scratch_complex_decoder_guarded_ptr) >>
  impl_tac >- (asm_simp_tac bool_ss [LENGTH_MAP] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qexistsl_tac [`actual`,`H`,`u`] >> asm_simp_tac bool_ss [val_in_memory_struct] >>
  conj_tac
  >- (irule static_fields_memory_zip >> fs[Once value_has_type_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule static_fields_memory_zip >>
      fs[Once value_has_type_def] >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED
