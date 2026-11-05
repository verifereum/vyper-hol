(* Static recursive-call boundaries, independent of calldata and runtime freshness. *)
Theory calldataRecursiveProducers
Ancestors
  calldataMembers calldataDynOwned abiDecoderLoopCode abiDecoderLoopEmit
  abiDecoderCoherence exprLoweringProps abiDecoderContract abiCallerAllocation list
  abiDecoderRecursiveLoopLayout abiDecoderArraySetupCode abiDecoderArraySetupInputs abiDecoderPhi fragExec
  abiEncoder emitHelper emitHelperProps compileEnv abiDecoderAppend abiDecoderReentry
  abiDecoderArrayInit abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderMemberInfos valueEncoding actualAllocCredit allocaFrontierBound context rich_list venomInst vyperCompiler

Theorem calldata_loop_child_static:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
    (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
    di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
  fn_has_code loop_st last fn ==>
  fn_has_code st0 st1 fn /\ fn_has_code middle st1 fn /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  middle.cs_next_id <= st1.cs_next_id /\
  middle.cs_next_var <= st1.cs_next_var /\
  ?bb. lookup_block st0.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule calldata_element_setup_static_live >> strip_tac >>
  `ci_mono middle st1` by
    (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`SND (SND ops)`,`FST (SND ops)`,
       `CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`di`,`middle`] mp_tac) >> simp[]) >>
  `st0.cs_current_insts = []` by
    (qpat_x_assum `abi_decode_loop_prefix _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def] >>
     strip_tac >> gvs[]) >>
  drule_all abi_decoder_array_body_entry_phi >> strip_tac >>
  fs[ci_mono_def] >> metis_tac[]
QED

(* Containment and scratch separation remain valid on repeated entry: no
   allocation ID is assumed absent, and a zero-sized child is allowed. *)
Theorem calldata_child_owner_window:
  alloca_inv s /\ FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= d /\ d+sz <= base_addr+cap /\ d+sz < dimword (:256) /\
  d <= e /\ e+childsz <= d+sz /\
  lo <= childlo /\ childhi <= hi /\ (oid < lo \/ hi <= oid) ==>
  base_addr <= e /\ e+childsz <= base_addr+cap /\
  e+childsz < dimword (:256) /\ e+childsz <= s.vs_alloca_next /\
  (oid < childlo \/ childhi <= oid) /\
  (!id q k. childlo <= id /\ id < childhi /\
    FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    e+childsz <= q \/ q+k <= e)
Proof
  strip_tac >>
  `e+childsz <= s.vs_alloca_next` by
    (irule abi_caller_allocation_end >>
     qpat_assum `FLOOKUP _ oid = _` (irule_at Any) >> simp[] >> decide_tac) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  `oid <> id` by decide_tac >>
  drule_all abi_caller_allocation_separate >> strip_tac >> decide_tac
QED

Theorem calldata_struct_child_metadata:
  abi_decoder_coherent ce env sf (StructT nsid) atv ==>
  ?args fields tvs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    atv = StructTV (ZIP (MAP FST args,tvs)) /\
    LENGTH fields = LENGTH args /\ LENGTH tvs = LENGTH args /\
    (!i. i < LENGTH args ==>
      abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid)
        (SND (EL i args)) (EL i tvs) /\
      type_memory_size (EL i tvs) = (\(name,ty,sz). sz) (EL i fields))
Proof
  simp_tac bool_ss [abi_decoder_coherent_struct_iff] >> strip_tac >>
  qexistsl_tac [`fields`,`tvs`] >> simp[] >>
  `LENGTH tvs = LENGTH fields` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp[] >> qx_gen_tac `i` >> strip_tac >>
  `abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (SND ((\(name,ty,sz). (name,ty)) (EL i fields))) (EL i tvs)` by
    (fs[LIST_REL_EL_EQN, EL_MAP]) >>
  simp[EL_MAP] >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  qpat_x_assum `EVERY _ fields` mp_tac >>
  rewrite_tac [EVERY_EL] >> disch_then (qspec_then `i` mp_tac) >>
  Cases_on `EL i fields` >> rename1 `EL i fields = (nm,tysz)` >>
  PairCases_on `tysz` >> gvs[]
QED

(* The exit phi premise is deliberately explicit: an empty current block in
   fn_has_code does not constrain the first instruction of its continuation. *)
Theorem calldata_loop_cfg_producer:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
    (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
    di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
  fn_has_code loop_st last fn /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  lookup_block (FST labels) fn.fn_blocks = SOME
    <|bb_label := FST labels; bb_instructions :=
      abi_decode_header_insts (loop_st.cs_next_id+1) ip src CALLDATALOAD
        (STRING #"%" (toString loop_st.cs_next_var))
        (STRING #"%" (toString (loop_st.cs_next_var+1)))
        (STRING #"%" (toString (loop_st.cs_next_var+2)))
        (STRING #"%" (toString (loop_st.cs_next_var+3))) st0.cs_current_bb (SND (SND labels))|> /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
      abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
        (STRING #"%" (toString st1.cs_next_var)) ip (FST labels)|> /\
  FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
  st0.cs_current_bb = FST (SND labels) /\ st0.cs_current_insts = [] /\
  last.cs_current_bb = SND (SND labels) /\ last.cs_current_insts = [] /\
  (?bb. lookup_block (SND (SND labels)) fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) /\
  loop_st.cs_next_id <= middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= last.cs_next_id
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule_all calldata_loop_child_static >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  `?bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb` by
    fs[fn_has_code_def] >>
  gvs[abiDecoderExecutionTheory.abi_decode_position_header_zero,
      abiDecoderExecutionTheory.abi_decode_position_header_delta_def] >>
  rpt conj_tac >> FIRST [decide_tac, metis_tac[]]
QED

Theorem calldata_member_address_static_live:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) a = ((ep,dp),mid) ==>
  a.cs_next_id <= mid.cs_next_id /\ a.cs_next_var <= mid.cs_next_var /\
  abi_decoder_operand_live mid.cs_next_var ep /\
  abi_decoder_operand_live mid.cs_next_var dp /\
  (!op. abi_decoder_operand_live a.cs_next_var op ==>
    abi_decoder_operand_live mid.cs_next_var op)
Proof
  Cases_on `dyn` >>
  simp[compile_getelemptr_abi_def,
    abiDecoderRangeTheory.compile_abi_dec_addr_zero,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  FIRST [simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
      rpt strip_tac >> irule fresh_var_distinct >> decide_tac,
    irule abi_decoder_operand_live_mono >>
      qexists_tac `a.cs_next_var` >> simp[]]
QED

Theorem calldata_member_child_static:
  (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) a = ((ep,dp),mid) /\
  compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
  fn_has_code a b fn ==>
  fn_has_code a mid fn /\ fn_has_code mid b fn /\
  a.cs_next_id <= mid.cs_next_id /\ mid.cs_next_id <= b.cs_next_id /\
  a.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= b.cs_next_var /\
  abi_decoder_operand_live mid.cs_next_var ep /\
  abi_decoder_operand_live mid.cs_next_var dp /\
  (!op. abi_decoder_operand_live a.cs_next_var op ==>
    abi_decoder_operand_live mid.cs_next_var op)
Proof
  strip_tac >>
  drule calldata_member_address_static_live >> strip_tac >>
  drule calldata_member_address_shape >> strip_tac >>
  `cs_extends a mid` by (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends mid b` by (drule cs_extends_abi_decode >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `ci_mono mid b` by
    (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`dp`,`ep`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`ei`,`mid`] mp_tac) >> simp[]) >>
  fs[ci_mono_def]
QED

(* A recursive loop child's real continuation begins with the backedge ADD.
   This certifies the child's empty-prefix exit, not the outer loop exit. *)
Theorem calldata_loop_child_continuation_phi:
  abi_decode_loop_suffix ip (Var iv) hdr exit_lbl st = ((),last) /\
  fn_has_code st last fn /\ st.cs_current_insts = [] ==>
  !bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  simp_tac bool_ss [abi_decode_loop_suffix_shape] >> strip_tac >> gvs[] >>
  `lookup_block st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st.cs_current_bb; bb_instructions :=
      abi_decode_backedge_insts st.cs_next_id iv
        (STRING #"%" (toString st.cs_next_var)) ip hdr|>` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fn_has_code_def, emitted_blocks_def, abi_decode_loop_suffix_state_def]) >>
  rpt strip_tac >> gvs[] >>
  simp[abiDecoderExecutionTheory.abi_decode_backedge_insts_def,
       venomExecSemanticsTheory.phi_prefix_length_def, venomInstTheory.mk_inst_def]
QED

(* The first actual member address instruction is ADD, on both offset paths. *)
Theorem calldata_member_address_continuation_phi:
  (do ep <- compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w);
      dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) a = ((ep,dp),mid) /\
  fn_has_code a mid fn /\ a.cs_current_insts = [] ==>
  !bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `dyn` >>
  simp[compile_getelemptr_abi_def,
    abiDecoderRangeTheory.compile_abi_dec_addr_zero,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[fn_has_code_def] >>
  Cases_on `bb.bb_instructions` >>
  gvs[venomExecSemanticsTheory.phi_prefix_length_def,
    venomInstTheory.mk_inst_def]
QED

Theorem calldata_member_tail_continuation_phi:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    elems ao vo a = ((),z) /\
  fn_has_code a z fn /\ a.cs_current_insts = [] /\
  (!bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  !bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `elems`
  >- simp[Once compile_abi_decode_to_buf_def, comp_return_def] >>
  rename1 `h::rest` >> PairCases_on `h` >>
  simp_tac bool_ss [Once compile_abi_decode_to_buf_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_getelemptr_abi src (dec_info_needs_offset h0) ao CALLDATALOAD (Lit 0w) (Lit 0w) a` >>
  rename1 `_ = (ep,mid)` >> simp_tac bool_ss [] >>
  Cases_on `emit_op ADD [dst; Lit (n2w vo)] mid` >>
  rename1 `_ = (dp,b)` >> simp_tac bool_ss [] >>
  Cases_on `compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) h0 b` >>
  rename1 `_ = (u,c)` >> Cases_on `u` >> simp_tac bool_ss [] >>
  strip_tac >> gvs[] >>
  `cs_extends b c` by (drule cs_extends_abi_decode >> simp[]) >>
  `cs_extends c z` by
    (irule (cj 2 cs_appends_abi_decode_mutual |> SRULE[cs_appends_def]) >>
     first_assum (irule_at Any)) >>
  `cs_extends b z` by metis_tac[cs_extends_trans] >>
  ` (do ep <- compile_getelemptr_abi src (dec_info_needs_offset h0) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) a = ((ep,dp),b)` by
    simp[comp_bind_def, comp_return_def] >>
  drule calldata_member_address_shape >> strip_tac >>
  `cs_extends a b` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code a b fn` by metis_tac[fn_has_code_split] >>
  metis_tac[calldata_member_address_continuation_phi]
QED

(* A nonempty emitted head certifies the installed exit, even when the
   surrounding decoder has changed blocks. Empty exits need a real suffix. *)
Theorem calldata_emitted_exit_head_phi:
  fn_has_code a z fn /\ z.cs_current_insts = i::is /\
  i.inst_opcode <> PHI ==>
  !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  rw[fn_has_code_def] >> gvs[] >>
  Cases_on `bb.bb_instructions` >>
  gvs[venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem calldata_recursive_changed_block_head:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) di a = ((),z) /\
  a.cs_blocks <> z.cs_blocks /\ z.cs_current_insts = h::t ==>
  h.inst_opcode <> PHI
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_to_buf_exit_phi >> strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[venomExecSemanticsTheory.phi_prefix_length_def]
QED

(* A changed, empty exit obtains its certificate from the actual enclosing
   suffix. The unchanged-block case intentionally remains a disjunct. *)
Theorem calldata_recursive_exit_continuation_phi:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) di a = ((),z) /\
  fn_has_code a z fn /\
  (z.cs_current_insts = [] ==>
    !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  a.cs_blocks = z.cs_blocks \/
  (!bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> Cases_on `a.cs_blocks = z.cs_blocks` >> simp[] >>
  Cases_on `z.cs_current_insts` >- metis_tac[] >>
  rename1 `z.cs_current_insts = h::t` >>
  `h.inst_opcode <> PHI` by metis_tac[calldata_recursive_changed_block_head] >>
  metis_tac[calldata_emitted_exit_head_phi]
QED



Theorem calldata_coherent_induction:
  (!ce env sf bt.
    abi_decoder_scalar_valid bt /\
    abi_decoder_header ce env (BaseT bt) (BaseTV bt) ==>
    P ce env sf (BaseT bt) (BaseTV bt)) /\
  (!ce env sf nsid n.
    FLOOKUP env nsid = SOME (FlagArgs n) /\ n <= 256 /\
    ce.ce_flag_n_members (nsid_to_string nsid) = n /\
    abi_decoder_header ce env (FlagT nsid) (FlagTV n) ==>
    P ce env sf (FlagT nsid) (FlagTV n)) /\
  (!ce env sf ty tv bound.
    abi_decoder_coherent ce env sf ty tv /\ P ce env sf ty tv /\
    abi_decoder_header ce env (ArrayT ty bound) (ArrayTV tv bound) ==>
    P ce env sf (ArrayT ty bound) (ArrayTV tv bound)) /\
  (!ce env sf tys tvs.
    LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
      P ce env sf ty tv) tys tvs /\
    abi_decoder_header ce env (TupleT tys) (TupleTV tvs) ==>
    P ce env sf (TupleT tys) (TupleTV tvs)) /\
  (!ce env sf nsid args fields tvs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
    LIST_REL (\ty tv.
      abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv /\
      P ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv) (MAP SND args) tvs /\
    abi_decoder_header ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) ==>
    P ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))) ==>
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==> P ce env sf ty tv
Proof
  strip_tac >>
  `!ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    abi_decoder_coherent ce env sf ty tv /\ P ce env sf ty tv`
    suffices_by metis_tac[] >>
  ho_match_mp_tac abi_decoder_coherent_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  (conj_tac
   >- (simp[Once abi_decoder_coherent_cases] >>
       fs[LIST_REL_CONJ, SF ETA_ss] >> metis_tac[]) >>
   metis_tac[])
QED

Theorem calldata_coherent_indexed_ih:
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    P ce env sf ty tv) tys tvs /\ i < LENGTH tys ==>
  abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
  P ce env sf (EL i tys) (EL i tvs)
Proof
  simp[LIST_REL_EL_EQN] >> metis_tac[]
QED

(* These certificates are obtained before applying a child execution IH.
   An unchanged-block child needs no new PHI certificate. A changed child with
   nonempty exit uses its own generated head; only the empty exit needs tail
   code. In the member case an empty tail inherits the enclosing certificate. *)
Theorem calldata_member_child_exit_certificate:
  compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
  fn_has_code mid b fn /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    rest ao vo b = ((),last) /\
  fn_has_code b last fn /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  mid.cs_blocks = b.cs_blocks \/
  (!bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule calldata_recursive_exit_continuation_phi >>
  disch_then irule >> simp[] >> strip_tac >>
  drule calldata_member_tail_continuation_phi >>
  disch_then (qspec_then `fn` mp_tac) >> simp[]
QED

Theorem calldata_loop_child_exit_certificate:
  compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
  fn_has_code mid b fn /\
  abi_decode_loop_suffix ip (Var iv) hdr exit_lbl b = ((),last) /\
  fn_has_code b last fn ==>
  mid.cs_blocks = b.cs_blocks \/
  (!bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule calldata_recursive_exit_continuation_phi >>
  disch_then irule >> simp[] >> strip_tac >>
  drule calldata_loop_child_continuation_phi >>
  disch_then (qspec_then `fn` mp_tac) >> simp[]
QED



(* Parent compilation, rather than caller-supplied phase equations, determines
   every nonbulk interval. The recursive child equation stays opaque. *)
Theorem calldata_nonbulk_parent_intervals:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray di asz msz dyn maxn) st = ((),last) /\
  (dyn \/ dec_info_needs_clamp di) /\ fn_has_code st last fn ==>
  ?ip cnt guard_st header_st loop_st labels st0 ops middle st1.
    abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
      ((ip,cnt),loop_st) /\
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),guard_st) /\
    abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
      (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      di middle = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
    fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
    fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\
    fn_has_code st1 last fn /\ fn_has_code loop_st last fn /\
    st.cs_next_id <= header_st.cs_next_id /\
    header_st.cs_next_id < middle.cs_next_id /\
    middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= last.cs_next_id /\
    st.cs_next_var <= loop_st.cs_next_var /\
    (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf dst src _ _ _ _ st = _` kall_tac >>
  qpat_x_assum `dyn \/ _` kall_tac >>
  drule abi_decode_array_loop_init_trace >> strip_tac >> gvs[] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  `addr = src /\
   abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),guard_st)` by
    (qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_zero_base_eq,
       abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_checked_prefix_def,
       abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
       abiDecoderDynarrayBoundTheory.abi_decode_dynarray_payload_guard_def,
       abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_prefix_def,
       abiDecoderDynarrayBoundTheory.abi_decode_dynarray_end_guard_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  gvs[] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_decoder_loop_prefix_extends >> strip_tac >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_extends >> strip_tac >>
  `cs_extends st loop_st /\ cs_extends st0 middle` by
    metis_tac[cs_extends_same_block, inst_extends_def] >>
  `cs_extends loop_st st1 /\ cs_extends loop_st last` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code st loop_st fn /\ fn_has_code loop_st last fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code loop_st st0 fn /\ fn_has_code st0 st1 fn /\
   fn_has_code st1 last fn /\ fn_has_code st0 middle fn /\ fn_has_code middle st1 fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `ci_mono middle st1` by
    (mp_tac (cj 1 ci_mono_compile_abi_decode) >>
     disch_then (qspecl_then [`SND (SND ops)`,`FST (SND ops)`,
       `CALLDATALOAD`,`Lit 0w`,`Lit 0w`,`di`,`middle`] mp_tac) >> simp[]) >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `?bb. lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX loop_st.cs_current_insts bb.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  `!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)` by
    (rpt strip_tac >> irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`,`loop_st.cs_current_bb`] >> simp[] >>
     irule rich_listTheory.IS_PREFIX_MEM >>
     qexists_tac `loop_st.cs_current_insts` >> simp[] >>
     irule rich_listTheory.MEM_DROP_IMP >>
     qexists_tac `LENGTH header_st.cs_current_insts` >> fs[emitted_insts_def]) >>
  gvs[ci_mono_def,
    abiDecoderExecutionTheory.abi_decode_position_header_delta_def]
QED

Theorem calldata_nonbulk_empty_exit:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray di asz msz dyn maxn) st = ((),last) /\
  (dyn \/ dec_info_needs_clamp di) ==> last.cs_current_insts = []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> simp[]
QED

(* The final empty-exit certificate belongs to the enclosing continuation.
   All internal intervals and names below come from the actual parent. *)
Theorem calldata_nonbulk_parent_shell:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray di asz msz dyn maxn) st = ((),last) /\
  (dyn \/ dec_info_needs_clamp di) /\ fn_has_code st last fn /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?ip cnt guard_st header_st loop_st labels st0 ops middle st1 body_bb exit_bb.
    abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
      ((ip,cnt),loop_st) /\
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),guard_st) /\
    abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
      (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      di middle = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
    st.cs_next_id <= header_st.cs_next_id /\
    header_st.cs_next_id < middle.cs_next_id /\
    middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= last.cs_next_id /\
    fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
    fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\ fn_has_code st1 last fn /\
    lookup_block (FST labels) fn.fn_blocks = SOME
      <|bb_label := FST labels; bb_instructions :=
        abi_decode_header_insts (loop_st.cs_next_id+1) ip src CALLDATALOAD
          (STRING #"%" (toString loop_st.cs_next_var))
          (STRING #"%" (toString (loop_st.cs_next_var+1)))
          (STRING #"%" (toString (loop_st.cs_next_var+2)))
          (STRING #"%" (toString (loop_st.cs_next_var+3)))
          (FST (SND labels)) (SND (SND labels))|> /\
    lookup_block (FST (SND labels)) fn.fn_blocks = SOME body_bb /\
    phi_prefix_length body_bb.bb_instructions = 0 /\
    st0.cs_current_bb = FST (SND labels) /\ st0.cs_current_insts = [] /\
    lookup_block st1.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
        abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
          (STRING #"%" (toString st1.cs_next_var)) ip (FST labels)|> /\
    FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
    lookup_block (SND (SND labels)) fn.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 /\
    last.cs_current_bb = SND (SND labels) /\ last.cs_current_insts = [] /\
    STRING #"%" (toString loop_st.cs_next_var) <>
      STRING #"%" (toString (loop_st.cs_next_var+1)) /\
    src <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
    ip <> Var (STRING #"%" (toString st1.cs_next_var)) /\
    (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
      op <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+1))) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+2))) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+3))) /\
      op <> Var (STRING #"%" (toString st1.cs_next_var)) /\
      abi_decoder_operand_live st0.cs_next_var op) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st0.cs_next_var op ==>
      abi_decoder_operand_live middle.cs_next_var op) /\
    (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_nonbulk_parent_intervals >> strip_tac >>
  qpat_x_assum `dyn \/ _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf dst src _ _ _ _ st = _` kall_tac >>
  drule_all calldata_loop_cfg_producer >> strip_tac >>
  drule_all calldata_loop_child_static >> strip_tac >>
  drule_all calldata_shell_static_producer >> strip_tac >>
  rename1 `lookup_block st0.cs_current_bb fn.fn_blocks = SOME body_bb` >>
  rename1 `lookup_block (SND (SND labels)) fn.fn_blocks = SOME exit_bb` >>
  qexistsl_tac [`ip`,`cnt`,`guard_st`,`header_st`,`loop_st`,`labels`,
    `st0`,`ops`,`middle`,`st1`,`body_bb`,`exit_bb`] >>
  asm_simp_tac bool_ss [] >>
  `STRING #"%" (toString loop_st.cs_next_var) <>
   STRING #"%" (toString (loop_st.cs_next_var+1))` by
    (rw[integer_wordTheory.toString_def, integerTheory.Num_EQ] >>
     strip_tac >> gvs[] >> intLib.COOPER_TAC) >>
  simp[] >> metis_tac[]
QED

Theorem calldata_nonbulk_parent_shell_conditional:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray di asz msz dyn maxn) st = ((),last) /\
  (dyn \/ dec_info_needs_clamp di) /\ fn_has_code st last fn /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  (last.cs_current_insts = [] ==>
    !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  ?ip cnt guard_st header_st loop_st labels st0 ops middle st1 body_bb exit_bb.
    abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn asz st =
      ((ip,cnt),loop_st) /\
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),guard_st) /\
    abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = (labels,st0) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di asz msz st0 =
      (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      di middle = ((),st1) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) st1 = ((),last) /\
    st.cs_next_id <= header_st.cs_next_id /\
    header_st.cs_next_id < middle.cs_next_id /\
    middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= last.cs_next_id /\
    fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
    fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\ fn_has_code st1 last fn /\
    lookup_block (FST labels) fn.fn_blocks = SOME
      <|bb_label := FST labels; bb_instructions :=
        abi_decode_header_insts (loop_st.cs_next_id+1) ip src CALLDATALOAD
          (STRING #"%" (toString loop_st.cs_next_var))
          (STRING #"%" (toString (loop_st.cs_next_var+1)))
          (STRING #"%" (toString (loop_st.cs_next_var+2)))
          (STRING #"%" (toString (loop_st.cs_next_var+3)))
          (FST (SND labels)) (SND (SND labels))|> /\
    lookup_block (FST (SND labels)) fn.fn_blocks = SOME body_bb /\
    phi_prefix_length body_bb.bb_instructions = 0 /\
    st0.cs_current_bb = FST (SND labels) /\ st0.cs_current_insts = [] /\
    lookup_block st1.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
        abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
          (STRING #"%" (toString st1.cs_next_var)) ip (FST labels)|> /\
    FST ops = Var (STRING #"%" (toString st0.cs_next_var)) /\
    lookup_block (SND (SND labels)) fn.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 /\
    last.cs_current_bb = SND (SND labels) /\ last.cs_current_insts = [] /\
    STRING #"%" (toString loop_st.cs_next_var) <>
      STRING #"%" (toString (loop_st.cs_next_var+1)) /\
    src <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
    ip <> Var (STRING #"%" (toString st1.cs_next_var)) /\
    (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
      op <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+1))) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+2))) /\
      op <> Var (STRING #"%" (toString (loop_st.cs_next_var+3))) /\
      op <> Var (STRING #"%" (toString st1.cs_next_var)) /\
      abi_decoder_operand_live st0.cs_next_var op) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st0.cs_next_var op ==>
      abi_decoder_operand_live middle.cs_next_var op) /\
    (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_nonbulk_empty_exit >> disch_tac >>
  `!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (qpat_x_assum `last.cs_current_insts = [] ==> _` mp_tac >>
     qpat_x_assum `last.cs_current_insts = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  drule_all calldata_nonbulk_parent_shell >> disch_then ACCEPT_TAC
QED

(* Indexed metadata and prefix extents are independent of execution, including
   empty member lists and zero-sized members. *)
Theorem calldata_member_indexed_metadata:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs ==>
  LENGTH (abi_decoder_member_infos sf ce tys) = LENGTH tvs /\
  (!i. i < LENGTH tys ==>
    abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
    EL i (abi_decoder_member_infos sf ce tys) =
      (type_to_abi_dec_info sf ce (EL i tys),
       abi_member_head_size (vyper_to_abi_type env (EL i tys)),
       type_memory_size (EL i tvs)) /\
    is_abi_dynamic ce.ce_struct_fields (EL i tys) =
      is_dynamic (vyper_to_abi_type env (EL i tys))) /\
  (!i. SUM (MAP (\(ei,az,mz). mz)
      (TAKE i (abi_decoder_member_infos sf ce tys))) =
    SUM (MAP type_memory_size (TAKE i tvs))) /\
  (!i. SUM (MAP (\(ei,az,mz). az)
      (TAKE i (abi_decoder_member_infos sf ce tys))) =
    SUM (MAP (abi_member_head_size o vyper_to_abi_type env) (TAKE i tys)))
Proof
  strip_tac >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `!i. i < LENGTH tys ==>
    abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
    abi_decoder_header ce env (EL i tys) (EL i tvs)` by
    (rpt strip_tac >> fs[LIST_REL_EL_EQN] >>
     metis_tac[abi_decoder_coherent_header]) >>
  `MAP (\(ei,az,mz). mz) (abi_decoder_member_infos sf ce tys) =
    MAP type_memory_size tvs` by
    (irule LIST_EQ >> simp[abi_decoder_member_infos_def] >>
     rpt strip_tac >> simp[EL_MAP] >>
     qpat_x_assum `!i. i < LENGTH tys ==> _`
       (qspec_then `x` mp_tac) >> simp[abi_decoder_header_def]) >>
  `MAP (\(ei,az,mz). az) (abi_decoder_member_infos sf ce tys) =
    MAP (abi_member_head_size o vyper_to_abi_type env) tys` by
    (irule LIST_EQ >> simp[abi_decoder_member_infos_def] >>
     rpt strip_tac >> simp[EL_MAP] >>
     qpat_x_assum `!i. i < LENGTH tys ==> _`
       (qspec_then `x` mp_tac) >> simp[abi_decoder_header_def]) >>
  conj_tac >- simp[abi_decoder_member_infos_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. i < LENGTH tys ==> _`
        (qspec_then `i` mp_tac) >>
      simp[abi_decoder_member_infos_def, EL_MAP, abi_decoder_header_def]) >>
  asm_rewrite_tac[MAP_TAKE]
QED

Theorem calldata_tuple_member_metadata:
  abi_decoder_coherent ce env sf (TupleT tys) atv ==>
  ?tvs.
    atv = TupleTV tvs /\
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    LENGTH tvs = LENGTH tys /\
    type_to_abi_dec_info sf ce (TupleT tys) =
      DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
        (abi_decoder_member_infos sf ce tys) /\
    type_memory_size atv = SUM (MAP type_memory_size tvs)
Proof
  simp_tac bool_ss [abi_decoder_coherent_tuple_iff] >> strip_tac >>
  qexists_tac `tvs` >> simp[abi_decoder_tuple_infos] >>
  conj_tac >- metis_tac[LIST_REL_LENGTH] >>
  simp_tac std_ss [type_memory_size_def] >>
  POP_ASSUM_LIST (K all_tac) >>
  Induct_on `tvs` >> simp[type_memory_size_def]
QED

Theorem calldata_struct_member_metadata:
  abi_decoder_coherent ce env sf (StructT nsid) atv ==>
  ?args fields tvs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    atv = StructTV (ZIP (MAP FST args,tvs)) /\
    LENGTH fields = LENGTH args /\ LENGTH tvs = LENGTH args /\
    MAP (FST o SND) fields = MAP SND args /\
    LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
      (MAP SND args) tvs /\
    type_to_abi_dec_info sf ce (StructT nsid) =
      DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args))
        (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args)) /\
    (!i. i < LENGTH args ==>
      type_memory_size (EL i tvs) = (\(name,ty,sz). sz) (EL i fields))
Proof
  strip_tac >> drule calldata_struct_child_metadata >> strip_tac >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  `LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
     (MAP SND args) tvs` by
    (simp[LIST_REL_EL_EQN, EL_MAP] >> metis_tac[]) >>
  qexistsl_tac [`args`,`fields`,`tvs`] >>
  simp[] >> drule abi_decoder_struct_infos >> simp[]
QED

Theorem calldata_fixed_member_metadata:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) atv ==>
  ?tv.
    atv = ArrayTV tv (Fixed n) /\
    abi_decoder_coherent ce env sf ty tv /\
    LIST_REL (abi_decoder_coherent ce env sf) (REPLICATE n ty) (REPLICATE n tv) /\
    type_to_abi_dec_info sf ce (ArrayT ty (Fixed n)) =
      DecComplex (is_abi_dynamic ce.ce_struct_fields ty)
        (abi_decoder_member_infos sf ce (REPLICATE n ty)) /\
    type_memory_size atv = n * type_memory_size tv /\
    (!i. i < n ==> EL i (REPLICATE n ty) = ty /\ EL i (REPLICATE n tv) = tv)
Proof
  simp_tac bool_ss [abi_decoder_coherent_array_iff] >> strip_tac >>
  qexists_tac `tv` >>
  simp[abi_decoder_fixed_array_infos, type_memory_size_def,
    LIST_REL_EL_EQN, rich_listTheory.EL_REPLICATE]
QED

Theorem calldata_index_alloca_site:
  abi_decode_index_init header_st = (ip,loop_st) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) ==>
  ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = header_st.cs_next_id /\
    ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w] /\
    alloca_size ins = 32
Proof
  strip_tac >>
  `MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString header_st.cs_next_var)])
    (emitted_insts header_st loop_st)` by
    (qpat_x_assum `abi_decode_index_init _ = _` mp_tac >>
     simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[DROP_LENGTH_APPEND]) >>
  qexists_tac `mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]` >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  simp[mk_inst_def, alloca_size_def] >> metis_tac[]
QED

Theorem calldata_owned_counter_address:
  abi_decode_index_init header_st = (ip,loop_st) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  lo <= header_st.cs_next_id /\ header_st.cs_next_id < hi /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < lo \/ hi <= oid) /\ base_addr <= d /\ d+sz <= base_addr+cap /\
  (!id q k. lo <= id /\ id < hi /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next) ==>
  ?p.
    ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
       p = initial.vs_alloca_next) \/
     (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
       p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
    (d+sz <= p \/ p+32 <= d) /\ p+32 < dimword (:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_index_alloca_site >> strip_tac >>
  `d+sz <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >>
     qpat_assum `FLOOKUP _ oid = _` (irule_at Any) >> simp[]) >>
  Cases_on `FLOOKUP initial.vs_allocas header_st.cs_next_id`
  >- (`header_st.cs_next_id NOTIN FDOM initial.vs_allocas` by
        metis_tac[finite_mapTheory.flookup_thm] >>
      `ins.inst_id NOTIN FDOM initial.vs_allocas` by simp[] >>
      `initial.vs_alloca_next+32 < dimword (:256)` by
        (drule_all actual_word_alloca_no_wrap >> simp[]) >>
      qexists_tac `initial.vs_alloca_next` >>
      simp_tac bool_ss [] >> metis_tac[]) >>
  rename1 `FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME slot` >>
  PairCases_on `slot` >>
  `slot1 = 32 /\ slot0 < dimword (:256) /\ slot0+32 <= initial.vs_alloca_next` by
    metis_tac[] >>
  qpat_x_assum `!id q k. _` kall_tac >>
  qpat_x_assum `slot1 = 32` SUBST_ALL_TAC >>
  `oid <> header_st.cs_next_id` by decide_tac >>
  `base_addr+cap <= slot0 \/ slot0+32 <= base_addr` by
    metis_tac[abi_caller_allocation_separate] >>
  `initial.vs_alloca_next <= unit_alloca_budget ctx` by
    (fs[alloca_frontier_inv_def] >> decide_tac) >>
  qexists_tac `slot0` >> simp_tac std_ss [] >> decide_tac
QED

(* CONSUMER COMPATIBILITY CHECKPOINT (.38, after .34-.37).
   Result: static producers are available, but universal assembly is NOT yet
   ready. In particular the member callback interface loses the tail equation.
   This is an interface gap, not checked falsehood of the frozen theorem.

   Generalized induction: calldata_coherent_induction keeps coherence together
   with P ce env sf ty tv. P must quantify all compiler/runtime/owner/global
   parameters listed in the recursive contract above. calldata_coherent_indexed_ih
   extracts this full P for each member; no runtime state is fixed by the rule.
   The final continuation input must be the conditional empty-exit certificate,
   not an unconditional certificate on an unchanged block with an earlier PHI.

   Base/flag cases: calldata_coherent_word_owned_run covers is_word_type.
   Dynamic bytes and StringT use calldata_coherent_bytes_owned_run and
   calldata_coherent_string_owned_run. Coherence/header inversion supplies
   their exact tv/descriptor/extent; these adapters require no recursive IH.
   Array bulk branch: calldata_coherent_bulk_array_owned_run applies when the
   child dynamicness and clamp test are both false, and reconstructs observed
   values directly. The empty fixed/tuple/struct cases have no child index;
   prefix identities and LIST_REL metadata hold without positivity assumptions.

   Tuple: calldata_tuple_member_metadata provides tvs and the emitted member
   list xs=abi_decoder_member_infos sf ce tys. Apply
   calldata_member_indexed_metadata to its LIST_REL for descriptor, child type,
   dynamicness, ABI offsets and memory offsets; indexed IH uses EL i tys/tvs.
   Struct: calldata_struct_member_metadata gives xs under sf minus nsid string,
   child source list MAP SND args and tvs under env minus nsid as well.
   MAP SND (ZIP (MAP FST args,tvs))=tvs follows from the supplied length equation.
   Thus the struct adapter's MAP SND ftypes is the same child value-type list;
   no restoration of either deleted map is permitted.
   Fixed: calldata_fixed_member_metadata gives source/value lists REPLICATE n
   ty/tv. The common indexed metadata theorem yields actual descriptor/stride
   and both prefix sums. The single array child IH is specialized at each index.
   For all three, calldata_member_child_static gives child live operands and
   compiler intervals from the actual address/child compilation. Owner exclusion
   and separation transfer via calldata_child_owner_window; runtime ownership
   is an input to the callback, not a premise of completed registration.

   Nonbulk dynamic array: calldata_nonbulk_parent_shell provides initializer,
   all five installed intervals, header/body/backedge/exit code, name separation
   and child operand liveness from the actual parent compiler equation.
   calldata_owned_counter_address with lo=st.cs_next_id, hi=last.cs_next_id,
   sz=type_memory_size (ArrayTV tv (Dynamic maxn)) gives the fresh/reused p and
   strict no-wrap; calldata_child_owner_window gives output bounds in callbacks.
   Coherent array inversion gives child ty/tv; dynamic_layout gives di, stride,
   and memory size. The nonbulk callback's middle/st1 are fixed shell states.
   Its ACTUAL suffix and fn_has_code st1 last justify
   calldata_loop_child_continuation_phi before invoking the child IH. The
   outer empty loop exit uses the inherited conditional final certificate.

   RESIDUAL: calldata_complex_tuple_owned_run's callback (AggregateTyped:85-129),
   reused for struct and fixed arrays, quantifies arbitrary i,a,mid,b and only
   supplies cs_extends st a, cs_extends b final, ci_mono and fn_has_code mid b fn.
   It does NOT supply compile_abi_decode_complex_elems ... rest ... b=((),final)
   or fn_has_code b final fn. calldata_member_child_exit_certificate REQUIRES
   both facts, and calldata_member_tail_continuation_phi also requires the
   actual tail equation. They cannot simply be drule'd at this callback.
   Internally calldata_members_owned_repeat_intervals DOES retain the tail
   equation in Inv (Members:1171-1174) and uses it before its callback application
   (Members:1251-1254,1298), but that provenance is erased by the exported
   callback signature. No theorem deriving it from the exported callback's
   weaker extension facts has been established. A strategist-owned interface
   repair is required before universal induction can use these member adapters;
   do not introduce a tail equation as an extra universal/top-level assumption.
*)

(* Conditional version: a nonempty tail supplies its own head, so only the
   empty-tail branch needs the inherited empty-exit certificate. *)
Theorem calldata_member_tail_empty_exit_phi:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    elems ao vo a = ((),z) /\
  fn_has_code a z fn /\
  (z.cs_current_insts = [] ==>
    !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  a.cs_current_insts = [] ==>
  !bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `elems`
  >- simp[Once compile_abi_decode_to_buf_def, comp_return_def] >>
  rename1 `h::rest` >> PairCases_on `h` >>
  simp_tac bool_ss [Once compile_abi_decode_to_buf_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_getelemptr_abi src (dec_info_needs_offset h0) ao CALLDATALOAD (Lit 0w) (Lit 0w) a` >>
  rename1 `_ = (ep,mid)` >> simp_tac bool_ss [] >>
  Cases_on `emit_op ADD [dst; Lit (n2w vo)] mid` >>
  rename1 `_ = (dp,b)` >> simp_tac bool_ss [] >>
  Cases_on `compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) h0 b` >>
  rename1 `_ = (u,c)` >> Cases_on `u` >> simp_tac bool_ss [] >>
  strip_tac >> strip_tac >> gvs[] >>
  `cs_extends b c` by (drule cs_extends_abi_decode >> simp[]) >>
  `cs_extends c z` by
    (irule (cj 2 cs_appends_abi_decode_mutual |> SRULE[cs_appends_def]) >>
     first_assum (irule_at Any)) >>
  `cs_extends b z` by metis_tac[cs_extends_trans] >>
  ` (do ep <- compile_getelemptr_abi src (dec_info_needs_offset h0) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)]; return (ep,dp) od) a = ((ep,dp),b)` by
    simp[comp_bind_def, comp_return_def] >>
  drule calldata_member_address_shape >> strip_tac >>
  `cs_extends a b` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code a b fn` by metis_tac[fn_has_code_split] >>
  metis_tac[calldata_member_address_continuation_phi]
QED

Theorem calldata_member_child_conditional_exit_certificate:
  compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
  fn_has_code mid b fn /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    rest ao vo b = ((),final) /\
  fn_has_code b final fn /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  (b.cs_current_insts = [] ==>
    !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> drule calldata_member_tail_empty_exit_phi >>
  disch_then (qspec_then `fn` mp_tac) >> simp[]
QED

(* The indexed inputs are the exact zero-offset callback facts exported by the
   typed tail companions. P keeps every runtime parameter generalized. *)
Theorem calldata_tuple_child_ih_inputs:
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    P ce env sf ty tv) tys tvs /\
  xs = abi_decoder_member_infos sf ce tys /\ i < LENGTH xs /\
  compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
  fn_has_code mid b fn /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DROP (SUC i) xs)
    (az + (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))
    (mz + (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) b = ((),final) /\
  fn_has_code b final fn /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
  P ce env sf (EL i tys) (EL i tvs) /\
  (b.cs_current_insts = [] ==>
    !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `i < LENGTH tys` by gvs[abi_decoder_member_infos_def] >>
  drule_all calldata_coherent_indexed_ih >> strip_tac >>
  simp[] >> drule calldata_member_tail_empty_exit_phi >>
  disch_then (qspec_then `fn` mp_tac) >> simp[]
QED

Theorem calldata_struct_child_ih_inputs:
  LIST_REL (\ty tv.
    abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv /\
    P ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv) (MAP SND args) tvs /\
  xs = abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args) /\
  i < LENGTH xs /\
  compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
  fn_has_code mid b fn /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DROP (SUC i) xs)
    (az + (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))
    (mz + (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) b = ((),final) /\
  fn_has_code b final fn /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (EL i (MAP SND args)) (EL i (MAP SND (ZIP (MAP FST args,tvs)))) /\
  P ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (EL i (MAP SND args)) (EL i (MAP SND (ZIP (MAP FST args,tvs)))) /\
  (b.cs_current_insts = [] ==>
    !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by simp[MAP_ZIP] >>
  simp[] >> drule_all calldata_tuple_child_ih_inputs >> simp[]
QED

Theorem calldata_fixed_child_ih_inputs:
  abi_decoder_coherent ce env sf ty tv /\ P ce env sf ty tv /\
  xs = abi_decoder_member_infos sf ce (REPLICATE n ty) /\
  i < LENGTH xs /\
  compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
  fn_has_code mid b fn /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DROP (SUC i) xs)
    (az + (0+SUM (MAP (\(ei,az,mz). az) (TAKE i xs))))
    (mz + (0+SUM (MAP (\(ei,az,mz). mz) (TAKE i xs)))) b = ((),final) /\
  fn_has_code b final fn /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  abi_decoder_coherent ce env sf (EL i (REPLICATE n ty)) (EL i (REPLICATE n tv)) /\
  P ce env sf (EL i (REPLICATE n ty)) (EL i (REPLICATE n tv)) /\
  (b.cs_current_insts = [] ==>
    !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    P ce env sf ty tv) (REPLICATE n ty) (REPLICATE n tv)` by
    simp[LIST_REL_EL_EQN, rich_listTheory.EL_REPLICATE] >>
  drule_all calldata_tuple_child_ih_inputs >> simp[]
QED

(* CHECKED RESOLUTION OF THE E0225 READINESS FINDING (.39--.41).
   The earlier RESIDUAL above is historical: the old public adapters still
   intentionally have that interface. New companions, not changed assumptions
   on a universal theorem, supply the missing provenance:
     calldata_members_owned_repeat_intervals_tail;
     calldata_complex_tuple_owned_run_tail;
     calldata_complex_struct_owned_run_tail;
     calldata_coherent_fixed_array_owned_run_tail.
   Each indexed callback has the actual rest=(DROP (SUC i) xs), ABI offset
   az+SUM(az,TAKE i xs), and destination offset mz+SUM(mz,TAKE i xs), as well as
   fn_has_code b final fn. These are emitted tails, not reconstructed code.

   The old tail producer required an UNCONDITIONAL final PHI certificate.
   calldata_member_tail_empty_exit_phi checks the precise conditional form:
   its empty-list proof identifies a=z, and its nonempty-list proof uses the
   generated address ADD head without any final certificate. The new
   calldata_member_child_conditional_exit_certificate concludes exactly the
   b.insts=[] ==> PHI-free lookup implication needed by the generalized IH;
   it does not substitute the unchanged-block disjunction for that implication.

   CHECKED INDEXED CONSUMERS:
   - calldata_tuple_child_ih_inputs: tys/tvs from the tuple induction case,
     xs=abi_decoder_member_infos sf ce tys, zero initial offsets. Extracts
     coherence and P at EL i tys/tvs and the conditional child certificate.
   - calldata_struct_child_ih_inputs: source list MAP SND args, env minus nsid,
     sf minus nsid_to_string nsid in BOTH coherence and P. The LIST_REL length
     equation discharges MAP SND(ZIP(MAP FST args,tvs))=tvs. Its conclusion is
     deliberately in the struct adapter's exact EL i(MAP SND ftypes) shape.
     Neither deleted map is restored.
   - calldata_fixed_child_ih_inputs: xs is the actual
     abi_decoder_member_infos sf ce(REPLICATE n ty), with a single coherent
     child/P lifted to REPLICATE n ty/tv. The tuple consumer checks the same
     DROP tail and zero-offset prefix sums; no synthesized member list is used.
   For zero members the i<LENGTH xs premise has no witness. For the final
   member DROP(SUC i) xs=[] is allowed: the checked empty-list branch above
   uses precisely the inherited conditional final certificate. No positivity
   or nonempty-tail premise has been added to any consumer.

   REMAINING CONSTRUCTOR MAPPING (source/signature recheck, not execution):
   - Scalar and FlagT: calldata_coherent_word_owned_run handles both via
     coherence and the finite word layout. BytesT/StringT use the checked
     calldata_coherent_bytes_owned_run/string_owned_run. No child IH.
   - Fixed arrays and tuple/struct aggregates: the new _tail adapters retain
     every typed-memory/val_wf, safe rejection, non-Error continuation, live
     operand, allocation-map/ownership and footprint conclusion. Descriptor,
     length and memory prefix equality come from *_member_metadata and
     calldata_member_indexed_metadata; calldata_member_child_static supplies
     live ep/dp and nested intervals, calldata_child_owner_window supplies oid
     exclusion. Runtime destination bounds and existing scratch ownership are
     callback inputs. The three consumers above supply child coherence/P and
     the formerly missing continuation input; P still quantifies all runtime
     states and resources, so no register freshness/registration is assumed.
   - Dynamic bulk arrays: calldata_coherent_bulk_array_owned_run when both
     child dynamicness and clamp need are false; no child IH (also count zero).
   - Dynamic nonbulk arrays: calldata_nonbulk_parent_intervals extracts actual
     initializer/setup/child/suffix phases. abi_decode_dyn_loop_trace together
     with abi_decoder_loop_suffix_facts identifies the exit as empty; therefore
     the inherited conditional outer certificate supplies the unconditional
     final certificate consumed by calldata_nonbulk_parent_shell. The shell
     gives installed intervals, names/live operands and actual counter site.
     calldata_owned_counter_address handles fresh/reused p, using inherited
     unit budget, distinct IDs, owner exclusion and existing slot certificates.
     Child coherence is the array induction premise; actual suffix plus
     fn_has_code st1 final fn feed calldata_loop_child_continuation_phi under
     st1.insts=[]. This is independent of the member-tail repair. The runtime
     callback keeps alloca/frontier/owner/bounds as inputs even on repeated
     entry; zero count needs no callback. No additional loop proof is claimed.

   No remaining missing child-IH INPUT was found in this recheck. This is not
   a proof of universal execution: application of all adapters under the full
   generalized P, callback resource instantiation, and preservation/composition
   still require a strategist-authorized assembly proof. The parent remains
   blocked until that review; registration, concrete entry, memory/pipeline
   and the frozen arbitrary-calldata theorem are still outside this boundary.
*)
