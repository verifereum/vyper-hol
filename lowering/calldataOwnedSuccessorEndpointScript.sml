(* Actual source-valid setup endpoints for owned array iteration. *)
Theory calldataOwnedSuccessorEndpoint
Ancestors
  abiDecoderFrame abiEncoder calldataEmptyArrayChild calldataStaticSetupEndpoint abiDecoderExecution abiDecoderLoopRegisters abiEncoderChildSuffix valueEncodingProofs successfulSequenceEndpoint calldataValidOwnedChild calldataValidOwnedStep
  calldataDynOwned calldataDynStep abiDecoderArraySetupInputs instIdxIndep
  abiDecoderValidArrayEntry abiDecoderContract abiDecoderCoherence abiDecoderDynamic
  abiDecoderOffset abiDecoderReentry abiDecoderTypedContract abiValidMember
  abiDecoderArrayBackedge abiDecoderDynamicLoopSetup decoderPrefixEdges safeSequence fragExecMem venomMemDefs compileEnv
  emitHelperProps exprLoweringProps venomState venomExecSemantics words list arithmetic

Theorem calldata_dynamic_valid_owned_array_child_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  eval_operand ip initial = SOME (n2w slot) /\ mload slot initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FLOOKUP initial.vs_allocas iid = SOME (slot,32) /\
  alloca_inv initial /\ slot < dimword (:256) /\
  fn_has_code st ready fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?child. ~child.vs_halted /\ child.vs_current_bb = ready.cs_current_bb /\
    child.vs_inst_idx = LENGTH ready.cs_current_insts /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b reserve_cap st.cs_next_var limit_st initial child /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op child = eval_operand op initial) /\
    child.vs_memory = initial.vs_memory /\
    child.vs_call_ctx = initial.vs_call_ctx /\
    child.vs_data_section = initial.vs_data_section /\
    child.vs_allocas = initial.vs_allocas /\
    child.vs_alloca_next = initial.vs_alloca_next /\
    ((!fuel. mem_safe_run fuel ctx fn child) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    (!fuel r. run_from fuel ctx fn child = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn child ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (n2w slot : bytes32) = slot` by simp[] >>
  `mload (w2n (n2w slot : bytes32)) initial = n2w j` by simp[] >>
  `slot+32 <= initial.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all abi_decoder_valid_array_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  `eval_operand src initial = SOME (n2w sb) /\
   eval_operand dst initial = SOME (n2w d)` by fs[abi_decoder_ranges_def] >>
  drule_all calldata_element_setup_repeat >> strip_tac >> gvs[] >>
  `run_inst_seq_mem_ok (emitted_insts st ready) initial` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (drule calldata_element_setup_opcodes >> simp[EVERY_MEM]) >>
     ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
     qexistsl_tac [`src`, `n2w slot`] >>
     goal_assum (drule_at Any) >> simp[w2n_n2w] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st ready)` by
    (drule calldata_element_setup_opcodes >> simp[EVERY_MEM]) >>
  mp_tac (Q.INST [`s` |-> `initial`, `t` |-> `prepared`, `P` |-> `\child.
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b reserve_cap st.cs_next_var limit_st initial child /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op child = eval_operand op initial)`] (SPEC_ALL successful_sequence_endpoint)) >>
  simp[eval_op_inst_idx] >> strip_tac >>
  qexists_tac `prepared with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  fs[eval_op_inst_idx, abi_decoder_valid_array_entry_def, abi_decoder_address_frame_def]
QED

Theorem calldata_general_array_child_endpoint[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  eval_operand ip initial = SOME (n2w slot) /\ mload slot initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FLOOKUP initial.vs_allocas iid = SOME (slot,32) /\
  alloca_inv initial /\ slot < dimword (:256) /\
  fn_has_code st ready fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?child. ~child.vs_halted /\ child.vs_current_bb = ready.cs_current_bb /\
    child.vs_inst_idx = LENGTH ready.cs_current_insts /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b reserve_cap st.cs_next_var limit_st initial child /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op child = eval_operand op initial) /\
    child.vs_memory = initial.vs_memory /\
    child.vs_call_ctx = initial.vs_call_ctx /\
    child.vs_data_section = initial.vs_data_section /\
    child.vs_allocas = initial.vs_allocas /\
    child.vs_alloca_next = initial.vs_alloca_next /\
    ((!fuel. mem_safe_run fuel ctx fn child) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    (!fuel r. run_from fuel ctx fn child = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn child ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (drule_all calldata_dynamic_valid_owned_array_child_endpoint >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  drule_all calldata_static_valid_owned_array_child_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  fs[abi_decoder_valid_array_entry_def, abi_decoder_address_frame_def]
QED

(* The header endpoint is specified explicitly, so its two transfers share
   exactly the same witness; no successful continuation is used for Pull. *)
Theorem calldata_valid_header_prepare_pullback[local]:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ j < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
  eval_operand src u = SOME srcword /\
  abi_decode_load CALLDATALOAD srcword u = n2w (LENGTH vs) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st u /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d outsz b reserve_cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    ~head.vs_halted /\ head.vs_current_bb = body_lbl /\ head.vs_inst_idx = 0 /\
    fresh_vars_wrt limit_st head /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
      d outsz b reserve_cap head /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD head) = bs /\
    eval_operand ip head = SOME (n2w p) /\ mload p head = n2w j /\
    head.vs_memory = u.vs_memory /\ head.vs_call_ctx = u.vs_call_ctx /\
    head.vs_data_section = u.vs_data_section /\ head.vs_allocas = u.vs_allocas /\
    head.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op head = eval_operand op u) /\
    (!fuel r. run_from fuel ctx fn head = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn head ==> mem_safe_run fuel' ctx fn u)) /\
    ((!fuel. mem_safe_run fuel ctx fn head) ==> !fuel. mem_safe_run fuel ctx fn u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_valid_header_prepare >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `src <> Var (STRING #"%" (toString next))` by
    (irule abi_decoder_live_excludes_output >> qexists_tac `next` >> simp[]) >>
  `STRING #"%" (toString next) <> STRING #"%" (toString (next+1))` by simp[] >>
  `mload (w2n (n2w p:bytes32)) u = n2w j /\
   w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` by simp[] >>
  `j <= LENGTH vs` by decide_tac >>
  `lookup_block (if j < LENGTH vs then body_lbl else exit_lbl) fn.fn_blocks =
    SOME body_bb` by simp[] >>
  `head = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j (LENGTH vs) u)` by simp[] >>
  qexists_tac `head` >> asm_rewrite_tac[] >> strip_tac >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] calldata_header_all_fuel_pullback) >>
  asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
  simp[] >> goal_assum (drule_at (Pat `!fuel. mem_safe_run fuel _ _ _`)) >>
  qexistsl_tac [`hid`, `ip`, `n2w p:bytes32`, `src`, `srcword`] >> simp[]
QED

Theorem calldata_valid_header_child_endpoint:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st0 = (ops,ready) /\ fn_has_code st0 ready fn /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ j < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
  eval_operand src u = SOME srcword /\
  abi_decode_load CALLDATALOAD srcword u = n2w (LENGTH vs) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  FLOOKUP u.vs_allocas iid = SOME (p,32) /\ alloca_inv u /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\ next <= st0.cs_next_var /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st u /\
  ready.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head entry.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b reserve_cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\
    entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
    entry.vs_data_section = u.vs_data_section /\ entry.vs_allocas = u.vs_allocas /\
    entry.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op entry = eval_operand op u) /\
    (!fuel r. run_from fuel ctx fn entry = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn entry ==> mem_safe_run fuel' ctx fn u)) /\
    ((!fuel. mem_safe_run fuel ctx fn entry) ==> !fuel. mem_safe_run fuel ctx fn u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_valid_header_prepare_pullback >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_operand_live st0.cs_next_var src /\
   abi_decoder_operand_live st0.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `abi_decoder_operand_live st0.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  `FLOOKUP head.vs_allocas iid = SOME (p,32) /\ alloca_inv head` by
    (asm_rewrite_tac[] >> metis_tac[cj 1 calldata_alloca_invariants_fields]) >>
  `head.vs_current_bb = st0.cs_current_bb /\
   head.vs_inst_idx = LENGTH st0.cs_current_insts` by simp[] >>
  drule_all calldata_general_array_child_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `entry.vs_current_bb = ready.cs_current_bb` >>
  qexistsl_tac [`head`, `entry`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[abi_decoder_operand_live_mono] >>
  conj_tac >- suspend "safe" >> metis_tac[]
QED
Resume calldata_valid_header_child_endpoint[safe]:
  qpat_assum `!fuel r. run_from fuel ctx fn entry = r /\ _ ==> _` mp_tac >>
  qpat_assum `!fuel r. run_from fuel ctx fn head = r /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> ntac 2 strip_tac >> rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn entry = r /\ _ ==> _` drule >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn head = r /\ _ ==> _` drule >>
  asm_rewrite_tac[] >> metis_tac[]
QED
Finalise calldata_valid_header_child_endpoint

(* Resource reassembly at the actual child and backedge witnesses. *)
Theorem calldata_owned_fixed_successor_endpoint:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s);
      H = \j s scratch.
        ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
        j <= LENGTH vs /\ LENGTH vs <= maxn /\
        eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
        eval_operand ip s = SOME (n2w p) /\ mload p s = n2w j /\
        abi_decode_load CALLDATALOAD srcword s = n2w (LENGTH vs) /\
        mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
        s.vs_call_ctx = initial.vs_call_ctx /\ s.vs_data_section = initial.vs_data_section /\
        FLOOKUP s.vs_allocas iid = SOME (p,32) /\
        FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
        alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
        Own st.cs_next_id end_st.cs_next_id s /\
        initial.vs_alloca_next <= s.vs_alloca_next /\
        (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
          FLOOKUP s.vs_allocas id = SOME (q,k)) /\
        (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
          FLOOKUP s.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
        (!op. abi_decoder_operand_live st.cs_next_var op ==>
          eval_operand op s = eval_operand op initial) /\
        abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial s /\
        MEM (p,32) scratch /\
        (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP s.vs_allocas id = SOME (q,k)) /\
        fresh_vars_wrt limit_st s /\
        abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
          d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap s /\
        mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
  in
  H j u old /\
  (!k. k < j ==> val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) u.vs_memory) /\
  st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= st1.cs_next_id /\
  st1.cs_next_id <= end_st.cs_next_id /\
  EVERY (val_wf tv) vs /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  p < dimword (:256) /\ d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (iid < ready.cs_next_id \/ st1.cs_next_id <= iid) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  nvar < limit_st.cs_next_var /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var (STRING #"%" (toString nvar)) /\ abi_decoder_operand_live next op) /\
  (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op) /\
  entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
  entry.vs_data_section = u.vs_data_section /\ entry.vs_allocas = u.vs_allocas /\
  entry.vs_alloca_next = u.vs_alloca_next /\
  (!op. abi_decoder_operand_live next op ==> eval_operand op entry = eval_operand op u) /\
  ~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
  child.vs_inst_idx = LENGTH st1.cs_current_insts /\
  val_wf tv (EL j vs) /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) child.vs_memory /\
  fresh_vars_wrt limit_st child /\
  child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
  alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
  Own ready.cs_next_id st1.cs_next_id child /\
  entry.vs_alloca_next <= child.vs_alloca_next /\
  (!id q k. FLOOKUP entry.vs_allocas id = SOME (q,k) ==>
    FLOOKUP child.vs_allocas id = SOME (q,k)) /\
  (!id. id < ready.cs_next_id \/ st1.cs_next_id <= id ==>
    FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id) /\
  (!op. abi_decoder_operand_live ready.cs_next_var op ==>
    eval_operand op child = eval_operand op entry) /\
  abi_decode_footprint_frame
    ((d+32+j*type_memory_size tv,type_memory_size tv)::new) entry child /\
  (!q k. MEM (q,k) new ==> ?id. ready.cs_next_id <= id /\ id < st1.cs_next_id /\
    FLOOKUP child.vs_allocas id = SOME (q,k)) /\
  v = jump_to hdr (mstore p (n2w (SUC j))
    (update_var (STRING #"%" (toString nvar)) (n2w (SUC j)) child)) /\
  Safe u entry /\ Pull u entry /\ Safe entry child /\ Pull entry child /\
  Safe child v /\ Pull child v ==>
  H (SUC j) v (old++new) /\
  (!k. k < SUC j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) v.vs_memory) /\ Safe u v /\ Pull u v
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Pull` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `H j u old` mp_tac >>
  qpat_assum `Abbrev (H = _)` (fn th => CONV_TAC
    (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldata_backedge_owned_state >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
  qpat_x_assum `v = jump_to _ _` (mk_asm "vdef") >>
  `SUC j <= maxn` by decide_tac >>
  `SUC j * type_memory_size tv <= maxn * type_memory_size tv` by
    simp[LE_MULT_RCANCEL] >>
  `j*type_memory_size tv + type_memory_size tv <= maxn*type_memory_size tv` by
    (qpat_assum `SUC j * _ <= _` mp_tac >> pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `!op. abi_decoder_operand_live next op ==>
    eval_operand op child = eval_operand op u` by
    (qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op entry = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live ready.cs_next_var op ==> eval_operand op child = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory =
   mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory` by suspend "child_prefix" >>
  conj_tac >- suspend "invariant" >>
  conj_tac >- suspend "prefix" >>
  conj_tac >- suspend "safe" >> suspend "pull"
QED
Resume calldata_owned_fixed_successor_endpoint[safe]:
  qpat_assum `Safe u entry` mp_tac >>
  qpat_assum `Safe entry child` mp_tac >> qpat_assum `Safe child v` mp_tac >>
  qpat_assum `Abbrev (Safe = _)` (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> POP_ASSUM_LIST (K all_tac) >>
  ntac 3 strip_tac >> rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn v = r /\ _ ==> _` drule >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn child = r /\ _ ==> _` drule >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn entry = r /\ _ ==> _` drule >>
  asm_rewrite_tac[] >> metis_tac[]
QED
Resume calldata_owned_fixed_successor_endpoint[pull]:
  qpat_assum `Pull u entry` mp_tac >> qpat_assum `Pull entry child` mp_tac >>
  qpat_assum `Pull child v` mp_tac >>
  simp_tac bool_ss [Abbr `Pull`] >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume calldata_owned_fixed_successor_endpoint[invariant]:
  qpat_assum `Abbrev (H = _)` (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >> BETA_TAC >>
  `!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op u` by
    (qpat_assum `!op. op = src \/ _ ==> _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op child = _` mp_tac >>
     qpat_assum `!op. op <> Var _ ==> eval_operand op v = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `eval_operand src v = SOME srcword /\ eval_operand dst v = SOME (n2w d) /\
   eval_operand ip v = SOME (n2w p)` by
    (qpat_assum `!op. op = src \/ _ ==> eval_operand op v = _` mp_tac >>
     qpat_assum `eval_operand src u = _` mp_tac >>
     qpat_assum `eval_operand dst u = _` mp_tac >>
     qpat_assum `eval_operand ip u = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `~v.vs_halted /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\
   mload p v = n2w (SUC j)` by
    (asm "vdef" (fn th => rewrite_tac[th]) >>
     conj_tac >- simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
     conj_tac >- simp[jump_to_def] >> conj_tac >- simp[jump_to_def] >>
     `!s. mload p (jump_to hdr s) = mload p s` by simp[mload_def, jump_to_def] >>
     asm_rewrite_tac[venomMemProofsTheory.mload_mstore_same_proof]) >>
  `abi_decode_load CALLDATALOAD srcword v = n2w (LENGTH vs)` by
    (fs[abi_decode_load_def, abi_decode_source_def]) >>
  asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac >- suspend "length_word" >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- suspend "ownership" >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "outside" >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "footprint" >>
  conj_tac >- simp[MEM_APPEND] >>
  conj_tac >- suspend "scratch" >> suspend "source"

QED
Resume calldata_owned_fixed_successor_endpoint[child_prefix]:
  `mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory =
   mem_bytes_at d (32+j*type_memory_size tv) entry.vs_memory` suffices_by simp[] >>
  irule (GEN_ALL calldata_child_preserves_contained_prefix) >> asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
  qexistsl_tac [`base_addr`,`cap`,`st1.cs_next_id`,`ready.cs_next_id`,`oid`] >>
  qpat_assum `entry.vs_allocas = u.vs_allocas` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  asm_rewrite_tac[] >> decide_tac
QED
Resume calldata_owned_fixed_successor_endpoint[length_word]:
  `mem_word_at d child.vs_memory = mem_word_at d u.vs_memory` by
    (drule (cj 2 mem_bytes_at_agree_window) >>
     disch_then (qspec_then `d` mp_tac) >> simp[]) >>
  `mem_bytes_at d 32 v.vs_memory = mem_bytes_at d 32 child.vs_memory` by
    (qpat_x_assum `!a len. _ ==> mem_bytes_at a len v.vs_memory = _`
       (qspecl_then [`d`,`32`] mp_tac) >> impl_tac >- decide_tac >> simp[]) >>
  drule (cj 2 mem_bytes_at_agree_window) >>
  disch_then (qspec_then `d` mp_tac) >> simp[]
QED
Resume calldata_owned_fixed_successor_endpoint[ownership]:
  qpat_assum `Own st.cs_next_id end_st.cs_next_id u` mp_tac >>
  qpat_assum `Own ready.cs_next_id st1.cs_next_id child` mp_tac >>
  qpat_assum `Abbrev (Own = _)` (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >> BETA_TAC >>
  ntac 2 strip_tac >> asm_rewrite_tac[] >>
  match_mp_tac (Q.INST [`s` |-> `u`, `a` |-> `ready.cs_next_id`,
    `b` |-> `st1.cs_next_id`] calldata_owned_interval_replace) >>
  asm_rewrite_tac[] >>
  qpat_assum `entry.vs_allocas = u.vs_allocas` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  asm_rewrite_tac[] >>
  qpat_assum `entry.vs_alloca_next <= child.vs_alloca_next` mp_tac >>
  qpat_assum `entry.vs_alloca_next = u.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume calldata_owned_fixed_successor_endpoint[outside]:
  qpat_assum `!id. id < ready.cs_next_id \/ _ ==> _` mp_tac >>
  qpat_assum `!id. id < st.cs_next_id \/ _ ==> _` mp_tac >>
  qpat_assum `entry.vs_allocas = u.vs_allocas` mp_tac >>
  qpat_assum `st.cs_next_id <= ready.cs_next_id` mp_tac >>
  qpat_assum `st1.cs_next_id <= end_st.cs_next_id` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `id < ready.cs_next_id \/ st1.cs_next_id <= id` by decide_tac >>
  metis_tac[]
QED
Resume calldata_owned_fixed_successor_endpoint[footprint]:
  `abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::old) initial entry` by
    (qpat_assum `abi_decode_footprint_frame _ initial u` mp_tac >>
     qpat_assum `entry.vs_memory = u.vs_memory` mp_tac >>
     qpat_assum `entry.vs_call_ctx = u.vs_call_ctx` mp_tac >>
     qpat_assum `entry.vs_data_section = u.vs_data_section` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [abiDecoderFrameTheory.abi_decode_footprint_frame_def]) >>
  `abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::(old++new)) initial child` by
    (irule calldata_footprint_accumulate >>
     qexistsl_tac [`d+32+j*type_memory_size tv`,`type_memory_size tv`,`entry`] >>
     asm_rewrite_tac[] >> decide_tac) >>
  `abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::(old++new)) child
    (mstore p (n2w (SUC j)) child)` by
    (irule abi_encoder_store_footprint >> simp[MEM_APPEND]) >>
  `abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::(old++new)) initial
    (mstore p (n2w (SUC j)) child)` by
    (irule abiDecoderFrameTheory.abi_decode_footprint_frame_trans >>
     qexists_tac `child` >> asm_rewrite_tac[]) >>
  irule abi_encoder_footprint_memory >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexists_tac `mstore p (n2w (SUC j)) child` >>
  asm_rewrite_tac[] >>
  asm "vdef" (fn th => rewrite_tac[th]) >>
  simp[jump_to_def, mstore_def, update_var_def]
QED
Resume calldata_owned_fixed_successor_endpoint[scratch]:
  `!q k. MEM (q,k) old ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP child.vs_allocas id = SOME (q,k)` by
    (match_mp_tac (Q.INST [`s` |-> `u`] calldata_scratch_witness_transport) >>
     asm_rewrite_tac[] >>
     qpat_assum `!id q k. FLOOKUP entry.vs_allocas id = _ ==> _` mp_tac >>
     qpat_assum `entry.vs_allocas = u.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_assum `!q k. MEM (q,k) old ==> _` mp_tac >>
  qpat_assum `!q k. MEM (q,k) new ==> _` mp_tac >>
  qpat_assum `st.cs_next_id <= ready.cs_next_id` mp_tac >>
  qpat_assum `st1.cs_next_id <= end_st.cs_next_id` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp_tac bool_ss [MEM_APPEND] >>
  rpt strip_tac
  >- (qpat_x_assum `!q k. MEM (q,k) old ==> _` drule >> simp[]) >>
  qpat_x_assum `!q k. MEM (q,k) new ==> _` drule >> strip_tac >>
  qexists_tac `id` >> asm_rewrite_tac[] >> decide_tac
QED
Resume calldata_owned_fixed_successor_endpoint[source]:
  conj_tac
  >- (asm "vdef" (fn th => rewrite_tac[th]) >> simp[] >>
      irule fresh_vars_wrt_mstore >>
      irule abi_decoder_generated_update_fresh >> asm_rewrite_tac[]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
  qpat_assum `mem_bytes_at _ _ (abi_decode_source _ u) = bs` mp_tac >>
  qpat_assum `!op. op = src \/ _ ==> eval_operand op v = _` mp_tac >>
  qpat_assum `v.vs_call_ctx = child.vs_call_ctx` mp_tac >>
  qpat_assum `child.vs_call_ctx = entry.vs_call_ctx` mp_tac >>
  qpat_assum `entry.vs_call_ctx = u.vs_call_ctx` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [abi_decoder_ranges_def, abi_decode_source_def, eval_operand_def] >>
  metis_tac[]
QED
Resume calldata_owned_fixed_successor_endpoint[prefix]:
  rpt strip_tac >>
  `k < LENGTH vs` by decide_tac >>
  `val_wf tv (EL k vs)` by metis_tac[EVERY_EL] >>
  `k <= j` by decide_tac >>
  `SUC k * type_memory_size tv <= maxn * type_memory_size tv` by
    (irule LESS_EQ_TRANS >> qexists_tac `SUC j * type_memory_size tv` >>
     asm_rewrite_tac[] >> simp[LE_MULT_RCANCEL]) >>
  `k*type_memory_size tv + type_memory_size tv <= maxn*type_memory_size tv` by
    (qpat_assum `SUC k * _ <= _` mp_tac >> pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) child.vs_memory` by
    (Cases_on `k = j` >- asm_rewrite_tac[] >>
     `k < j` by decide_tac >>
     irule (cj 1 val_in_memory_mem_agree_proof) >>
     conj_tac >- asm_rewrite_tac[] >> qexists_tac `u.vs_memory` >>
     reverse conj_tac >- metis_tac[] >>
     drule (cj 1 mem_bytes_at_agree_window) >>
     disch_then (qspecl_then [`d+32+k*type_memory_size tv`,`type_memory_size tv`] mp_tac) >>
     impl_tac >- (
       `SUC k * type_memory_size tv <= j * type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
       qpat_assum `SUC k * _ <= _` mp_tac >>
       pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >> simp[]) >>
  irule (cj 1 val_in_memory_mem_agree_proof) >>
  conj_tac >- asm_rewrite_tac[] >> qexists_tac `child.vs_memory` >>
  asm_rewrite_tac[] >> sym_tac >>
  qpat_x_assum `!a len. _ ==> mem_bytes_at a len v.vs_memory = _` irule >> decide_tac
QED
Finalise calldata_owned_fixed_successor_endpoint

(* The recursive child is selected once; both transfers follow that witness. *)
Theorem calldata_owned_header_successor_endpoint:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s);
      H = \j s scratch.
        ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
        j <= LENGTH vs /\ LENGTH vs <= maxn /\
        eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
        eval_operand ip s = SOME (n2w p) /\ mload p s = n2w j /\
        abi_decode_load CALLDATALOAD srcword s = n2w (LENGTH vs) /\
        mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
        s.vs_call_ctx = initial.vs_call_ctx /\ s.vs_data_section = initial.vs_data_section /\
        FLOOKUP s.vs_allocas iid = SOME (p,32) /\
        FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
        alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
        Own st.cs_next_id end_st.cs_next_id s /\
        initial.vs_alloca_next <= s.vs_alloca_next /\
        (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
          FLOOKUP s.vs_allocas id = SOME (q,k)) /\
        (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
          FLOOKUP s.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
        (!op. abi_decoder_operand_live st.cs_next_var op ==>
          eval_operand op s = eval_operand op initial) /\
        abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial s /\
        MEM (p,32) scratch /\
        (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP s.vs_allocas id = SOME (q,k)) /\
        fresh_vars_wrt limit_st s /\
        abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
          d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap s /\
        mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
  in
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st0 = (ops,ready) /\ fn_has_code st0 ready fn /\
  st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= st1.cs_next_id /\
  st1.cs_next_id <= end_st.cs_next_id /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv
        (STRING #"%" (toString nvar)) ip hdr|> /\
  FST ops = Var biv /\ abi_decoder_operand_live ready.cs_next_var (FST ops) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  ((!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) \/
   (type_to_abi_dec_info sf ce ty = DecComplex T [] /\ ready = st1 /\
    EVERY (value_has_type tv) vs)) /\
  EVERY (val_wf tv) vs /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (iid < ready.cs_next_id \/ st1.cs_next_id <= iid) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\ next <= st0.cs_next_var /\
  next+4 <= limit_st.cs_next_var /\ ready.cs_next_var <= limit_st.cs_next_var /\
  nvar < limit_st.cs_next_var /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var (STRING #"%" (toString nvar)) /\ abi_decoder_operand_live next op) /\
  (!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op) /\
  (!head entry.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b reserve_cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
    alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    Own ready.cs_next_id st1.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= d+32+j*type_memory_size tv /\
    d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
    d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256) ==>
    ?child new.
      ~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
      child.vs_inst_idx = LENGTH st1.cs_current_insts /\
      val_wf tv (EL j vs) /\
      val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) child.vs_memory /\
      fresh_vars_wrt limit_st child /\
      child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
      alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
      Own ready.cs_next_id st1.cs_next_id child /\
      entry.vs_alloca_next <= child.vs_alloca_next /\
      (!id q k. FLOOKUP entry.vs_allocas id = SOME (q,k) ==>
        FLOOKUP child.vs_allocas id = SOME (q,k)) /\
      (!id. id < ready.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id) /\
      (!op. abi_decoder_operand_live ready.cs_next_var op ==>
        eval_operand op child = eval_operand op entry) /\
      abi_decode_footprint_frame
        ((d+32+j*type_memory_size tv,type_memory_size tv)::new) entry child /\
      (!q k. MEM (q,k) new ==> ?id. ready.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP child.vs_allocas id = SOME (q,k)) /\ Safe entry child /\ Pull entry child) /\
  H j u old /\
  (!k. k < j ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) u.vs_memory) ==>
  ?v new. H (SUC j) v (old++new) /\
    (!k. k < SUC j ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) v.vs_memory) /\ Safe u v /\ Pull u v
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Pull` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!head entry. _` (mk_asm "child") >>
  qpat_assum `H j u old` mp_tac >>
  qpat_assum `Abbrev (H = _)` (fn th => CONV_TAC
    (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `lookup_block hdr fn.fn_blocks = SOME _` mp_tac >>
  qpat_assum `u.vs_current_bb = hdr` (fn th => rewrite_tac [GSYM th]) >>
  disch_tac >>
  suspend "boundary"
QED
Resume calldata_owned_header_successor_endpoint[boundary]:
  `?entry child new.
    entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
    entry.vs_data_section = u.vs_data_section /\ entry.vs_allocas = u.vs_allocas /\
    entry.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op entry = eval_operand op u) /\
    eval_operand (FST ops) entry = SOME (n2w j) /\
    ~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
    child.vs_inst_idx = LENGTH st1.cs_current_insts /\
    val_wf tv (EL j vs) /\
    val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) child.vs_memory /\
    fresh_vars_wrt limit_st child /\
    child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
    alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
    Own ready.cs_next_id st1.cs_next_id child /\
    entry.vs_alloca_next <= child.vs_alloca_next /\
    (!id q k. FLOOKUP entry.vs_allocas id = SOME (q,k) ==>
      FLOOKUP child.vs_allocas id = SOME (q,k)) /\
    (!id. id < ready.cs_next_id \/ st1.cs_next_id <= id ==>
      FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id) /\
    (!op. abi_decoder_operand_live ready.cs_next_var op ==>
      eval_operand op child = eval_operand op entry) /\
    abi_decode_footprint_frame
      ((d+32+j*type_memory_size tv,type_memory_size tv)::new) entry child /\
    (!q k. MEM (q,k) new ==> ?id. ready.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP child.vs_allocas id = SOME (q,k)) /\
    Safe u entry /\ Pull u entry /\ Safe entry child /\ Pull entry child` by
    suspend "selection" >>
  suspend "covered_backedge"
QED
Resume calldata_owned_header_successor_endpoint[selection]:
  Cases_on `!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem`
  >- suspend "ordinary" >>
  suspend "empty"
QED
Resume calldata_owned_header_successor_endpoint[ordinary]:
  drule_all calldata_valid_header_child_endpoint >>
  disch_then (qspec_then `ctx` (qx_choose_then `head` (qx_choose_then `entry`
    (map_every assume_tac o CONJUNCTS)))) >>
  suspend "child_input"
QED
Resume calldata_owned_header_successor_endpoint[child_input]:
  `j+1 <= maxn` by decide_tac >>
  `j*type_memory_size tv+type_memory_size tv <= maxn*type_memory_size tv` by
    (`(j+1)*type_memory_size tv <= maxn*type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(j+1)*_ <= maxn*_` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  `alloca_inv entry /\ alloca_frontier_inv ctx fn site entry` by
    (mp_tac (Q.INST [`s` |-> `u`, `t` |-> `entry`]
       (SPEC_ALL calldata_alloca_invariants_fields)) >> asm_rewrite_tac[]) >>
  `Own ready.cs_next_id st1.cs_next_id entry` by
    (qpat_assum `Own st.cs_next_id end_st.cs_next_id u` mp_tac >>
     qpat_assum `Abbrev (Own = _)` (fn th =>
       pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >> BETA_TAC >> strip_tac >>
     asm_rewrite_tac[] >> match_mp_tac (Q.INST
       [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`]
       calldata_owned_interval_restrict) >> asm_rewrite_tac[]) >>
  `fresh_vars_wrt limit_st entry` by
    (qpat_assum `abi_decoder_valid_array_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_valid_array_entry_def, LET_THM]) >>
  asm_x "child" (qspecl_then [`head`,`entry`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  disch_then (qx_choose_then `child` (qx_choose_then `new`
    (map_every assume_tac o CONJUNCTS))) >>
  `eval_operand (FST ops) entry = SOME (n2w j)` by
    (qpat_assum `abi_decoder_valid_array_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decoder_valid_array_entry_def, LET_THM] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `Safe u entry /\ Pull u entry` by
    (qpat_assum `!fuel r. run_from fuel ctx fn entry = r /\ _ ==> _` mp_tac >>
     qpat_assum `(!fuel. mem_safe_run fuel ctx fn entry) ==> _` mp_tac >>
     qpat_assum `Abbrev (Safe = _)` mp_tac >>
     qpat_assum `Abbrev (Pull = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`entry`, `child`, `new`] >> asm_rewrite_tac[]
QED
Resume calldata_owned_header_successor_endpoint[empty]:
  `type_to_abi_dec_info sf ce ty = DecComplex T [] /\ ready = st1 /\
   EVERY (value_has_type tv) vs` by metis_tac[] >>
  drule_all calldata_valid_header_prepare_pullback >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `value_has_type tv (EL j vs)` by fs[EVERY_EL] >>
  drule_all calldata_empty_dynamic_child_value >> strip_tac >>
  `~dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` by
    simp[dec_info_needs_offset_def] >>
  `abi_decoder_operand_live st0.cs_next_var src /\
   abi_decoder_operand_live st0.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand src head = SOME (n2w sb) /\
   eval_operand dst head = SOME (n2w d)` by fs[abi_decoder_ranges_def] >>
  `FLOOKUP head.vs_allocas iid = SOME (p,32) /\ alloca_inv head` by
    (asm_rewrite_tac[] >> metis_tac[cj 1 calldata_alloca_invariants_fields]) >>
  `head.vs_current_bb = st0.cs_current_bb /\
   head.vs_inst_idx = LENGTH st0.cs_current_insts` by simp[] >>
  drule_all calldata_offset_free_array_setup_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `entry.vs_current_bb = ready.cs_current_bb` >>
  suspend "empty_fields"
QED
Resume calldata_owned_header_successor_endpoint[empty_fields]:
  asm_x "child" kall_tac >>
  `entry.vs_memory = u.vs_memory /\ entry.vs_allocas = u.vs_allocas /\
   entry.vs_alloca_next = u.vs_alloca_next /\
   entry.vs_call_ctx = u.vs_call_ctx /\ entry.vs_data_section = u.vs_data_section` by
    asm_rewrite_tac[] >>
  `alloca_inv entry /\ alloca_frontier_inv ctx fn site entry` by
    (mp_tac (Q.INST [`s` |-> `u`, `t` |-> `entry`]
       (SPEC_ALL calldata_alloca_invariants_fields)) >> asm_rewrite_tac[]) >>
  `!op. abi_decoder_operand_live next op ==>
    eval_operand op entry = eval_operand op u` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `Safe u entry /\ Pull u entry` by suspend "empty_transfers" >>
  `?child. child = entry` by simp[] >> rename1 `child = entry` >>
  `?new. new = ([]:(num#num) list)` by simp[] >> rename1 `new = []` >>
  `~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
   child.vs_inst_idx = LENGTH st1.cs_current_insts /\
   val_wf tv (EL j vs) /\
   val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) child.vs_memory /\
   fresh_vars_wrt limit_st child /\
   child.vs_call_ctx = entry.vs_call_ctx /\ child.vs_data_section = entry.vs_data_section /\
   alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
   Own ready.cs_next_id st1.cs_next_id child /\
   entry.vs_alloca_next <= child.vs_alloca_next /\
   (!id q k. FLOOKUP entry.vs_allocas id = SOME (q,k) ==>
     FLOOKUP child.vs_allocas id = SOME (q,k)) /\
   (!id. id < ready.cs_next_id \/ st1.cs_next_id <= id ==>
     FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id) /\
   (!op. abi_decoder_operand_live ready.cs_next_var op ==>
     eval_operand op child = eval_operand op entry) /\
   abi_decode_footprint_frame
     ((d+32+j*type_memory_size tv,type_memory_size tv)::new) entry child /\
   (!q k. MEM (q,k) new ==> ?id. ready.cs_next_id <= id /\ id < st1.cs_next_id /\
     FLOOKUP child.vs_allocas id = SOME (q,k)) /\ Safe entry child /\ Pull entry child` by
    (simp[Abbr `Own`, Abbr `Safe`, Abbr `Pull`,
      abi_decode_footprint_frame_refl] >>
     conj_tac >- (rpt gen_tac >> strip_tac >> fs[]) >>
     gen_tac >> strip_tac >> qexists_tac `fuel` >> simp[]) >>
  qpat_x_assum `child = entry` kall_tac >>
  qpat_x_assum `new = []` kall_tac >>
  qexistsl_tac [`entry`, `child`, `new`] >> asm_rewrite_tac[]
QED
Resume calldata_owned_header_successor_endpoint[empty_transfers]:
  simp_tac bool_ss [Abbr `Safe`, Abbr `Pull`] >> conj_tac
  >- (qpat_assum `!fuel r. run_from fuel ctx fn entry = r /\ _ ==> _` mp_tac >>
      qpat_assum `!fuel r. run_from fuel ctx fn head = r /\ _ ==> _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> ntac 2 strip_tac >> rpt strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn entry = r /\ _ ==> _`
        (qspecl_then [`fuel`, `run_from fuel ctx fn entry`] mp_tac) >>
      asm_rewrite_tac[] >> strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn head = r /\ _ ==> _` drule >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_assum `(!fuel. mem_safe_run fuel ctx fn entry) ==> _` mp_tac >>
  qpat_assum `(!fuel. mem_safe_run fuel ctx fn head) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume calldata_owned_header_successor_endpoint[covered_backedge]:
  asm_x "child" kall_tac >>
  rename1 `~child.vs_halted` >>
  `!op. abi_decoder_operand_live next op ==>
    eval_operand op child = eval_operand op u` by
    (qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op _ = eval_operand op u` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live ready.cs_next_var op ==> eval_operand op child = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live next op ==> abi_decoder_operand_live ready.cs_next_var op` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `eval_operand (Var biv) child = SOME (n2w j) /\
   eval_operand ip child = SOME (n2w p)` by
    (conj_tac
     >- (qpat_assum `FST ops = Var biv` mp_tac >>
         qpat_assum `eval_operand (FST ops) entry = _` mp_tac >>
         qpat_assum `abi_decoder_operand_live ready.cs_next_var (FST ops)` mp_tac >>
         qpat_assum `!op. abi_decoder_operand_live ready.cs_next_var op ==> eval_operand op child = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     qpat_assum `abi_decoder_operand_live next ip` mp_tac >>
     qpat_assum `eval_operand ip u = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op child = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `w2n (n2w p:bytes32) = p` by simp[w2n_n2w, LESS_MOD] >>
  `w2n (n2w p:bytes32)+32 <= child.vs_alloca_next` by
    (asm_rewrite_tac[] >> decide_tac) >>
  qabbrev_tac `v = jump_to hdr (mstore p (n2w (SUC j))
    (update_var (STRING #"%" (toString nvar)) (n2w (SUC j)) child))` >>
  qpat_x_assum `Abbrev (v = _)`
    (mk_asm "vdef" o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  suspend "edges"
QED
Resume calldata_owned_header_successor_endpoint[edges]:
  `lookup_block child.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv
        (STRING #"%" (toString nvar)) ip hdr|>` by asm_rewrite_tac[] >>
  `phi_prefix_length (abi_decode_header_insts hid ip src CALLDATALOAD
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3))) body_lbl exit_lbl) = 0` by
    simp[abi_decode_header_insts_def, phi_prefix_length_def, venomInstTheory.mk_inst_def] >>
  `ip <> Var (STRING #"%" (toString nvar))` by
    (qpat_assum `!op. op = src \/ _ ==> _` (qspec_then `ip` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `Safe child v` by suspend "back_safe" >>
  `Pull child v` by suspend "back_pull" >>
  suspend "assemble"
QED
Resume calldata_owned_header_successor_endpoint[back_safe]:
  qpat_assum `Abbrev (Safe = _)` (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  qpat_assum `lookup_block child.vs_current_bb fn.fn_blocks = SOME _`
    (mp_then (Pos hd) mp_tac calldata_backedge_safe_transfer) >>
  simp_tac (srw_ss()) [] >>
  disch_then (resolve_then (Pos hd) mp_tac EQ_REFL) >>
  disch_then (drule_at (Pat `eval_operand (Var biv) child = _`)) >>
  disch_then (drule_at (Pat `eval_operand ip child = _`)) >>
  disch_then (drule_at (Pat `lookup_block hdr fn.fn_blocks = _`)) >>
  disch_then (qspecl_then [`LENGTH vs`,`fuel`,`ctx`] mp_tac) >>
  asm "vdef" (fn th => asm_simp_tac (srw_ss()) [GSYM th]) >>
  disch_then irule
QED
Resume calldata_owned_header_successor_endpoint[back_pull]:
  qpat_assum `Abbrev (Pull = _)` (fn th =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> disch_tac >> gen_tac >>
  qpat_assum `lookup_block child.vs_current_bb fn.fn_blocks = SOME _`
    (mp_then (Pos hd) mp_tac calldata_backedge_all_fuel_pullback) >>
  simp_tac (srw_ss()) [] >>
  disch_then (resolve_then (Pos hd) mp_tac EQ_REFL) >>
  disch_then (drule_at (Pat `eval_operand (Var biv) child = _`)) >>
  disch_then (drule_at (Pat `eval_operand ip child = _`)) >>
  disch_then (drule_at (Pat `lookup_block hdr fn.fn_blocks = _`)) >>
  disch_then (qspecl_then [`LENGTH vs`,`fuel`,`ctx`] mp_tac) >>
  asm "vdef" (fn th => asm_simp_tac (srw_ss()) [GSYM th])
QED
Resume calldata_owned_header_successor_endpoint[assemble]:
  mp_tac calldata_owned_fixed_successor_endpoint >>
  qpat_assum `Abbrev (Own = _)` (fn th =>
    pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  CONV_TAC (LAND_CONV (REWR_CONV LET_THM THENC BETA_CONV)) >>
  qpat_assum `Abbrev (Safe = _)` (fn th =>
    pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  CONV_TAC (LAND_CONV (REWR_CONV LET_THM THENC BETA_CONV)) >>
  qpat_assum `Abbrev (Pull = _)` (fn th =>
    pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  CONV_TAC (LAND_CONV (REWR_CONV LET_THM THENC BETA_CONV)) >>
  qpat_assum `Abbrev (H = _)` (fn th =>
    pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  CONV_TAC (LAND_CONV (REWR_CONV LET_THM THENC BETA_CONV)) >>
  (impl_tac >- (asm "vdef" (fn th => asm_rewrite_tac [th]))) >>
  strip_tac >> qexistsl_tac [`v`,`new`] >> asm_rewrite_tac[]
QED
Finalise calldata_owned_header_successor_endpoint
