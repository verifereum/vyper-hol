(* Actual source-valid setup endpoints for owned array iteration. *)
Theory calldataOwnedSuccessorEndpoint
Ancestors
  successfulSequenceEndpoint calldataValidOwnedChild calldataValidOwnedStep
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
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
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
      (Lit 0w) sb d b cap st.cs_next_var limit_st initial child /\
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
      (Lit 0w) sb d b cap st.cs_next_var limit_st initial child /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op child = eval_operand op initial)`] (SPEC_ALL successful_sequence_endpoint)) >>
  simp[eval_op_inst_idx] >> strip_tac >>
  qexists_tac `prepared with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  fs[eval_op_inst_idx, abi_decoder_valid_array_entry_def, abi_decoder_address_frame_def]
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
    d outsz b cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    ~head.vs_halted /\ head.vs_current_bb = body_lbl /\ head.vs_inst_idx = 0 /\
    fresh_vars_wrt limit_st head /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
      d outsz b cap head /\
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
  is_dynamic (vyper_to_abi_type env ty) /\
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
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head entry.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b cap st0.cs_next_var limit_st head entry /\
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
  drule_all calldata_dynamic_valid_owned_array_child_endpoint >>
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
