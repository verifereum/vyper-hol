(* A source-valid static child and both safety transfers at one endpoint. *)
Theory calldataStaticSetupEndpoint
Ancestors
  successfulSequenceEndpoint calldataStaticChildSetup calldataDynOwned calldataDynStep
  abiDecoderArraySetupInputs instIdxIndep
  abiDecoderValidArrayEntry abiDecoderContract abiDecoderCoherence abiDecoderDynamic
  abiDecoderOffset abiDecoderReentry abiDecoderTypedContract abiValidMember
  safeSequence fragExecMem venomMemDefs compileEnv emitHelperProps exprLoweringProps
  venomState venomExecSemantics words list arithmetic

Theorem calldata_static_valid_owned_array_child_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
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
  drule_all calldata_static_valid_array_setup_sequence >> strip_tac >>
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
  simp[eval_op_inst_idx]
QED
