(* Arbitrary-byte traversal through the actual compiled dynamic loop. *)
Theory abiMalformedCompiledLoop
Ancestors
  abiMalformedConstructorInduction abiDecoderRecursiveLoopEntry
  abiDecoderRecursiveLoopLayout abiDecoderArraySetupCode
  abiMalformedRecursiveInterface abiMalformedConditionalTraversal
  abiDecoderLoopEmit abiDecoderLoopCode abiDecoderCounters
  abiDecoderExecution venomExecSemantics abiDecoderContract abiDecoderPhi fragExec compileEnv venomInst words list arithmetic pred_set

Theorem abi_malformed_compiled_loop:
  compile_abi_decode_dyn_loop dst src MLOAD base_op hi di abi_sz mem_sz ip cnt start = ((),en) /\
  fn_has_code start en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry ctx func cenv cx es start sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME (n2w slot) /\ mload slot s = 0w /\
  slot < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\
  inst.inst_id IN sites /\ inst.inst_id <> live /\ inst.inst_id <> dstid /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ ~s.vs_halted /\
  n = abi_head_word (DROP p xs) /\ p+32 <= L /\ p+32+n*abi_sz <= L /\
  abi_sz = (if is_dynamic (vyper_to_abi_type env ty) then 32
            else static_length (vyper_to_abi_type env ty)) /\
  dec_info_needs_offset di = is_dynamic (vyper_to_abi_type env ty) /\
  (case di of DecPrimWord clamp =>
    ~is_dynamic (vyper_to_abi_type env ty) /\ abi_sz = 32 | _ => T) /\
  abi_sz < dimword (:256) /\
  (!j. j<n ==> d+32+j*mem_sz+childsz <= d+outsz) /\
  abi_decoder_operand_live start.cs_next_var ip /\
  abi_malformed_scratch_sites start en func SUBSET sites /\
  (!childsrc childdst child child_end.
    compile_abi_decode_to_buf childdst childsrc MLOAD base_op hi di child = ((),child_end) /\
    fn_has_code child child_end func ==>
    abi_malformed_constructor env ty di ctx func cenv cx es child child_end
      base_op hi childsrc childdst childsz) ==>
  frag_outcome ctx func s en
    (\u. (?avs. abi_reflected_prefix env ty (DROP (p+32) xs) n avs) /\
      abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s u /\
      fresh_vars_wrt ceiling u)
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule_all abi_decoder_loop_phase_entry >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `abi_malformed_constructor env ty di ctx func cenv cx es middle st1
    base_op hi (FST (SND ops)) (SND (SND ops)) childsz` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `abi_sz = _` SUBST_ALL_TAC >>
  irule abi_malformed_conditional_traversal >> simp[] >>
  goal_assum (drule_at (Pat `abi_malformed_entry ctx func cenv cx es start sites dstid live base_op hi src dst B L xs p d outsz s`)) >>
  simp[] >>
  goal_assum (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >>
  qexistsl_tac [
    `<|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
      abi_decode_backedge_insts st1.cs_next_id (STRING #"%" (toString st0.cs_next_var))
        (STRING #"%" (toString st1.cs_next_var)) ip (FST labels)|>`,
    `st1.cs_next_id`, `st1`, `abi_malformed_scratch_sites middle st1 func`,
    `childsz`, `start.cs_next_id`,
    `start with <|cs_current_bb := FST labels; cs_current_insts := []|>`,
    `start.cs_next_id+1`, `inst`, `st1.cs_next_var`, `q`, `slot`] >>
  simp[] >> conj_tac
  >- (drule abi_malformed_constructor_traversal_child >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!j. j < n ==> _` (qspec_then `j` mp_tac) >> fs[]) >>
  conj_tac >- (qpat_x_assum `n = _` SUBST_ALL_TAC >> fs[]) >>
  conj_tac
  >- (Cases_on `base_op = Lit 0w` >>
      simp[abi_decode_position_header_insts_def, abi_decode_header_insts_def,
           phi_prefix_length_def, mk_inst_def]) >>
  conj_tac
  >- (irule SUBSET_TRANS >> qexists_tac `abi_malformed_scratch_sites start en func` >>
      simp[] >> irule abi_malformed_scratch_sites_nested >> simp[]) >>
  fs[]
QED
