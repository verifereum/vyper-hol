(* Reach a physical recursive child after either actual array-address prefix. *)
Theory abiScratchDecoderArrayEntry
Ancestors
  abiScratchDecoderContract abiScratchDecoderArraySetup abiScratchDecoderArrayChild
  abiScratchDecoderAddress abiDecoderArraySetupInputs abiDecoderArrayBody
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderLoop abiDecodeRanges abiValidMemberWindows abiValidMembers
  abiEncoder fragExec compileEnv valueEncoding vyperABI vyperValue contractABI
  venomState venomExecSemantics words list arithmetic

Theorem abi_scratch_decoder_array_setup_from_state:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_budget first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st ready (\s. s = initial)
    (abi_scratch_decoder_array_setup_post ce env ty bs j ready ops sb d
      st.cs_next_var limit_st initial) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_scratch_decoder_array_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_array_setup_reach:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_budget first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st ready func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared.
    abi_scratch_decoder_input ce env sf ty tv
      (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs)))
      (EL j vs) ready (FST (SND ops)) (SND (SND ops)) opc hi
      (sb + (32 + abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
        (j * abi_member_head_size (vyper_to_abi_type env ty))))
      (d + 32 + j * type_memory_bytes ce ty) first last b cap prepared /\
    eval_operand (FST ops) prepared = SOME (n2w j) /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_array_setup_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  qhdtm_x_assum `abi_scratch_decoder_array_setup_post`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_array_setup_post_def]) >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `new_next` |-> `ready.cs_next_var`,
    `len` |-> `LENGTH (bs:word8 list)`,
    `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`, `hi_op` |-> `hi:operand`]
    abi_scratch_decoder_address_observations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] (Q.INST [`st` |-> `ready`,
    `s` |-> `prepared:venom_state`, `childsrc` |-> `FST (SND (ops:operand # operand # operand))`,
    `childdst` |-> `SND (SND (ops:operand # operand # operand))`]
    abi_scratch_decoder_array_child_input)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `~prepared.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `prepared` >> RULE_ASSUM_TAC (SIMP_RULE arith_ss []) >> asm_simp_tac arith_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_ARRAY_ENTRY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical array child entry not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderArrayEntry");

