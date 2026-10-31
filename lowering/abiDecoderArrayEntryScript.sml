(* Reach the recursive child's actual program point after emitted array setup. *)
Theory abiDecoderArrayEntry
Ancestors
  abiDecoderArraySetupInputs abiDecoderArraySlice abiDecoderPointed
  abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry
  abiDecoderDynamicLoopSetup abiDecoderLoop abiDecoderContract
  fragExec instIdxIndep compileEnv valueEncoding vyperABI vyperValue
  venomState venomExecSemantics emitHelperProps words list

Theorem abi_decoder_prune_inst_idx:
  abi_decoder_prune_vars next (s with vs_inst_idx := ix) =
    (abi_decoder_prune_vars next s) with vs_inst_idx := ix
Proof
  simp[abi_decoder_prune_vars_def, venom_state_component_equality]
QED

Theorem abi_decoder_pruned_pre_inst_idx:
  abi_decoder_recursive_pre ce env sf ty tv di av v st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars next (s with vs_inst_idx := ix)) <=>
  abi_decoder_recursive_pre ce env sf ty tv di av v st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars next s)
Proof
  simp_tac bool_ss [abi_decoder_prune_inst_idx, abi_decoder_recursive_pre_inst_idx]
QED

Definition abi_decoder_array_entry_def:
  abi_decoder_array_entry ce env sf ty tv av v child_st last ops opc hi
      child_sb child_d b cap next limit_st initial i t <=>
    abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      child_st last (FST (SND ops)) (SND (SND ops)) opc hi child_sb child_d b cap
      (abi_decoder_prune_vars child_st.cs_next_var t) /\
    eval_operand (FST ops) t = SOME (n2w i) /\ fresh_vars_wrt limit_st t /\
    abi_decoder_address_frame next initial t
End

Theorem abi_decoder_array_entry_inst_idx[simp]:
  abi_decoder_array_entry ce env sf ty tv av v child_st last ops opc hi
    child_sb child_d b cap next limit_st initial i (t with vs_inst_idx := ix) <=>
  abi_decoder_array_entry ce env sf ty tv av v child_st last ops opc hi
    child_sb child_d b cap next limit_st initial i t
Proof
  simp[abi_decoder_array_entry_def, abi_decoder_pruned_pre_inst_idx,
    fresh_vars_wrt_def, abi_decoder_address_frame_def, eval_op_inst_idx, mload_def]
QED

Theorem abi_decoder_array_setup_from_state:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc initial) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_reservation middle.cs_next_id last b cap initial /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st middle (\s. s = initial)
    (abi_decoder_array_entry ce env sf ty tv av v middle last ops opc hi
      (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
      (d + 32 + LENGTH pre * type_memory_bytes ce ty) b cap st.cs_next_var limit_st
      initial (LENGTH pre)) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_dynarray_child_inputs >> strip_tac >>
  qexists_tac `t` >> gvs[abi_decoder_array_entry_def, Excl "enc_def"]
QED

Theorem abi_decoder_array_setup_reach:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  fn_has_code st middle func /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc initial) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_reservation middle.cs_next_id last b cap initial /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_decoder_array_entry ce env sf ty tv av v middle last ops opc hi
      (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
      (d + 32 + LENGTH pre * type_memory_bytes ce ty) b cap st.cs_next_var limit_st
      initial (LENGTH pre) prepared /\
    prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_array_setup_from_state >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `~prepared.vs_halted` by fs[abi_decoder_array_entry_def, abi_decoder_address_frame_def] >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED
