(* Compose actual generic initialization with finite recursive array execution. *)
Theory abiDecoderRecursiveArrayExecute
Ancestors
  abiDecoderRecursiveArrayCode abiDecoderRecursiveArrayInit abiDecoderRecursiveArrayFacts
  abiDecoderRecursiveLoopEntry abiDecoderRecursiveInitEffect abiDecoderRecursiveLoopContext
  abiDecoderEffect abiDecoderCoherence abiDecoderTypedContract abiDecoderAllocation
  abiDecoderContract abiDecoderCorrect abiDecoderLoop abiDecoderReentry
  fragExec compileEnv valueEncoding vyperABI vyperValue venomState words list arithmetic

Theorem abi_decoder_recursive_array_execute:
  compile_abi_decode_to_buf dst src opc hi_op
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn)
    st = ((),final) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  abi_decoder_correct ce env sf ty tv /\ fn_has_code st final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi_op sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_array_pre_observations >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  `loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all (Q.INST [`owner_hi` |-> `final.cs_next_id`] abi_decoder_recursive_array_initialize) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `fresh_vars_wrt limit_st prepared /\ abi_decoder_budget first last b cap prepared`
    by fs[abi_decoder_effect_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`,
    `ip` |-> `FST (setup:operand # operand)`,
    `cnt` |-> `SND (setup:operand # operand)`,
    `next` |-> `loop_st.cs_next_var`, `start` |-> `loop_st:compile_state`,
    `initial` |-> `prepared:venom_state`, `site` |-> `loop_st.cs_next_id-2`]
    abi_decoder_recursive_loop_from_state) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  `abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared t` by
    (mp_tac (Q.INST [`s` |-> `prepared:venom_state`, `t` |-> `t:venom_state`,
      `lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`, `next` |-> `st.cs_next_var`,
      `child_next` |-> `loop_st.cs_next_var`,
      `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] abi_decoder_effect_lower_vars) >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t` by
    (drule_all abi_decoder_effect_trans >> simp[]) >>
  `abi_decode_sim ctx func initial t` by metis_tac[abi_decode_sim_trans] >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_RECURSIVE_ARRAY_EXECUTE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI recursive array execution not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderRecursiveArrayExecute");
