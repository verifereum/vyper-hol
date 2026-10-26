(* The actual backedge advances the index and preserves the encoded prefix and tail cursor. *)
Theory abiEncoderArrayBackedgeMemory
Ancestors
  abiEncoderArrayBackedge abiEncoderArrayIndexUpdate abiEncoderArrayMemory abiEncoderArrayCursor
  abiEncoderMembersDefs abiEncoderChildInputs abiDecoderEffect abiDecoderContract abiDecoderLoop
  abiDecoderReentry compileEnv valueEncoding contractABI venomState finite_map words list arithmetic

Theorem abi_encoder_array_backedge_memory:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\
  abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap d output_size b cap k initial /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo owner_st off initial /\
  (active ==> site < cursor_site) /\ owner_st.cs_next_id <= last /\
  owner_st.cs_next_var <= next /\ next < limit_st.cs_next_var /\
  j < LENGTH avs /\ fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial ==>
  ?actual. abi_encoder_array_memory ei asz msz active ty avs owner_st src dst sb source_cap
      d output_size b cap k actual /\
    abi_encoder_cursor T ip site slot first lo owner_st (SUC j) actual /\
    abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo owner_st off actual /\
    abi_decoder_effect first last site (site+1) owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_memory_typed >> strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `s` |-> `initial:venom_state`,
    `cursor_op` |-> `ip:operand`, `off` |-> `j:num`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_operand_live next ip` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `n` |-> `LENGTH (avs:abi_value list)`]
    abi_encoder_array_backedge_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`lo` |-> `site:num`, `hi` |-> `site+1`, `sz` |-> `output_size:num`]
    abi_encoder_single_scratch_effect) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> disch_tac >>
  `abi_decoder_effect first last site (site+1) owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >> qexistsl_tac [`d`, `site+1`, `site`, `next`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `new_j` |-> `SUC j`] abi_encoder_array_index_update) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_BACKEDGE_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array backedge memory not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayBackedgeMemory");
