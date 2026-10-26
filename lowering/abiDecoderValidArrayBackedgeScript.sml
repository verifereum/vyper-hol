(* The index store is separate from the array output and the unread source. *)
Theory abiDecoderValidArrayBackedge
Ancestors
  abiDecoderValidArrayMemory abiDecoderArrayBackedge abiDecoderArrayPrefix abiDecoderFrameCompose abiDecoderFrame
  abiDecoderContract abiDecoderReentry abiDecoderReentryAllocation abiDecoderExecution
  valueEncodingProps valueEncoding venomMemProofs venomState venomInst
  exprLoweringProps compileEnv vyperTyping words arithmetic list rich_list
Libs
  Omega

Theorem abi_decoder_valid_array_index_write:
  abi_decoder_valid_array_memory opc bs tv vs sb d j s /\ all_have_type tv vs /\
  abi_decode_source_opcode opc /\
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  (opc = MLOAD ==> sb + LENGTH bs <= slot \/
                     slot + 32 <= sb) ==>
  abi_decoder_valid_array_memory opc bs tv vs sb d j (mstore slot w s)
Proof
  simp_tac bool_ss [abi_decoder_valid_array_memory_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (TAKE j vs) * type_memory_size tv <= LENGTH vs * type_memory_size tv`
    by simp[LE_MULT_RCANCEL, LENGTH_TAKE, MIN_LE] >>
  `all_have_type tv (TAKE j vs)` by
    (fs[all_have_type_EVERY] >> irule EVERY_TAKE >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`slot`, `32`, `d`,
    `32 + LENGTH (vs:vyperValue$value list) * type_memory_size tv`,
    `LENGTH (TAKE j (vs:vyperValue$value list)) * type_memory_size tv`]
    abi_decoder_array_disjoint_windows) >>
  impl_tac >- asm_simp_tac bool_ss [LE_ADD_LCANCEL, ADD_ASSOC] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `mem_word_at d (mstore slot w s).vs_memory = mem_word_at d s.vs_memory` by
    (irule mstore_mem_word_at_disjoint >> first_assum ACCEPT_TAC) >>
  `abi_decode_frame slot 32 s (mstore slot w s)` by
    (simp[abi_decode_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
     simp[mstore_def, write_memory_with_expansion_def]) >>
  `elems_in_memory (TAKE j vs) (d + 32) tv (mstore slot w s).vs_memory` by
    (drule_all abi_decode_frame_preserves_elements >> simp[]) >>
  `mem_bytes_at sb (LENGTH bs)
     (abi_decode_source opc (mstore slot w s)) =
   mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s)` by
    (irule abi_decode_frame_source_window >> simp[Excl "enc_def"] >>
     qexistsl_tac [`slot`, `32`] >> simp[Excl "enc_def"]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_array_backedge:
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME (n2w slot) /\
  slot < dimword (:256) /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) s /\ all_have_type tv vs /\
  abi_decode_source_opcode opc /\
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  (opc = MLOAD ==> sb + LENGTH bs <= slot \/
                     slot + 32 <= sb) /\
  abi_decoder_operand_live first ip /\ first <= next /\
  next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?result_st. exec_block fuel ctx bb s = OK result_st /\
    abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) result_st /\
    mload slot result_st = n2w (SUC j) /\
    result_st.vs_current_bb = hdr /\ result_st.vs_inst_idx = 0 /\ ~result_st.vs_halted /\
    fresh_vars_wrt limit_st result_st /\
    (!op w. abi_decoder_operand_live first op /\ eval_operand op s = SOME w ==>
      eval_operand op result_st = SOME w) /\
    result_st.vs_allocas = s.vs_allocas /\ result_st.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] s result_st /\
    result_st = jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString next)) (n2w (SUC j)) s))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `ip <> Var (STRING #"%" (toString next))` by
    (drule_all abi_decoder_live_excludes_output >> simp[]) >>
  qabbrev_tac `result_st = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString next)) (n2w (SUC j)) s))` >>
  `exec_block fuel ctx bb s = OK result_st` by
    (drule_all abi_decode_backedge_control >>
     simp[Abbr`result_st`, w2n_n2w, Excl "enc_def"]) >>
  `abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) result_st` by
    (simp_tac bool_ss [Abbr`result_st`, abi_decoder_valid_array_memory_jump] >>
     irule abi_decoder_valid_array_index_write >>
     asm_simp_tac bool_ss [abi_decoder_valid_array_memory_update]) >>
  `result_st.vs_vars = s.vs_vars |+ (STRING #"%" (toString next),n2w (SUC j)) /\
   result_st.vs_labels = s.vs_labels` by
    simp[Abbr`result_st`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `!op w. abi_decoder_operand_live first op /\ eval_operand op s = SOME w ==>
    eval_operand op result_st = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live next op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >> metis_tac[]) >>
  `abi_decode_footprint_frame [(slot,32)] s result_st /\
   mload slot result_st = n2w (SUC j)` by
    (mp_tac (Q.INST [`p` |-> `(n2w slot : bytes32)`, `fp` |-> `[(slot:num,32:num)]`,
       `nv` |-> `STRING #"%" (toString (next:num))`, `w` |-> `(n2w (SUC j):bytes32)`]
       (INST_TYPE [alpha |-> ``:256``] abi_decode_backedge_observations)) >>
     simp[Abbr`result_st`, w2n_n2w]) >>
  qexists_tac `result_st` >> asm_simp_tac bool_ss [] >>
  simp[Abbr`result_st`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_ARRAY_BACKEDGE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid array backedge not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidArrayBackedge");
