(* An index-slot write preserves the complete source/output prefix and optional tail cursor. *)
Theory abiEncoderArrayIndexUpdate
Ancestors
  abiEncoderArrayMemory abiEncoderArrayCursor abiEncoderMembersDefs abiEncoderChildInputs
  abiDecoderEffect abiDecoderFrame abiDecoderContract abiDecoderReentry compileEnv
  valueEncoding venomState finite_map words list arithmetic

Theorem abi_encoder_array_index_update:
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap k initial /\
  abi_encoder_cursor T ip site slot first lo st j initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo st off initial /\
  (active ==> site < cursor_site) /\ st.cs_next_id <= last /\
  abi_decoder_budget first last b cap initial /\
  abi_decoder_effect first last site (site+1) st.cs_next_var limit_st d output_size b cap initial actual /\
  abi_decode_footprint_frame [(slot,32)] initial actual /\
  actual.vs_allocas = initial.vs_allocas /\ mload slot actual = n2w new_j ==>
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap k actual /\
  abi_encoder_cursor T ip site slot first lo st new_j actual /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo st off actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`cursor_op` |-> `ip:operand`, `off` |-> `j:num`, `s` |-> `initial:venom_state`]
    abi_encoder_cursor_bounds) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  `abi_footprint_disjoint d output_size [(slot,32)]` by
    (full_simp_tac (srw_ss()) [abi_footprint_disjoint_def, Excl "enc_def"] >> decide_tac) >>
  mp_tac (Q.INST [`dyn` |-> `active:bool`, `j` |-> `k:num`, `lo` |-> `site:num`, `hi` |-> `site+1`,
    `fp` |-> `[(slot:num,32:num)]`] abi_encoder_array_memory_scratch) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`cursor_op` |-> `ip:operand`, `active` |-> `T`, `off` |-> `j:num`,
    `next_off` |-> `new_j:num`, `next` |-> `st.cs_next_var`, `owned_lo` |-> `site:num`,
    `sz` |-> `output_size:num`, `owned_hi` |-> `site+1`] abi_encoder_cursor_effect_registered) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  `abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo st off actual` by
    (Cases_on `active`
     >- (mp_tac (Q.INST [`active` |-> `T`, `cursor_op` |-> `dyn_ptr:operand`,
           `site` |-> `cursor_site:num`, `slot` |-> `cursor_slot:num`, `next` |-> `st.cs_next_var`,
           `sz` |-> `output_size:num`, `owned_lo` |-> `site:num`, `owned_hi` |-> `site+1`] abi_encoder_cursor_effect_protected) >>
         impl_tac >- (full_simp_tac bool_ss [abi_encoder_cursor_def] >> decide_tac) >>
         asm_simp_tac bool_ss []) >> simp[abi_encoder_cursor_def]) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_INDEX_UPDATE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array index update not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayIndexUpdate");
