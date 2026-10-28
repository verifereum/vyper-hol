(* TOP-LEVEL: actual flat-field compilation advances instruction identities.
   Its allocation-preserving execution therefore retains the fresh boundary
   needed by a following allocated array field. *)
Theory abiFlatIdCode
Ancestors
  abiFlatFieldsDefs abiFieldsStructure abiComplexStructure abiStaticChildCode abiComplexCode
  abiChildCode abiBytestringCode abiEncoder abiAllocationFresh abiAllocatorState
  compileEnv emitHelper venomState list words arithmetic

Theorem compile_abi_flat_static_ids:
  !dst src info mem_size payload cs op cs'.
    abi_flat_valid (AbiFlatStatic info mem_size payload) /\
    compile_abi_encode_to_buf dst src info cs = (op,cs') ==> cs.cs_next_id <= cs'.cs_next_id
Proof
  rpt gen_tac >> strip_tac >> Cases_on `info` >>
  gvs[abi_flat_valid_def, Once compile_abi_encode_child_def, compile_abi_encode_static_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem compile_abi_flat_static_child_ids:
  !dst src info mem_size payload head_offset dyn_ptr cs op cs'.
    abi_flat_valid (AbiFlatStatic info mem_size payload) /\
    compile_abi_encode_child dst src info F head_offset dyn_ptr cs = (op,cs') ==>
    cs.cs_next_id <= cs'.cs_next_id
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _` (ASSUME_TAC o REWRITE_RULE [compile_abi_child_static_cuts]) >>
  drule_all compile_abi_flat_static_ids >> simp[abi_complex_field_cut_def] >> decide_tac
QED

Theorem compile_abi_child_bytes_ids:
  !dst src cap head_offset dyn_ptr cs op cs'.
    compile_abi_encode_child dst src (AbiBytestring cap) T head_offset dyn_ptr cs = (op,cs') ==>
    cs'.cs_next_id = cs.cs_next_id + 16
Proof
  rpt gen_tac >>
  simp_tac (srw_ss()) [compile_abi_child_dynamic_split, compile_abi_child_prefix_result, compile_abi_child_suffix_result] >>
  rpt strip_tac >> drule compile_abi_bytestring_code >> strip_tac >>
  gvs[abi_child_prefix_cut_def, abi_child_suffix_cut_def]
QED

Theorem compile_abi_flat_singleton_ids:
  !dst src row source_offset head_offset dyn_ptr cs cs'.
    abi_flat_valid row /\ compile_abi_encode_complex_elems dst src [abi_flat_entry row]
      source_offset head_offset dyn_ptr cs = (Lit 0w,cs') ==> cs.cs_next_id <= cs'.cs_next_id
Proof
  rpt gen_tac >> Cases_on `row` >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [_] _ _ _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [abi_flat_entry_def]) >>
  simp_tac (srw_ss()) [compile_abi_fields_cons_cuts, abi_complex_fields_nil] >> strip_tac >>
  FIRST [drule_all compile_abi_flat_static_child_ids >> simp[abi_complex_field_cut_def] >> decide_tac,
    drule_all compile_abi_child_bytes_ids >> simp[abi_complex_field_cut_def] >> decide_tac]
QED

Theorem abi_flat_field_allocator_fresh:
  !dst src row source_offset head_offset dyn_ptr cs cs' before after.
    abi_flat_valid row /\ compile_abi_encode_complex_elems dst src [abi_flat_entry row]
      source_offset head_offset dyn_ptr cs = (Lit 0w,cs') /\
    abi_allocation_fresh cs.cs_next_id before /\ abi_allocator_state after = abi_allocator_state before ==>
    abi_allocation_fresh cs'.cs_next_id after
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_abi_flat_singleton_ids >> DISCH_TAC >>
  `abi_allocation_fresh cs'.cs_next_id before` by
    (mp_tac (Q.SPECL [`cs.cs_next_id`, `cs'.cs_next_id`, `before`] abi_allocation_fresh_mono) >> simp[]) >>
  mp_tac (Q.SPECL [`before`, `after`, `cs'.cs_next_id`] abi_allocation_fresh_state) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed flat compiler allocation-identity bounds: " ^ name)
  end) (DB.thms "abiFlatIdCode")
