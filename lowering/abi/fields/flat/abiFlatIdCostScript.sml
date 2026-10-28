(* TOP-LEVEL: exact instruction-identity cost of each native flat field.
   These compiler facts locate the scratch requests of later mixed fields. *)
Theory abiFlatIdCost
Ancestors
  abiFlatIdCode abiFlatFieldsDefs abiFieldsStructure abiComplexStructure abiStaticChildCode abiComplexCode
  abiEncoder compileEnv emitHelper venomState list words arithmetic

Definition abi_flat_id_cost_def:
  abi_flat_id_cost (AbiFlatStatic info mem_size payload) =
    (if info = AbiPrimWord then 4 else if info = AbiComplex [] then 2 else 3) /\
  abi_flat_id_cost (AbiFlatBytes cap mem_size bs) = 17
End

Theorem compile_abi_flat_static_singleton_cost:
  !dst src info mem_size payload source_offset head_offset dyn_ptr cs cs'.
    abi_flat_valid (AbiFlatStatic info mem_size payload) /\
    compile_abi_encode_complex_elems dst src [abi_flat_entry (AbiFlatStatic info mem_size payload)]
      source_offset head_offset dyn_ptr cs = (Lit 0w,cs') ==>
    cs'.cs_next_id = cs.cs_next_id + (if info = AbiPrimWord then 4 else if info = AbiComplex [] then 2 else 3)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [_] _ _ _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [abi_flat_entry_def]) >>
  simp_tac (srw_ss()) [compile_abi_fields_cons_cuts, abi_complex_fields_nil] >> strip_tac >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _` (mp_tac o REWRITE_RULE [compile_abi_child_static_cuts]) >>
  strip_tac >> Cases_on `info` >>
  gvs[abi_flat_valid_def, Once compile_abi_encode_child_def, compile_abi_encode_static_def,
    abi_complex_field_cut_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem compile_abi_flat_bytes_singleton_cost:
  !dst src cap mem_size bs source_offset head_offset dyn_ptr cs cs'.
    abi_flat_valid (AbiFlatBytes cap mem_size bs) /\
    compile_abi_encode_complex_elems dst src [abi_flat_entry (AbiFlatBytes cap mem_size bs)]
      source_offset head_offset dyn_ptr cs = (Lit 0w,cs') ==> cs'.cs_next_id = cs.cs_next_id + 17
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [_] _ _ _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [abi_flat_entry_def]) >>
  simp_tac (srw_ss()) [compile_abi_fields_cons_cuts, abi_complex_fields_nil] >> strip_tac >>
  drule_all compile_abi_child_bytes_ids >> simp[abi_complex_field_cut_def]
QED

Theorem compile_abi_flat_singleton_cost:
  !dst src row source_offset head_offset dyn_ptr cs cs'.
    abi_flat_valid row /\ compile_abi_encode_complex_elems dst src [abi_flat_entry row]
      source_offset head_offset dyn_ptr cs = (Lit 0w,cs') ==> cs'.cs_next_id = cs.cs_next_id + abi_flat_id_cost row
Proof
  rpt gen_tac >> Cases_on `row` >> simp_tac bool_ss [abi_flat_id_cost_def] >>
  FIRST [MATCH_ACCEPT_TAC compile_abi_flat_static_singleton_cost, MATCH_ACCEPT_TAC compile_abi_flat_bytes_singleton_cost]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed exact native flat field compiler cost: " ^ name)
  end) (DB.thms "abiFlatIdCost")
