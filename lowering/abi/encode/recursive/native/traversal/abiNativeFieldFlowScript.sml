(* TOP-LEVEL: the real field compiler advances history and operand bounds;
   its deterministic remaining action supplies the enclosing endpoint. *)
Theory abiNativeFieldFlow
Ancestors
  abiNativeStaticChild abiIdFlow abiFieldsStructure abiComplexStructure abiComplexCode
  compileIdFlow compileEnv fragExec venomState list arithmetic

Theorem abi_native_field_compiler_flow:
  !dst src info is_dyn source_offset head_offset dyn_ptr cs ret mid.
    compiler_id_history cs /\
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info is_dyn head_offset dyn_ptr
      (abi_complex_field_cut src source_offset cs) = (ret,mid) ==>
    cs_extends cs mid /\ cs.cs_next_var <= mid.cs_next_var /\ compiler_id_history mid
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_abi_child_extends >> DISCH_TAC >>
  drule_all compile_abi_child_next_var >> DISCH_TAC >>
  `compiler_id_history (abi_complex_field_cut src source_offset cs)` by
    (irule abi_address_id_history >> simp[]) >>
  `compiler_id_history mid` by
    (drule compile_abi_child_id_flow >> strip_tac >>
     first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends cs mid` by
    (irule cs_extends_trans >> qexists_tac `abi_complex_field_cut src source_offset cs` >>
     simp[abi_complex_field_extends]) >>
  asm_simp_tac bool_ss [] >> fs[abi_complex_field_cut_def] >> decide_tac
QED

Theorem abi_native_field_continuation:
  !dst src info abi_sz mem_sz is_dyn rest source_offset head_offset dyn_ptr cs ret after child_ret mid.
    compile_abi_encode_complex_elems dst src ((info,abi_sz,mem_sz,is_dyn)::rest)
      source_offset head_offset dyn_ptr cs = (ret,after) /\
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info is_dyn head_offset dyn_ptr
      (abi_complex_field_cut src source_offset cs) = (child_ret,mid) ==>
    compile_abi_encode_complex_elems dst src rest (source_offset + mem_sz) (head_offset + abi_sz)
      dyn_ptr mid = (ret,after)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _`
    (strip_assume_tac o PURE_REWRITE_RULE [compile_abi_fields_cons_cuts]) >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native field compiler continuation: " ^ name)
  end) (DB.thms "abiNativeFieldFlow")
