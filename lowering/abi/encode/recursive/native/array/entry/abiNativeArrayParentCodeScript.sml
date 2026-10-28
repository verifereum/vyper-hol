(* TOP-LEVEL: the actual parent-cell setup preserves compiler history and
   contributes its ALLOCA instruction to the containing function/profile. *)
Theory abiNativeArrayParentCode
Ancestors
  abiDynArrayCode abiAllocationSiteProfile compileAllocaProfiles compileAllocaProvenance compileIdFlow
  abiStaticLoopCode compileEnv fragExec venomState venomInst list words arithmetic

Theorem abi_native_array_parent_history:
  !dst src cs. compiler_id_history cs ==> compiler_id_history (abi_dynarray_entry_cut dst src cs)
Proof
  rpt gen_tac >> simp[compiler_id_history_def, abi_dynarray_entry_cut_def,
    abi_dynarray_entry_insts_def, mk_inst_def, EVERY_MEM] >> rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem abi_native_array_parent_provenance:
  !dst src cs after func parent_inst.
    parent_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] /\
    compiler_id_history cs /\ cs_extends (abi_dynarray_entry_cut dst src cs) after /\
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func ==>
    MEM parent_inst.inst_id (compiler_alloca_ids cs after) /\ MEM parent_inst (fn_insts func) /\
    compiler_instruction_member (abi_dynarray_entry_cut dst src cs) parent_inst
Proof
  rpt gen_tac >> strip_tac >>
  `MEM parent_inst (abi_dynarray_entry_cut dst src cs).cs_current_insts` by
    simp[abi_dynarray_entry_cut_def, abi_dynarray_entry_insts_def, MEM_APPEND] >>
  `compiler_instruction_member (abi_dynarray_entry_cut dst src cs) parent_inst` by
    simp[compiler_instruction_member_def] >>
  `compiler_instruction_member after parent_inst` by
    (drule_all compiler_instruction_member_extends >> simp[]) >>
  `MEM parent_inst.inst_id (compiler_alloca_ids cs after)` by
    (irule compiler_alloca_profile_fresh_member >> simp[mk_inst_def]) >>
  `MEM parent_inst (fn_insts func)` by (drule_all fn_has_code_current_member >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native array parent compiler provenance: " ^ name)
  end) (DB.thms "abiNativeArrayParentCode")
