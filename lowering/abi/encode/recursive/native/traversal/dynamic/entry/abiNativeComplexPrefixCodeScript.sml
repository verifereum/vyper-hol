(* TOP-LEVEL: the actual aggregate prefix contributes its counter ALLOCA
   to the enclosing computed profile and containing function. Compiler
   freshness concerns emitted instructions, independently of runtime slots. *)
Theory abiNativeComplexPrefixCode
Ancestors
  abiComplexCode abiComplexStructure abiAllocationSiteProfile compileAllocaProfiles compileAllocaProvenance
  compileIdFlow compileEnv venomState venomInst list words arithmetic

Definition abi_native_complex_counter_inst_def:
  abi_native_complex_counter_inst cs =
    mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0]
End

Theorem abi_native_complex_prefix_history:
  !head_size cs.
    compiler_id_history cs ==> compiler_id_history (abi_complex_prefix_cut head_size cs)
Proof
  rpt gen_tac >> simp[compiler_id_history_def, abi_complex_prefix_cut_def,
    abi_complex_prefix_insts_def, EVERY_MEM, mk_inst_def] >> rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem abi_native_complex_prefix_provenance:
  !head_size cs after func.
    compiler_id_history cs /\ cs_extends (abi_complex_prefix_cut head_size cs) after /\
    fn_has_code cs (abi_complex_prefix_cut head_size cs) func ==>
    MEM (abi_native_complex_counter_inst cs).inst_id (compiler_alloca_ids cs after) /\
    MEM (abi_native_complex_counter_inst cs) (fn_insts func) /\
    compiler_instruction_member (abi_complex_prefix_cut head_size cs) (abi_native_complex_counter_inst cs)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (abi_native_complex_counter_inst cs) (abi_complex_prefix_cut head_size cs).cs_current_insts` by
    simp[abi_native_complex_counter_inst_def, abi_complex_prefix_cut_def, abi_complex_prefix_insts_def, MEM_APPEND] >>
  `compiler_instruction_member (abi_complex_prefix_cut head_size cs) (abi_native_complex_counter_inst cs)` by
    simp[compiler_instruction_member_def] >>
  `compiler_instruction_member after (abi_native_complex_counter_inst cs)` by
    (drule_all compiler_instruction_member_extends >> simp[]) >>
  `MEM (abi_native_complex_counter_inst cs).inst_id (compiler_alloca_ids cs after)` by
    (irule compiler_alloca_profile_fresh_member >>
     simp[abi_native_complex_counter_inst_def, mk_inst_def]) >>
  `MEM (abi_native_complex_counter_inst cs) (fn_insts func)` by
    (drule_all fn_has_code_current_member >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual complex prefix compiler provenance: " ^ name)
  end) (DB.thms "abiNativeComplexPrefixCode")
