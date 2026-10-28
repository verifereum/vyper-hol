(* TOP-LEVEL: both actual setup allocations belong to the real child
   prefix, enclosing function and computed allocation profile. The actual
   six-instruction setup path reaches the generated header. *)
Theory abiNativeDynamicArrayStartCode
Ancestors
  abiNativeDynamicArrayStartState abiNativeDynamicArrayParts abiDynamicLoopStructure abiDynamicLoopCode abiDynamicLoopEntry
  abiStaticLoopCode abiFieldOperands abiBytestringCode abiAllocationSiteProfile abiEncoderStructure
  compileAllocaProfiles compileAllocaProvenance compileIdFlow compileEnv fragExec venomState venomInst list rich_list words arithmetic

Definition abi_native_dynamic_array_index_inst_def:
  abi_native_dynamic_array_index_inst cs = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0]
End

Definition abi_native_dynamic_array_tail_inst_def:
  abi_native_dynamic_array_tail_inst cs = mk_inst (cs.cs_next_id + 2) ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 1]
End

Theorem abi_native_dynamic_array_start_members:
  !dst src width stride len_op cs.
    compiler_instruction_member (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) (abi_native_dynamic_array_index_inst cs) /\
    compiler_instruction_member (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) (abi_native_dynamic_array_tail_inst cs)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_instruction_member_def] >> conj_tac >> disj2_tac >>
  qexists_tac `<|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts ++
    abi_dynamic_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label width len_op|>` >>
  simp[abi_dynamic_loop_prefix_cut_def, abi_dynamic_loop_entry_def, abi_native_dynamic_array_index_inst_def,
    abi_native_dynamic_array_tail_inst_def, MEM_APPEND]
QED

Theorem abi_native_dynamic_array_start_provenance:
  !root_cs root_after dst src info width stride len_op cs ret after child_len mid func inst.
    cs_extends root_cs cs /\ compiler_id_history cs /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    fn_has_code cs after func /\ cs_extends after root_after /\
    MEM inst [abi_native_dynamic_array_index_inst cs;abi_native_dynamic_array_tail_inst cs] ==>
    MEM inst.inst_id (compiler_alloca_ids root_cs root_after) /\ MEM inst (fn_insts func) /\
    compiler_instruction_member (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) inst
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_array_parts >> strip_tac >>
  qspecl_then [`dst`, `src`, `width`, `stride`, `len_op`, `cs`] strip_assume_tac abi_native_dynamic_array_start_members >>
  `compiler_instruction_member (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) inst` by fs[MEM] >>
  `cs.cs_next_id <= inst.inst_id /\ inst.inst_opcode = ALLOCA` by
    (Cases_on `inst = abi_native_dynamic_array_index_inst cs` >>
     fs[MEM, abi_native_dynamic_array_index_inst_def, abi_native_dynamic_array_tail_inst_def, mk_inst_def]) >>
  `cs_extends (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid` by
    (drule_all compile_abi_encode_extends >> simp[]) >>
  `cs_extends (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) after` by
    (irule cs_extends_trans >> qexists_tac `mid` >> simp[]) >>
  `cs_extends cs after` by
    (irule cs_extends_trans >> qexists_tac `abi_dynamic_loop_prefix_cut dst src width stride len_op cs` >>
     simp[abi_dynamic_loop_cuts_extend]) >>
  `compiler_instruction_member after inst` by (drule_all compiler_instruction_member_extends >> simp[]) >>
  `compiler_instruction_member root_after inst` by
    (qspecl_then [`after`, `root_after`, `inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `~compiler_instruction_member cs inst` by (irule compiler_id_history_fresh >> simp[]) >>
  `~compiler_instruction_member root_cs inst` by
    (DISCH_TAC >> qspecl_then [`root_cs`, `cs`, `inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `MEM inst.inst_id (compiler_alloca_ids root_cs root_after)` by
    (simp_tac bool_ss [compiler_alloca_ids_member] >> qexists_tac `inst` >> simp[]) >>
  `MEM inst (fn_insts func)` by
    (qspecl_then [`cs`, `after`, `func`, `inst`] mp_tac compiler_new_instruction_member >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_dynamic_array_start_path:
  !ctx func dst src width stride len_op cs ss length_word.
    fn_has_code cs (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand len_op ss = SOME length_word /\ abi_operand_before cs.cs_next_var len_op ==>
    fragment_path ctx func ss (abi_native_dynamic_array_start_state cs width length_word ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_dynamic_loop_contains_prefix >> strip_tac >>
  qspecl_then [`cs.cs_next_var`, `len_op`, `cs.cs_next_var`, `2`] mp_tac abi_operand_before_names >>
  impl_tac >- simp[] >> simp_tac (srw_ss()) [compiler_var_names_def, GENLIST, compiler_var_name_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block cs.cs_current_bb _ = SOME entry_bb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) _ = SOME header_bb` >>
  qspecl_then [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`, `width`, `len_op`, `ss`,
    `length_word`, `entry_bb`, `header_bb`] mp_tac abi_dynamic_loop_entry_path >>
  impl_tac >- asm_simp_tac (srw_ss()) [Abbr`entry_bb`, Abbr`header_bb`, abi_dynamic_loop_no_phi, DROP_LENGTH_APPEND,
    compiler_var_name_def] >> simp_tac bool_ss [abi_native_dynamic_array_start_state_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array setup code and allocation provenance: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStartCode")
