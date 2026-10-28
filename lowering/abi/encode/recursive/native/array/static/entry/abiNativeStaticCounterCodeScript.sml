(* TOP-LEVEL: the actual index ALLOCA belongs to the reused loop's header
   compiler context, containing function and enclosing allocation profile. *)
Theory abiNativeStaticCounterCode
Ancestors
  abiNativeStaticHeaderCode abiStaticLoopCode abiDynArrayCode abiAllocationSiteProfile
  compileAllocaProfiles compileAllocaProvenance compileIdFlow compileEnv fragExec venomState venomInst list words arithmetic

Theorem abi_native_static_counter_member:
  !cs counter_inst.
    counter_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] ==>
    compiler_instruction_member (abi_native_static_header_cut cs) counter_inst
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [compiler_instruction_member_def] >> disj2_tac >>
  qexists_tac `<|bb_label := cs.cs_current_bb; bb_instructions := cs.cs_current_insts ++
    abi_static_loop_entry cs.cs_next_id cs.cs_next_var cs.cs_next_label|>` >>
  simp[abi_native_static_header_cut_def, abi_static_loop_entry_def, MEM_APPEND]
QED

Theorem abi_native_static_header_contains:
  !dst src info width stride len_op cs ret after func.
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func ==>
    fn_has_code cs (abi_native_static_header_cut cs) func /\ fn_has_code (abi_native_static_header_cut cs) after func
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends cs (abi_native_static_header_cut cs)` by simp[abi_native_static_header_extends] >>
  drule_all abi_native_static_header_continuation >> DISCH_TAC >>
  drule_all fn_has_code_split >> simp_tac bool_ss []
QED

Theorem abi_native_static_counter_provenance:
  !root_cs root_after dst src info width stride len_op cs ret after func counter_inst.
    counter_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] /\
    cs_extends root_cs cs /\ compiler_id_history cs /\
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\
    fn_has_code cs after func /\ cs_extends after root_after ==>
    MEM counter_inst.inst_id (compiler_alloca_ids root_cs root_after) /\ MEM counter_inst (fn_insts func) /\
    compiler_instruction_member (abi_native_static_header_cut cs) counter_inst
Proof
  rpt gen_tac >> strip_tac >> drule abi_native_static_counter_member >> DISCH_TAC >>
  drule_all abi_native_static_header_continuation >> DISCH_TAC >>
  `compiler_instruction_member after counter_inst` by
    (drule_all compiler_instruction_member_extends >> simp[]) >>
  `compiler_instruction_member root_after counter_inst` by
    (qspecl_then [`after`, `root_after`, `counter_inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `~compiler_instruction_member cs counter_inst` by
    (irule compiler_id_history_fresh >> simp[mk_inst_def]) >>
  `~compiler_instruction_member root_cs counter_inst` by
    (DISCH_TAC >> qspecl_then [`root_cs`, `cs`, `counter_inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `MEM counter_inst.inst_id (compiler_alloca_ids root_cs root_after)` by
    (simp_tac bool_ss [compiler_alloca_ids_member] >> qexists_tac `counter_inst` >> simp[mk_inst_def]) >>
  `cs_extends cs after` by (drule_all compile_abi_dyn_static_loop_extends >> simp[]) >>
  `MEM counter_inst (fn_insts func)` by
    (qspecl_then [`cs`, `after`, `func`, `counter_inst`] mp_tac compiler_new_instruction_member >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_static_counter_local_profile:
  !cs counter_inst.
    counter_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] /\
    compiler_id_history cs ==>
    MEM cs.cs_next_id (compiler_alloca_ids cs (abi_native_static_header_cut cs))
Proof
  rpt gen_tac >> strip_tac >> drule abi_native_static_counter_member >> DISCH_TAC >>
  `~compiler_instruction_member cs counter_inst` by
    (irule compiler_id_history_fresh >> simp[mk_inst_def]) >>
  simp_tac bool_ss [compiler_alloca_ids_member] >> qexists_tac `counter_inst` >> simp[mk_inst_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native static index allocation provenance: " ^ name)
  end) (DB.thms "abiNativeStaticCounterCode")
