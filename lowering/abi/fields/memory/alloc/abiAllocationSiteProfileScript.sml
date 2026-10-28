(* TOP-LEVEL: actual buffer allocation sites belong to the enclosing code's
   computed scratch profile. Freshness follows from compiler ID history;
   runtime allocation IDs may already be cached from earlier iterations. *)
Theory abiAllocationSiteProfile
Ancestors
  compileIdFlow compileAllocaProfiles compileAllocaProvenance
  abiBufferAllocationCode compileEnv fragExec venomInst list words arithmetic

Theorem compiler_alloca_profile_fresh_member:
  !before after inst.
    compiler_id_history before /\ before.cs_next_id <= inst.inst_id /\
    compiler_instruction_member after inst /\ inst.inst_opcode = ALLOCA ==>
    MEM inst.inst_id (compiler_alloca_ids before after)
Proof
  rpt gen_tac >> strip_tac >> drule_all compiler_id_history_fresh >> DISCH_TAC >>
  simp_tac bool_ss [compiler_alloca_ids_member] >> qexists_tac `inst` >> simp[]
QED

Theorem compile_alloc_buffer_site_profile:
  !before site site_after after byte_count buf.
    compiler_id_history before /\ before.cs_next_id <= site.cs_next_id /\
    compile_alloc_buffer byte_count site = (buf,site_after) /\ cs_extends site_after after ==>
    MEM site.cs_next_id (compiler_alloca_ids before after)
Proof
  rpt gen_tac >> strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  qabbrev_tac `inst = mk_inst site.cs_next_id ALLOCA [Lit (n2w byte_count)]
    [STRING #"%" (toString site.cs_next_var)]` >>
  `MEM inst site_after.cs_current_insts` by simp[Abbr`inst`, MEM_APPEND] >>
  `compiler_instruction_member after inst` by
    (drule_all compiler_current_instruction_extends >> simp[]) >>
  `inst.inst_id = site.cs_next_id /\ inst.inst_opcode = ALLOCA` by simp[Abbr`inst`, mk_inst_def] >>
  qspecl_then [`before`, `after`, `inst`] mp_tac compiler_alloca_profile_fresh_member >>
  impl_tac >- simp[] >> simp[]
QED

Theorem compile_alloc_buffer_prefix_profile:
  !prefix before value site site_after after byte_count buf.
    compiler_id_history before /\ compiler_ids_mono prefix /\ prefix before = (value,site) /\
    compile_alloc_buffer byte_count site = (buf,site_after) /\ cs_extends site_after after ==>
    MEM site.cs_next_id (compiler_alloca_ids before after)
Proof
  rpt gen_tac >> strip_tac >> drule_all compiler_ids_mono_result >> DISCH_TAC >>
  drule_all compile_alloc_buffer_site_profile >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual allocation site profile: " ^ name)
  end) (DB.thms "abiAllocationSiteProfile")
