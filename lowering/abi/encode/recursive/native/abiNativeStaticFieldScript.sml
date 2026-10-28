(* TOP-LEVEL: a complete static field step executes the actual source ADD,
   destination ADD and arbitrary recursive child. Its sole semantic child
   premise is the induction assertion at the original source-memory stride. *)
Theory abiNativeStaticField
Ancestors
  abiNativeEncodingDefs abiNativeStaticChild abiFieldAddress abiFieldBytesPath
  abiComplexCode abiComplexStructure abiMemoryLeafRun
  compileEnv fragExec venomState valueEncoding list words arithmetic

Theorem abi_native_static_field:
  !info mem_sz reference payload ctx func dst src source_offset head_offset dyn_ptr cs ret after ss
      dst_addr root_addr source_id target_id.
    abi_native_encoder info (w2n root_addr + source_offset) mem_sz reference payload /\
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info F head_offset dyn_ptr
      (abi_complex_field_cut src source_offset cs) = (ret,after) /\
    fn_has_code cs after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    abi_operand_before cs.cs_next_var dst /\ w2n root_addr + source_offset < dimword (:256) /\
    abi_native_memory_ready func cs after source_id target_id (root_addr + n2w source_offset) mem_sz
      (dst_addr + n2w head_offset) payload ss /\
    mem_bytes_at (w2n root_addr + source_offset) mem_sz reference =
      mem_bytes_at (w2n root_addr + source_offset) mem_sz ss.vs_memory ==>
    ?out. abi_native_encoding_result ctx func cs after ret (dst_addr + n2w head_offset) payload ss out
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `w2n (root_addr + n2w source_offset) = w2n root_addr + source_offset` by
    (irule abi_field_word_address >> simp[]) >>
  `cs_extends (abi_complex_field_cut src source_offset cs) after` by
    (drule_all compile_abi_child_extends >> simp[]) >>
  `fn_has_code cs (abi_complex_field_cut src source_offset cs) func /\
    fn_has_code (abi_complex_field_cut src source_offset cs) after func` by
    (irule fn_has_code_split >> simp[abi_complex_field_extends]) >>
  qspecl_then [`cs`, `source_offset`, `root_addr`, `ss`, `dst`, `dst_addr`]
    mp_tac abi_native_address_inputs >> impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`func`, `cs`, `after`, `source_id`, `target_id`, `root_addr + n2w source_offset`, `mem_sz`,
    `dst_addr + n2w head_offset`, `payload`, `ss`, `src`, `source_offset`, `root_addr`]
    mp_tac abi_native_address_ready >> impl_tac >- simp[] >> DISCH_TAC >>
  qspecl_then [`info`, `mem_sz`, `reference`, `payload`, `ctx`, `func`, `dst`,
    `Var (compiler_var_name cs.cs_next_var 0)`, `head_offset`, `dyn_ptr`,
    `abi_complex_field_cut src source_offset cs`, `ret`, `after`,
    `abi_field_address_state cs source_offset root_addr ss`, `dst_addr`,
    `root_addr + n2w source_offset`, `source_id`, `target_id`] mp_tac abi_native_static_child >>
  impl_tac >- (simp[abi_complex_field_cut_def, abi_field_address_state_frame] >> fs[]) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >> qexists_tac `out` >>
  qspecl_then [`ctx`, `func`, `src`, `source_offset`, `cs`, `after`, `ss`, `root_addr`, `ret`,
    `dst_addr + n2w head_offset`, `payload`, `out`] mp_tac abi_native_address_run >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete native static recursive field: " ^ name)
  end) (DB.thms "abiNativeStaticField")
