(* TOP-LEVEL: execute the real static-child ADD and invoke the recursive
   induction assertion. The wrapper result has its own computed profile;
   no execution result for the child is an input premise. *)
Theory abiNativeStaticChild
Ancestors
  abiNativeEncodingDefs abiNativeResources abiMemoryLeafRun abiMemoryStaticChildRun
  abiStaticChildCode abiFieldAddress abiFieldOperands abiChildFlatCode
  abiComplexCode abiAllocationTrace abiAllocatorState compileAllocaProvenance
  compileIdFlow compileEnv venomState venomInst list pair words arithmetic

Theorem abi_address_alloca_profile:
  !base_op offset cs after.
    compiler_alloca_ids (abi_complex_field_cut base_op offset cs) after =
      compiler_alloca_ids cs after
Proof
  rpt gen_tac >>
  `(\inst. inst.inst_opcode = ALLOCA /\
      ~compiler_instruction_member (abi_complex_field_cut base_op offset cs) inst) =
    (\inst. inst.inst_opcode = ALLOCA /\ ~compiler_instruction_member cs inst)` by
    (simp_tac bool_ss [FUN_EQ_THM] >> qx_gen_tac `inst` >>
     Cases_on `inst.inst_opcode = ALLOCA` >> simp[] >>
     `inst <> mk_inst cs.cs_next_id ADD [base_op; Lit (n2w offset)]
       [compiler_var_name cs.cs_next_var 0]` by (strip_tac >> gvs[mk_inst_def]) >>
     simp[compiler_instruction_member_def, abi_complex_field_cut_def, MEM_APPEND]) >>
  simp[compiler_alloca_ids_def]
QED

Theorem abi_address_id_history:
  !base_op offset cs.
    compiler_id_history cs ==> compiler_id_history (abi_complex_field_cut base_op offset cs)
Proof
  rw[compiler_id_history_def, abi_complex_field_cut_def, EVERY_APPEND, EVERY_MEM, mk_inst_def] >>
  res_tac >> simp[] >> decide_tac
QED

Theorem abi_native_address_ready:
  !func cs cs' source_id target_id src_addr span encoded_addr payload ss base_op offset base_addr.
    abi_native_memory_ready func cs cs' source_id target_id src_addr span encoded_addr payload ss ==>
    abi_native_memory_ready func (abi_complex_field_cut base_op offset cs) cs'
      source_id target_id src_addr span encoded_addr payload
      (abi_field_address_state cs offset base_addr ss)
Proof
  rpt gen_tac >> DISCH_TAC >>
  `compiler_id_history cs` by fs[abi_native_memory_ready_def] >>
  `compiler_id_history (abi_complex_field_cut base_op offset cs)` by
    (irule abi_address_id_history >> simp[]) >>
  `abi_native_memory_ready func (abi_complex_field_cut base_op offset cs) cs'
    source_id target_id src_addr span encoded_addr payload ss` by
    (fs[abi_native_memory_ready_def, abi_address_alloca_profile] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  irule abi_native_ready_allocator_state >> qexists_tac `ss` >>
  simp[abi_allocator_state_def, abi_field_address_state_def, update_var_def]
QED

Theorem abi_native_address_inputs:
  !cs offset dst_addr ss src src_addr.
    abi_operand_before cs.cs_next_var src /\ eval_operand src ss = SOME src_addr ==>
    eval_operand (Var (compiler_var_name cs.cs_next_var 0))
      (abi_field_address_state cs offset dst_addr ss) = SOME (dst_addr + n2w offset) /\
    eval_operand src (abi_field_address_state cs offset dst_addr ss) = SOME src_addr /\
    abi_operand_before (cs.cs_next_var + 1) (Var (compiler_var_name cs.cs_next_var 0)) /\
    abi_operand_before (cs.cs_next_var + 1) src
Proof
  rpt gen_tac >> strip_tac >>
  `src <> Var (compiler_var_name cs.cs_next_var 0)` by
    (irule abi_operand_before_self >> simp[]) >>
  simp[abi_field_address_state_value, abi_field_address_state_operand, abi_operand_before_reserved] >>
  irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]
QED

Theorem abi_native_address_run:
  !ctx func base_op offset cs cs' ss base_addr ret dst_addr payload out.
    fn_has_code cs (abi_complex_field_cut base_op offset cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand base_op ss = SOME base_addr /\
    abi_native_encoding_result ctx func (abi_complex_field_cut base_op offset cs) cs' ret
      dst_addr payload (abi_field_address_state cs offset base_addr ss) out ==>
    abi_native_encoding_result ctx func cs cs' ret dst_addr payload ss out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def]) >>
  `abi_encoding_result ctx func cs cs' ret dst_addr payload
    (abi_allocation_windows (compiler_alloca_ids cs cs') out) ss out` by
    (qspecl_then [`ctx`, `func`, `base_op`, `offset`, `cs`, `cs'`, `ss`, `base_addr`, `ret`,
       `dst_addr`, `payload`,
       `abi_allocation_windows (compiler_alloca_ids (abi_complex_field_cut base_op offset cs) cs') out`, `out`]
       mp_tac abi_memory_address_run >> simp[abi_address_alloca_profile]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs cs') ss out` by
    (qspecl_then [`32`, `compiler_alloca_ids (abi_complex_field_cut base_op offset cs) cs'`,
       `abi_field_address_state cs offset base_addr ss`, `out`, `ss`, `out`]
       mp_tac abi_allocation_trace_fields >>
     simp[abi_address_alloca_profile, abi_allocator_state_def, abi_field_address_state_def, update_var_def]) >>
  PURE_REWRITE_TAC [abi_native_encoding_result_def] >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_static_child:
  !info span reference payload ctx func dst src head_offset dyn_ptr cs ret cs' ss
      dst_addr src_addr source_id target_id.
    abi_native_encoder info (w2n src_addr) span reference payload /\
    compile_abi_encode_child dst src info F head_offset dyn_ptr cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    abi_native_memory_ready func cs cs' source_id target_id src_addr span
      (dst_addr + n2w head_offset) payload ss /\
    mem_bytes_at (w2n src_addr) span reference = mem_bytes_at (w2n src_addr) span ss.vs_memory ==>
    ?out. abi_native_encoding_result ctx func cs cs' ret (dst_addr + n2w head_offset) payload ss out
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule_all abi_child_static_contains >> strip_tac >>
  `compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 0)) src info
    (abi_complex_field_cut dst head_offset cs) = (ret,cs')` by
    fs[compile_abi_child_static_cuts] >>
  qspecl_then [`cs`, `head_offset`, `dst_addr`, `ss`, `src`, `src_addr`]
    mp_tac abi_native_address_inputs >> impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`func`, `cs`, `cs'`, `source_id`, `target_id`, `src_addr`, `span`,
    `dst_addr + n2w head_offset`, `payload`, `ss`, `dst`, `head_offset`, `dst_addr`]
    mp_tac abi_native_address_ready >> impl_tac >- simp[] >> DISCH_TAC >>
  qpat_x_assum `abi_native_encoder _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_native_encoder_def]) >>
  disch_then (qspecl_then [`ctx`, `func`, `Var (compiler_var_name cs.cs_next_var 0)`, `src`,
    `abi_complex_field_cut dst head_offset cs`, `ret`, `cs'`,
    `abi_field_address_state cs head_offset dst_addr ss`, `src_addr`,
    `dst_addr + n2w head_offset`, `source_id`, `target_id`] mp_tac) >>
  impl_tac >- simp[abi_complex_field_cut_def, abi_field_address_state_frame] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >>
  qspecl_then [`ctx`, `func`, `dst`, `head_offset`, `cs`, `cs'`, `ss`, `dst_addr`, `ret`,
    `dst_addr + n2w head_offset`, `payload`, `out`] mp_tac abi_native_address_run >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native static recursive child execution: " ^ name)
  end) (DB.thms "abiNativeStaticChild")
