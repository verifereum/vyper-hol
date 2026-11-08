Theory entryReachBodyDecoderWindowCertificate
Ancestors
  entryReachBodyDecoderIdCoverage entryReachBodyDecoderIdCoverageCompile
  actualDecoderPackaging localPtrsProps
  abiDecoderContract abiDecoderCode compileEnv loweringShapeDefs venomInst
  abiEncoderWindowContract abiDecoderAllocation vyperCompiler words pred_set

Theorem entry_decoder_window_shape:
  entry_decoder_id_coverage a b /\
  (!j. MEM j (state_insts b) ==> MEM j (fn_insts func)) /\
  fn_inst_ids_distinct func /\ MEM i (fn_insts func) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id ==>
  abi_decoder_alloc_shape i
Proof
  rw[entry_decoder_id_coverage_def] >>
  first_x_assum (qspec_then `i.inst_id` mp_tac) >> simp[] >> strip_tac >>
  `i' = i` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[]
QED

Theorem entry_decoder_window_alloca:
  entry_decoder_id_coverage a b /\
  (!j. MEM j (state_insts b) ==> MEM j (fn_insts func)) /\
  fn_inst_ids_distinct func /\ MEM i (fn_insts func) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
  i.inst_opcode = ALLOCA ==>
  i.inst_operands = [Lit 32w] /\ ?out. i.inst_outputs = [out]
Proof
  strip_tac >> drule_all entry_decoder_window_shape >>
  simp[abi_decoder_alloc_shape_def]
QED

Theorem entry_decoder_packaged_window_shape:
  entry_decoder_id_coverage a b /\ cs_extends b entry_end /\
  func = mk_raw_function "__entry" (all_blocks entry_end) /\
  fn_inst_ids_distinct func /\ MEM i (fn_insts func) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id ==>
  abi_decoder_alloc_shape i
Proof
  strip_tac >> irule entry_decoder_window_shape >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[external_phase_decoder_owned, decoder_code_member_state_insts]
QED

Theorem entry_decoder_to_buf_window_shape:
  compile_abi_decode_to_buf dst src opc hi info a = ((),b) /\
  abi_decode_source_opcode opc /\
  (!j. MEM j (state_insts b) ==> MEM j (fn_insts func)) /\
  fn_inst_ids_distinct func /\ MEM i (fn_insts func) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id ==>
  abi_decoder_alloc_shape i
Proof
  strip_tac >> drule_all entry_decoder_to_buf_id_coverage >> strip_tac >>
  irule entry_decoder_window_shape >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `func` >> simp[]
QED

Theorem entry_decoder_complex_elems_window_shape:
  compile_abi_decode_complex_elems dst src opc hi elems ao vo a = ((),b) /\
  abi_decode_source_opcode opc /\
  (!j. MEM j (state_insts b) ==> MEM j (fn_insts func)) /\
  fn_inst_ids_distinct func /\ MEM i (fn_insts func) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id ==>
  abi_decoder_alloc_shape i
Proof
  strip_tac >> drule_all entry_decoder_complex_elems_id_coverage >> strip_tac >>
  irule entry_decoder_window_shape >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `func` >> simp[]
QED

Theorem entry_decoder_dyn_loop_window_shape:
  compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt a = ((),b) /\
  abi_decode_source_opcode opc /\
  (!j. MEM j (state_insts b) ==> MEM j (fn_insts func)) /\
  fn_inst_ids_distinct func /\ MEM i (fn_insts func) /\
  a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id ==>
  abi_decoder_alloc_shape i
Proof
  strip_tac >> drule_all entry_decoder_dyn_loop_id_coverage >> strip_tac >>
  irule entry_decoder_window_shape >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `func` >> simp[]
QED

Theorem entry_decoder_window_scratch_sizes:
  entry_decoder_id_coverage a b /\
  (!j. MEM j (state_insts b) ==> MEM j (fn_insts func)) /\
  fn_inst_ids_distinct func ==>
  (!id. id IN window_alloca_sites func
       (abi_decoder_ids a.cs_next_id b.cs_next_id) ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_opcode = ALLOCA /\ alloca_size inst = 32) /\
  (!inst. MEM inst (fn_insts func) /\
    inst.inst_id IN window_alloca_sites func
      (abi_decoder_ids a.cs_next_id b.cs_next_id) ==>
    alloca_size inst = 32)
Proof
  strip_tac >>
  `!i. MEM i (fn_insts func) /\
       a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id ==>
       abi_decoder_alloc_shape i` by
    (rpt strip_tac >> irule entry_decoder_window_shape >>
     qexistsl_tac [`a`, `b`, `func`] >> simp[]) >>
  conj_tac
  >- (rw[window_alloca_sites_def, abi_decoder_ids_def] >>
      qexists_tac `inst` >> simp[] >>
      first_x_assum drule_all >>
      simp[abi_decoder_alloc_shape_def, alloca_size_def, dimword_def]) >>
  rw[window_alloca_sites_def, abi_decoder_ids_def] >>
  `inst' = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[] >>
  first_x_assum drule_all >>
  simp[abi_decoder_alloc_shape_def, alloca_size_def, dimword_def]
QED
