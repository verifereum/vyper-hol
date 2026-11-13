(* Shared allocator observations for captured argument materialisation. *)
Theory extcallAllocMemory
Ancestors
  actualAllocExec loweringPosts exprLoweringProps loweringHalt
  venomState venomInst words list

Theorem extcall_alloc_immutable_separation:
  compile_alloc_buffer n sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es u /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,n) /\
  cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
    SOME (ImmutableLoc io) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
    name = SOME (itv,iv) ==>
  loweringStateRelDefs$regions_disjoint b n io (type_memory_size itv)
Proof
  strip_tac >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  `immutable_alloca_sep func cenv cx es u` by fs[stmt_state_rel_def] >>
  pop_assum mp_tac >> simp[immutable_alloca_sep_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >> simp[mk_inst_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
  metis_tac[]
QED

Theorem extcall_alloc_data_section:
  compile_alloc_buffer n sm = (buf,mid) /\
  run_inst_seq (emitted_insts sm mid) s = OK q ==>
  q.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  qpat_x_assum `run_inst_seq _ s = OK q` mp_tac >>
  simp[emitted_insts_def, DROP_PREFIX, run_inst_seq_def,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def,
    venomExecSemanticsTheory.exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED
