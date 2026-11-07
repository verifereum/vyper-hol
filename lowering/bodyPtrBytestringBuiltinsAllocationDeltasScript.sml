(* Chronological deltas compose allocation ages, not block adjacency. *)
Theory bodyPtrBytestringBuiltinsAllocationDeltas
Ancestors
  bodyPtrBytestringBuiltinsAllocationOrigins loweringShapeDefs
  emitHelper compileEnv arithmetic list venomInst

Theorem allocation_delta_compose:
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  state_insts sm = state_insts sa ++ xs /\
  state_insts sb = state_insts sm ++ ys /\
  alloca_output_interval sa.cs_next_var sm.cs_next_var xs /\
  alloca_output_interval sm.cs_next_var sb.cs_next_var ys ==>
  ?zs. state_insts sb = state_insts sa ++ zs /\
       alloca_output_interval sa.cs_next_var sb.cs_next_var zs
Proof
  rpt strip_tac >> qexists_tac `xs ++ ys` >>
  simp[APPEND_ASSOC] >> irule alloca_output_interval_append >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem emit_op_allocation_delta:
  emit_op opc args sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  Cases_on `opc = ALLOCA`
  >- (gvs[] >> strip_tac >> drule emit_op_alloca_origin >>
      strip_tac >> gvs[]) >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  gvs[state_insts_def, all_blocks_def, FLAT_APPEND, APPEND_ASSOC] >>
  simp[alloca_output_interval_def, mk_inst_def]
QED

Theorem emit_void_allocation_delta:
  emit_void opc args sa = (u,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> strip_tac >>
  gvs[state_insts_def, all_blocks_def, FLAT_APPEND, APPEND_ASSOC] >>
  simp[alloca_output_interval_def, mk_inst_def]
QED

Theorem new_block_allocation_delta:
  new_block label sa = (u,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  strip_tac >> drule state_insts_new_block >> strip_tac >>
  gvs[new_block_def] >> qexists_tac `[]` >> simp[]
QED

Theorem return_allocation_delta:
  comp_return x sa = (u,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  qexists_tac `[]` >> simp[]
QED
