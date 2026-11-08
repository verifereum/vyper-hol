(* Finite Empty allocation origins; no global compiler exclusion is asserted. *)
Theory bodyPtrBytestringBuiltinsEmptySeam
Ancestors
  bodyPtrBytestringBuiltinsAllocationDeltas
  bodyPtrBytestringBuiltinsAllocationOrigins
  bodyPtrBytestringBuiltinsAllocationSeparation
  bodyPtrBytestringBuiltinsBufferOrigins
  bodyPtrBytestringBuiltinsCompilerSeams
  exprSafeOperand builtinSimple context loweringShapeDefs emitHelper compileEnv list venomInst

Theorem zero_words_allocation_free_delta:
  !n pop sa sb.
  compile_zero_words pop n sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          (!i. MEM i delta ==> i.inst_opcode <> ALLOCA)
Proof
  Induct_on `n`
  >- (simp[compile_zero_words_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]) >>
  simp[compile_zero_words_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  qexists_tac `delta ++
    [mk_inst cs'.cs_next_id ADD [pop; Lit (n2w (n * 32))]
       [STRING #"%" (toString cs'.cs_next_var)];
     mk_inst (cs'.cs_next_id + 1) MSTORE
       [Var (STRING #"%" (toString cs'.cs_next_var)); Lit 0w] []]` >>
  gvs[state_insts_def, all_blocks_def, FLAT_APPEND, APPEND_ASSOC,
      MEM_APPEND, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem zero_words_allocation_delta:
  compile_zero_words pop n sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  strip_tac >> drule zero_words_allocation_free_delta >> strip_tac >>
  simp[alloca_output_interval_def] >>
  metis_tac[]
QED

Theorem empty_complex_allocation_delta:
  compile_builtin_empty_complex bytes flag sa = (child,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  Cases_on `flag` >>
  simp[compile_builtin_empty_complex_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_allocation_delta >> strip_tac
  >- (drule emit_void_allocation_delta >> strip_tac >>
      conj_tac >- decide_tac >>
      irule allocation_delta_compose >> goal_assum (drule_at Any) >> simp[]) >>
  drule zero_words_allocation_delta >> strip_tac >>
  conj_tac >- decide_tac >>
  irule allocation_delta_compose >> goal_assum (drule_at Any) >> simp[]
QED

Theorem empty_child_ne_saved_allocation:
  compile_alloc_buffer parent_bytes sa = (parent,sb) /\
  compile_builtin_empty_complex bytes flag sb = (child,sc) ==>
  ?delta. state_insts sc = state_insts sb ++ delta /\
    (!i x. MEM i delta /\ i.inst_opcode = ALLOCA /\
           MEM x i.inst_outputs ==> parent.buf_operand <> Var x)
Proof
  rpt strip_tac >> drule alloc_buffer_safe_operand >> strip_tac >>
  drule empty_complex_allocation_delta >> strip_tac >>
  qexists_tac `delta` >> simp[] >> rpt strip_tac >>
  metis_tac[alloca_output_ne_safe_operand]
QED
