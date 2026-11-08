(* Finite Empty allocation origins; no global compiler exclusion is asserted. *)
Theory bodyPtrBytestringBuiltinsEmptySeam
Ancestors
  bodyPtrBytestringBuiltinsAllocationDeltas
  bodyPtrBytestringBuiltinsAllocationOrigins
  bodyPtrBytestringBuiltinsAllocationSeparation
  bodyPtrBytestringBuiltinsBufferOrigins
  bodyPtrBytestringBuiltinsCompilerSeams
  exprSafeOperand emitHelperProps builtinSimple context loweringShapeDefs emitHelper compileEnv list venomInst

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

(* Only the cut after the header's first record is excluded here. The old
   parent is obtained by allocation, not by assuming an environment age. *)
Theorem empty_saved_parent_header_cut:
  compile_alloc_buffer parent_bytes sa = (parent,sb) /\
  compile_builtin_empty_complex bytes flag sb = (child,sc) /\
  emit_op ADD [parent.buf_operand; Lit 32w] sc = (dst,sd) ==>
  ?delta. state_insts sc = state_insts sb ++ delta /\
    (!p i tail q j0 j1 j2 j3 cap b d off.
      delta = p ++ [i] ==>
      [i] ++ emitted_insts sc sd ++ tail <>
        [mk_inst j0 ALLOCA [Lit (n2w cap)] [b];
         mk_inst j1 ADD [Var b; Lit 32w] [d];
         mk_inst j2 ALLOCA [Lit 64w] [off];
         mk_inst j3 MSTORE [Var off; Lit 0w] []] ++ q)
Proof
  rpt strip_tac >> drule_all empty_child_ne_saved_allocation >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `delta` >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `mk_inst j0 ALLOCA [Lit (n2w cap)] [b]` mp_tac) >>
  simp[MEM_APPEND, mk_inst_def] >> gvs[mk_inst_def]
QED

(* A zero-sized non-bytestring child really can end in its allocation:
   no post-allocation store may be assumed when proving the cut above. *)
Theorem empty_zero_nonbytes_is_alloc:
  compile_builtin_empty_complex 0 F = compile_alloc_buffer 0
Proof
  simp[FUN_EQ_THM, compile_builtin_empty_complex_def, compile_zero_words_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  gen_tac >> pairarg_tac >> simp[]
QED
