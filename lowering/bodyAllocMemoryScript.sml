(* Actual body allocation sites: membership and reused-site size. *)
Theory bodyAllocMemory
Ancestors
  builtinBytesMemory allocaFootprint abiBuiltinAllocation exprLoweringProps
  fragExec emitHelperProps emitHelper compileEnv venomInst venomState
  venomExecSemantics venomMemDefs list finite_map words arithmetic

Theorem compile_alloc_buffer_body_inst[local]:
  !n sa buf sb func.
    compile_alloc_buffer n sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa ==>
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
          [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  fs[get_instruction_def] >> metis_tac[EL_MEM]
QED

Theorem compile_alloc_buffer_body_site:
  !ctx func cenv cx es s n sa buf sb.
    compile_alloc_buffer n sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ n < dimword (:256) ==>
    ?p. FLOOKUP (abi_builtin_allocate_state sa.cs_next_id n s).vs_allocas
          sa.cs_next_id = SOME (p,n)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_body_inst >> strip_tac >>
  simp[alloca_site_cases] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- simp[] >>
  PairCases_on `x` >>
  fs[stmt_state_rel_def] >>
  qpat_x_assum `!inst n base sz. _` drule >>
  simp[mk_inst_def]
QED

Theorem compile_alloc_buffer_body_header_mem_ok:
  !ctx func cenv cx es s n sa buf sm value sb.
    compile_alloc_buffer n sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; value] sm = ((),sb) /\
    fn_has_code sa sm func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ fresh_vars_wrt sa s /\
    32 <= n /\ n < dimword (:256) ==>
    run_inst_seq_mem_ok
      (emitted_insts sa sm ++ emitted_insts sm sb) s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_body_site >> strip_tac >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  irule compile_alloc_buffer_header_store_mem_ok >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem compile_alloc_buffer_body_frontier:
  !ctx func cenv cx es s n sa buf sb.
    compile_alloc_buffer n sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    stmt_state_rel ctx func cenv cx es s /\ n < dimword (:256) ==>
    s.vs_alloca_next <=
      (abi_builtin_allocate_state sa.cs_next_id n s).vs_alloca_next
Proof
  rpt strip_tac >> simp[abi_builtin_allocate_state_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id = NONE` >> simp[]
QED

Theorem compile_alloc_buffer_body_header_slice:
  !n sa buf sm value sb func s.
    compile_alloc_buffer n sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand; value] sm = ((),sb) /\
    fn_has_code sa sb func /\ ~block_is_terminated sa /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       DROP s.vs_inst_idx bb.bb_instructions =
         (emitted_insts sa sm ++ emitted_insts sm sb) ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sm ++ emitted_insts sm sb) =
      LENGTH sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sm ++ emitted_insts sm sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
  FAIL_TAC "slice"
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ALLOC_MEMORY_AUDIT OK\n"
     else raise Fail "body allocation inherited admission"
  end) [compile_alloc_buffer_body_site,
        compile_alloc_buffer_body_header_mem_ok,
        compile_alloc_buffer_body_frontier];
