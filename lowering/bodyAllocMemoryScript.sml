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

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ALLOC_MEMORY_AUDIT OK\n"
     else raise Fail "body allocation inherited admission"
  end) [compile_alloc_buffer_body_site];
