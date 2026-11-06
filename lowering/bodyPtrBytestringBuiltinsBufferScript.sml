Theory bodyPtrBytestringBuiltinsBuffer
Ancestors
  bodyPtrBytestringBuiltinsAllocation loweringHalt emitHelperProps
  context emitHelper compileEnv fragExec venomInst list

Theorem compile_alloc_buffer_counted_edge_covers:
  compile_alloc_buffer n sa = (buf,sb) /\ buf.buf_operand = Var out /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ptr_covers
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s u tn)
    out (u with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out])
     (fn_insts func)` by
    (irule lookup_block_fn_insts >> qexists_tac `bb` >> simp[] >>
     gvs[get_instruction_def] >> metis_tac[MEM_EL]) >>
  irule alloca_counted_edge_covers >> metis_tac[]
QED
