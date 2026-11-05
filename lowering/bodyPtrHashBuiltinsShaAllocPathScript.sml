(* The SHA output allocation is a checked, zero-GAS prefix. *)
Theory bodyPtrHashBuiltinsShaAllocPath
Ancestors
  bodyPtrHashBuiltinsShaAllocInput fragGasSeqPtr fragExecPtr
  loweringHalt emitHelperProps ptrDiscipline venomInst venomState
  words list rich_list exprLoweringProps arithmetic

Theorem hash_alloca_counted_path:
  !D ctx fn PG G tn s bb id m q t.
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit (n2w m)] [q]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w m)] [q]) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w m)] [q]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w m)] [q]) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ALLOCA [Lit (n2w m)] [q]] s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w m)] [q]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w m)] [q]) s t tn)` by
    simp[inst_seq_ptr_def, ptr_inst_ok_alloca] >>
  `run_inst_seq [mk_inst id ALLOCA [Lit (n2w m)] [q]] s = OK t` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id ALLOCA [Lit (n2w m)] [q]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[mk_inst_def, is_terminator_def, ADD1]
QED

Theorem hash_literal_alloc_counted_path:
  !D ctx fn PG G tn s bb sa sm buf m t q.
  compile_alloc_buffer m sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\ buf.buf_operand = Var q /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)] [q]) t)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)] [q]) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_emission >> strip_tac >>
     drule emitted_insts_emit_inst >> simp[emitted_insts_def] >>
     strip_tac >> gvs[]) >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  irule hash_alloca_counted_path >> simp[] >> qexists_tac `bb` >> simp[]
QED
