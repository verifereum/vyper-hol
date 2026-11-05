(* Counted, checked paths for the reason encoder's straight-line prefix. *)
Theory reasonPrefixPtr
Ancestors
  reasonPrefixResourcesPtr reasonBufferPtr ghostPcTransportPtr
  fragGasSeqPtr fragGasPathPtr fragExec emitHelperProps exprLoweringProps
  ptrSafeRun ptrDiscipline venomInst venomInstProofs venomState
  venomExecSemantics context emitHelper compileEnv allocationPtr fragExecPtr

(* The compiler equation supplies the instruction lookup; callers supply only
   the semantic step and check, never a hand-built control-flow edge. *)
Theorem reason_encoder_emit_path_ptr:
  emit_inst opc ops outs sa = ((), sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ptr_inst_ok D 0 0 ctx func G tn (mk_inst sa.cs_next_id opc ops outs) s /\
  step_inst_base (mk_inst sa.cs_next_id opc ops outs) s = OK t ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc ops outs) t)
    (step_taint (mk_inst sa.cs_next_id opc ops outs) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc ops outs)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id opc ops outs) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~t.vs_halted` by
    (drule step_preserves_halted >> simp[mk_inst_def]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s
    (if (mk_inst sa.cs_next_id opc ops outs).inst_opcode = GAS then 1 else 0)
    (step_prov PG G (mk_inst sa.cs_next_id opc ops outs) t)
    (step_taint (mk_inst sa.cs_next_id opc ops outs) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule straight_line_ptr_edge >> simp[mk_inst_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem reason_encoder_alloc_path_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  buf.buf_operand = Var out /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `emit_inst ALLOCA [Lit (n2w n)] [out]
    (sa with cs_next_var := sa.cs_next_var + 1) = ((),sb)` by
    (gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, fresh_var_def,
         fresh_id_def, emit_inst_def, emit_def]) >>
  drule reason_encoder_emit_path_ptr >>
  simp[ptr_inst_ok_alloca, mk_inst_def, is_terminator_def] >>
  disch_then irule >>
  gvs[fn_has_code_def, emitted_blocks_def, GSYM mk_inst_def, ptr_inst_ok_alloca]
QED

(* Compiler layout, separate from all execution and ghost reasoning. *)
Theorem reason_encoder_prefix_code:
  compile_alloc_buffer n cc = (buf,c1) /\
  emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] c1 = ((),c2) /\
  emit_op ADD [buf.buf_operand; Lit 32w] c2 = (payload,c3) /\
  compile_alloc_buffer m c3 = (tuple,c4) /\
  buf.buf_operand = Var out /\ payload = Var x /\ tuple.buf_operand = Var out2 ==>
  c4.cs_current_bb = cc.cs_current_bb /\ c4.cs_blocks = cc.cs_blocks /\
  c4.cs_current_insts = cc.cs_current_insts ++
    [mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out];
     mk_inst c1.cs_next_id MSTORE [Var out; Lit 0x08c379a0w] [];
     mk_inst c2.cs_next_id ADD [Var out; Lit 32w] [x];
     mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]]
Proof
  strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, listTheory.APPEND_ASSOC]
QED
