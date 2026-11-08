(* Counted safe instruction boundaries for tuple prefix construction. *)
Theory assignTuplePtrPrefix
Ancestors
  assignTuplePtrBoundary fragGasSeqPtr fragGasPathPtr exprLoweringProps
  emitHelperProps emitHelper fragExec venomInst venomState venomExecSemantics
  ptrSafeRun venomInstProofs typedCopyPtr list

Theorem emit_inst_zero_path_ptr:
  emit_inst opc ops outs sa = ((), sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst sa.cs_next_id opc ops outs) s /\
  step_inst_base (mk_inst sa.cs_next_id opc ops outs) s = OK u ==>
  gas_path_ptr D lo ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc ops outs) u)
    (step_taint (mk_inst sa.cs_next_id opc ops outs) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc ops outs)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_ptr_edge D lo ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc ops outs) u)
    (step_taint (mk_inst sa.cs_next_id opc ops outs) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
     simp[mk_inst_def] >> disch_then irule >> gvs[mk_inst_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id opc ops outs) s = OK u` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule step_preserves_halted >> simp[mk_inst_def]
QED

Theorem emit_mload_zero_path_ptr:
  emit_inst MLOAD [Var src] [tmp] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
    (OK (update_var tmp (mload (w2n a) s) s with
      vs_inst_idx := SUC s.vs_inst_idx)) /\
  op_taint (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [tmp]) s
    (update_var tmp (mload (w2n a) s) s) tn) (Var tmp) = {}
Proof
  strip_tac >> conj_tac
  >- (irule emit_inst_zero_path_ptr >>
      simp[is_terminator_def] >> conj_tac
      >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def] >>
      irule ptr_inst_ok_mload >> simp[]) >>
  irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]
QED
