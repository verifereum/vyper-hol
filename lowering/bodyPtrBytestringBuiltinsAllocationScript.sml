Theory bodyPtrBytestringBuiltinsAllocation
Ancestors
  allocationPtr fragExecPtr fragGasSeqPtr ghostPcTransportPtr
  bodyPtrDefs ptrSafeRun venomInst venomState exprLoweringProps
  typedCopyPtr finite_map words venomExecSemantics ptrDiscipline

Theorem alloca_counted_edge_covers:
  !D ctx func cenv cx es s id n out u PG G tn bb.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    gas_path_ptr_edge D 0 ctx func PG G tn s 0
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
      out (u with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt strip_tac
  >- (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
      simp[ptr_inst_ok_alloca, mk_inst_def, is_terminator_def] >>
      disch_then irule >> simp[GSYM mk_inst_def, ptr_inst_ok_alloca]) >>
  simp[] >> irule alloca_step_ptr_covers >> metis_tac[]
QED

Theorem pointer_offset_counted_edge:
  !D ctx func PG G tn s bb id root out a off delta.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ADD [Var root; delta] [out]) /\
    lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
    eval_operand delta s = SOME (n2w off) /\ op_taint tn delta = {} ==>
    gas_path_ptr_edge D 0 ctx func PG G tn s 0
      (step_prov PG G (mk_inst id ADD [Var root; delta] [out])
        (update_var out (a + n2w off) s))
      (step_taint (mk_inst id ADD [Var root; delta] [out]) s
        (update_var out (a + n2w off) s) tn)
      (OK ((update_var out (a + n2w off) s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id ADD [Var root; delta] [out]) s =
    OK (update_var out (a + n2w off) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors,
       instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[GSYM mk_inst_def] >> irule ptr_inst_ok_copy_len_binop >>
  simp[op_taint_def]
QED

Theorem pointer_offset_covers:
  !PG G tn s id root out a off total n delta.
    lookup_var root s = SOME a /\ ptr_covers G tn root s total /\
    eval_operand delta s = SOME (n2w off) /\ op_taint tn delta = {} /\
    off + n <= total /\ w2n a + off < dimword(:256) ==>
    ptr_covers
      (step_prov PG G (mk_inst id ADD [Var root; delta] [out])
        (update_var out (a + n2w off) s))
      (step_taint (mk_inst id ADD [Var root; delta] [out]) s
        (update_var out (a + n2w off) s) tn)
      out ((update_var out (a + n2w off) s) with
        vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt strip_tac >>
  simp[ptr_covers_def, copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE, lookup_var_def,
       update_var_def, w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  decide_tac
QED

Theorem alloca_old_register_ghost_frame:
  x <> out ==>
  FLOOKUP (step_prov PG G (mk_inst id ALLOCA [sz] [out]) u) x = FLOOKUP G x /\
  op_taint (step_taint (mk_inst id ALLOCA [sz] [out]) s u tn) (Var x) =
    op_taint tn (Var x)
Proof
  strip_tac >>
  Cases_on `FLOOKUP u.vs_allocas id` >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
    step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `x'` >> simp[FLOOKUP_UPDATE]
QED
