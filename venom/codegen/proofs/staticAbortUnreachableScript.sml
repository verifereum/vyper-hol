(* Immediate local assertion jump: no value correspondence is needed. *)
Theory staticAbortUnreachable
Ancestors
  staticAbortTrace stackOpAsmSim stackOpSim asmSem asmIR list arithmetic

Theorem static_abort_unreachable_progress:
  asm_block_at prog s.as_pc
    [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
  1 <= LENGTH s.as_stack /\ FLOOKUP lo lbl = SOME off /\
  FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME (s.as_pc + 3) ==>
  (?n t. n <= 4 /\ static_abort_normal lo o2pc prog n s t /\
     t.as_pc = s.as_pc + 4 /\ LENGTH t.as_stack + 1 = LENGTH s.as_stack /\
     t.as_call_ctx = s.as_call_ctx) \/
  (?n t. n <= 4 /\ static_abort_exception lo o2pc prog n s t)
Proof
  strip_tac >> Cases_on `s.as_stack` >> fs[] >>
  rename1 `s.as_stack = v::rest` >>
  fs[asm_block_at_cons] >>
  `!u. asm_step_op o2pc "JUMPI" u = asm_jumpi o2pc u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``asm_jumpi``])) >> simp[]) >>
  Cases_on `v = 0w`
  >- (disj2_tac >>
      qexistsl [`3`, `s with <|as_stack := rest; as_pc := s.as_pc + 2; as_returndata := []|>`] >>
      simp[static_abort_exception_def, static_abort_trace_def] >>
      conj_tac
      >- (disj1_tac >> rewrite_tac[numLib.num_CONV ``3:num``] >>
          simp[Once asm_steps_def, asm_step_def, asm_next_def] >>
          rewrite_tac[numLib.num_CONV ``2:num``] >>
          simp[Once asm_steps_def, asm_step_jumpi, asm_jumpi_def, asm_next_def] >>
          rewrite_tac[numLib.num_CONV ``1:num``] >>
          simp[asm_steps_def, asm_step_invalid]) >>
      rpt gen_tac >> strip_tac >>
      `k = 0 \/ k = 1 \/ k = 2` by decide_tac >> gvs[]
      >- (simp[static_abort_safe_at_def] >> EVAL_TAC) >>
      qpat_x_assum `asm_steps _ _ _ _ _ = _` mp_tac >>
      rewrite_tac[numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``] >>
      simp[asm_steps_def, asm_step_jumpi, asm_jumpi_def, asm_next_def] >>
      simp[asm_step_def, asm_jumpi_def, asm_next_def] >>
      strip_tac >> gvs[static_abort_safe_at_def] >> EVAL_TAC) >>
  disj1_tac >> qexistsl [`3`, `s with <|as_stack := rest; as_pc := s.as_pc + 4|>`] >>
  simp[static_abort_normal_def, static_abort_trace_def] >>
  conj_tac
  >- (rewrite_tac[numLib.num_CONV ``3:num``] >>
      simp[Once asm_steps_def, asm_step_def, asm_next_def] >>
      rewrite_tac[numLib.num_CONV ``2:num``] >>
      simp[Once asm_steps_def, asm_step_jumpi, asm_jumpi_def, asm_next_def] >>
      rewrite_tac[numLib.num_CONV ``1:num``] >>
      simp[asm_steps_def, asm_step_def, asm_next_def]) >>
  rpt gen_tac >> strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2` by decide_tac >> gvs[]
  >- (simp[static_abort_safe_at_def] >> EVAL_TAC) >>
  qpat_x_assum `asm_steps _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_jumpi, asm_jumpi_def, asm_next_def] >>
  simp[asm_step_def, asm_jumpi_def, asm_next_def] >>
  strip_tac >> gvs[static_abort_safe_at_def] >> EVAL_TAC
QED
