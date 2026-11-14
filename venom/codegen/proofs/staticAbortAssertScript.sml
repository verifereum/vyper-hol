(* Finite ASSERT traces with immediate-label placement supplied explicitly. *)
Theory staticAbortAssert
Ancestors
  staticAbortTrace stackPlanGen planExec stackOpAsmSim stackOpSim asmSem
  asmIR list arithmetic

Theorem static_abort_assert_chunk:
  asm_block_at prog s.as_pc
    [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] /\
  s.as_stack = v::rest /\ FLOOKUP lo "revert" = SOME off /\
  FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME dest ==>
  static_abort_normal lo o2pc prog 3 s
    (s with <|as_stack := rest;
      as_pc := if v = 0w then dest else s.as_pc + 3|>)
Proof
  strip_tac >> fs[asm_block_at_cons] >>
  simp[static_abort_normal_def, static_abort_trace_def] >>
  conj_tac
  >- (Cases_on `v = 0w` >>
      rewrite_tac[numLib.num_CONV ``3:num``] >>
      simp[Once asm_steps_def, asm_step_iszero, asm_unop_def, asm_next_def] >>
      rewrite_tac[numLib.num_CONV ``2:num``] >>
      simp[Once asm_steps_def, asm_step_def, asm_next_def] >>
      rewrite_tac[numLib.num_CONV ``1:num``] >>
      simp[asm_steps_def, asm_step_jumpi, asm_jumpi_def, asm_next_def]) >>
  rpt gen_tac >> strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2` by decide_tac >> gvs[]
  >- (simp[static_abort_safe_at_def] >> EVAL_TAC) >>
  qpat_x_assum `asm_steps _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_iszero, asm_unop_def, asm_next_def] >>
  simp[asm_step_def, asm_next_def] >>
  strip_tac >> gvs[static_abort_safe_at_def] >> EVAL_TAC
QED

Theorem static_abort_revert_postamble:
  asm_block_at prog s.as_pc (execute_plan fmp revert_postamble) ==>
  static_abort_exception lo o2pc prog 4 s
    (s with <|as_pc := s.as_pc + 3; as_returndata := []|>)
Proof
  simp[revert_postamble_def, execute_plan_def, exec_stack_op_def,
       encode_num_bytes_fuel_def, asm_block_at_cons] >> strip_tac >>
  `word_of_bytes F 0w (REVERSE (encode_num_bytes_fuel 32 0)) = (0w:bytes32)` by EVAL_TAC >>
  `!u. asm_step lo o2pc (AsmOp "DUP1") u = asm_dup 0 u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``asm_dup``])) >> simp[]) >>
  `!u. asm_step_op o2pc "DUP1" u = asm_dup 0 u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV
      [``asm_dup``])) >> simp[]) >>
  simp[static_abort_exception_def, static_abort_trace_def] >>
  conj_tac
  >- (disj2_tac >> rewrite_tac[numLib.num_CONV ``4:num``] >>
      simp[Once asm_steps_def, asm_step_def, asm_next_def] >>
      rewrite_tac[numLib.num_CONV ``3:num``] >>
      simp[Once asm_steps_def, asm_step_def, asm_next_def] >>
      rewrite_tac[numLib.num_CONV ``2:num``] >>
      simp[Once asm_steps_def, asm_dup_def, asm_next_def] >>
      rewrite_tac[numLib.num_CONV ``1:num``] >>
      simp[asm_steps_def, asm_step_revert, asm_revert_op_def] >>
      simp[asm_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >> gvs[]
  >- simp[static_abort_safe_at_def] >>
  qpat_x_assum `asm_steps _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[numLib.num_CONV ``3:num``, numLib.num_CONV ``2:num``,
              numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_def, asm_next_def] >>
  simp[asm_dup_def, asm_next_def] >>
  strip_tac >> gvs[static_abort_safe_at_def] >> EVAL_TAC
QED

Theorem static_abort_assert_progress:
  asm_block_at prog s.as_pc
    [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] /\
  1 <= LENGTH s.as_stack /\ FLOOKUP lo "revert" = SOME off /\
  FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME dest /\
  asm_block_at prog dest (execute_plan fmp revert_postamble) ==>
  (?t. static_abort_normal lo o2pc prog 3 s t /\
       t.as_pc = s.as_pc + 3 /\ LENGTH t.as_stack + 1 = LENGTH s.as_stack /\
       t.as_call_ctx = s.as_call_ctx) \/
  (?n t. n <= 7 /\ static_abort_exception lo o2pc prog n s t)
Proof
  strip_tac >> Cases_on `s.as_stack` >> fs[] >>
  rename1 `s.as_stack = v::rest` >>
  drule_all (SRULE [] static_abort_assert_chunk) >> strip_tac >>
  Cases_on `v = 0w`
  >- (disj2_tac >>
      qmatch_asmsub_abbrev_tac `static_abort_normal lo o2pc prog 3 s t` >>
      `asm_block_at prog t.as_pc (execute_plan fmp revert_postamble)` by
        simp[Abbr `t`] >>
      drule static_abort_revert_postamble >> strip_tac >>
      qexistsl [`7`, `t with <|as_pc := t.as_pc + 3; as_returndata := []|>`] >>
      simp[] >>
      drule static_abort_exception_append >>
      disch_then (qspecl_then [`t with <|as_pc := t.as_pc + 3; as_returndata := []|>`, `4`] mp_tac) >> simp[]) >>
  disj1_tac >> goal_assum (drule_at Any) >> simp[]
QED
