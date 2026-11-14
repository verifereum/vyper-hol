(* Runtime template accounting is distinct from planner bookkeeping. *)
Theory staticAbortEmit
Ancestors
  staticAbortStraight staticAbortAssert staticAbortUnreachable staticAbortTerminal
  stackPlanGen planExec asmSymSem asmSem asmIR venomInst list arithmetic
  staticAbortTrace stackOpSim stackOpAsmSim

Definition static_abort_emit_io_def:
  static_abort_emit_io inst (a:num) (b:num) <=>
    (?name. venom_to_evm_name inst.inst_opcode = SOME name /\
       static_abort_straight name b /\ a = asm_op_arity name) \/
    (inst.inst_opcode = INITIAL_FMP /\ a = 0 /\ b = 1) \/
    (inst.inst_opcode = BUMP /\ a = 2 /\ b = 2) \/
    (inst.inst_opcode = ISTORE /\ a = 2 /\ b = 0) \/
    (MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\ a = 1 /\ b = 0) \/
    (venom_to_evm_name inst.inst_opcode = NONE /\
     ~MEM inst.inst_opcode [INITIAL_FMP;BUMP;JNZ;JMP;DJMP;INVOKE;RET;
                           ASSERT;ASSERT_UNREACHABLE;LOG;ISTORE] /\ a = 0 /\ b = 0)
End

Definition static_abort_emit_labels_def:
  static_abort_emit_labels lo o2pc prog fmp pc inst ops <=>
    (inst.inst_opcode = ASSERT ==>
      ?off dest. FLOOKUP lo "revert" = SOME off /\
        FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME dest /\
        asm_block_at prog dest (execute_plan fmp revert_postamble)) /\
    (!lbl. inst.inst_opcode = ASSERT_UNREACHABLE /\
      ops = [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl] ==>
      ?off. FLOOKUP lo lbl = SOME off /\
        FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME (pc + 3))
End

Theorem static_abort_emit_io_total:
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                        SSTORE;TSTORE;LOG] ==>
  ?a b. static_abort_emit_io inst a b
Proof
  Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def] >>
  simp[static_abort_emit_io_def, venom_to_evm_name_def] >>
  pure_rewrite_tac[static_abort_straight_def] >> EVAL_TAC >> simp[]
QED

Theorem static_abort_emit_empty:
  venom_to_evm_name inst.inst_opcode = NONE /\
  ~MEM inst.inst_opcode [INITIAL_FMP;BUMP;JNZ;JMP;DJMP;INVOKE;RET;
                        ASSERT;ASSERT_UNREACHABLE;LOG;ISTORE] ==>
  generate_emit_ops inst topics ps = ([],ps)
Proof
  simp[generate_emit_ops_def] >> strip_tac >> gvs[]
QED

Theorem static_abort_emit_assert_labels:
  inst.inst_opcode = ASSERT ==>
  (static_abort_emit_labels lo o2pc prog fmp pc inst ops <=>
    ?off dest. FLOOKUP lo "revert" = SOME off /\
      FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME dest /\
      asm_block_at prog dest (execute_plan fmp revert_postamble))
Proof
  simp[static_abort_emit_labels_def]
QED

Theorem static_abort_emit_unreachable_labels:
  inst.inst_opcode = ASSERT_UNREACHABLE ==>
  (static_abort_emit_labels lo o2pc prog fmp pc inst
     [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl] <=>
    ?off. FLOOKUP lo lbl = SOME off /\
      FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME (pc + 3))
Proof
  simp[static_abort_emit_labels_def]
QED

Theorem static_abort_emit_terminal_progress:
  generate_emit_ops inst topics ps = (ops,ps1) /\
  MEM inst.inst_opcode [SSTORE;TSTORE;LOG] /\
  (inst.inst_opcode = LOG ==> topics <= 4) /\
  (if inst.inst_opcode = LOG then 2 + topics else 2) <= LENGTH s.as_stack /\
  s.as_call_ctx.cc_static /\
  asm_block_at prog s.as_pc (execute_plan fmp ops) ==>
  ?t. static_abort_exception lo o2pc prog 1 s t
Proof
  simp[] >> strip_tac >> gvs[] >>
  fs[generate_emit_ops_def, venom_to_evm_name_def] >>
  gvs[execute_plan_def, exec_stack_op_def] >>
  irule static_abort_terminal_step >> simp[]
  >- (qexists `"SSTORE"` >> simp[] >> EVAL_TAC >> simp[])
  >- (qexists `"TSTORE"` >> simp[] >> EVAL_TAC >> simp[]) >>
  `topics = 0 \/ topics = 1 \/ topics = 2 \/ topics = 3 \/ topics = 4` by decide_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `AsmOp name` >>
  qexists `name` >>
  gvs[Abbr `name`, ASCIInumbersTheory.num_to_dec_string_compute] >>
  EVAL_TAC >> simp[]
QED

Theorem static_abort_emit_initial[local]:
  asm_block_at prog s.as_pc [AsmPush bytes] ==>
  ?t. static_abort_normal lo o2pc prog 1 s t /\
    t.as_pc = s.as_pc + 1 /\ LENGTH t.as_stack = LENGTH s.as_stack + 1 /\
    t.as_call_ctx = s.as_call_ctx
Proof
  strip_tac >> fs[asm_block_at_cons] >>
  qexists `asm_next (s with as_stack := word_of_bytes F 0w (REVERSE bytes) :: s.as_stack)` >>
  simp[static_abort_normal_def, static_abort_trace_def, static_abort_safe_at_def,
       asm_next_def] >>
  rewrite_tac[numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_def, asm_next_def]
QED

Theorem static_abort_emit_special[local]:
  (code = [AsmOp "DUP2"; AsmOp "ADD"] /\ a = 2 /\ b = 2 \/
   code = [AsmOp "SWAP1"; AsmOp "MSTORE"] /\ a = 2 /\ b = 0) /\
  a <= LENGTH s.as_stack /\ asm_block_at prog s.as_pc code ==>
  ?t. static_abort_normal lo o2pc prog 2 s t /\
    t.as_pc = s.as_pc + 2 /\ LENGTH t.as_stack + a = LENGTH s.as_stack + b /\
    t.as_call_ctx = s.as_call_ctx
Proof
  `!u. asm_step_op o2pc "DUP2" u = asm_dup 1 u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``asm_dup``])) >> simp[]) >>
  `!u. asm_step_op o2pc "SWAP1" u = asm_swap 1 u` by
    (gen_tac >> CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``asm_swap``])) >> simp[]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `_ <= LENGTH s.as_stack` mp_tac >>
  simp[quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] >> strip_tac >> gvs[] >>
  fs[asm_block_at_cons] >>
  simp[static_abort_normal_def] >>
  rewrite_tac[numLib.num_CONV ``2:num``, numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_def, asm_dup_def, asm_swap_def, asm_next_def] >>
  simp[asm_step_op_def, asm_step_compare_def, asm_step_bitwise_def,
       asm_step_arith_def, asm_step_memory_def, asm_dup_def, asm_swap_def,
       asm_binop_def, asm_mstore_def, asm_next_def, LUPDATE_compute] >>
  simp[static_abort_trace_def] >>
  (rpt gen_tac >> strip_tac >>
   Cases_on `k = 0`
   >- (gvs[static_abort_safe_at_def] >> EVAL_TAC) >>
   `k = 1` by decide_tac >> gvs[] >>
   qpat_x_assum `asm_steps _ _ _ _ _ = _` mp_tac >>
   rewrite_tac[numLib.num_CONV ``1:num``] >>
   simp[asm_steps_def, asm_step_def, asm_dup_def, asm_swap_def,
        asm_next_def, LUPDATE_compute] >>
   strip_tac >> gvs[static_abort_safe_at_def] >> EVAL_TAC)
QED

Theorem static_abort_emit_progress:
  generate_emit_ops inst topics ps = (ops,ps1) /\
  static_abort_emit_io inst a b /\ a <= LENGTH s.as_stack /\
  asm_block_at prog s.as_pc (execute_plan fmp ops) /\
  static_abort_emit_labels lo o2pc prog fmp s.as_pc inst ops ==>
  (?n t. n <= LENGTH (execute_plan fmp ops) /\
    static_abort_normal lo o2pc prog n s t /\
    t.as_pc = s.as_pc + LENGTH (execute_plan fmp ops) /\
    LENGTH t.as_stack + a = LENGTH s.as_stack + b /\
    t.as_call_ctx = s.as_call_ctx) \/
  (?n t. n <= LENGTH (execute_plan fmp ops) + 4 /\
    static_abort_exception lo o2pc prog n s t)
Proof
  strip_tac >> fs[static_abort_emit_io_def]
  >- (drule generate_emit_ops_some >>
      disch_then (qspecl_then [`topics`, `ps`] assume_tac) >> gvs[] >>
      fs[execute_plan_def, exec_stack_op_def] >>
      drule_all static_abort_straight_step >>
      disch_then (qspecl_then [`o2pc`, `lo`] strip_assume_tac)
      >- (disj1_tac >> qexistsl [`1`, `t`] >> simp[]) >>
      disj2_tac >> qexistsl [`1`, `t`] >> simp[])
  >- (fs[generate_emit_ops_def] >> gvs[execute_plan_def, exec_stack_op_def] >>
      drule static_abort_emit_initial >>
      disch_then (qspecl_then [`o2pc`, `lo`] strip_assume_tac) >>
      disj1_tac >> qexistsl [`1`, `t`] >> simp[])
  >- (fs[generate_emit_ops_def] >>
      gvs[bump_emit_ops_def, execute_plan_def, exec_stack_op_def, dup_name_def] >>
      drule_at (Pos last) static_abort_emit_special >> simp[] >>
      disch_then (qspecl_then [`o2pc`, `lo`] mp_tac) >>
      strip_tac >> disj1_tac >> qexistsl [`2`, `t`] >> simp[])
  >- (fs[generate_emit_ops_def, venom_to_evm_name_def] >>
      gvs[execute_plan_def, exec_stack_op_def] >>
      drule_at (Pos last) static_abort_emit_special >> simp[] >>
      disch_then (qspecl_then [`o2pc`, `lo`] mp_tac) >>
      strip_tac >> disj1_tac >> qexistsl [`2`, `t`] >> simp[])
  >- (fs[generate_emit_ops_def, venom_to_evm_name_def] >>
      gvs[execute_plan_def, exec_stack_op_def, static_abort_emit_labels_def] >>
      drule_all (SRULE [execute_plan_def] static_abort_assert_progress) >> strip_tac
      >- (disj1_tac >> qexistsl [`3`, `t`] >> simp[]) >>
      disj2_tac >> goal_assum (drule_at Any) >> simp[])
  >- (fs[generate_emit_ops_def, venom_to_evm_name_def] >> pairarg_tac >> gvs[] >>
      gvs[execute_plan_def, exec_stack_op_def, static_abort_emit_labels_def] >>
      drule_all (SRULE [] static_abort_unreachable_progress) >> strip_tac
      >- (disj1_tac >> qexistsl [`n`, `t`] >> simp[]) >>
      disj2_tac >> qexistsl [`n`, `t`] >> simp[]) >>
  drule_all (SRULE [] static_abort_emit_empty) >>
  disch_then (qspecl_then [`topics`, `ps`] assume_tac) >> gvs[execute_plan_def] >>
  disj1_tac >> qexistsl [`0`, `s`] >> simp[]
QED
