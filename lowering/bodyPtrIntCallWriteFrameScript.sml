(* Ordinary write exclusion; exceptional revert forwarding is explicit. *)
Theory bodyPtrIntCallWriteFrame
Ancestors bodyPtrIntCallConfinement ptrDiscipline pred_set arithmetic
  venomExecSemantics

Theorem intcall_access_write_outside:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  intcall_prov_outside P PG G /\ (!i. i < lo ==> i NOTIN P) /\
  MEM (off,len) (source_memory_write_ranges inst s) /\
  off <= a /\ a < off + len ==> a NOTIN P
Proof
  rpt strip_tac >>
  Cases_on `lo < off + len`
  >- (fs[access_ok_def] >>
      `len <> 0` by decide_tac >>
      qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges inst s) /\ _ ==> _` drule >>
      simp[] >> rpt strip_tac >>
      fs[intcall_prov_outside_def] >>
      qpat_x_assum `!x site. FLOOKUP G x = SOME site ==> _` drule >>
      simp[intcall_site_outside_def, DISJOINT_DEF, EXTENSION] >>
      disch_then (qspec_then `a` mp_tac) >> simp[] >> decide_tac) >>
  `a < lo` by decide_tac >> metis_tac[]
QED

(* Counterexample to the proposed range inclusion without operand evaluation:
   ghost taint can mention an undefined value variable. The source range
   requires its evaluation, whereas written_taint only evaluates the address. *)
Theorem intcall_written_range_missing_value_probe:
  let inst = mk_inst 0 MSTORE [Lit 64w; Var "missing"] [];
      s = ARB with vs_vars := FEMPTY;
      tn = empty_taint with t_var := FEMPTY |+ ("missing", {0})
  in
    (!op k. MEM op inst.inst_operands /\ k IN op_taint tn op ==> k < 32) /\
    64 IN written_taint tn inst s /\
    source_memory_write_ranges inst s = []
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >> simp[wordsTheory.dimword_def]
QED

(* Evaluation supplier at the actual ghost consumer. This is deliberately
   restricted to the two opcodes for which written_taint omits value
   evaluation; arbitrary successful opcodes need not evaluate all operands. *)
Theorem intcall_store_ok_evaluates:
  (inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE) /\
  inst.inst_operands = [a; v] /\ step_inst fuel ctx inst s = OK t ==>
  (?off. eval_operand a s = SOME off) /\
  (?value. eval_operand v s = SOME value)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
      AllCaseEqs()]
QED

(* C1.2.6 evaluation-supplier audit (not a whole-run frame theorem).

   Proposed corrected range boundary:
     operand word taint is bounded by 32 /\
     (!a v. inst.inst_operands = [a;v] /\
       (inst.inst_opcode = MSTORE \/ inst.inst_opcode = ISTORE) ==>
       ?value. eval_operand v s = SOME value)
     ==> written_taint tn inst s SUBSET
         range_bytes (source_memory_write_ranges inst s).
   This is a proposed signature, NOT an exported/asserted theorem here.

   Exhaustive written_taint branches (ptrDiscipline, written_taint_def):
   - MSTORE and ISTORE, exactly two operands: written_taint tests address
     only. fixed_source_write_range tests address AND value. The checked
     intcall_store_ok_evaluates supplies the missing evaluation when
     step_inst = OK t; bounded op_taint supplies the 32-byte range bound.
   - MCOPY, exactly three operands: both definitions test dst/src/size.
     No extra evaluation premise is needed; membership already bounds
     the offset by w2n size via written_taint_def.
   - All other opcode/arity combinations: written_taint is empty. This
     includes MSTORE8, other copies, external calls, storage writes and
     all terminators. Range inclusion alone is vacuous in these branches;
     it does NOT settle new_site_bytes or provenance preservation.

   Consumer/supplier ledger (ptrSafeRun, ghost_defs):
   - ghost_step non-INVOKE calls step_taint ONLY on OK t. The checked
     supplier above therefore applies to precisely the store transitions
     that can affect its returned memory ghost.
   - ghost_step non-INVOKE Error/Halt/IntRet branches return (G,tn).
     No written_taint frame premise is needed for this unchanged ghost.
   - ghost_block advances ghost_step only after step_inst = OK t for a
     non-terminator (ghost_block_step). For Error/Halt/IntRet it returns
     (G,tn), even though ptr_safe_block still checks ptr_safe_step at the
     failing instruction. Thus ptr_safe_step itself does NOT supply
     evaluability, but no failed-instruction ghost update is consumed.
   - OK terminator: halted returns (G,tn); otherwise entry_taint_vars
     changes t_var only and recursion continues with the same t_mem.
     ghost_block_intret already exports the IntRet unchanged-ghost fact.
   - ghost_blocks: zero fuel, missing block, or failed eval_phis returns
     (G,tn). Successful eval_phis recurses into ghost_block; it does not
     itself call step_taint or add memory taint. ghost_run only dispatches
     to ghost_block (or returns the unchanged ghost for missing block).
   - INVOKE is separate: decode/lookup/eval_operands/setup failures leave
     (G,tn) unchanged. Successful setup invokes ghost_blocks on the callee
     EVEN IF the eventual concrete call fails. ghost_step_invoke exposes
     this exact conditional boundary; its reset of t_var preserves t_mem.
     Nested framing must therefore cover ALL ghost_blocks outcomes, not
     just successful callee returns. Each internal ordinary store update
     still has its local OK supplier by the same ghost_block definition.

   Conclusion: the missing value-evaluation premise is supplied locally
   on every store ghost transition. A global assumption that every
   instruction's operands evaluate is neither supplied nor necessary.
   This repairs the evaluation gap in the proposed range auxiliary only.
   Site confinement, operand-taint bounds, low-region exclusion, revert
   forwarding and fresh-allocation separation remain unproved reachability
   obligations. Neither the missing-value probe nor this audit refutes or
   proves body_intcall_eq_ptr.
*)
