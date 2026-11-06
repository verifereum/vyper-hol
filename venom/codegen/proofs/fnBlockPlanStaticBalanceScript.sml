Theory fnBlockPlanStaticBalance
Ancestors
  stackPlanGen stackPlanOps stackPlanTypes stackModel asmIR integer prefixExec

(* Physical planner bookkeeping; SOEmit is deliberately opaque. *)
Definition stack_op_weight_def:
  (stack_op_weight (SOPush op) = (1:int)) /\
  (stack_op_weight (SOPop n) = -(&n)) /\
  (stack_op_weight (SOSwap n) = 0) /\
  (stack_op_weight (SODup n) = 1) /\
  (stack_op_weight (SOPoke n op) = 0) /\
  (stack_op_weight (SOSpill n) = -1) /\
  (stack_op_weight (SORestore n) = 1) /\
  (stack_op_weight (SOEmit name) = 0) /\
  (stack_op_weight SOInitialFmp = 1) /\
  (stack_op_weight (SOLabel name) = 0) /\
  (stack_op_weight (SOPushLabel name) = 1) /\
  (stack_op_weight (SOPushOfst name n) = 1)
End

Definition trace_weight_def:
  (trace_weight [] = (0:int)) /\
  (trace_weight (x::xs) = stack_op_weight x + trace_weight xs)
End

Theorem trace_weight_append:
  !xs ys. trace_weight (xs ++ ys) = trace_weight xs + trace_weight ys
Proof
  Induct >> simp[trace_weight_def, INT_ADD_ASSOC]
QED

Definition regular_correction_def:
  regular_correction inst topics =
    &(LENGTH inst.inst_outputs) - &(LENGTH (compute_operands inst)) -
    trace_weight (FST (generate_emit_ops inst topics (init_plan_state 0)))
End

Theorem generate_emit_ops_stack:
  (SND (generate_emit_ops inst topics ps)).ps_stack = ps.ps_stack
Proof
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >~ [`venom_to_evm_name _ = SOME _`]
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      rpt (CASE_TAC >> gvs[])) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      rpt (CASE_TAC >> gvs[])) >>
  Cases_on `inst.inst_opcode = DJMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      Cases_on `HD inst.inst_operands` >> simp[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = RET`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- (gvs[] >> simp[generate_emit_ops_def, fresh_label_def]) >>
  Cases_on `inst.inst_opcode = LOG`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ISTORE` >> gvs[] >> simp[generate_emit_ops_def]
QED

Theorem generate_emit_ops_weight:
  trace_weight (FST (generate_emit_ops inst topics ps)) =
  trace_weight (FST (generate_emit_ops inst topics qs))
Proof
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >~ [`venom_to_evm_name _ = SOME _`] >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      rpt (CASE_TAC >> gvs[trace_weight_def, stack_op_weight_def])) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      rpt (CASE_TAC >> gvs[trace_weight_def, stack_op_weight_def])) >>
  Cases_on `inst.inst_opcode = DJMP` >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      Cases_on `HD inst.inst_operands` >>
      simp[fresh_label_def, trace_weight_def, stack_op_weight_def]) >>
  Cases_on `inst.inst_opcode = RET` >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT` >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- (gvs[] >> simp[generate_emit_ops_def, fresh_label_def, trace_weight_def,
          stack_op_weight_def]) >>
  Cases_on `inst.inst_opcode = LOG` >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ISTORE` >> gvs[] >> simp[generate_emit_ops_def]
QED

(* INVOKE's two synthetic pushes are independent of its output arity. *)
Theorem regular_correction_invoke:
  inst.inst_opcode = INVOKE /\ HD inst.inst_operands = Label callee ==>
  regular_correction inst topics =
    &(LENGTH inst.inst_outputs) - &(LENGTH (compute_operands inst)) - 2
Proof
  strip_tac >>
  simp[regular_correction_def, generate_emit_ops_def, venom_to_evm_name_def,
       fresh_label_def, trace_weight_def, stack_op_weight_def] >>
  intLib.ARITH_TAC
QED

Theorem regular_correction_invoke_two_outputs:
  inst.inst_opcode = INVOKE /\ HD inst.inst_operands = Label callee /\
  LENGTH inst.inst_outputs = 2 ==>
  regular_correction inst topics = -(&(LENGTH (compute_operands inst)))
Proof
  strip_tac >> drule_all regular_correction_invoke >> simp[]
QED

Theorem push_outputs_length:
  !outs ps.
  LENGTH (FOLDL (\s out.
    s with ps_stack := stack_push (Var out) s.ps_stack) ps outs).ps_stack =
  LENGTH ps.ps_stack + LENGTH outs
Proof
  Induct >> simp[] >> simp[stack_push_def]
QED

Theorem regular_silent_core_balance:
  LENGTH (compute_operands inst) <= LENGTH ps4.ps_stack /\
  ps5 = ps4 with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack /\
  ps6 = FOLDL (\s out.
    s with ps_stack := stack_push (Var out) s.ps_stack) ps5 inst.inst_outputs /\
  generate_emit_ops inst topics ps6 = (emit_ops, ps7) ==>
  &(LENGTH ps7.ps_stack) = &(LENGTH ps4.ps_stack) +
    trace_weight emit_ops + regular_correction inst topics
Proof
  strip_tac >>
  `ps7.ps_stack = ps6.ps_stack` by
    metis_tac[generate_emit_ops_stack, pairTheory.SND] >>
  `trace_weight emit_ops =
    trace_weight (FST (generate_emit_ops inst topics (init_plan_state 0)))` by
    metis_tac[generate_emit_ops_weight, pairTheory.FST] >>
  gvs[regular_correction_def, push_outputs_length, stack_pop_def,
      listTheory.LENGTH_TAKE] >>
  intLib.ARITH_TAC
QED

Theorem whole_trace_height_reflection:
  &(LENGTH out1) = &(LENGTH in1) + trace_weight ops + correction /\
  &(LENGTH out2) = &(LENGTH in2) + trace_weight ops + correction /\
  LENGTH in1 = LENGTH in2 ==>
  LENGTH out1 = LENGTH out2
Proof
  intLib.ARITH_TAC
QED

Theorem whole_trace_empty_reflection:
  (0:int) = &(LENGTH in1) + trace_weight ops + correction /\
  &(LENGTH out2) = &(LENGTH in2) + trace_weight ops + correction /\
  LENGTH in1 = LENGTH in2 ==>
  out2 = []
Proof
  strip_tac >> `LENGTH out2 = 0` by intLib.ARITH_TAC >>
  fs[listTheory.LENGTH_NIL]
QED

(* Remaining certificate map (obligations, NOT assumptions or proved claims):
 *
 * Physical fragments:
 *   fragment ps = (ops, qs) ==> &LENGTH qs.ps_stack =
 *     &LENGTH ps.ps_stack + trace_weight ops.
 * Needed for input/restore/reorder, popmany/optimistic-swap, and cleanup.
 * planWf.emit_input_plan_wf_len supplies prefix_wf and prefix_end_len
 * equality only when opc <> INVOKE and literal-label lookups succeed.
 * planWf.reorder_plan_wf_len supplies those two facts under target length
 * <= stack length and <=16. A bridge from prefix_wf/end_len to signed
 * weight remains to prove, as does the INVOKE input variant. Existing
 * planAlign.popmany_plan_contiguous_prefix_wf supplies only prefix_wf,
 * requires present contiguous top operands, <=16 and strict stack bound;
 * it is not the general popmany balance certificate. release_dead_spills
 * does not modify the stack; spill/restore validity must still be carried.
 *
 * Non-underflow:
 *   operand coverage + structural wf ==> LENGTH (compute_operands inst)
 *     <= LENGTH (SND (emit_input_plan ...)).ps_stack.
 * Reorder must preserve this bound before regular_silent_core_balance.
 * This is needed on BOTH DFS and replay states, not just the DFS run.
 *
 * Source corrections:
 *   regular: regular_correction inst topics (proved for silent core only).
 *   PHI: correction 0 when valid in-range poke, duplication and dead-output
 *     pop fragments balance. Must prove phi depth validity; phi readiness
 *     excludes unwanted source retention, not a substitute for validity.
 *   OFFSET: correction 0 (push trace matches pushed output); malformed
 *     label branch leaves both unchanged. NOP/param body skips: 0.
 *   prepare_params: add LENGTH (get_params entry.bb_instructions), since
 *     each parameter silently pushes one output; remaining pop/swap trace
 *     must balance. This correction is present only at the entry block.
 *   fold: sum source-indexed corrections, with LOG topics computed from
 *     the instruction, over non_param_insts. Need a successful-plan fold
 *     theorem and all intermediate validity/bounds before summing.
 *   block: SOLabel weight 0; parameter correction plus fold correction.
 *     Successful revert rejection removes no emitted operations.
 *
 * Regional exhaustion and entry transfer (still unproved):
 *   Actual DFS entries and saved sibling stacks on a RET-reaching region
 *     need no markers and exact live support, plus sufficient ownership
 *     to establish all pipeline bounds. Carry cleanup promise falsity
 *     through actual DFS calls, with RetRegion excluding new safe elision.
 *   lineage_entry_inventory gives non-marker slots/spills live at the
 *     predecessor end and converse ownership, but permits markers.
 *   lineage_entry_join_stack gives marker-prefix ++ input_vars_from stack,
 *     but does not bound marker-prefix length or identify spill maps.
 *   Need marker-free canonical joins and PHI overwrite initialization;
 *     OFFSET outputs_used, SSA/dominance and empty NOP reads are needed
 *     for exact support and RET DFS exit emptiness.
 *   Need LENGTH ps_lineage.ps_stack = LENGTH ps_dfs.ps_stack for the same
 *     regional label. At unique predecessors this requires a mutual DFS
 *     call/saved-sibling invariant and lineage induction; at joins it
 *     requires the marker-free canonical interface. dfs_fields alone is
 *     insufficient. Arbitrary replay h/promised remain arbitrary.
 * Once these certificates hold, whole_trace_empty_reflection uses equal
 * WHOLE block ops and source correction, not cancellation of cleanup ops.
 *)

Theorem stack_op_wf_signed_balance[local]:
  !op lo n. FST (stack_op_wf lo op n) /\
    (!v. op <> SOPush (Var v)) ==>
    &(SND (stack_op_wf lo op n)) = (&n:int) + stack_op_weight op
Proof
  Cases >> simp[stack_op_wf_def, stack_op_weight_def] >> rpt gen_tac
  >~ [`stack_op_wf lo (SOPush operand) n`]
  >- (Cases_on `operand` >>
      simp[stack_op_wf_def, stack_op_weight_def] >>
      rpt strip_tac >> intLib.ARITH_TAC) >>
  rpt strip_tac >> intLib.ARITH_TAC
QED

Theorem prefix_wf_signed_balance:
  !ops lo n. prefix_wf lo n ops /\
    (!v. ~MEM (SOPush (Var v)) ops) ==>
    &(prefix_end_len lo n ops) = (&n:int) + trace_weight ops
Proof
  Induct >> simp[prefix_wf_def, prefix_end_len_def, trace_weight_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >>
  `&(SND (stack_op_wf lo h n)) = (&n:int) + stack_op_weight h` by
    (irule stack_op_wf_signed_balance >> simp[] >> metis_tac[]) >>
  gvs[] >> intLib.ARITH_TAC
QED

Theorem spill_fold_no_push_var[local]:
  !items acc_ops offsets al ops offsets' al'.
  FOLDL (\(ops, offs, al) item.
    (\(off, al'). (ops ++ [SOSpill off], SNOC off offs, al'))
      (alloc_spill_slot al))
    (acc_ops, offsets, al) items = (ops, offsets', al') /\
  ~MEM (SOPush (Var v)) acc_ops ==>
  ~MEM (SOPush (Var v)) ops
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >> simp[] >>
  rename1 `alloc_spill_slot al = (off, alloc)` >> strip_tac >>
  first_x_assum (qspec_then `acc_ops ++ [SOSpill off]` mp_tac) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem do_dup_no_push_var[local]:
  do_dup dist ps = (ops, ps') ==>
  !v. ~MEM (SOPush (Var v)) ops
Proof
  simp[do_dup_def] >> IF_CASES_TAC >- (rw[] >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
  rpt IF_CASES_TAC >> simp[] >> rpt gen_tac >>
  drule spill_fold_no_push_var >> simp[]
QED

Theorem emit_one_input_no_push_var:
  !opc nl op ps v.
    ~MEM (SOPush (Var v)) (FST (emit_one_input opc nl op ps))
Proof
  `!dist st v. ~MEM (SOPush (Var v)) (FST (do_dup dist st))` by
    (rpt gen_tac >> Cases_on `do_dup dist st` >>
     metis_tac[do_dup_no_push_var, pairTheory.FST]) >>
  rpt gen_tac >> Cases_on `op` >>
  simp[emit_one_input_def, is_var_operand_def, do_restore_def] >>
  rpt (CASE_TAC >> simp[]) >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[pairTheory.FST]
QED

Theorem emit_input_plan_no_push_var:
  !operands opc nl ps v.
    ~MEM (SOPush (Var v)) (FST (emit_input_plan opc operands nl ps))
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> simp[] >>
  metis_tac[emit_one_input_no_push_var, pairTheory.FST]
QED
