Theory fnBlockPlanStaticBalance
Ancestors
  stackPlanGen stackPlanOps stackPlanTypes stackModel asmIR integer prefixExec planWf
  cleanOpsSim

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


Theorem do_restore_signed_balance:
  do_restore op ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def, stack_push_def, trace_weight_def, stack_op_weight_def] >>
  rpt strip_tac >> gvs[trace_weight_def, stack_op_weight_def] >>
  intLib.ARITH_TAC
QED

Theorem restore_spilled_plan_signed_balance:
  !items ps ops qs. restore_spilled_plan items ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  Induct_on `items` >> rpt gen_tac
  >- simp[restore_spilled_plan_def, trace_weight_def] >>
  simp[restore_spilled_plan_def, LET_THM] >>
  pairarg_tac >>
  Cases_on `restore_spilled_plan items ps1` >>
  simp[] >> strip_tac >> gvs[] >>
  drule do_restore_signed_balance >> strip_tac >>
  first_x_assum drule >> simp[trace_weight_append] >> intLib.ARITH_TAC
QED

Theorem do_swap_no_push_var[local]:
  do_swap dist ps = (ops, qs) ==> !v. ~MEM (SOPush (Var v)) ops
Proof
  simp[do_swap_def] >>
  Cases_on `dist = 0` >- simp[] >>
  Cases_on `dist <= 16` >- (rw[] >> simp[]) >>
  simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[listTheory.MEM_MAP, PULL_EXISTS] >>
  rpt gen_tac >> drule spill_fold_no_push_var >> simp[]
QED

Theorem do_spill_tos_no_push_var[local]:
  do_spill_tos ps = (ops, qs) ==> !v. ~MEM (SOPush (Var v)) ops
Proof
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >> rw[] >> simp[]
QED

Theorem do_spill_at_no_push_var[local]:
  do_spill_at dist ps = (ops, qs) ==> !v. ~MEM (SOPush (Var v)) ops
Proof
  simp[do_spill_at_def] >> IF_CASES_TAC >> simp[]
  >- metis_tac[do_spill_tos_no_push_var] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule do_spill_tos_no_push_var >> simp[]
QED

Theorem do_restore_no_push_var[local]:
  do_restore op ps = (ops, qs) ==> !v. ~MEM (SOPush (Var v)) ops
Proof
  simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >> rw[] >> simp[]
QED

Theorem reduce_depth_plan_no_push_var[local]:
  !fuel target_ops target_op f n ps ops qs.
  reduce_depth_plan fuel target_ops target_op f n ps = (ops, qs) ==>
  !v. ~MEM (SOPush (Var v)) ops
Proof
  Induct >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth target_op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  qmatch_goalsub_rename_tac `select_spill_candidate _ _ dist _` >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops dist n` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[do_spill_at_no_push_var]
QED

Theorem reorder_one_no_push_var[local]:
  reorder_one dfg target_ops idx op ps = (ops, qs) ==>
  !v. ~MEM (SOPush (Var v)) ops
Proof
  simp[reorder_one_def] >> pairarg_tac >>
  `!v. ~MEM (SOPush (Var v)) restore_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[do_restore_no_push_var]) >>
  gvs[] >> qpat_x_assum `_ = (restore_ops, ps1)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps1.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  pairarg_tac >>
  `!v. ~MEM (SOPush (Var v)) reduce_ops` by
    (gvs[AllCaseEqs()] >> metis_tac[reduce_depth_plan_no_push_var]) >>
  gvs[] >> qpat_x_assum `_ = (reduce_ops, ps2)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
              (LENGTH target_ops) ps2.ps_stack` >> simp[]
  >- (rw[] >> gvs[]) >>
  rpt IF_CASES_TAC >> simp[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[do_swap_no_push_var, listTheory.MEM_APPEND]
QED

Theorem reorder_fold_no_push_var[local]:
  !xs acc_ops ps ops qs.
  FOLDL (\(ops, ps) (idx, op).
    (\(step_ops, ps'). (ops ++ step_ops, ps'))
      (reorder_one dfg target_ops idx op ps)) (acc_ops, ps) xs =
    (ops, qs) /\ ~MEM (SOPush (Var v)) acc_ops ==>
  ~MEM (SOPush (Var v)) ops
Proof
  Induct >> rpt gen_tac >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rename1 `FOLDL _ _ (item::xs)` >>
  PairCases_on `item` >> simp[] >>
  rename1 `reorder_one dfg target_ops idx op ps` >>
  Cases_on `reorder_one dfg target_ops idx op ps` >> simp[] >> strip_tac >>
  qmatch_asmsub_rename_tac `reorder_one _ _ _ _ _ = (step_ops, next_ps)` >>
  first_x_assum (qspec_then `acc_ops ++ step_ops` mp_tac) >> simp[] >>
  disch_then drule >> drule reorder_one_no_push_var >> simp[]
QED

Theorem reorder_plan_no_push_var:
  reorder_plan dfg target_ops ps = (ops, qs) ==>
  !v. ~MEM (SOPush (Var v)) ops
Proof
  simp[reorder_plan_def] >> strip_tac >> rpt gen_tac >>
  drule reorder_fold_no_push_var >> simp[]
QED

Theorem reorder_plan_signed_balance:
  LENGTH target_ops <= LENGTH ps.ps_stack /\ LENGTH target_ops <= 16 /\
  reorder_plan dfg target_ops ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  strip_tac >> drule_all reorder_plan_wf_len >>
  disch_then (qspecl_then [`dfg`, `FEMPTY`] mp_tac) >> simp[] >> strip_tac >>
  drule prefix_wf_signed_balance >>
  impl_tac >- metis_tac[reorder_plan_no_push_var] >> simp[]
QED

Theorem do_swap_signed_balance:
  dist < LENGTH ps.ps_stack /\ do_swap dist ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  strip_tac >> drule do_swap_wf_len >>
  disch_then (qspec_then `FEMPTY` mp_tac) >> simp[] >> strip_tac >>
  drule prefix_wf_signed_balance >>
  impl_tac >- metis_tac[do_swap_no_push_var] >> simp[]
QED

Theorem optimistic_swap_plan_signed_balance:
  optimistic_swap_plan dfg inst nl nt ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  simp[optimistic_swap_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >>
  simp[] >> rpt strip_tac >> gvs[trace_weight_def] >>
  irule do_swap_signed_balance >>
  metis_tac[stack_get_depth_bound]
QED

Theorem popmany_fold_signed_balance[local]:
  !items acc_ops ps ops qs.
  FOLDL (\(ops, ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops, ps)
    | SOME dist =>
      let (swap_ops, ps') = if dist = 0 then ([], ps) else do_swap dist ps in
      (ops ++ swap_ops ++ [SOPop 1],
       ps' with ps_stack := stack_pop 1 ps'.ps_stack))
    (acc_ops, ps) items = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) +
    trace_weight ops - trace_weight acc_ops
Proof
  Induct >> rpt gen_tac >- (simp[] >> rpt strip_tac >> gvs[] >> intLib.ARITH_TAC) >>
  gvs[LET_THM] >> Cases_on `stack_get_depth h ps.ps_stack` >> simp[] >>
  rename1 `stack_get_depth h ps.ps_stack = SOME dist` >>
  `dist < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  Cases_on `dist = 0` >> simp[]
  >- (strip_tac >> first_x_assum drule >>
      simp[trace_weight_append, trace_weight_def, stack_op_weight_def,
           stack_pop_def, listTheory.LENGTH_TAKE_EQ] >> intLib.ARITH_TAC) >>
  Cases_on `do_swap dist ps` >> simp[] >>
  rename1 `do_swap dist ps = (swap_ops, next_ps)` >>
  `LENGTH next_ps.ps_stack = LENGTH ps.ps_stack` by
    (drule do_swap_length >> simp[]) >>
  drule_all do_swap_signed_balance >> strip_tac >> strip_tac >>
  first_x_assum drule >>
  simp[trace_weight_append, trace_weight_def, stack_op_weight_def,
       stack_pop_def, listTheory.LENGTH_TAKE_EQ] >> intLib.ARITH_TAC
QED

Theorem popmany_individual_signed_balance:
  popmany_individual items ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  simp[popmany_individual_def, LET_THM] >> strip_tac >>
  drule (SRULE [LET_THM] popmany_fold_signed_balance) >> simp[trace_weight_def]
QED

Theorem popmany_plan_signed_balance:
  popmany_plan items ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  Cases_on `items` >- (simp[popmany_plan_def, trace_weight_def] >> rw[]) >>
  rename1 `popmany_plan (item::rest) ps` >>
  pure_rewrite_tac[popmany_plan_def, LET_THM] >> BETA_TAC >>
  reverse (Cases_on `EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) (item::rest))`)
  >- (asm_rewrite_tac[] >> strip_tac >> drule popmany_individual_signed_balance >> simp[]) >>
  asm_rewrite_tac[] >>
  reverse (Cases_on `is_contiguous_top
    (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) (item::rest)))`)
  >- (asm_rewrite_tac[] >> strip_tac >> drule popmany_individual_signed_balance >> simp[]) >>
  asm_rewrite_tac[] >>
  `LENGTH (item::rest) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  Cases_on `do_swap (LENGTH (item::rest)) ps` >> simp[] >>
  rename1 `do_swap (LENGTH (item::rest)) ps = (swap_ops, next_ps)` >>
  `LENGTH next_ps.ps_stack = LENGTH ps.ps_stack` by
    (drule do_swap_length >> simp[]) >>
  drule_all do_swap_signed_balance >> strip_tac >> strip_tac >>
  gvs[trace_weight_append, trace_weight_def, stack_op_weight_def,
      stack_pop_def, listTheory.LENGTH_TAKE_EQ] >> intLib.ARITH_TAC
QED

Theorem do_dup_signed_balance:
  dist < LENGTH ps.ps_stack /\ do_dup dist ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  strip_tac >> drule do_dup_wf_len >>
  disch_then (qspec_then `FEMPTY` mp_tac) >> simp[] >> strip_tac >>
  drule prefix_wf_signed_balance >>
  impl_tac >- metis_tac[do_dup_no_push_var] >> simp[]
QED

Theorem emit_one_input_signed_balance:
  (opc = INVOKE ==> !l. op <> Label l) /\
  emit_one_input opc nl op ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  Cases_on `op` >> simp[emit_one_input_def, is_var_operand_def, LET_THM]
  >- (rpt strip_tac >> gvs[stack_push_def, trace_weight_def, stack_op_weight_def] >>
      intLib.ARITH_TAC)
  >- (pairarg_tac >> simp[] >>
      `&(LENGTH ps1.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight restore_ops` by
        (qpat_x_assum `_ = (restore_ops, ps1)` mp_tac >>
         IF_CASES_TAC >> simp[]
         >- (strip_tac >> drule do_restore_signed_balance >> simp[]) >>
         rpt strip_tac >> gvs[trace_weight_def]) >>
      Cases_on `MEM s nl` >> simp[]
      >- (Cases_on `stack_get_depth (Var s) ps1.ps_stack` >> simp[]
          >- (rpt strip_tac >> gvs[]) >>
          rename1 `stack_get_depth (Var s) ps1.ps_stack = SOME dist` >>
          Cases_on `do_dup dist ps1` >> simp[] >> rpt strip_tac >> gvs[] >>
          `dist < LENGTH ps1.ps_stack` by metis_tac[stack_get_depth_bound] >>
          drule_all do_dup_signed_balance >> simp[trace_weight_append] >> intLib.ARITH_TAC) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[stack_push_def, trace_weight_def, stack_op_weight_def] >>
  intLib.ARITH_TAC
QED

Theorem emit_input_plan_signed_balance:
  !operands opc nl ps ops qs.
  (!l. opc = INVOKE ==> ~MEM (Label l) operands) /\
  emit_input_plan opc operands nl ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  Induct >> rpt gen_tac
  >- (simp[emit_input_plan_def, trace_weight_def] >> rpt strip_tac >> gvs[]) >>
  simp[emit_input_plan_def, LET_THM] >> pairarg_tac >>
  Cases_on `emit_input_plan opc operands nl ps1` >> simp[] >> strip_tac >> gvs[] >>
  `opc = INVOKE ==> !l. h <> Label l` by metis_tac[] >>
  drule_all emit_one_input_signed_balance >> strip_tac >>
  `!l. opc = INVOKE ==> ~MEM (Label l) operands` by metis_tac[] >>
  first_x_assum (qspec_then `opc` mp_tac) >>
  disch_then drule_all >> simp[trace_weight_append] >> intLib.ARITH_TAC
QED

Theorem phi_lookup_bound[local]:
  stack_get_phi_depth items stk = SOME dist ==> dist < LENGTH stk
Proof
  simp[stack_get_phi_depth_def] >> strip_tac >>
  drule stack_find_bound >> simp[]
QED

Theorem generate_phi_plan_signed_balance:
  generate_phi_plan inst nl halting ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  simp[generate_phi_plan_def, LET_THM] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack` >>
  simp[] >- (rpt strip_tac >> gvs[trace_weight_def]) >>
  rename1 `stack_get_phi_depth _ _ = SOME dist` >>
  `dist < LENGTH ps.ps_stack` by metis_tac[phi_lookup_bound] >>
  IF_CASES_TAC >> simp[]
  >- (Cases_on `do_dup dist ps` >> simp[] >>
      rename1 `do_dup dist ps = (dup_ops, next_ps)` >>
      drule_all do_dup_signed_balance >> strip_tac >>
      IF_CASES_TAC >> simp[]
      >- (Cases_on `popmany_plan [Var (HD inst.inst_outputs)]
            (next_ps with ps_stack := stack_poke 0 (Var (HD inst.inst_outputs)) next_ps.ps_stack)` >>
          simp[] >> rpt strip_tac >> gvs[] >>
          drule popmany_plan_signed_balance >>
          simp[stack_poke_def, listTheory.LENGTH_LUPDATE, trace_weight_append,
               trace_weight_def, stack_op_weight_def] >> intLib.ARITH_TAC) >>
      rpt strip_tac >> gvs[stack_poke_def, listTheory.LENGTH_LUPDATE,
        trace_weight_append, trace_weight_def, stack_op_weight_def]) >>
  IF_CASES_TAC >> simp[]
  >- (Cases_on `popmany_plan [Var (HD inst.inst_outputs)]
        (ps with ps_stack := stack_poke dist (Var (HD inst.inst_outputs)) ps.ps_stack)` >>
      simp[] >> rpt strip_tac >> gvs[] >>
      drule popmany_plan_signed_balance >>
      simp[stack_poke_def, listTheory.LENGTH_LUPDATE, trace_weight_append,
           trace_weight_def, stack_op_weight_def]) >>
  rpt strip_tac >> gvs[stack_poke_def, listTheory.LENGTH_LUPDATE,
    trace_weight_def, stack_op_weight_def]
QED

Theorem generate_offset_plan_signed_balance:
  generate_offset_plan inst ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  simp[generate_offset_plan_def, LET_THM] >> Cases_on `EL 1 inst.inst_operands` >>
  simp[] >> rpt strip_tac >>
  gvs[stack_push_def, trace_weight_def, stack_op_weight_def] >> intLib.ARITH_TAC
QED

Theorem param_push_fold_length[local]:
  !params ps.
  LENGTH (FOLDL (\s inst. s with ps_stack :=
    stack_push (Var (HD inst.inst_outputs)) s.ps_stack) ps params).ps_stack =
  LENGTH ps.ps_stack + LENGTH params
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then `ps with ps_stack :=
    stack_push (Var (HD h.inst_outputs)) ps.ps_stack` mp_tac) >>
  simp[stack_push_def]
QED

Theorem prepare_params_plan_signed_balance:
  prepare_params_plan lv fn ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops +
    &(LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  simp[prepare_params_plan_def, LET_THM] >>
  Cases_on `get_params (HD fn.fn_blocks).bb_instructions = []` >> simp[]
  >- (rpt strip_tac >> gvs[trace_weight_def]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule popmany_plan_signed_balance >> strip_tac >>
  drule optimistic_swap_plan_signed_balance >>
  simp[param_push_fold_length, trace_weight_append] >> intLib.ARITH_TAC
QED

Theorem clean_stack_plan_signed_balance:
  clean_stack_plan lv cfg fn bb ps = (ops, qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops
Proof
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[]
  >- (rpt strip_tac >> gvs[trace_weight_def]) >>
  rename1 `cfg_preds_of cfg bb.bb_label = pred::rest` >>
  reverse (Cases_on `rest`) >> simp[]
  >- (rpt strip_tac >> gvs[trace_weight_def]) >>
  IF_CASES_TAC >> simp[]
  >- (rpt strip_tac >> gvs[trace_weight_def]) >>
  Cases_on `lookup_block pred fn.fn_blocks` >> simp[]
  >- (rpt strip_tac >> gvs[trace_weight_def]) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[trace_weight_def] >>
  drule popmany_plan_signed_balance >> simp[mark_dead_stack_def]
QED
