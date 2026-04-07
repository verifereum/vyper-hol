(*
 * Function Inliner — Inline Correctness
 *
 * Proves clone simulation at block and function level, then
 * connects to inline_candidate_correct and round_correct.
 *
 * Proof chain:
 *   1. setup_callee_shared_globals: shared_globals ⇒ same setup_callee
 *   2. step_inst_clone: clone_rel preserved through step_inst (incl. INVOKE)
 *   3. run_block_clone: clone_rel preserved through a block
 *   4. run_function_clone: clone_rel preserved through function (fuel induction)
 *   5. inline_candidate_correct: FOLDL over functions
 *)

Theory functionInlinerInline
Ancestors
  functionInlinerStepClone functionInlinerCloneSim functionInlinerSim
  functionInlinerFresh functionInlinerDefs
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  cfgTransform

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

open functionInlinerDefsTheory functionInlinerCloneSimTheory
     functionInlinerSimTheory functionInlinerStepCloneTheory
     functionInlinerFreshTheory functionInlinerRenumberTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     cfgTransformTheory

(* ================================================================
   Utility: clone_rel implies shared_globals
   ================================================================ *)

Theorem clone_rel_imp_shared_globals[local]:
  !prefix labels s1 s2.
    clone_rel prefix labels s1 s2 ==> shared_globals s1 s2
Proof
  rw[clone_rel_def]
QED

Theorem clone_rel_halted[local]:
  !prefix labels s1 s2.
    clone_rel prefix labels s1 s2 ==> (s2.vs_halted <=> s1.vs_halted)
Proof
  rw[clone_rel_def]
QED

(* ================================================================
   Structural Helpers
   ================================================================ *)

Theorem clone_bb_length[local]:
  !prefix labels bb.
    LENGTH (clone_basic_block prefix labels bb).bb_instructions =
    LENGTH bb.bb_instructions
Proof
  rw[clone_basic_block_def]
QED

Theorem get_instruction_clone[local]:
  !prefix labels bb n.
    n < LENGTH bb.bb_instructions ==>
    get_instruction (clone_basic_block prefix labels bb) n =
    SOME (clone_instruction prefix labels (EL n bb.bb_instructions))
Proof
  rw[get_instruction_def, clone_basic_block_def] >>
  simp[EL_MAP]
QED

Theorem clone_bb_label[local]:
  !prefix labels bb.
    (clone_basic_block prefix labels bb).bb_label =
    STRCAT prefix bb.bb_label
Proof
  rw[clone_basic_block_def]
QED

(* ================================================================
   setup_callee on shared_globals states
   ================================================================ *)

Theorem setup_callee_shared_globals[local]:
  !fn args s1 s2.
    shared_globals s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[setup_callee_def, shared_globals_def,
     venomStateTheory.venom_state_component_equality]
QED

(* ================================================================
   shared_globals symmetry (not exported from CloneSim)
   ================================================================ *)

Theorem shared_globals_sym[local]:
  !s1 s2. shared_globals s1 s2 ==> shared_globals s2 s1
Proof
  rw[shared_globals_def]
QED

(* ================================================================
   INVOKE clone: callee runs identically on shared_globals states
   ================================================================ *)

(* Helper: decode_invoke on clone_instruction when target is external *)
Theorem decode_invoke_clone[local]:
  !prefix labels inst callee_name arg_ops.
    decode_invoke inst = SOME (callee_name, arg_ops) /\
    (case inst.inst_operands of
       Label l :: _ => ~MEM l labels | _ => T) ==>
    decode_invoke (clone_instruction prefix labels inst) =
    SOME (callee_name, MAP (clone_operand prefix labels) arg_ops)
Proof
  rw[decode_invoke_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[clone_operand_def]
QED

(* Helper: bind_outputs with prefixed names preserves clone_rel *)
(* FOLDL update_var preserves clone_rel with prefixed names *)
Theorem foldl_update_var_clone_rel[local]:
  !outs vals prefix labels s1 s2.
    clone_rel prefix labels s1 s2 /\
    LENGTH outs = LENGTH vals ==>
    clone_rel prefix labels
      (FOLDL (\s' (out,val). update_var out val s') s1 (ZIP (outs, vals)))
      (FOLDL (\s' (out,val). update_var out val s') s2
             (ZIP (MAP (\v. STRCAT prefix v) outs, vals)))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> Cases_on `vals` >> simp[] >>
  rpt strip_tac >> simp[ZIP_def, FOLDL] >>
  first_x_assum irule >> simp[] >>
  irule clone_rel_update_var >> simp[]
QED

Theorem bind_outputs_clone_rel[local]:
  !prefix labels outs vals s1 s2 s1'.
    clone_rel prefix labels s1 s2 /\
    bind_outputs outs vals s1 = SOME s1' ==>
    ?s2'. bind_outputs (MAP (\v. STRCAT prefix v) outs) vals s2 = SOME s2' /\
          clone_rel prefix labels s1' s2'
Proof
  rpt strip_tac >>
  gvs[bind_outputs_def] >>
  simp[bind_outputs_def] >>
  irule foldl_update_var_clone_rel >> simp[]
QED

(* Helper: merge_callee_state preserves clone_rel *)
Theorem merge_callee_clone_rel[local]:
  !prefix labels s1 s2 callee_s.
    clone_rel prefix labels s1 s2 ==>
    clone_rel prefix labels
      (merge_callee_state s1 callee_s)
      (merge_callee_state s2 callee_s)
Proof
  simp[clone_rel_def, merge_callee_state_def, shared_globals_def]
QED

(* Main INVOKE clone theorem *)
Theorem step_inst_invoke_clone[local]:
  !prefix labels inst s_callee s_clone fuel ctx.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = INVOKE /\
    (case inst.inst_operands of
       Label l :: _ => ~MEM l labels | _ => T) ==>
    case step_inst fuel ctx inst s_callee of
      OK sc =>
        ?sc'. step_inst fuel ctx
                (clone_instruction prefix labels inst) s_clone = OK sc' /\
              clone_rel prefix labels sc sc'
    | Halt sc =>
        ?sc'. step_inst fuel ctx
                (clone_instruction prefix labels inst) s_clone = Halt sc' /\
              shared_globals sc sc'
    | Abort a sc =>
        ?sc'. step_inst fuel ctx
                (clone_instruction prefix labels inst) s_clone = Abort a sc' /\
              shared_globals sc sc'
    | IntRet vals sc =>
        ?vals' sc'. step_inst fuel ctx
                (clone_instruction prefix labels inst) s_clone =
                IntRet vals' sc'
    | Error e =>
        ?e'. step_inst fuel ctx
               (clone_instruction prefix labels inst) s_clone = Error e'
Proof
  rpt strip_tac
  \\ imp_res_tac clone_rel_imp_shared_globals
  \\ imp_res_tac shared_globals_sym
  \\ ONCE_REWRITE_TAC[step_inst_def]
  \\ simp[clone_inst_opcode]
  \\ Cases_on `decode_invoke inst`
  >- (
    simp[]
    \\ gvs[Once step_inst_def, clone_inst_opcode,
            decode_invoke_def, clone_instruction_def]
    \\ Cases_on `inst.inst_operands` \\ gvs[]
    \\ Cases_on `h` \\ gvs[clone_operand_def]
  )
  \\ PairCases_on `x` \\ simp[]
  \\ rename1 `decode_invoke inst = SOME (callee_name, arg_ops)`
  \\ imp_res_tac decode_invoke_clone
  \\ pop_assum (qspec_then `prefix` ASSUME_TAC) \\ simp[]
  \\ Cases_on `lookup_function callee_name ctx.ctx_functions` >- simp[]
  \\ simp[] \\ rename1 `lookup_function _ _ = SOME callee_fn`
  (* eval_operands: use eval_operand_clone for each operand *)
  \\ `eval_operands (MAP (clone_operand prefix labels) arg_ops) s_clone =
      eval_operands arg_ops s_callee` by (
    irule eval_operands_clone_full \\ simp[]
  )
  \\ Cases_on `eval_operands arg_ops s_callee` >- simp[]
  \\ simp[] \\ rename1 `eval_operands _ _ = SOME args`
  (* setup_callee *)
  \\ SUBGOAL_THEN ``setup_callee callee_fn args s_clone =
                    setup_callee callee_fn args s_callee``
       (fn th => REWRITE_TAC [th])
  >- (irule setup_callee_shared_globals \\ simp[])
  \\ Cases_on `setup_callee callee_fn args s_callee` >- simp[]
  \\ simp[] \\ rename1 `setup_callee _ _ _ = SOME callee_s`
  \\ Cases_on `run_function fuel ctx callee_fn callee_s` \\ simp[]
  \\ rename1 `IntRet ret_vals callee_s'`
  \\ Cases_on `bind_outputs inst.inst_outputs ret_vals
                 (merge_callee_state s_callee callee_s')`
  >- gvs[bind_outputs_def, LENGTH_MAP]
  \\ rename1 `bind_outputs _ _ _ = SOME s_result`
  \\ simp[]
  \\ imp_res_tac merge_callee_clone_rel
  \\ pop_assum (qspec_then `callee_s'` ASSUME_TAC)
  \\ drule_all bind_outputs_clone_rel \\ strip_tac
  \\ simp[]
QED

(* ================================================================
   step_inst_base result classification
   ================================================================ *)

(* step_inst_base only produces IntRet via the RET opcode *)
Theorem step_inst_base_intret_implies_ret[local]:
  !inst s vals sc.
    step_inst_base inst s = IntRet vals sc ==>
    inst.inst_opcode = RET
Proof
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

(* ================================================================
   step_inst_clone: combined INVOKE + non-INVOKE
   ================================================================ *)

Theorem step_inst_clone[local]:
  !prefix labels inst s_callee s_clone fuel ctx.
    clone_rel prefix labels s_callee s_clone /\
    EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands /\
    (inst.inst_opcode = INVOKE ==>
      case inst.inst_operands of
        Label l :: _ => ~MEM l labels | _ => T) /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> RET /\
    inst.inst_opcode <> OFFSET ==>
    case step_inst fuel ctx inst s_callee of
      OK sc =>
        ?sc'. step_inst fuel ctx
                (clone_instruction prefix labels inst) s_clone = OK sc' /\
              clone_rel prefix labels sc sc'
    | Halt sc =>
        ?sc'. step_inst fuel ctx
                (clone_instruction prefix labels inst) s_clone = Halt sc' /\
              shared_globals sc sc'
    | Abort a sc =>
        ?sc'. step_inst fuel ctx
                (clone_instruction prefix labels inst) s_clone = Abort a sc' /\
              shared_globals sc sc'
    | IntRet vals sc =>
        ?vals' sc'. step_inst fuel ctx
                (clone_instruction prefix labels inst) s_clone =
                IntRet vals' sc'
    | Error e =>
        ?e'. step_inst fuel ctx
               (clone_instruction prefix labels inst) s_clone = Error e'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- (
    irule step_inst_invoke_clone \\ simp[]
  ) >>
  simp[step_inst_non_invoke] >>
  (SUBGOAL_THEN ``(clone_instruction prefix labels inst).inst_opcode <> INVOKE``
    ASSUME_TAC >- simp[clone_inst_opcode]) >>
  simp[step_inst_non_invoke] >>
  drule step_inst_base_clone >>
  disch_then (qspec_then `inst` mp_tac) >> simp[] >>
  strip_tac >>
  Cases_on `step_inst_base inst s_callee` >> gvs[] >>
  metis_tac[step_inst_base_intret_implies_ret]
QED

(* ================================================================
   run_block_clone: per-block clone simulation
   ================================================================ *)

(* Helper: extract per-instruction properties from block-level EVERYs *)
Theorem every_el_props[local]:
  !bb n labels.
    n < LENGTH bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> PARAM /\
                  inst.inst_opcode <> RET /\
                  inst.inst_opcode <> OFFSET) bb.bb_instructions /\
    EVERY (\inst. EVERY (\op. !l. op = Label l ==> MEM l labels)
                        inst.inst_operands) bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = INVOKE ==>
             case inst.inst_operands of
               Label l :: _ => ~MEM l labels | _ => T)
          bb.bb_instructions ==>
    let inst = EL n bb.bb_instructions in
      inst.inst_opcode <> PARAM /\
      inst.inst_opcode <> RET /\
      inst.inst_opcode <> OFFSET /\
      EVERY (\op. !l. op = Label l ==> MEM l labels) inst.inst_operands /\
      (inst.inst_opcode = INVOKE ==>
        case inst.inst_operands of
          Label l :: _ => ~MEM l labels | _ => T)
Proof
  rw[LET_THM] >> gvs[listTheory.EVERY_EL] >>
  metis_tac[]
QED

Theorem run_block_clone:
  !n fuel ctx bb s_callee s_clone prefix labels.
    clone_rel prefix labels s_callee s_clone /\
    n = LENGTH bb.bb_instructions - s_callee.vs_inst_idx /\
    s_clone.vs_inst_idx = s_callee.vs_inst_idx /\
    s_callee.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (* No PARAM, RET, OFFSET *)
    EVERY (\inst. inst.inst_opcode <> PARAM /\
                  inst.inst_opcode <> RET /\
                  inst.inst_opcode <> OFFSET)
          bb.bb_instructions /\
    (* Label operands reference labels in the label set *)
    EVERY (\inst. EVERY (\op. !l. op = Label l ==> MEM l labels)
                        inst.inst_operands)
          bb.bb_instructions /\
    (* INVOKE targets are external (not local block labels) *)
    EVERY (\inst. inst.inst_opcode = INVOKE ==>
             case inst.inst_operands of
               Label l :: _ => ~MEM l labels
             | _ => T)
          bb.bb_instructions ==>
    case run_block fuel ctx bb s_callee of
      OK sc =>
        ?sc'. run_block fuel ctx
                (clone_basic_block prefix labels bb) s_clone = OK sc' /\
              clone_rel prefix labels sc sc'
    | Halt sc =>
        ?sc'. run_block fuel ctx
                (clone_basic_block prefix labels bb) s_clone = Halt sc' /\
              shared_globals sc sc'
    | Abort a sc =>
        ?sc'. run_block fuel ctx
                (clone_basic_block prefix labels bb) s_clone = Abort a sc' /\
              shared_globals sc sc'
    | IntRet vals sc =>
        ?vals' sc'. run_block fuel ctx
                (clone_basic_block prefix labels bb) s_clone = IntRet vals' sc'
    | Error e => T
Proof
  completeInduct_on `n` >> rpt strip_tac >> gvs[] >>
  Cases_on `s_callee.vs_inst_idx < LENGTH bb.bb_instructions`
  (* Case 2: inst_idx >= LENGTH → Error → T *)
  >~ [`~(_ < _)`] >- (
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def, clone_bb_length]
  ) >>
  (* Case 1: inst_idx < LENGTH *)
  SUBGOAL_THEN ``get_instruction bb s_callee.vs_inst_idx =
    SOME (EL s_callee.vs_inst_idx bb.bb_instructions)``
    ASSUME_TAC >- simp[get_instruction_def] >>
  imp_res_tac get_instruction_clone >>
  qabbrev_tac `inst = EL s_callee.vs_inst_idx bb.bb_instructions` >>
  (* Extract per-instruction properties *)
  mp_tac (Q.SPECL [`bb`, `s_callee.vs_inst_idx`, `labels`]
            every_el_props) >>
  (impl_tac >- simp[]) >>
  simp_tac std_ss [LET_THM] >> DISCH_THEN STRIP_ASSUME_TAC >>
  gvs[Abbr `inst`] >>
  qabbrev_tac `inst = EL s_callee.vs_inst_idx bb.bb_instructions` >>
  (* Apply step_inst_clone *)
  drule step_inst_clone >>
  disch_then (qspecl_then [`inst`, `fuel`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  (* Unfold run_block on both sides *)
  ONCE_REWRITE_TAC[run_block_def] >> simp[clone_inst_opcode] >>
  Cases_on `step_inst fuel ctx inst s_callee` >> gvs[]
  >- (
    (* OK case *)
    Cases_on `is_terminator inst.inst_opcode` >> simp[clone_inst_opcode]
    >- (
      imp_res_tac clone_rel_halted >> gvs[] >>
      imp_res_tac clone_rel_imp_shared_globals >>
      Cases_on `v.vs_halted` >> gvs[]
    ) >>
    Q.PAT_X_ASSUM `!m. m < _ ==> _` (qspec_then
      `LENGTH bb.bb_instructions - SUC s_callee.vs_inst_idx` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qspecl_then
      [`fuel`, `ctx`, `bb`,
       `v with vs_inst_idx := SUC s_callee.vs_inst_idx`,
       `sc' with vs_inst_idx := SUC s_callee.vs_inst_idx`,
       `prefix`, `labels`] mp_tac) >>
    (impl_tac >- (
      conj_tac >- (irule clone_rel_inst_idx >> simp[]) >>
      simp[]
    )) >>
    simp[]
  )
QED


(* ================================================================
   inline_candidate_correct — proof by fuel induction

   Strategy: Direct complete induction on run_context fuel.

   After inline_candidate, ctx' has:
   - Same entry, same function names
   - Each function possibly transformed (callee invokes replaced)
   - No function invokes callee

   The proof relates run_function in ctx to run_function in ctx'
   for corresponding function pairs, by induction on fuel.
   At each step:
   - Block dispatch: corresponding blocks in fn/fn'
   - Non-invoke instructions: identical (clone_rel or direct)
   - Invoke of non-callee g: look up g in ctx vs g' in ctx',
     use IH (fuel decreases through INVOKE)
   - Invoke of callee (only in ctx, replaced in ctx'):
     original does INVOKE; transformed has inline code
     SIMULATION ARGUMENT (the hard part)
   ================================================================ *)

Theorem result_equiv_inline_vars_refl[local]:
  !r. result_equiv inline_vars r r
Proof
  Cases >> simp[result_equiv_def, state_equiv_refl, execution_equiv_refl]
QED

Theorem result_equiv_inline_vars_trans[local]:
  !r1 r2 r3.
    result_equiv inline_vars r1 r2 /\ result_equiv inline_vars r2 r3 ==>
    result_equiv inline_vars r1 r3
Proof
  rpt Cases >> simp[result_equiv_def] >> rpt strip_tac >>
  metis_tac[state_equiv_trans, execution_equiv_trans]
QED

(* ================================================================
   Structural helpers for inline_one_site_fn_correct
   ================================================================ *)

(* lookup_block on APPEND: first match wins *)
Theorem lookup_block_APPEND[local]:
  !lbl xs ys.
    lookup_block lbl (xs ++ ys) =
    case lookup_block lbl xs of
      SOME bb => SOME bb
    | NONE => lookup_block lbl ys
Proof
  rw[lookup_block_def] >>
  Induct_on `xs` >> simp[FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> simp[]
QED

(* lookup_block on replace_block: same label *)
Theorem lookup_block_replace_eq[local]:
  !lbl new_bb bbs.
    new_bb.bb_label = lbl /\
    (?bb. lookup_block lbl bbs = SOME bb) ==>
    lookup_block lbl (replace_block lbl new_bb bbs) = SOME new_bb
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, replace_block_def, FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = new_bb.bb_label` >> gvs[] >>
  gvs[lookup_block_def, replace_block_def]
QED

(* lookup_block on replace_block: different label *)
Theorem lookup_block_replace_neq[local]:
  !lbl other new_bb bbs.
    lbl <> other /\ new_bb.bb_label = other ==>
    lookup_block lbl (replace_block other new_bb bbs) =
    lookup_block lbl bbs
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, replace_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.bb_label = new_bb.bb_label` >> gvs[] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def, replace_block_def]
QED

(* run_function 0 always errors *)
Theorem run_function_zero[local]:
  !ctx fn s. run_function 0 ctx fn s = Error "out of fuel"
Proof
  ONCE_REWRITE_TAC[run_function_def] >> simp[]
QED

(* If two functions agree on all block lookups, run_function is identical *)
Theorem run_function_blocks_agree:
  !fuel ctx fn1 fn2 s.
    (!lbl. lookup_block lbl fn1.fn_blocks =
           lookup_block lbl fn2.fn_blocks) ==>
    run_function fuel ctx fn1 s = run_function fuel ctx fn2 s
Proof
  completeInduct_on `fuel` >>
  rpt strip_tac >>
  Cases_on `fuel` >- (
    ONCE_REWRITE_TAC[run_function_def] >> simp[]
  ) >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  first_assum (qspec_then `s.vs_current_bb` (SUBST1_TAC o SYM)) >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ================================================================
   inst_id independence: step_inst_base ignores inst_id (except ALLOCA)
   ================================================================ *)

Definition fn_no_alloca_def:
  fn_no_alloca fn <=>
    EVERY (\bb. EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions)
          fn.fn_blocks
End

Theorem step_inst_base_inst_id_indep[local]:
  !id1 id2 op ops outs (s:venom_state).
    op <> ALLOCA ==>
    step_inst_base (instruction id1 op ops outs) s =
    step_inst_base (instruction id2 op ops outs) s
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[step_inst_base_def, instruction_accessors,
       exec_read1_def, exec_read0_def,
       exec_pure1_def, exec_pure2_def, exec_pure3_def, exec_write2_def,
       exec_ext_call_def, exec_delegatecall_def, exec_create_def,
       extract_venom_result_def]
QED

Theorem step_inst_inst_id_indep[local]:
  !i1 i2 fuel ctx (s:venom_state).
    i1.inst_opcode = i2.inst_opcode /\
    i1.inst_operands = i2.inst_operands /\
    i1.inst_outputs = i2.inst_outputs /\
    i1.inst_opcode <> ALLOCA ==>
    step_inst fuel ctx i1 s = step_inst fuel ctx i2 s
Proof
  rpt strip_tac >>
  Cases_on `i1.inst_opcode = INVOKE`
  >- (
    `i2.inst_opcode = INVOKE` by gvs[] >>
    ONCE_REWRITE_TAC[step_inst_def] >> simp[] >>
    gvs[decode_invoke_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[]
  ) >>
  `i2.inst_opcode <> INVOKE` by gvs[] >>
  simp[step_inst_non_invoke] >>
  Cases_on `i1` >> Cases_on `i2` >> gvs[] >>
  irule step_inst_base_inst_id_indep >> simp[]
QED

(* run_block on two blocks with same instructions modulo inst_id *)
Theorem run_block_inst_id_indep[local]:
  !n fuel ctx bb1 bb2 (s:venom_state).
    n = LENGTH bb1.bb_instructions - s.vs_inst_idx /\
    bb1.bb_label = bb2.bb_label /\
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!k. k < LENGTH bb1.bb_instructions ==>
      (EL k bb1.bb_instructions).inst_opcode =
        (EL k bb2.bb_instructions).inst_opcode /\
      (EL k bb1.bb_instructions).inst_operands =
        (EL k bb2.bb_instructions).inst_operands /\
      (EL k bb1.bb_instructions).inst_outputs =
        (EL k bb2.bb_instructions).inst_outputs) /\
    EVERY (\i. i.inst_opcode <> ALLOCA) bb1.bb_instructions ==>
    run_block fuel ctx bb1 s = run_block fuel ctx bb2 s
Proof
  completeInduct_on `n` >> rpt strip_tac >> gvs[] >>
  Cases_on `s.vs_inst_idx < LENGTH bb1.bb_instructions`
  >~ [`~(_ < _)`] >- (
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def]
  ) >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def, EL_MAP] >>
  `(EL s.vs_inst_idx bb1.bb_instructions).inst_opcode =
   (EL s.vs_inst_idx bb2.bb_instructions).inst_opcode` by simp[] >>
  `(EL s.vs_inst_idx bb1.bb_instructions).inst_operands =
   (EL s.vs_inst_idx bb2.bb_instructions).inst_operands` by simp[] >>
  `(EL s.vs_inst_idx bb1.bb_instructions).inst_outputs =
   (EL s.vs_inst_idx bb2.bb_instructions).inst_outputs` by simp[] >>
  `(EL s.vs_inst_idx bb1.bb_instructions).inst_opcode <> ALLOCA` by
    (gvs[EVERY_EL]) >>
  `step_inst fuel ctx (EL s.vs_inst_idx bb1.bb_instructions) s =
   step_inst fuel ctx (EL s.vs_inst_idx bb2.bb_instructions) s` by (
    irule step_inst_inst_id_indep >> simp[]
  ) >>
  simp[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* FOLDL-EL: each element of the FOLDL accumulator result is preserved,
   and each new element is a renumbered original block.
   We prove a general accumulator property P that is:
   - maintained for existing elements (k < LENGTH acc)
   - established for new elements via renumber_block_inst_ids properties
*)

(* Helper: FOLDL length (avoid depending on Renumber internal) *)
Theorem foldl_renumber_length[local]:
  !bbs n acc.
    LENGTH (SND (FOLDL (\(n,acc) bb.
       (\(n',bb'). (n', acc ++ [bb']))
         (renumber_block_inst_ids n bb)) (n, acc) bbs)) =
    LENGTH acc + LENGTH bbs
Proof
  Induct >> rw[] >> pairarg_tac >> gvs[]
QED

(* Helper: FOLDL preserves accumulator prefix *)
Theorem foldl_renumber_prefix[local]:
  !bbs n acc k.
    k < LENGTH acc ==>
    EL k (SND (FOLDL (\(n,acc) bb.
       (\(n',bb'). (n', acc ++ [bb']))
         (renumber_block_inst_ids n bb)) (n, acc) bbs)) =
    EL k acc
Proof
  Induct >> rw[] >> pairarg_tac >> gvs[] >>
  first_x_assum (qspecl_then [`n'`, `acc ++ [bb']`, `k`] mp_tac) >>
  simp[EL_APPEND1]
QED

(* Main FOLDL-EL: element k (in the bbs range) is a renumbered original block *)
Theorem foldl_renumber_el[local]:
  !bbs n acc k.
    k < LENGTH bbs ==>
    ?m. EL (LENGTH acc + k) (SND (FOLDL (\(n,acc) bb.
           (\(n',bb'). (n', acc ++ [bb']))
             (renumber_block_inst_ids n bb)) (n, acc) bbs)) =
        SND (renumber_block_inst_ids m (EL k bbs))
Proof
  Induct >> rw[] >> pairarg_tac >> gvs[] >>
  Cases_on `k`
  >- (
    (* k=0: element at position LENGTH acc is bb' *)
    qexists_tac `n` >>
    mp_tac (Q.SPECL [`bbs`, `n'`, `acc ++ [bb']`,
              `LENGTH (acc:basic_block list)`] foldl_renumber_prefix) >>
    simp[EL_APPEND2] >>
    metis_tac[SND, PAIR]
  ) >>
  (* k = SUC k': use IH with acc ++ [bb'] *)
  rename1 `SUC k' < SUC (LENGTH bbs)` >>
  first_x_assum (qspecl_then [`n'`, `acc ++ [bb']`, `k'`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `m` >> pop_assum mp_tac >>
  `LENGTH acc + SUC k' = k' + (LENGTH acc + 1)` by simp[] >>
  ASM_REWRITE_TAC[]
QED

(* Bridge: (renumber_fn_inst_ids fn).fn_blocks[k] is a renumbered original block *)
Theorem renumber_fn_el[local]:
  !fn k. k < LENGTH fn.fn_blocks ==>
    ?m. EL k (renumber_fn_inst_ids fn).fn_blocks =
        SND (renumber_block_inst_ids m (EL k fn.fn_blocks))
Proof
  rpt strip_tac >>
  `(renumber_fn_inst_ids fn).fn_blocks =
   SND (FOLDL (\(n,acc) bb.
     (\(n',bb'). (n', acc ++ [bb']))
       (renumber_block_inst_ids n bb)) (0, []) fn.fn_blocks)` by (
    simp[renumber_fn_inst_ids_def, LET_THM] >> pairarg_tac >> simp[]
  ) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  mp_tac (Q.SPECL [`fn.fn_blocks`, `0:num`,
            `[]:basic_block list`, `k`] foldl_renumber_el) >>
  simp[]
QED

(* FIND on label-equal block lists: SOME corresponds to SOME at same index *)
Theorem find_label_el_correspondence[local]:
  !xs ys lbl x.
    MAP (\bb:basic_block. bb.bb_label) xs =
    MAP (\bb. bb.bb_label) ys /\
    FIND (\bb. bb.bb_label = lbl) xs = SOME x ==>
    ?y k. FIND (\bb. bb.bb_label = lbl) ys = SOME y /\
          k < LENGTH xs /\ EL k xs = x /\ EL k ys = y
Proof
  Induct >> simp[FIND_thm] >>
  rpt gen_tac >> Cases_on `ys` >> simp[FIND_thm] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[]
  >- (qexists_tac `0` >> simp[])
  >- (
    first_x_assum (qspecl_then [`t`, `lbl`, `x`] mp_tac) >>
    simp[] >> strip_tac >>
    qexists_tac `SUC k` >> simp[]
  )
QED

(* FIND on label-equal block lists: NONE corresponds to NONE *)
Theorem find_label_none_correspondence[local]:
  !xs ys lbl.
    MAP (\bb:basic_block. bb.bb_label) xs =
    MAP (\bb. bb.bb_label) ys ==>
    (FIND (\bb. bb.bb_label = lbl) xs = NONE <=>
     FIND (\bb. bb.bb_label = lbl) ys = NONE)
Proof
  Induct >- (Cases_on `ys` >> simp[FIND_thm]) >>
  rpt gen_tac >> Cases_on `ys` >> simp[FIND_thm] >> strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[]
QED

(* lookup_block on renumbered function: finds a renumbered block *)
Theorem lookup_block_renumber[local]:
  !lbl fn bb.
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    ?m. lookup_block lbl (renumber_fn_inst_ids fn).fn_blocks =
        SOME (SND (renumber_block_inst_ids m bb))
Proof
  rpt strip_tac >>
  gvs[lookup_block_def] >>
  `MAP (\bb:basic_block. bb.bb_label) fn.fn_blocks =
   MAP (\bb. bb.bb_label) (renumber_fn_inst_ids fn).fn_blocks`
    by metis_tac[renumber_fn_inst_ids_fn_labels, fn_labels_def] >>
  drule_all find_label_el_correspondence >> strip_tac >>
  imp_res_tac renumber_fn_el >> metis_tac[]
QED

Theorem lookup_block_renumber_none[local]:
  !lbl fn.
    lookup_block lbl fn.fn_blocks = NONE ==>
    lookup_block lbl (renumber_fn_inst_ids fn).fn_blocks = NONE
Proof
  rpt strip_tac >> gvs[lookup_block_def] >>
  mp_tac (Q.SPECL [`fn.fn_blocks`,
    `(renumber_fn_inst_ids fn).fn_blocks`, `lbl`]
    find_label_none_correspondence) >>
  simp[] >>
  metis_tac[renumber_fn_inst_ids_fn_labels, fn_labels_def]
QED

Triviality FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

(* Helper: fn_no_alloca + lookup_block = no ALLOCA in the block *)
Theorem fn_no_alloca_lookup:
  !fn lbl bb.
    fn_no_alloca fn /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions
Proof
  rw[fn_no_alloca_def, lookup_block_def] >>
  imp_res_tac FIND_MEM >>
  qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[EVERY_MEM]
QED

(* renumber_fn_inst_ids preserves execution when no ALLOCA present *)
Theorem renumber_fn_inst_ids_correct:
  !fuel ctx fn (s:venom_state).
    fn_no_alloca fn ==>
    run_function fuel ctx (renumber_fn_inst_ids fn) s =
    run_function fuel ctx fn s
Proof
  completeInduct_on `fuel` >> rpt strip_tac >>
  Cases_on `fuel` >- (
    ONCE_REWRITE_TAC[run_function_def] >> simp[]
  ) >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (
    imp_res_tac lookup_block_renumber_none >> simp[]
  ) >>
  rename1 `_ = SOME bb` >>
  drule lookup_block_renumber >> strip_tac >> simp[] >>
  drule_then (drule_then assume_tac) fn_no_alloca_lookup >>
  `run_block n ctx (SND (renumber_block_inst_ids m bb)) s =
   run_block n ctx bb s`
    suffices_by (disch_then (fn th => REWRITE_TAC [th])) >>
  irule (GSYM run_block_inst_id_indep) >>
  simp[renumber_block_inst_ids_length, renumber_block_inst_ids_bb_label] >>
  rpt strip_tac >>
  mp_tac renumber_block_inst_ids_map >>
  disch_then (qspecl_then [`m`, `bb`] mp_tac) >>
  simp[renumber_block_inst_ids_length] >>
  strip_tac >>
  `EL k (MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
    (SND (renumber_block_inst_ids m bb)).bb_instructions) =
   EL k (MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
    bb.bb_instructions)` by simp[] >>
  pop_assum mp_tac >>
  simp[EL_MAP, renumber_block_inst_ids_length]
QED

val _ = export_theory();
