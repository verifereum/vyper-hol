(*
 * Pointer-safe runs
 *
 * ptr_safe_run D lo fuel ctx fn PG G tn s says that every instruction the
 * run of fn from s executes, in callee frames too, satisfies ptr_inst_ok
 * with the ghost provenance G and taint tn that frame_reachable gives it:
 * ptr_discipline's per-state conjunct, and taint_within's bounds at call
 * requests and at the halt.  The check follows the runner's own recursion
 * (step_inst, exec_block, run_blocks) and threads the ghost as
 * frame_reachable does.  After an INVOKE the caller goes on with the taint
 * its callee returned with, which ghost_blocks computes along the callee's
 * run.
 *
 * TOP-LEVEL:
 *   ghost_step, ghost_block, ghost_blocks
 *                         — the ghost along step_inst, exec_block and
 *                           run_blocks: the ghost after a step, and the
 *                           ghost at the instruction a function's run
 *                           returns or stops at
 *   ptr_inst_ok           — the check at one instruction
 *   ptr_safe_step, ptr_safe_block, ptr_safe_blocks
 *                         — the check along step_inst, exec_block and
 *                           run_blocks
 *   ptr_safe_run          — the check from inside a block
 *   ghost_run, block_run, frame_run
 *                         — the ghost and the run from inside a block
 *   *_step, *_terminator, *_block(s)_block, ptr_safe_step_invoke, ...
 *                         — unfolding
 *   ghost_fuel_mono_up, ghost_run_fuel_mono_up
 *                         — more fuel, when the run does not fail, ends
 *                           with the same ghost
 *   ptr_safe_fuel_mono_down, ptr_safe_run_fuel_mono_down,
 *   ptr_safe_fuel_mono_up, ptr_safe_blocks_all_fuel
 *                         — as for memSafeRun
 *   frames_ok, ptr_point  — what a frame_reachable state on a safe run
 *                           carries: its own run and each caller's run
 *                           after it returns are safe
 *   ptr_safe_ptr_discipline
 *                         — the bridge: a safe entry run gives
 *                           ptr_discipline and taint_within
 *)

Theory ptrSafeRun
Ancestors
  list finite_map venomExecSemantics venomExecProofs venomInstProofs
  venomInst venomState contextCodegenRel contextCodegenRelProps
  ptrDiscipline

(* Whole-block source continuation retains the original entry root. *)
Theorem frame_reachable_exec_block_successor:
  !s inst G tn t u j.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    frame_reachable vs ctx [] [] G tn fn inst s /\
    exec_block fuel ctx bb s = OK t /\ ~t.vs_halted /\
    enters_block fn t u /\ active_inst fn j u ==>
    ?G' tn'. frame_reachable vs ctx [] [] G' tn' fn j u
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  `active_inst fn inst s` by
    (irule lookup_instruction_active >> metis_tac[]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK mid` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
      drule_all frame_reachable_block >> metis_tac[]) >>
  simp[] >> strip_tac >>
  Cases_on `get_instruction bb (SUC s.vs_inst_idx)`
  >- (qpat_x_assum `exec_block _ _ _ (_ with vs_inst_idx := _) = _` mp_tac >>
      once_rewrite_tac[exec_block_def] >> simp[]) >>
  rename1 `get_instruction bb (SUC s.vs_inst_idx) = SOME next` >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `active_inst fn next (mid with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule lookup_instruction_active >> simp[] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by
    (gvs[get_instruction_def, AllCaseEqs(), EVERY_EL] >> metis_tac[]) >>
  `?G1 tn1. frame_reachable vs ctx [] [] G1 tn1 fn next
      (mid with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[frame_reachable_next] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (gvs[get_instruction_def, AllCaseEqs()] >> decide_tac)) >>
  disch_then (qspec_then `mid with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >> metis_tac[]
QED

(* ===== The ghost along a run ===== *)

(* ghost_step is the ghost after a step: frame_reachable's next rule, or,
   for an INVOKE, its ret rule with the taint the callee returns with.
   ghost_block and ghost_blocks give the ghost at the instruction where the
   function's run stops: the one that returns (IntRet), halts, aborts or
   fails.  A block's ghost is the ghost past its PHIs: entry_prov and
   entry_taint_vars apply when a terminator enters the next block, and a
   callee starts with frame_reachable's call-rule ghost. *)
Definition ghost_defs:
  (ghost_step fuel ctx PG G (tn:taint) inst s =
    if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => (G, tn)
      | SOME (nm, ops) =>
          case lookup_function nm ctx.ctx_functions of
            NONE => (G, tn)
          | SOME callee =>
              case eval_operands ops s of
                NONE => (G, tn)
              | SOME args =>
                  case setup_callee callee args s of
                    NONE => (G, tn)
                  | SOME cs =>
                      (DRESTRICT G (COMPL (set inst.inst_outputs)),
                       SND (ghost_blocks fuel ctx callee (MAP (op_prov G) ops)
                              FEMPTY (tn with t_var := FEMPTY) cs)
                         with t_var :=
                           DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
    else
      case step_inst fuel ctx inst s of
        OK s' => (step_prov PG G inst s', step_taint inst s s' tn)
      | _ => (G, tn))
  /\
  (ghost_block fuel ctx fn PG G tn bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => (G, tn)
    | SOME inst =>
        case step_inst fuel ctx inst s of
          OK s' =>
            if is_terminator inst.inst_opcode then
              (if s'.vs_halted then (G, tn)
               else ghost_blocks fuel ctx fn PG (entry_prov fn s' G)
                      (entry_taint_vars fn s' tn) s')
            else
              ghost_block fuel ctx fn PG
                (FST (ghost_step fuel ctx PG G tn inst s))
                (SND (ghost_step fuel ctx PG G tn inst s)) bb
                (s' with vs_inst_idx := SUC s.vs_inst_idx)
        | _ => (G, tn))
  /\
  (ghost_blocks fuel ctx fn PG G tn s =
    case fuel of
      0 => (G, tn)
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => (G, tn)
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              OK s_phi =>
                ghost_block fuel' ctx fn PG G tn bb
                  (s_phi with vs_inst_idx :=
                     phi_prefix_length bb.bb_instructions)
            | _ => (G, tn))
Termination
  qexists_tac `inv_image ($< LEX $<)
    (\x. case x of
      | INL (fuel, ctx, PG, G, tn, inst, s) => (fuel, 1)
      | INR (INL (fuel, ctx, fn, PG, G, tn, bb, s)) =>
          (fuel, 2 + (LENGTH bb.bb_instructions - s.vs_inst_idx))
      | INR (INR (fuel, ctx, fn, PG, G, tn, s)) => (fuel, 0))` >>
  conj_tac >-
    (irule relationTheory.WF_inv_image >>
     MATCH_ACCEPT_TAC (MATCH_MP pairTheory.WF_LEX
       (CONJ prim_recTheory.WF_LESS prim_recTheory.WF_LESS))) >>
  simp_tac bool_ss [relationTheory.inv_image_thm, sumTheory.sum_case_def,
    pairTheory.pair_case_def, pairTheory.LEX_DEF_THM] >>
  rpt strip_tac >> gvs[get_instruction_def]
End

val ghost_step_def = save_thm("ghost_step_def", cj 1 ghost_defs);
val ghost_block_def = save_thm("ghost_block_def", cj 2 ghost_defs);
val ghost_blocks_def = save_thm("ghost_blocks_def", cj 3 ghost_defs);

(* ===== The check ===== *)

(* ptr_discipline's per-state conjunct, and taint_within's bounds where a
   step adds a call request and where it halts. *)
Definition ptr_inst_ok_def:
  ptr_inst_ok (D:dead) lo fuel ctx fn G tn inst s <=>
    access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (inst.inst_opcode <> INVOKE ==>
     (!s'. step_inst fuel ctx inst s = OK s' /\
           LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
           tn.t_stor SUBSET
             D.d_stor s.vs_call_ctx.cc_address
               (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
           tn.t_trans SUBSET
             D.d_trans s.vs_call_ctx.cc_address
               (s.vs_transient s.vs_call_ctx.cc_address)) /\
     (!s_h. step_inst fuel ctx inst s = Halt s_h ==>
            (step_taint inst s s_h tn).t_stor SUBSET
              D.d_stor s_h.vs_call_ctx.cc_address
                (s_h.vs_accounts s_h.vs_call_ctx.cc_address).storage /\
            (step_taint inst s s_h tn).t_trans SUBSET
              D.d_trans s_h.vs_call_ctx.cc_address
                (s_h.vs_transient s_h.vs_call_ctx.cc_address) /\
            (step_taint inst s s_h tn).t_imm SUBSET
              D.d_imm s_h.vs_immutables /\
            ret_taint tn inst s SUBSET D.d_ret s_h.vs_returndata))
End

(* The check along the runner, with the ghost: ptr_safe_step checks an
   instruction and, for an INVOKE, the callee's run; ptr_safe_block every
   instruction exec_block runs and, past a terminator that enters a block,
   the run of the blocks after it; ptr_safe_blocks a run from a block's
   entry.  Where the run stops the check stops too. *)
Definition ptr_safe_defs:
  (ptr_safe_step D lo fuel ctx fn PG G tn inst s <=>
    ptr_inst_ok D lo fuel ctx fn G tn inst s /\
    if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => T
      | SOME (nm, ops) =>
          case lookup_function nm ctx.ctx_functions of
            NONE => T
          | SOME callee =>
              case eval_operands ops s of
                NONE => T
              | SOME args =>
                  case setup_callee callee args s of
                    NONE => T
                  | SOME cs =>
                      ptr_safe_blocks D lo fuel ctx callee
                        (MAP (op_prov G) ops) FEMPTY
                        (tn with t_var := FEMPTY) cs
    else T)
  /\
  (ptr_safe_block D lo fuel ctx fn PG G tn bb s <=>
    case get_instruction bb s.vs_inst_idx of
      NONE => T
    | SOME inst =>
        ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
        case step_inst fuel ctx inst s of
          OK s' =>
            if is_terminator inst.inst_opcode then
              (s'.vs_halted \/
               ptr_safe_blocks D lo fuel ctx fn PG (entry_prov fn s' G)
                 (entry_taint_vars fn s' tn) s')
            else
              ptr_safe_block D lo fuel ctx fn PG
                (FST (ghost_step fuel ctx PG G tn inst s))
                (SND (ghost_step fuel ctx PG G tn inst s)) bb
                (s' with vs_inst_idx := SUC s.vs_inst_idx)
        | _ => T)
  /\
  (ptr_safe_blocks D lo fuel ctx fn PG G tn s <=>
    case fuel of
      0 => T
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => T
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              OK s_phi =>
                ptr_safe_block D lo fuel' ctx fn PG G tn bb
                  (s_phi with vs_inst_idx :=
                     phi_prefix_length bb.bb_instructions)
            | _ => T)
Termination
  qexists_tac `inv_image ($< LEX $<)
    (\x. case x of
      | INL (D, lo, fuel, ctx, fn, PG, G, tn, inst, s) => (fuel, 1)
      | INR (INL (D, lo, fuel, ctx, fn, PG, G, tn, bb, s)) =>
          (fuel, 2 + (LENGTH bb.bb_instructions - s.vs_inst_idx))
      | INR (INR (D, lo, fuel, ctx, fn, PG, G, tn, s)) => (fuel, 0))` >>
  conj_tac >-
    (irule relationTheory.WF_inv_image >>
     MATCH_ACCEPT_TAC (MATCH_MP pairTheory.WF_LEX
       (CONJ prim_recTheory.WF_LESS prim_recTheory.WF_LESS))) >>
  simp_tac bool_ss [relationTheory.inv_image_thm, sumTheory.sum_case_def,
    pairTheory.pair_case_def, pairTheory.LEX_DEF_THM] >>
  rpt strip_tac >> gvs[get_instruction_def]
End

val ptr_safe_step_def = save_thm("ptr_safe_step_def", cj 1 ptr_safe_defs);
val ptr_safe_block_def = save_thm("ptr_safe_block_def", cj 2 ptr_safe_defs);
val ptr_safe_blocks_def = save_thm("ptr_safe_blocks_def", cj 3 ptr_safe_defs);

(* The check from inside a block: the rest of the current block, and the
   blocks after it. *)
Definition ptr_safe_run_def:
  ptr_safe_run D lo fuel ctx fn PG G tn s <=>
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => T
    | SOME bb => ptr_safe_block D lo fuel ctx fn PG G tn bb s
End

(* The ghost where the run from inside a block stops. *)
Definition ghost_run_def:
  ghost_run fuel ctx fn PG G tn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => (G, tn)
    | SOME bb => ghost_block fuel ctx fn PG G tn bb s
End

(* run_from's run, as two steps: the rest of a block, then the blocks after
   it. *)
Definition block_run_def:
  block_run fuel ctx fn bb s =
    case exec_block fuel ctx bb s of
      OK s' => if s'.vs_halted then Halt s' else run_blocks fuel ctx fn s'
    | r => r
End

Definition frame_run_def:
  frame_run fuel ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => Error "block not found"
    | SOME bb => block_run fuel ctx fn bb s
End

(* ===== Unfolding ===== *)

Theorem step_inst_non_invoke_fuel:
  !f1 f2 ctx inst s.
    inst.inst_opcode <> INVOKE ==>
    step_inst f1 ctx inst s = step_inst f2 ctx inst s
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC [step_inst_def] >> simp[]
QED

Theorem step_inst_intret_not_invoke:
  !fuel ctx inst s ret s'.
    step_inst fuel ctx inst s = IntRet ret s' ==> inst.inst_opcode <> INVOKE
Proof
  rpt gen_tac >> ONCE_REWRITE_TAC [step_inst_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  BasicProvers.every_case_tac >> simp[]
QED

Theorem run_blocks_block_run:
  !fuel ctx fn s bb s_phi.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi ==>
    run_blocks (SUC fuel) ctx fn s =
    block_run fuel ctx fn bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >> simp[Once run_blocks_def, block_run_def] >>
  BasicProvers.every_case_tac >> simp[]
QED

Theorem block_run_step:
  !fuel ctx fn bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    block_run fuel ctx fn bb s =
    block_run fuel ctx fn bb (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `exec_block fuel ctx bb s =
   exec_block fuel ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >> simp[]) >>
  simp[block_run_def]
QED

Theorem block_run_terminator:
  !fuel ctx fn bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\ is_terminator inst.inst_opcode /\
    ~s'.vs_halted ==>
    block_run fuel ctx fn bb s = run_blocks fuel ctx fn s'
Proof
  rpt strip_tac >>
  `exec_block fuel ctx bb s = OK s'` by simp[Once exec_block_def] >>
  simp[block_run_def]
QED

Theorem block_run_head:
  !fuel ctx fn bb s inst.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    (!e. block_run fuel ctx fn bb s <> Error e) ==>
    !e. step_inst fuel ctx inst s <> Error e
Proof
  rpt strip_tac >>
  `exec_block fuel ctx bb s = Error e` by simp[Once exec_block_def] >>
  gvs[block_run_def]
QED

Theorem block_run_fuel_mono:
  !n m ctx fn bb s.
    (!e. block_run n ctx fn bb s <> Error e) /\ n <= m ==>
    block_run m ctx fn bb s = block_run n ctx fn bb s
Proof
  rpt strip_tac >>
  `!e. exec_block n ctx bb s <> Error e` by
    (rpt strip_tac >> gvs[block_run_def]) >>
  `exec_block m ctx bb s = exec_block n ctx bb s` by
    metis_tac[cj 2 fuel_mono] >>
  simp[block_run_def] >>
  Cases_on `exec_block n ctx bb s` >> gvs[block_run_def] >> rw[] >>
  gvs[] >> metis_tac[cj 3 fuel_mono]
QED

Theorem frame_run_fuel_mono:
  !n m ctx fn s.
    (!e. frame_run n ctx fn s <> Error e) /\ n <= m ==>
    frame_run m ctx fn s = frame_run n ctx fn s
Proof
  rw[frame_run_def] >> Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  gvs[] >> metis_tac[block_run_fuel_mono]
QED

Theorem ghost_step_non_invoke:
  !fuel ctx PG G tn inst s s'.
    inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' ==>
    ghost_step fuel ctx PG G tn inst s =
    (step_prov PG G inst s', step_taint inst s s' tn)
Proof
  rw[Once ghost_step_def]
QED

Theorem ghost_step_invoke:
  !fuel ctx PG G tn inst s nm ops callee args cs.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
    ghost_step fuel ctx PG G tn inst s =
    (DRESTRICT G (COMPL (set inst.inst_outputs)),
     SND (ghost_blocks fuel ctx callee (MAP (op_prov G) ops) FEMPTY
            (tn with t_var := FEMPTY) cs)
       with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
Proof
  rw[Once ghost_step_def]
QED

Theorem ghost_block_step:
  !fuel ctx fn PG G tn bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    ghost_block fuel ctx fn PG G tn bb s =
    ghost_block fuel ctx fn PG (FST (ghost_step fuel ctx PG G tn inst s))
      (SND (ghost_step fuel ctx PG G tn inst s)) bb
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rw[Once ghost_block_def]
QED

Theorem ghost_block_terminator:
  !fuel ctx fn PG G tn bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\ is_terminator inst.inst_opcode /\
    ~s'.vs_halted ==>
    ghost_block fuel ctx fn PG G tn bb s =
    ghost_blocks fuel ctx fn PG (entry_prov fn s' G)
      (entry_taint_vars fn s' tn) s'
Proof
  rw[Once ghost_block_def]
QED

Theorem ghost_block_intret:
  !fuel ctx fn PG G tn bb s inst ret s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = IntRet ret s' ==>
    ghost_block fuel ctx fn PG G tn bb s = (G, tn)
Proof
  rw[Once ghost_block_def]
QED

Theorem ghost_blocks_block:
  !fuel ctx fn PG G tn s bb s_phi.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi ==>
    ghost_blocks (SUC fuel) ctx fn PG G tn s =
    ghost_block fuel ctx fn PG G tn bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rw[Once ghost_blocks_def]
QED

Theorem ptr_safe_block_head:
  !D lo fuel ctx fn PG G tn bb s inst.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ptr_safe_block D lo fuel ctx fn PG G tn bb s ==>
    ptr_safe_step D lo fuel ctx fn PG G tn inst s
Proof
  rw[Once ptr_safe_block_def] >> gvs[]
QED

Theorem ptr_safe_block_step:
  !D lo fuel ctx fn PG G tn bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    (ptr_safe_block D lo fuel ctx fn PG G tn bb s <=>
     ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
     ptr_safe_block D lo fuel ctx fn PG
       (FST (ghost_step fuel ctx PG G tn inst s))
       (SND (ghost_step fuel ctx PG G tn inst s)) bb
       (s' with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rw[Once ptr_safe_block_def]
QED

Theorem ptr_safe_block_terminator:
  !D lo fuel ctx fn PG G tn bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\ is_terminator inst.inst_opcode /\
    ~s'.vs_halted ==>
    (ptr_safe_block D lo fuel ctx fn PG G tn bb s <=>
     ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
     ptr_safe_blocks D lo fuel ctx fn PG (entry_prov fn s' G)
       (entry_taint_vars fn s' tn) s')
Proof
  rw[Once ptr_safe_block_def]
QED

Theorem ptr_safe_blocks_block:
  !D lo fuel ctx fn PG G tn s bb s_phi.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi ==>
    (ptr_safe_blocks D lo (SUC fuel) ctx fn PG G tn s <=>
     ptr_safe_block D lo fuel ctx fn PG G tn bb
       (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
  rw[Once ptr_safe_blocks_def]
QED

Theorem ptr_safe_step_invoke:
  !D lo fuel ctx fn PG G tn inst s nm ops callee args cs.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
    (ptr_safe_step D lo fuel ctx fn PG G tn inst s <=>
     ptr_inst_ok D lo fuel ctx fn G tn inst s /\
     ptr_safe_blocks D lo fuel ctx callee (MAP (op_prov G) ops) FEMPTY
       (tn with t_var := FEMPTY) cs)
Proof
  rw[Once ptr_safe_step_def]
QED

Theorem ptr_safe_step_inst_ok:
  !D lo fuel ctx fn PG G tn inst s.
    ptr_safe_step D lo fuel ctx fn PG G tn inst s ==>
    ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  rw[Once ptr_safe_step_def]
QED

(* ptr_inst_ok looks at steps other than INVOKE, which take no fuel. *)
Theorem ptr_inst_ok_fuel:
  !D lo f1 f2 ctx fn G tn inst s.
    ptr_inst_ok D lo f1 ctx fn G tn inst s <=>
    ptr_inst_ok D lo f2 ctx fn G tn inst s
Proof
  rw[ptr_inst_ok_def] >> Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  `step_inst f1 ctx inst s = step_inst f2 ctx inst s` by
    metis_tac[step_inst_non_invoke_fuel] >>
  simp[]
QED

(* ===== Fuel ===== *)

(* With more fuel a run that does not fail is the same run, so it ends
   with the same ghost. *)
Theorem ghost_fuel_mono_up:
  (!n ctx PG G tn inst s m.
     (!e. step_inst n ctx inst s <> Error e) /\ n <= m ==>
     ghost_step m ctx PG G tn inst s = ghost_step n ctx PG G tn inst s) /\
  (!n ctx fn PG G tn bb s m.
     (!e. block_run n ctx fn bb s <> Error e) /\ n <= m ==>
     ghost_block m ctx fn PG G tn bb s = ghost_block n ctx fn PG G tn bb s) /\
  (!n ctx fn PG G tn s m.
     (!e. run_blocks n ctx fn s <> Error e) /\ n <= m ==>
     ghost_blocks m ctx fn PG G tn s = ghost_blocks n ctx fn PG G tn s)
Proof
  ho_match_mp_tac ghost_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (qpat_x_assum `!e. step_inst _ _ _ _ <> _` mp_tac >>
          ONCE_REWRITE_TAC [step_inst_def] >>
          simp[Once ghost_step_def, SimpLHS] >>
          simp[Once ghost_step_def, SimpRHS] >>
          BasicProvers.every_case_tac >> simp[] >> rpt strip_tac >> gvs[] >>
          first_x_assum (qspec_then `m` mp_tac) >> simp[]) >>
      `step_inst m ctx inst s = step_inst n ctx inst s` by
        metis_tac[step_inst_non_invoke_fuel] >>
      simp[Once ghost_step_def, SimpLHS] >>
      simp[Once ghost_step_def, SimpRHS])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `get_instruction bb s.vs_inst_idx`
      >- (ONCE_REWRITE_TAC [ghost_block_def] >> simp[]) >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `!e. step_inst n ctx inst s <> Error e` by metis_tac[block_run_head] >>
      `step_inst m ctx inst s = step_inst n ctx inst s` by
        metis_tac[cj 1 fuel_mono] >>
      Cases_on `step_inst n ctx inst s`
      >~ [`step_inst n ctx inst s = OK s'`]
      >- (Cases_on `is_terminator inst.inst_opcode`
          >- (Cases_on `s'.vs_halted`
              >- (ONCE_REWRITE_TAC [ghost_block_def] >> simp[]) >>
              `ghost_block m ctx fn PG G tn bb s =
               ghost_blocks m ctx fn PG (entry_prov fn s' G)
                 (entry_taint_vars fn s' tn) s'` by
                metis_tac[ghost_block_terminator] >>
              `ghost_block n ctx fn PG G tn bb s =
               ghost_blocks n ctx fn PG (entry_prov fn s' G)
                 (entry_taint_vars fn s' tn) s'` by
                metis_tac[ghost_block_terminator] >>
              simp[] >> first_x_assum irule >> simp[] >>
              metis_tac[block_run_terminator]) >>
          `ghost_block m ctx fn PG G tn bb s =
           ghost_block m ctx fn PG (FST (ghost_step m ctx PG G tn inst s))
             (SND (ghost_step m ctx PG G tn inst s)) bb
             (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
            metis_tac[ghost_block_step] >>
          `ghost_block n ctx fn PG G tn bb s =
           ghost_block n ctx fn PG (FST (ghost_step n ctx PG G tn inst s))
             (SND (ghost_step n ctx PG G tn inst s)) bb
             (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
            metis_tac[ghost_block_step] >>
          `ghost_step m ctx PG G tn inst s = ghost_step n ctx PG G tn inst s` by
            (first_x_assum irule >> simp[]) >>
          simp[] >> first_x_assum irule >> simp[] >>
          metis_tac[block_run_step]) >>
      (ONCE_REWRITE_TAC [ghost_block_def] >> simp[])) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `n` >- (ONCE_REWRITE_TAC [run_blocks_def] >> simp[]) >>
  strip_tac >> rename1 `SUC n <= m` >>
  `?m'. m = SUC m' /\ n <= m'` by (Cases_on `m` >> fs[]) >>
  gvs[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (ONCE_REWRITE_TAC [ghost_blocks_def] >> simp[]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis _ _ = OK s_phi` >>
      drule_all ghost_blocks_block >> simp[] >> disch_then kall_tac >>
      first_x_assum irule >> simp[] >>
      metis_tac[run_blocks_block_run]) >>
  (ONCE_REWRITE_TAC [ghost_blocks_def] >> simp[])
QED

Theorem ghost_run_fuel_mono_up:
  !n m ctx fn PG G tn s.
    (!e. frame_run n ctx fn s <> Error e) /\ n <= m ==>
    ghost_run m ctx fn PG G tn s = ghost_run n ctx fn PG G tn s
Proof
  rw[ghost_run_def, frame_run_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  metis_tac[ghost_fuel_mono_up]
QED

(* With less fuel the run is a prefix of the same path. *)
Theorem ptr_safe_fuel_mono_down:
  (!D lo n ctx fn PG G tn inst s m.
     ptr_safe_step D lo m ctx fn PG G tn inst s /\ n <= m ==>
     ptr_safe_step D lo n ctx fn PG G tn inst s) /\
  (!D lo n ctx fn PG G tn bb s m.
     ptr_safe_block D lo m ctx fn PG G tn bb s /\ n <= m ==>
     ptr_safe_block D lo n ctx fn PG G tn bb s) /\
  (!D lo n ctx fn PG G tn s m.
     ptr_safe_blocks D lo m ctx fn PG G tn s /\ n <= m ==>
     ptr_safe_blocks D lo n ctx fn PG G tn s)
Proof
  ho_match_mp_tac ptr_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC [ptr_safe_step_def] >> strip_tac >>
      conj_tac >- metis_tac[ptr_inst_ok_fuel] >>
      Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
      BasicProvers.every_case_tac >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `get_instruction bb s.vs_inst_idx`
      >- simp[Once ptr_safe_block_def] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `ptr_safe_step D lo m ctx fn PG G tn inst s` by
        metis_tac[ptr_safe_block_head] >>
      Cases_on `step_inst n ctx inst s`
      >~ [`step_inst n ctx inst s = OK s'`]
      >- (`step_inst m ctx inst s = OK s'` by
            (qspecl_then [`n`, `m`, `ctx`, `inst`, `s`, `OK s'`] mp_tac
               (cj 1 fuel_mono) >> simp[]) >>
          Cases_on `is_terminator inst.inst_opcode`
          >- (Cases_on `s'.vs_halted`
              >- (simp[Once ptr_safe_block_def] >> metis_tac[]) >>
              qpat_x_assum `ptr_safe_block _ _ m _ _ _ _ _ _ _` mp_tac >>
              ONCE_REWRITE_TAC [ptr_safe_block_def] >> simp[] >>
              metis_tac[]) >>
          `ghost_step m ctx PG G tn inst s = ghost_step n ctx PG G tn inst s` by
            (irule (cj 1 ghost_fuel_mono_up) >> simp[]) >>
          qpat_x_assum `ptr_safe_block _ _ m _ _ _ _ _ _ _` mp_tac >>
          ONCE_REWRITE_TAC [ptr_safe_block_def] >> simp[] >>
          metis_tac[]) >>
      simp[Once ptr_safe_block_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `n` >- (ONCE_REWRITE_TAC [ptr_safe_blocks_def] >> simp[]) >>
  strip_tac >> rename1 `SUC n <= m` >>
  `?m'. m = SUC m' /\ n <= m'` by (Cases_on `m` >> fs[]) >>
  gvs[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once ptr_safe_blocks_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis _ _ = OK s_phi` >> metis_tac[ptr_safe_blocks_block]) >>
  simp[Once ptr_safe_blocks_def]
QED

Theorem ptr_safe_run_fuel_mono_down:
  !D lo m n ctx fn PG G tn s.
    ptr_safe_run D lo m ctx fn PG G tn s /\ n <= m ==>
    ptr_safe_run D lo n ctx fn PG G tn s
Proof
  rw[ptr_safe_run_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  metis_tac[ptr_safe_fuel_mono_down]
QED

(* With more fuel a run that does not fail is the same run. *)
Theorem ptr_safe_fuel_mono_up:
  (!D lo n ctx fn PG G tn inst s m.
     ptr_safe_step D lo n ctx fn PG G tn inst s /\
     (!e. step_inst n ctx inst s <> Error e) /\ n <= m ==>
     ptr_safe_step D lo m ctx fn PG G tn inst s) /\
  (!D lo n ctx fn PG G tn bb s m.
     ptr_safe_block D lo n ctx fn PG G tn bb s /\
     (!e. block_run n ctx fn bb s <> Error e) /\ n <= m ==>
     ptr_safe_block D lo m ctx fn PG G tn bb s) /\
  (!D lo n ctx fn PG G tn s m.
     ptr_safe_blocks D lo n ctx fn PG G tn s /\
     (!e. run_blocks n ctx fn s <> Error e) /\ n <= m ==>
     ptr_safe_blocks D lo m ctx fn PG G tn s)
Proof
  ho_match_mp_tac ptr_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC [ptr_safe_step_def] >> strip_tac >>
      conj_tac >- metis_tac[ptr_inst_ok_fuel] >>
      Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
      qpat_x_assum `!e. step_inst _ _ _ _ <> _` mp_tac >>
      ONCE_REWRITE_TAC [step_inst_def] >> simp[] >>
      BasicProvers.every_case_tac >> gvs[] >> rpt strip_tac >>
      first_x_assum irule >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `get_instruction bb s.vs_inst_idx`
      >- simp[Once ptr_safe_block_def] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `!e. step_inst n ctx inst s <> Error e` by metis_tac[block_run_head] >>
      `step_inst m ctx inst s = step_inst n ctx inst s` by
        metis_tac[cj 1 fuel_mono] >>
      `ptr_safe_step D lo n ctx fn PG G tn inst s` by
        metis_tac[ptr_safe_block_head] >>
      `ptr_safe_step D lo m ctx fn PG G tn inst s` by
        (first_x_assum irule >> simp[]) >>
      Cases_on `step_inst n ctx inst s`
      >~ [`step_inst n ctx inst s = OK s'`]
      >- (Cases_on `is_terminator inst.inst_opcode`
          >- (Cases_on `s'.vs_halted`
              >- simp[Once ptr_safe_block_def] >>
              `!e. run_blocks n ctx fn s' <> Error e` by
                metis_tac[block_run_terminator] >>
              qpat_x_assum `ptr_safe_block _ _ n _ _ _ _ _ _ _` mp_tac >>
              ONCE_REWRITE_TAC [ptr_safe_block_def] >> simp[] >>
              metis_tac[]) >>
          `ghost_step m ctx PG G tn inst s = ghost_step n ctx PG G tn inst s` by
            (irule (cj 1 ghost_fuel_mono_up) >> simp[]) >>
          `!e. block_run n ctx fn bb (s' with vs_inst_idx := SUC s.vs_inst_idx)
               <> Error e` by metis_tac[block_run_step] >>
          qpat_x_assum `ptr_safe_block _ _ n _ _ _ _ _ _ _` mp_tac >>
          ONCE_REWRITE_TAC [ptr_safe_block_def] >> simp[] >>
          metis_tac[]) >>
      simp[Once ptr_safe_block_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `n` >- (ONCE_REWRITE_TAC [run_blocks_def] >> simp[]) >>
  strip_tac >> rename1 `SUC n <= m` >>
  `?m'. m = SUC m' /\ n <= m'` by (Cases_on `m` >> fs[]) >>
  gvs[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once ptr_safe_blocks_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis _ _ = OK s_phi` >>
      `!e. block_run n ctx fn bb
             (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
           <> Error e` by metis_tac[run_blocks_block_run] >>
      metis_tac[ptr_safe_blocks_block]) >>
  simp[Once ptr_safe_blocks_def]
QED

(* A safe run that does not fail is safe at every fuel. *)
Theorem ptr_safe_blocks_all_fuel:
  !D lo fuel ctx fn PG G tn s.
    ptr_safe_blocks D lo fuel ctx fn PG G tn s /\
    (!e. run_blocks fuel ctx fn s <> Error e) ==>
    !m. ptr_safe_blocks D lo m ctx fn PG G tn s
Proof
  rpt strip_tac >> Cases_on `m <= fuel`
  >- metis_tac[ptr_safe_fuel_mono_down] >>
  irule (cj 3 ptr_safe_fuel_mono_up) >> qexists_tac `fuel` >> simp[]
QED

(* ===== Reachability ===== *)

(* What a frame_reachable state on a safe run carries: the run from it is
   safe at every fuel, and so is each caller's run from where the frame
   returns to it, with the ghost frame_reachable's ret rule gives it. *)
Definition frames_ok_def:
  (frames_ok D lo ctx [] fn PG G tn s <=> T) /\
  (frames_ok D lo ctx (f::stk) fn PG G tn s <=>
    !fuel ret s_end s'.
      frame_run fuel ctx fn s = IntRet ret s_end /\
      bind_outputs f.cf_inst.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
        SOME s' ==>
      (!fuel'.
         ptr_safe_run D lo fuel' ctx f.cf_fn f.cf_params
           (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
           (SND (ghost_run fuel ctx fn PG G tn s) with t_var :=
              DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
           (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)) /\
      frames_ok D lo ctx stk f.cf_fn f.cf_params
        (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
        (SND (ghost_run fuel ctx fn PG G tn s) with t_var :=
           DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
        (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
End

Definition ptr_point_def:
  ptr_point D lo ctx stk fn PG G tn s <=>
    (!fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    frames_ok D lo ctx stk fn PG G tn s
End

(* frames_ok looks only at where the run returns, and the taint it returns
   with. *)
Theorem frames_ok_transfer:
  !D lo ctx stk fn PG G tn s fn2 PG2 G2 tn2 s2.
    frames_ok D lo ctx stk fn PG G tn s /\
    (!fuel ret s_end.
       frame_run fuel ctx fn2 s2 = IntRet ret s_end ==>
       ?fuel1. frame_run fuel1 ctx fn s = IntRet ret s_end /\
               SND (ghost_run fuel1 ctx fn PG G tn s) =
               SND (ghost_run fuel ctx fn2 PG2 G2 tn2 s2)) ==>
    frames_ok D lo ctx stk fn2 PG2 G2 tn2 s2
Proof
  Cases_on `stk` >> simp[frames_ok_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule_all >> metis_tac[]
QED

Theorem active_inst_lookup[local]:
  !fn inst s.
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s ==>
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
         get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def, fn_labels_def] >> qexists_tac `bb` >>
  simp[get_instruction_def] >> irule MEM_lookup_block >> simp[]
QED

Theorem enters_block_lookup[local]:
  !fn s s1.
    enters_block fn s s1 ==>
    ?bb s_phi. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
               eval_phis s bb.bb_instructions = OK s_phi /\
               s1 = s_phi with vs_inst_idx :=
                      phi_prefix_length bb.bb_instructions /\
               lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb
Proof
  rw[enters_block_def] >> simp[] >>
  metis_tac[eval_phis_preserves_current_bb]
QED

(* Entering a block on a run that is safe at every fuel: the run from past
   its PHIs is, and returns the same way with the same ghost. *)
Theorem ptr_safe_enters_block[local]:
  !D lo ctx fn PG G tn s s1.
    enters_block fn s s1 /\
    (!fuel. ptr_safe_blocks D lo fuel ctx fn PG G tn s) ==>
    !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s1
Proof
  rpt strip_tac >> drule enters_block_lookup >> strip_tac >>
  simp[ptr_safe_run_def] >>
  metis_tac[ptr_safe_blocks_block]
QED

Theorem frame_run_enters_block[local]:
  !ctx fn PG G tn s s1 fuel.
    enters_block fn s s1 ==>
    run_blocks (SUC fuel) ctx fn s = frame_run fuel ctx fn s1 /\
    ghost_blocks (SUC fuel) ctx fn PG G tn s = ghost_run fuel ctx fn PG G tn s1
Proof
  rpt gen_tac >> strip_tac >> drule enters_block_lookup >> strip_tac >>
  simp[frame_run_def, ghost_run_def] >>
  metis_tac[run_blocks_block_run, ghost_blocks_block]
QED

Theorem ptr_point_entry[local]:
  !D lo ctx fn s s1.
    enters_block fn s s1 /\
    (!fuel. ptr_safe_blocks D lo fuel ctx fn [] FEMPTY entry_taint s) ==>
    ptr_point D lo ctx [] fn [] FEMPTY entry_taint s1
Proof
  rw[ptr_point_def, frames_ok_def] >> metis_tac[ptr_safe_enters_block]
QED

Theorem ptr_point_next[local]:
  !D lo ctx stk fn PG G tn inst s s' f0.
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
    ptr_point D lo ctx stk fn PG G tn s /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst f0 ctx inst s = OK s' ==>
    ptr_point D lo ctx stk fn PG (step_prov PG G inst s')
      (step_taint inst s s' tn) (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt gen_tac >> simp[ptr_point_def] >> strip_tac >>
  drule_all active_inst_lookup >> strip_tac >>
  `!fuel. step_inst fuel ctx inst s = OK s'` by
    metis_tac[step_inst_non_invoke_fuel] >>
  `s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `!fuel. ghost_step fuel ctx PG G tn inst s =
          (step_prov PG G inst s', step_taint inst s s' tn)` by
    metis_tac[ghost_step_non_invoke] >>
  conj_tac
  >- (gen_tac >>
      `ptr_safe_block D lo fuel ctx fn PG G tn bb s` by
        (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _`
           (qspec_then `fuel` mp_tac) >> simp[ptr_safe_run_def]) >>
      simp[ptr_safe_run_def] >>
      qspecl_then [`D`, `lo`, `fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`, `s`,
                   `inst`, `s'`] mp_tac ptr_safe_block_step >>
      simp[]) >>
  irule frames_ok_transfer >> qexistsl [`G`, `PG`, `fn`, `s`, `tn`] >>
  simp[] >> rpt strip_tac >> qexists_tac `fuel` >>
  qspecl_then [`fuel`, `ctx`, `fn`, `bb`, `s`, `inst`, `s'`] mp_tac
    block_run_step >>
  qspecl_then [`fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`, `s`, `inst`, `s'`]
    mp_tac ghost_block_step >>
  gvs[frame_run_def, ghost_run_def]
QED

Theorem ptr_point_block[local]:
  !D lo ctx stk fn PG G tn inst s s' s1 f0.
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
    ptr_point D lo ctx stk fn PG G tn s /\
    is_terminator inst.inst_opcode /\ step_inst f0 ctx inst s = OK s' /\
    ~s'.vs_halted /\ enters_block fn s' s1 ==>
    ptr_point D lo ctx stk fn PG (entry_prov fn s' G)
      (entry_taint_vars fn s' tn) s1
Proof
  rpt gen_tac >> simp[ptr_point_def] >> strip_tac >>
  drule_all active_inst_lookup >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  `!fuel. step_inst fuel ctx inst s = OK s'` by
    metis_tac[step_inst_non_invoke_fuel] >>
  conj_tac
  >- (irule ptr_safe_enters_block >> qexists_tac `s'` >> simp[] >>
      gen_tac >>
      `ptr_safe_block D lo fuel ctx fn PG G tn bb s` by
        (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _`
           (qspec_then `fuel` mp_tac) >> simp[ptr_safe_run_def]) >>
      qspecl_then [`D`, `lo`, `fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`, `s`,
                   `inst`, `s'`] mp_tac ptr_safe_block_terminator >>
      simp[]) >>
  irule frames_ok_transfer >> qexistsl [`G`, `PG`, `fn`, `s`, `tn`] >>
  simp[] >> rpt strip_tac >> qexists_tac `SUC fuel` >>
  drule_then (qspecl_then [`ctx`, `PG`, `entry_prov fn s' G`,
                           `entry_taint_vars fn s' tn`, `fuel`] strip_assume_tac)
    frame_run_enters_block >>
  qspecl_then [`SUC fuel`, `ctx`, `fn`, `bb`, `s`, `inst`, `s'`] mp_tac
    block_run_terminator >>
  qspecl_then [`SUC fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`, `s`, `inst`,
               `s'`] mp_tac ghost_block_terminator >>
  gvs[frame_run_def, ghost_run_def]
QED

Theorem ptr_point_call[local]:
  !D lo ctx stk PG G tn caller ivk s nm ops callee args cs s1.
    ALL_DISTINCT (fn_labels caller) /\ active_inst caller ivk s /\
    ptr_point D lo ctx stk caller PG G tn s /\
    ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm, ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 ==>
    ptr_point D lo ctx
      (<| cf_fn := caller; cf_inst := ivk; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      callee (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) s1
Proof
  rpt gen_tac >> simp[ptr_point_def] >> strip_tac >>
  drule_all active_inst_lookup >> strip_tac >>
  `!fuel. ptr_safe_block D lo fuel ctx caller PG G tn bb s` by
    (gen_tac >> qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _`
       (qspec_then `fuel` mp_tac) >> simp[ptr_safe_run_def]) >>
  `!fuel. ptr_safe_blocks D lo fuel ctx callee (MAP (op_prov G) ops) FEMPTY
            (tn with t_var := FEMPTY) cs` by
    metis_tac[ptr_safe_block_head, ptr_safe_step_invoke] >>
  conj_tac >- metis_tac[ptr_safe_enters_block] >>
  simp[frames_ok_def] >> rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `ptr_safe_run D lo _ ctx caller PG GR tnR s2` >>
  drule_then (qspecl_then [`ctx`, `MAP (op_prov G) ops`, `FEMPTY`,
                           `tn with t_var := FEMPTY`, `fuel`] strip_assume_tac)
    frame_run_enters_block >>
  `!M. SUC fuel <= M ==>
       step_inst M ctx ivk s = OK s' /\
       ghost_step M ctx PG G tn ivk s = (GR, tnR)` by
    (rpt gen_tac >> strip_tac >>
     `run_blocks M ctx callee cs = IntRet ret s_end` by
       (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `SUC fuel` >> simp[]) >>
     `ghost_blocks M ctx callee (MAP (op_prov G) ops) FEMPTY
        (tn with t_var := FEMPTY) cs =
      ghost_run fuel ctx callee (MAP (op_prov G) ops) FEMPTY
        (tn with t_var := FEMPTY) s1` by
       (qpat_x_assum `ghost_blocks _ _ _ _ _ _ _ = _` (SUBST1_TAC o SYM) >>
        irule (cj 3 ghost_fuel_mono_up) >> simp[]) >>
     conj_tac
     >- (simp[Once step_inst_def] >> gvs[]) >>
     drule_all ghost_step_invoke >> simp[Abbr `GR`, Abbr `tnR`]) >>
  `s'.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `!M. _ ==> _` (qspec_then `SUC fuel` mp_tac) >> simp[] >>
     strip_tac >> drule step_preserves_control_flow >>
     simp[is_terminator_def]) >>
  `~is_terminator ivk.inst_opcode` by simp[is_terminator_def] >>
  conj_tac
  >- (gen_tac >> irule ptr_safe_run_fuel_mono_down >>
      qexists_tac `MAX fuel' (SUC fuel)` >> simp[] >>
      qpat_x_assum `!M. _ ==> _` (qspec_then `MAX fuel' (SUC fuel)` mp_tac) >>
      simp[] >> strip_tac >>
      qspecl_then [`D`, `lo`, `MAX fuel' (SUC fuel)`, `ctx`, `caller`, `PG`,
                   `G`, `tn`, `bb`, `s`, `ivk`, `s'`] mp_tac
        ptr_safe_block_step >>
      simp[Abbr `s2`, ptr_safe_run_def]) >>
  irule frames_ok_transfer >> qexistsl [`G`, `PG`, `caller`, `s`, `tn`] >>
  simp[] >> rpt strip_tac >> qexists_tac `MAX fuel' (SUC fuel)` >>
  qpat_x_assum `!M. _ ==> _` (qspec_then `MAX fuel' (SUC fuel)` mp_tac) >>
  simp[] >> strip_tac >>
  `frame_run (MAX fuel' (SUC fuel)) ctx caller s2 =
   frame_run fuel' ctx caller s2` by
    (irule frame_run_fuel_mono >> simp[]) >>
  `ghost_run (MAX fuel' (SUC fuel)) ctx caller PG GR tnR s2 =
   ghost_run fuel' ctx caller PG GR tnR s2` by
    (irule ghost_run_fuel_mono_up >> simp[]) >>
  qspecl_then [`MAX fuel' (SUC fuel)`, `ctx`, `caller`, `bb`, `s`, `ivk`,
               `s'`] mp_tac block_run_step >>
  qspecl_then [`MAX fuel' (SUC fuel)`, `ctx`, `caller`, `PG`, `G`, `tn`, `bb`,
               `s`, `ivk`, `s'`] mp_tac ghost_block_step >>
  gvs[frame_run_def, ghost_run_def, Abbr `s2`]
QED

Theorem ptr_point_ret[local]:
  !D lo ctx f stk fn PG G tn rinst s ret s_end s' fuel.
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn rinst s /\
    ptr_point D lo ctx (f::stk) fn PG G tn s /\
    step_inst fuel ctx rinst s = IntRet ret s_end /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
      SOME s' ==>
    ptr_point D lo ctx stk f.cf_fn f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  rpt gen_tac >> simp[ptr_point_def] >> strip_tac >>
  drule_all active_inst_lookup >> strip_tac >>
  `frame_run fuel ctx fn s = IntRet ret s_end` by
    (simp[frame_run_def, block_run_def] >> simp[Once exec_block_def]) >>
  `ghost_run fuel ctx fn PG G tn s = (G, tn)` by
    (simp[ghost_run_def] >> metis_tac[ghost_block_intret]) >>
  qpat_x_assum `frames_ok _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[frames_ok_def] >> disch_then drule_all >> simp[]
QED

(* Every frame_reachable state of a unit whose entry run is safe at every
   fuel is on a safe run, with the ghost frame_reachable gives it. *)
Theorem frame_reachable_ptr_point[local]:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    !D lo.
      EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
      (!name efn lbl.
         ctx.ctx_entry = SOME name /\
         lookup_function name ctx.ctx_functions = SOME efn /\
         fn_entry_label efn = SOME lbl ==>
         !fuel. ptr_safe_blocks D lo fuel ctx efn [] FEMPTY entry_taint
                  (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                               vs_inst_idx := 0 |>)) ==>
      MEM fn ctx.ctx_functions /\
      EVERY (\f. MEM f.cf_fn ctx.ctx_functions) stk /\
      ptr_point D lo ctx stk fn PG G tn s
Proof
  Induct_on `frame_reachable` >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac
  >- (conj_tac >- metis_tac[lookup_function_MEM] >> simp[] >>
      irule ptr_point_entry >> metis_tac[])
  >- (first_x_assum (qspecl_then [`D`, `lo`] mp_tac) >> simp[] >> strip_tac >>
      irule ptr_point_next >> fs[EVERY_MEM] >> metis_tac[])
  >- (first_x_assum (qspecl_then [`D`, `lo`] mp_tac) >> simp[] >> strip_tac >>
      irule ptr_point_block >> fs[EVERY_MEM] >> metis_tac[])
  >- (first_x_assum (qspecl_then [`D`, `lo`] mp_tac) >> simp[] >> strip_tac >>
      conj_tac >- metis_tac[lookup_function_MEM] >>
      irule ptr_point_call >> fs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`D`, `lo`] mp_tac) >> simp[] >> strip_tac >>
  irule ptr_point_ret >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_point_inst_ok[local]:
  !D lo ctx stk fn PG G tn inst s fuel.
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
    ptr_point D lo ctx stk fn PG G tn s ==>
    ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  rw[ptr_point_def] >> drule_all active_inst_lookup >> strip_tac >>
  first_x_assum (qspec_then `fuel` mp_tac) >> simp[ptr_safe_run_def] >>
  metis_tac[ptr_safe_block_head, ptr_safe_step_inst_ok]
QED

(* The bridge: a unit whose functions and their reachable parts are
   pointer-confined, and whose entry run is pointer-safe at every fuel, has
   the pointer discipline and keeps its taint within D.  Distinct labels are needed: the reachability rules
   take any block with the current label (active_inst), the run takes the
   first (lookup_block). *)
Theorem ptr_safe_ptr_discipline:
  !D lo P ctx vs name fn lbl.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
    EVERY (fn_ptr_ok P) ctx.ctx_functions /\
    EVERY (\f. fn_ptr_ok P (reachable_fn f)) ctx.ctx_functions /\
    (!fuel. ptr_safe_blocks D lo fuel ctx fn [] FEMPTY entry_taint
              (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                          vs_inst_idx := 0 |>)) /\
    lo <= vs.vs_alloca_next ==>
    ptr_discipline lo ctx vs /\ taint_within D ctx vs
Proof
  rpt gen_tac >> strip_tac >>
  `!stk PG G tn f inst s.
     frame_reachable vs ctx stk PG G tn f inst s ==>
     active_inst f inst s /\ !fuel. ptr_inst_ok D lo fuel ctx f G tn inst s` by
    (rpt gen_tac >> strip_tac >>
     drule frame_reachable_ptr_point >>
     disch_then (qspecl_then [`D`, `lo`] mp_tac) >>
     impl_tac >- (simp[] >> rpt strip_tac >> gvs[]) >>
     strip_tac >>
     `ALL_DISTINCT (fn_labels f)` by fs[EVERY_MEM] >>
     `active_inst f inst s` by
       (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[Once frame_reachable_cases] >> rw[] >> simp[]) >>
     metis_tac[ptr_point_inst_ok]) >>
  conj_tac
  >- (simp[ptr_discipline_def] >> qexists_tac `P` >>
      conj_tac >- fs[EVERY_MEM] >>
      rpt gen_tac >> strip_tac >> first_x_assum drule >>
      simp[ptr_inst_ok_def]) >>
  simp[taint_within_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum drule >>
      disch_then (qspec_then `fuel` mp_tac o CONJUNCT2) >>
      simp[ptr_inst_ok_def]) >>
  rpt gen_tac >> simp[final_taint_def] >> strip_tac >>
  first_x_assum drule >> disch_then (qspec_then `fuel` mp_tac o CONJUNCT2) >>
  simp[ptr_inst_ok_def]
QED
