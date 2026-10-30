(*
 * Memory-safe runs
 *
 * mem_safe_run fuel ctx fn s says that every instruction the run of fn from
 * s executes, in callee frames too, reads and writes memory only below the
 * allocation frontier of the state it runs in (inst_mem_below_frontier).
 * The check follows the runner's own recursion (step_inst, exec_block,
 * run_blocks), so it sees exactly the instructions the run executes, in
 * the states it executes them in.
 *
 * TOP-LEVEL:
 *   mem_safe_step, mem_safe_block, mem_safe_blocks
 *                         — the check along step_inst, exec_block and
 *                           run_blocks
 *   mem_safe_run          — the check along a run from inside a block
 *                           (fragExec's run_from)
 *   mem_safe_step_non_invoke, mem_safe_step_invoke, mem_safe_block_step,
 *   mem_safe_run_step, mem_safe_run_head, mem_safe_run_terminator,
 *   mem_safe_blocks_run   — unfolding
 *   mem_safe_fuel_mono_down, mem_safe_run_fuel_mono_down
 *                         — less fuel runs a prefix of the same path
 *   mem_safe_fuel_mono_up — more fuel, when the run does not fail
 *                           (the run_from form, mem_safe_run_fuel_mono_up,
 *                           is in fragExecMem, next to run_from's theory)
 *   mem_safe_blocks_all_fuel — a safe non-Error run is safe at every fuel
 *   mem_safe_point        — an instruction state on a run that is safe at
 *                           every fuel
 *   mem_safe_point_closed, mem_safe_point_entry, mem_safe_point_mem
 *                         — mem_safe_point is a reachability invariant
 *   mem_safe_raw_unit_memory_ok — the bridge to raw_unit_memory_ok
 *)

Theory memSafeRun
Ancestors
  list venomExecSemantics venomExecProofs venomInstProofs venomInst
  venomState contextCodegenRel contextCodegenRelProps unitTransformDefs

(* ===== Definitions ===== *)

(* The memory check along the runner: mem_safe_step checks an instruction
   and, for INVOKE, the callee's run; mem_safe_block every instruction
   exec_block runs; mem_safe_blocks every block run_blocks enters.  Where
   the run stops (Error, Abort, Halt, IntRet, out of fuel) the check stops
   too. *)
Definition mem_safe_defs:
  (mem_safe_step fuel ctx inst s <=>
    inst_mem_below_frontier inst s /\
    if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => T
      | SOME (callee_name, arg_ops) =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => T
          | SOME callee_fn =>
              case eval_operands arg_ops s of
                NONE => T
              | SOME args =>
                  case setup_callee callee_fn args s of
                    NONE => T
                  | SOME callee_s => mem_safe_blocks fuel ctx callee_fn callee_s
    else T)
  /\
  (mem_safe_block fuel ctx bb s <=>
    case get_instruction bb s.vs_inst_idx of
      NONE => T
    | SOME inst =>
        mem_safe_step fuel ctx inst s /\
        case step_inst fuel ctx inst s of
          OK s' =>
            if is_terminator inst.inst_opcode then T
            else mem_safe_block fuel ctx bb
                   (s' with vs_inst_idx := SUC s.vs_inst_idx)
        | _ => T)
  /\
  (mem_safe_blocks fuel ctx fn s <=>
    case fuel of
      0 => T
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => T
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              OK s_phi =>
                mem_safe_block fuel' ctx bb
                  (s_phi with vs_inst_idx :=
                     phi_prefix_length bb.bb_instructions) /\
                (case exec_block fuel' ctx bb
                        (s_phi with vs_inst_idx :=
                           phi_prefix_length bb.bb_instructions) of
                   OK s' =>
                     if s'.vs_halted then T else mem_safe_blocks fuel' ctx fn s'
                 | _ => T)
            | _ => T)
Termination
  qexists_tac `inv_image ($< LEX $<)
    (\x. case x of
      | INL (fuel, ctx, inst, s) => (fuel, 1)
      | INR (INL (fuel, ctx, bb, s)) =>
          (fuel, 2 + (LENGTH bb.bb_instructions - s.vs_inst_idx))
      | INR (INR (fuel, ctx, fn, s)) => (fuel, 0))` >>
  conj_tac >-
    (irule relationTheory.WF_inv_image >>
     MATCH_ACCEPT_TAC (MATCH_MP pairTheory.WF_LEX
       (CONJ prim_recTheory.WF_LESS prim_recTheory.WF_LESS))) >>
  simp_tac bool_ss [relationTheory.inv_image_thm, sumTheory.sum_case_def,
    pairTheory.pair_case_def, pairTheory.LEX_DEF_THM] >>
  rpt strip_tac >> gvs[get_instruction_def]
End

val mem_safe_step_def = save_thm("mem_safe_step_def", cj 1 mem_safe_defs);
val mem_safe_block_def = save_thm("mem_safe_block_def", cj 2 mem_safe_defs);
val mem_safe_blocks_def = save_thm("mem_safe_blocks_def", cj 3 mem_safe_defs);

(* The check along run_from: the rest of the current block, then the blocks
   after it. *)
Definition mem_safe_run_def:
  mem_safe_run fuel ctx fn s <=>
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => T
    | SOME bb =>
        mem_safe_block fuel ctx bb s /\
        case exec_block fuel ctx bb s of
          OK s' => if s'.vs_halted then T else mem_safe_blocks fuel ctx fn s'
        | _ => T
End

(* ===== Unfolding ===== *)

Theorem mem_safe_step_non_invoke:
  !fuel ctx inst s.
    inst.inst_opcode <> INVOKE ==>
    (mem_safe_step fuel ctx inst s <=> inst_mem_below_frontier inst s)
Proof
  rw[Once mem_safe_step_def]
QED

Theorem mem_safe_step_invoke:
  !fuel ctx inst s name arg_ops callee args cs.
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (name, arg_ops) /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops s = SOME args /\
    setup_callee callee args s = SOME cs ==>
    (mem_safe_step fuel ctx inst s <=>
     inst_mem_below_frontier inst s /\ mem_safe_blocks fuel ctx callee cs)
Proof
  rw[Once mem_safe_step_def]
QED

Theorem mem_safe_block_step:
  !fuel ctx bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    (mem_safe_block fuel ctx bb s <=>
     mem_safe_step fuel ctx inst s /\
     mem_safe_block fuel ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rw[Once mem_safe_block_def]
QED

(* A non-terminator step moves the check on, like run_from_step. *)
Theorem mem_safe_run_step:
  !fuel ctx fn s bb inst s'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    (mem_safe_run fuel ctx fn s <=>
     mem_safe_step fuel ctx inst s /\
     mem_safe_run fuel ctx fn (s' with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `exec_block fuel ctx bb s =
   exec_block fuel ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >> simp[]) >>
  drule_all mem_safe_block_step >> strip_tac >>
  simp[mem_safe_run_def] >> metis_tac[]
QED

Theorem mem_safe_run_head:
  !fuel ctx fn s bb inst.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    mem_safe_run fuel ctx fn s ==>
    mem_safe_step fuel ctx inst s
Proof
  rw[mem_safe_run_def] >> pop_assum mp_tac >>
  simp[Once mem_safe_block_def]
QED

(* A terminator that does not halt hands the check to the next block. *)
Theorem mem_safe_run_terminator:
  !fuel ctx fn s bb inst s'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' /\ ~s'.vs_halted /\
    mem_safe_run fuel ctx fn s ==>
    mem_safe_blocks fuel ctx fn s'
Proof
  rpt strip_tac >>
  `exec_block fuel ctx bb s = OK s'` by simp[Once exec_block_def] >>
  gvs[mem_safe_run_def]
QED

(* Entering a block is checking from past its PHIs, like
   run_blocks_run_from. *)
Theorem mem_safe_blocks_run:
  !fuel ctx fn s bb s_phi.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK s_phi ==>
    (mem_safe_blocks (SUC fuel) ctx fn s <=>
     mem_safe_run fuel ctx fn
       (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
  rpt strip_tac >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  simp[Once mem_safe_blocks_def, mem_safe_run_def]
QED

(* ===== Fuel ===== *)

(* With less fuel the run is a prefix of the same path, so it executes
   fewer instructions. *)
Theorem mem_safe_fuel_mono_down:
  (!n ctx inst s m.
     mem_safe_step m ctx inst s /\ n <= m ==> mem_safe_step n ctx inst s) /\
  (!n ctx bb s m.
     mem_safe_block m ctx bb s /\ n <= m ==> mem_safe_block n ctx bb s) /\
  (!n ctx fn s m.
     mem_safe_blocks m ctx fn s /\ n <= m ==> mem_safe_blocks n ctx fn s)
Proof
  ho_match_mp_tac mem_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC[mem_safe_step_def] >>
      Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
      BasicProvers.every_case_tac >> simp[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC[mem_safe_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      strip_tac >> conj_tac >- metis_tac[] >>
      Cases_on `step_inst n ctx inst s` >> simp[] >>
      rename1 `step_inst n ctx inst s = OK s1` >>
      `step_inst m ctx inst s = OK s1` by
        (qspecl_then [`n`, `m`, `ctx`, `inst`, `s`, `OK s1`] mp_tac
           (cj 1 fuel_mono) >> simp[]) >>
      rw[] >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `n` >- (ONCE_REWRITE_TAC [mem_safe_blocks_def] >> simp[]) >>
  strip_tac >> rename1 `SUC n <= m` >>
  `?m'. m = SUC m' /\ n <= m'` by (Cases_on `m` >> fs[]) >>
  gvs[] >>
  qpat_x_assum `mem_safe_blocks _ _ _ _` mp_tac >>
  ONCE_REWRITE_TAC[mem_safe_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis _ _ = OK s_phi` >>
  strip_tac >> conj_tac >- metis_tac[] >>
  Cases_on `exec_block n ctx bb
              (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[] >>
  rename1 `exec_block n ctx bb _ = OK s2` >>
  `exec_block m' ctx bb
     (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK s2` by
    (qspecl_then [`n`, `m'`, `ctx`, `bb`,
                  `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
                  `OK s2`] mp_tac (cj 2 fuel_mono) >> simp[]) >>
  gvs[] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem mem_safe_run_fuel_mono_down:
  !m n ctx fn s.
    mem_safe_run m ctx fn s /\ n <= m ==> mem_safe_run n ctx fn s
Proof
  rpt gen_tac >> simp[mem_safe_run_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >> strip_tac >>
  conj_tac >- metis_tac[mem_safe_fuel_mono_down] >>
  Cases_on `exec_block n ctx bb s` >> simp[] >>
  rename1 `exec_block n ctx bb s = OK s1` >>
  `exec_block m ctx bb s = OK s1` by
    (qspecl_then [`n`, `m`, `ctx`, `bb`, `s`, `OK s1`] mp_tac
       (cj 2 fuel_mono) >> simp[]) >>
  gvs[] >> rw[] >> gvs[] >> metis_tac[mem_safe_fuel_mono_down]
QED

(* With more fuel a run that does not fail is the same run. *)
Theorem mem_safe_fuel_mono_up:
  (!n ctx inst s m.
     mem_safe_step n ctx inst s /\ (!e. step_inst n ctx inst s <> Error e) /\
     n <= m ==> mem_safe_step m ctx inst s) /\
  (!n ctx bb s m.
     mem_safe_block n ctx bb s /\ (!e. exec_block n ctx bb s <> Error e) /\
     n <= m ==> mem_safe_block m ctx bb s) /\
  (!n ctx fn s m.
     mem_safe_blocks n ctx fn s /\ (!e. run_blocks n ctx fn s <> Error e) /\
     n <= m ==> mem_safe_blocks m ctx fn s)
Proof
  ho_match_mp_tac mem_safe_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC[mem_safe_step_def, step_inst_def] >>
      Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
      BasicProvers.every_case_tac >> simp[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      ONCE_REWRITE_TAC[mem_safe_block_def, exec_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      strip_tac >>
      `!e. step_inst n ctx inst s <> Error e` by
        (rpt strip_tac >> gvs[]) >>
      `step_inst m ctx inst s = step_inst n ctx inst s` by
        (qspecl_then [`n`, `m`, `ctx`, `inst`, `s`,
                      `step_inst n ctx inst s`] mp_tac
           (cj 1 fuel_mono) >> simp[]) >>
      conj_tac >- metis_tac[] >>
      Cases_on `step_inst n ctx inst s` >> gvs[] >>
      rw[] >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `n` >- (ONCE_REWRITE_TAC [run_blocks_def] >> simp[]) >>
  strip_tac >> rename1 `SUC n <= m` >>
  `?m'. m = SUC m' /\ n <= m'` by (Cases_on `m` >> fs[]) >>
  gvs[] >>
  qpat_x_assum `mem_safe_blocks _ _ _ _` mp_tac >>
  qpat_x_assum `!e. run_blocks _ _ _ _ <> _` mp_tac >>
  ONCE_REWRITE_TAC[mem_safe_blocks_def, run_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >>
  rename1 `eval_phis _ _ = OK s_phi` >>
  strip_tac >> strip_tac >>
  `!e. exec_block n ctx bb
         (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) <>
       Error e` by (rpt strip_tac >> gvs[]) >>
  `exec_block m' ctx bb
     (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
   exec_block n ctx bb
     (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (qspecl_then [`n`, `m'`, `ctx`, `bb`,
                  `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
                  `exec_block n ctx bb (s_phi with vs_inst_idx :=
                     phi_prefix_length bb.bb_instructions)`]
       mp_tac (cj 2 fuel_mono) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  conj_tac >- metis_tac[] >>
  Cases_on `exec_block n ctx bb
              (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[] >> rw[] >> gvs[] >> metis_tac[]
QED

(* A safe run that does not fail is safe at every fuel. *)
Theorem mem_safe_blocks_all_fuel:
  !fuel ctx fn s.
    mem_safe_blocks fuel ctx fn s /\ (!e. run_blocks fuel ctx fn s <> Error e) ==>
    !m. mem_safe_blocks m ctx fn s
Proof
  rpt strip_tac >> Cases_on `m <= fuel`
  >- metis_tac[mem_safe_fuel_mono_down] >>
  irule (cj 3 mem_safe_fuel_mono_up) >> qexists_tac `fuel` >> simp[]
QED

(* ===== Reachability ===== *)

(* An instruction state of fn on a run that is memory-safe at every fuel.
   With distinct labels, the block active_inst picks is the one run_from
   runs. *)
Definition mem_safe_point_def:
  mem_safe_point ctx fn inst s <=>
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
    !fuel. mem_safe_run fuel ctx fn s
End

Theorem active_inst_lookup[local]:
  !fn inst s.
    ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s ==>
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
         get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def, fn_labels_def] >> qexists_tac `bb` >>
  simp[get_instruction_def] >> irule MEM_lookup_block >> simp[]
QED

Theorem mem_safe_point_mem:
  !ctx fn inst s.
    mem_safe_point ctx fn inst s ==> inst_mem_below_frontier inst s
Proof
  rw[mem_safe_point_def] >> drule_all active_inst_lookup >> strip_tac >>
  `mem_safe_step 0 ctx inst s` by metis_tac[mem_safe_run_head] >>
  pop_assum mp_tac >> simp[Once mem_safe_step_def]
QED

(* Entering a block on a run that is safe at every fuel. *)
Theorem mem_safe_enters_block[local]:
  !ctx fn s s1.
    enters_block fn s s1 /\ (!fuel. mem_safe_blocks fuel ctx fn s) ==>
    !fuel. mem_safe_run fuel ctx fn s1
Proof
  rw[enters_block_def] >> metis_tac[mem_safe_blocks_run]
QED

Theorem mem_safe_point_entry:
  !ctx fn s.
    ALL_DISTINCT (fn_labels fn) /\ (!fuel. mem_safe_blocks fuel ctx fn s) ==>
    fn_entry_inv mem_safe_point ctx fn s
Proof
  rw[fn_entry_inv_def, mem_safe_point_def] >>
  metis_tac[mem_safe_enters_block]
QED

Theorem mem_safe_point_step[local]:
  !ctx fn inst inst' s s' f0.
    mem_safe_point ctx fn inst s /\ ~is_terminator inst.inst_opcode /\
    step_inst f0 ctx inst s = OK s' /\
    active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
    mem_safe_point ctx fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt gen_tac >> simp[mem_safe_point_def] >> strip_tac >>
  qspecl_then [`fn`, `inst`, `s`] mp_tac active_inst_lookup >> simp[] >>
  strip_tac >>
  qx_gen_tac `g` >>
  irule mem_safe_run_fuel_mono_down >> qexists_tac `MAX g f0` >> simp[] >>
  `step_inst (MAX g f0) ctx inst s = OK s'` by
    (qspecl_then [`f0`, `MAX g f0`, `ctx`, `inst`, `s`, `OK s'`] mp_tac
       (cj 1 fuel_mono) >> simp[]) >>
  metis_tac[mem_safe_run_step]
QED

Theorem mem_safe_point_jump[local]:
  !ctx fn inst inst' s s' s1 f0.
    mem_safe_point ctx fn inst s /\ is_terminator inst.inst_opcode /\
    step_inst f0 ctx inst s = OK s' /\ ~s'.vs_halted /\
    enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
    mem_safe_point ctx fn inst' s1
Proof
  rpt gen_tac >> simp[mem_safe_point_def] >> strip_tac >>
  qspecl_then [`fn`, `inst`, `s`] mp_tac active_inst_lookup >> simp[] >>
  strip_tac >>
  `!g. mem_safe_blocks g ctx fn s'` by
    (qx_gen_tac `g` >> irule (cj 3 mem_safe_fuel_mono_down) >>
     qexists_tac `MAX g f0` >> simp[] >>
     `step_inst (MAX g f0) ctx inst s = OK s'` by
       (qspecl_then [`f0`, `MAX g f0`, `ctx`, `inst`, `s`, `OK s'`] mp_tac
          (cj 1 fuel_mono) >> simp[]) >>
     metis_tac[mem_safe_run_terminator]) >>
  metis_tac[mem_safe_enters_block]
QED

Theorem mem_safe_point_callee[local]:
  !ctx caller inv s nm ops callee args cs.
    EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions /\
    mem_safe_point ctx caller inv s /\ inv.inst_opcode = INVOKE /\
    decode_invoke inv = SOME (nm, ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
    fn_entry_inv mem_safe_point ctx callee cs
Proof
  rpt gen_tac >> simp[mem_safe_point_def] >> strip_tac >>
  `ALL_DISTINCT (fn_labels callee)` by
    (drule lookup_function_MEM >> fs[EVERY_MEM]) >>
  drule_all active_inst_lookup >> strip_tac >>
  `!fuel. mem_safe_blocks fuel ctx callee cs` by
    metis_tac[mem_safe_run_head, mem_safe_step_invoke] >>
  metis_tac[mem_safe_point_entry]
QED

(* Every successor the reachability clauses allow is the next state of the
   same deterministic run. *)
Theorem mem_safe_point_closed:
  !ctx.
    EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions ==>
    reachability_closed mem_safe_point ctx
Proof
  rw[reachability_closed_def]
  >- metis_tac[mem_safe_point_step]
  >- metis_tac[mem_safe_point_jump] >>
  metis_tac[mem_safe_point_callee]
QED

(* The bridge: a memory-safe run from the unit's entry, and an invariant J
   that bounds the frontier (alloca_frontier_inv under the unit's alloca
   budget), give raw_unit_memory_ok.  Distinct labels are needed: the
   reachability clauses take any block with the current label (active_inst),
   the run takes the first (lookup_block).  A safe run that does not fail is
   safe at every fuel (mem_safe_blocks_all_fuel). *)
Theorem mem_safe_raw_unit_memory_ok:
  !ctx vs name fn lbl J.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
    reachability_closed J ctx /\
    fn_entry_inv J ctx fn
      (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                  vs_inst_idx := 0 |>) /\
    (!f inst s. J ctx f inst s ==> s.vs_alloca_next < dimword (:256)) /\
    (!fuel. mem_safe_blocks fuel ctx fn
              (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                          vs_inst_idx := 0 |>)) ==>
    raw_unit_memory_ok ctx vs
Proof
  rw[raw_unit_memory_ok_def, codegen_reachability_package_def] >>
  qexists_tac `\c f i s. mem_safe_point c f i s /\ J c f i s` >>
  rpt conj_tac
  >- (irule reachability_closed_conj >> simp[mem_safe_point_closed])
  >- (irule fn_entry_inv_conj >> simp[] >>
      irule mem_safe_point_entry >> simp[] >>
      drule lookup_function_MEM >> fs[EVERY_MEM]) >>
  metis_tac[mem_safe_point_mem]
QED
