(*
 * Function Inliner — Simulation Infrastructure
 *
 * Contains:
 * 1. Fuel monotonicity (copied from crossBlockSimProofs)
 * 2. Context simulation: same function in different contexts
 * 3. Main inline_candidate simulation theorem
 *)

Theory functionInlinerSim
Ancestors
  functionInlinerDefs functionInlinerFresh functionInlinerRenumber
  stateEquiv stateEquivProps
  venomExecSemantics venomInst venomWf cfgTransform

open stringTheory ASCIInumbersTheory

(* ===== Structural fn_name preservation ===== *)

Theorem inline_call_site_fn_name:
  !(prefix:string) ret_lbl caller callee bb_lbl idx.
    (inline_call_site prefix ret_lbl caller callee bb_lbl idx).fn_name =
    caller.fn_name
Proof
  rw[inline_call_site_def, LET_THM] >>
  rpt (CASE_TAC >> gvs[]) >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem fix_inline_phis_fn_name:
  !orig new_lbl ret_bb func.
    (fix_inline_phis orig new_lbl ret_bb func).fn_name = func.fn_name
Proof
  rw[fix_inline_phis_def, LET_THM]
QED

Theorem inline_one_site_fn_name:
  !caller callee ist caller' ist'.
    inline_one_site caller callee ist = SOME (caller', ist') ==>
    caller'.fn_name = caller.fn_name
Proof
  rw[inline_one_site_def, LET_THM] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  simp[renumber_fn_inst_ids_fn_name] >>
  CASE_TAC >> simp[inline_call_site_fn_name, fix_inline_phis_fn_name]
QED

Theorem inline_at_sites_fn_name:
  !n caller callee ist caller' ist'.
    inline_at_sites n caller callee ist = (caller', ist') ==>
    caller'.fn_name = caller.fn_name
Proof
  Induct >> rw[inline_at_sites_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac inline_one_site_fn_name >> gvs[] >>
  first_x_assum drule >> simp[]
QED

(* ===== terminates (from passSimulationDefs) ===== *)

Definition terminates_def:
  terminates r <=> case r of Error _ => F | _ => T
End

(* ===== Fuel monotonicity ===== *)

Triviality step_inst_invoke_fuel_0:
  !ctx inst s. inst.inst_opcode = INVOKE ==>
    ?e. step_inst 0 ctx inst s = Error e
Proof
  rw[step_inst_def, run_function_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[]
QED

Triviality step_inst_fuel_mono:
  !f ctx inst st k.
    (!e. step_inst f ctx inst st <> Error e) ==>
    (!ctx' fn' s'. terminates (run_function f ctx' fn' s') ==>
       !k'. run_function (f + k') ctx' fn' s' = run_function f ctx' fn' s') ==>
    step_inst (f + k) ctx inst st = step_inst f ctx inst st
Proof
  rw[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    `step_inst f ctx inst st =
       case decode_invoke inst of
         NONE => Error "invoke: bad operand format"
       | SOME (callee_name, arg_ops) =>
           case lookup_function callee_name ctx.ctx_functions of
             NONE => Error "invoke: function not found"
           | SOME callee_fn =>
               case eval_operands arg_ops st of
                 NONE => Error "invoke: undefined argument"
               | SOME args =>
                   case setup_callee callee_fn args st of
                     NONE => Error "invoke: empty function"
                   | SOME callee_s =>
                       case run_function f ctx callee_fn callee_s of
                         OK v => Error "invoke: callee did not return"
                       | Halt s'' => Halt s''
                       | Abort a s'' => Abort a s''
                       | IntRet vals callee_s' =>
                           (case bind_outputs inst.inst_outputs vals
                                   (merge_callee_state st callee_s') of
                             NONE => Error "invoke: return arity mismatch"
                           | SOME s'' => OK s'')
                       | Error e => Error e`
      by simp[Once step_inst_def] >>
    Cases_on `decode_invoke inst`
    >- gvs[]
    >- (
      Cases_on `x` >>
      rename1 `decode_invoke inst = SOME (cn, ao)` >>
      Cases_on `lookup_function cn ctx.ctx_functions`
      >- gvs[]
      >- (
        rename1 `_ = SOME cfn` >>
        Cases_on `eval_operands ao st`
        >- gvs[]
        >- (
          rename1 `_ = SOME args` >>
          Cases_on `setup_callee cfn args st`
          >- gvs[]
          >- (
            rename1 `_ = SOME cs` >>
            `terminates (run_function f ctx cfn cs)` by
              (Cases_on `run_function f ctx cfn cs` >>
               gvs[terminates_def]) >>
            `run_function (f + k) ctx cfn cs = run_function f ctx cfn cs` by
              (first_x_assum irule >> simp[]) >>
            rw[step_inst_def]
          )
        )
      )
    )
  )
  >- metis_tac[step_inst_non_invoke]
QED

Triviality run_block_fuel_mono_lem:
  !n (ctx:venom_context) (bb:basic_block) (st:venom_state) f.
    n = LENGTH bb.bb_instructions - st.vs_inst_idx ==>
    (!e. run_block f ctx bb st <> Error e) ==>
    (!ctx' fn' s'. terminates (run_function f ctx' fn' s') ==>
       !k. run_function (f + k) ctx' fn' s' = run_function f ctx' fn' s') ==>
    !k. run_block (f + k) ctx bb st = run_block f ctx bb st
Proof
  completeInduct_on `n` >> rw[] >>
  simp[Once run_block_def] >>
  `run_block f ctx bb st =
   case get_instruction bb st.vs_inst_idx of
     NONE => Error "block not terminated"
   | SOME inst =>
     case step_inst f ctx inst st of
       OK st' => if is_terminator inst.inst_opcode then
                   if st'.vs_halted then Halt st' else OK st'
                 else run_block f ctx bb (st' with vs_inst_idx := SUC st.vs_inst_idx)
     | Halt st' => Halt st'
     | Abort a st' => Abort a st'
     | IntRet vals st' => IntRet vals st'
     | Error e => Error e` by simp[Once run_block_def] >>
  Cases_on `get_instruction bb st.vs_inst_idx`
  >- gvs[]
  >- (
    rename1 `_ = SOME inst` >>
    gvs[] >>
    `!e. step_inst f ctx inst st <> Error e` by
      (spose_not_then strip_assume_tac >> gvs[]) >>
    `step_inst (f + k) ctx inst st = step_inst f ctx inst st` by
      (irule step_inst_fuel_mono >> simp[]) >>
    gvs[] >>
    Cases_on `step_inst f ctx inst st` >> gvs[]
    >- (
      rename1 `_ = OK st'` >>
      IF_CASES_TAC >> gvs[] >>
      `st'.vs_inst_idx = st.vs_inst_idx`
        by metis_tac[step_inst_preserves_inst_idx] >>
      `st.vs_inst_idx < LENGTH bb.bb_instructions`
        by (fs[get_instruction_def] >>
            Cases_on `st.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[]) >>
      first_x_assum irule >> simp[]
    )
  )
QED

Theorem run_function_fuel_mono:
  !fuel ctx fn s.
    terminates (run_function fuel ctx fn s) ==>
    !k. run_function (fuel + k) ctx fn s = run_function fuel ctx fn s
Proof
  completeInduct_on `fuel` >> rw[] >>
  Cases_on `fuel`
  >- fs[Once run_function_def, terminates_def]
  >- (
    rename1 `SUC f` >>
    `run_function (SUC f) ctx fn s =
     case lookup_block s.vs_current_bb fn.fn_blocks of
       NONE => Error "block not found"
     | SOME bb =>
         case run_block f ctx bb s of
           OK s' => if s'.vs_halted then Halt s'
                    else run_function f ctx fn s'
         | IntRet vals s' => IntRet vals s'
         | Halt s' => Halt s'
         | Abort a s' => Abort a s'
         | Error e => Error e` by simp[Once run_function_def] >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
    >- gvs[terminates_def]
    >- (
      rename1 `_ = SOME bb` >>
      `!e. run_block f ctx bb s <> Error e` by
        (spose_not_then strip_assume_tac >> gvs[terminates_def]) >>
      `!ctx' fn' s'. terminates (run_function f ctx' fn' s') ==>
         !k. run_function (f + k) ctx' fn' s' = run_function f ctx' fn' s'`
        by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
      `!k'. run_block (f + k') ctx bb s = run_block f ctx bb s` by
        metis_tac[run_block_fuel_mono_lem] >>
      `run_function (SUC f + k) ctx fn s =
       case lookup_block s.vs_current_bb fn.fn_blocks of
         NONE => Error "block not found"
       | SOME bb' =>
           case run_block (f + k) ctx bb' s of
             OK s' => if s'.vs_halted then Halt s'
                      else run_function (f + k) ctx fn s'
           | IntRet vals s' => IntRet vals s'
           | Halt s' => Halt s'
           | Abort a s' => Abort a s'
           | Error e => Error e`
        by (`SUC f + k = SUC (f + k)` by simp[] >>
            pop_assum SUBST1_TAC >> simp[Once run_function_def]) >>
      gvs[] >>
      Cases_on `run_block f ctx bb s` >> gvs[] >>
      rename1 `_ = OK v` >>
      IF_CASES_TAC >> gvs[terminates_def] >>
      first_x_assum irule >> simp[]
    )
  )
QED

Theorem run_block_fuel_mono:
  !f ctx bb s.
    (!e. run_block f ctx bb s <> Error e) ==>
    !k. run_block (f + k) ctx bb s = run_block f ctx bb s
Proof
  rpt strip_tac >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] run_block_fuel_mono_lem) >>
  simp[] >> metis_tac[run_function_fuel_mono]
QED

(* ===== Helper: merge_callee_state with execution_equiv ===== *)

(* If callee states have execution_equiv (side effects match), then
   merging with the same caller state produces identical results.
   This is the key lemma that makes non-caller simulation work:
   inline_vars differences in callee's vs_vars are discarded by merge. *)
Theorem merge_callee_execution_equiv:
  !vars c1 c2 caller.
    execution_equiv vars c1 c2 ==>
    merge_callee_state caller c1 = merge_callee_state caller c2
Proof
  rw[execution_equiv_def, merge_callee_state_def]
QED

(* ===== Helper: setup_callee entry label preservation ===== *)

(* If two functions have the same first block label and both are non-empty,
   setup_callee produces the same state. *)
Theorem setup_callee_same_entry:
  !fn1 fn2 args s.
    ~NULL fn1.fn_blocks /\ ~NULL fn2.fn_blocks /\
    (HD fn1.fn_blocks).bb_label = (HD fn2.fn_blocks).bb_label ==>
    setup_callee fn1 args s = setup_callee fn2 args s
Proof
  rw[setup_callee_def]
QED

(* ===== Same-function, different-context simulation ===== *)

(* When running the SAME function fn in two contexts ctx and ctx',
   starting from IDENTICAL state s, if for every INVOKE:
   (1) lookup correspondence holds (NONE maps to NONE), and
   (2) the IH guarantees callee simulation (with same starting state),
   then the results are equivalent.

   Key insight: merge_callee_state discards callee's vs_vars entirely,
   so any inline_vars differences in callee execution vanish at the
   caller level. After each INVOKE, caller states are IDENTICAL. *)

(* ===== Same-fuel simulation ===== *)

(* Key insight: when the callee_sim hypothesis uses the SAME fuel on both
   sides, step_inst for INVOKE produces IDENTICAL OK states (because
   merge_callee_state discards callee vs_vars). This avoids the fuel
   composition problem entirely — no need to find a single existential
   fuel that works for both the step and the continuation.

   The same-fuel callee_sim is achievable because same_fn_diff_ctx_sim
   is proved by induction on fuel, providing the IH at all f < fuel.
   Within run_block at fuel f, step_inst calls run_function at fuel f,
   and the IH covers f < SUC f = fuel. *)

(* ===== INVOKE Inversion Lemma ===== *)

(* When step_inst returns OK for INVOKE, extract all intermediate values.
   This eliminates repeated INVOKE case analysis across multiple lemmas. *)
Triviality step_inst_invoke_ok_inv:
  !fuel ctx inst s s1.
    inst.inst_opcode = INVOKE /\
    step_inst fuel ctx inst s = OK s1 ==>
    ?cn ao cfn args cs vals cs'.
      decode_invoke inst = SOME (cn, ao) /\
      lookup_function cn ctx.ctx_functions = SOME cfn /\
      eval_operands ao s = SOME args /\
      setup_callee cfn args s = SOME cs /\
      run_function fuel ctx cfn cs = IntRet vals cs' /\
      bind_outputs inst.inst_outputs vals (merge_callee_state s cs') = SOME s1
Proof
  rpt strip_tac >>
  pop_assum mp_tac >> simp[Once step_inst_def] >>
  BasicProvers.EVERY_CASE_TAC
QED

(* INVOKE expansion lemma: step_inst for INVOKE rewrites to the decode chain.
   Avoids repeated `simp[Once step_inst_def]` + backtick-by patterns. *)
Triviality step_inst_invoke_expand:
  !fuel ctx inst s.
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst s =
      case decode_invoke inst of
        NONE => Error "invoke: bad operand format"
      | SOME (callee_name, arg_ops) =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => Error "invoke: function not found"
          | SOME callee_fn =>
              case eval_operands arg_ops s of
                NONE => Error "invoke: undefined argument"
              | SOME args =>
                  case setup_callee callee_fn args s of
                    NONE => Error "invoke: empty function"
                  | SOME callee_s =>
                      case run_function fuel ctx callee_fn callee_s of
                        OK v => Error "invoke: callee did not return"
                      | Halt s'' => Halt s''
                      | Abort a s'' => Abort a s''
                      | IntRet vals callee_s' =>
                          (case bind_outputs inst.inst_outputs vals
                                  (merge_callee_state s callee_s') of
                            NONE => Error "invoke: return arity mismatch"
                          | SOME s'' => OK s'')
                      | Error e => Error e
Proof
  simp[Once step_inst_def]
QED

(* ===== Context simulation =====

   Master theorem: if two contexts have function correspondence
   (same names, matching entry labels), then running ANY function
   in either context produces equivalent results.

   Proved by completeInduct_on fuel. The IH provides both:
   - Callee pair sim (for INVOKE: fn1 from ctx, fn2 from ctx')
   - Same-fn sim (for run_function continuation) *)

(* --- Helper: run_block step equations --- *)

Triviality run_block_non_term_ok:
  !fuel ctx bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    run_block fuel ctx bb s =
      run_block fuel ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >> simp[Once run_block_def]
QED

Triviality run_block_term_ok:
  !fuel ctx bb s inst s'.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    run_block fuel ctx bb s =
      (if s'.vs_halted then Halt s' else OK s')
Proof
  rpt strip_tac >> simp[Once run_block_def]
QED

Triviality run_block_no_inst:
  !fuel ctx bb s.
    get_instruction bb s.vs_inst_idx = NONE ==>
    run_block fuel ctx bb s = Error "block not terminated"
Proof
  rpt strip_tac >> simp[Once run_block_def]
QED

Triviality run_block_non_ok:
  !fuel ctx bb s inst.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    (!s1. step_inst fuel ctx inst s <> OK s1) ==>
    run_block fuel ctx bb s = step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[]
QED

Triviality run_function_zero:
  !ctx fn s.
    run_function 0 ctx fn s = Error "out of fuel"
Proof
  simp[Once run_function_def]
QED

Triviality run_function_suc:
  !f ctx fn s.
    run_function (SUC f) ctx fn s =
      case lookup_block s.vs_current_bb fn.fn_blocks of
        NONE => Error "block not found"
      | SOME bb =>
          case run_block f ctx bb s of
            OK s'' =>
              if s''.vs_halted then Halt s'' else run_function f ctx fn s''
          | Halt s'' => Halt s''
          | Abort a s'' => Abort a s''
          | IntRet vals s'' => IntRet vals s''
          | Error e => Error e
Proof
  simp[Once run_function_def]
QED

(* NOTE: ctx_corr-based infrastructure (step_inst_ok_preserved,
   step_inst_result_equiv, run_block_ok_preserved, run_block_result_equiv)
   was removed — superseded by the stronger ctx_agree theorems below
   which prove EQUALITY (not just result_equiv) under identical lookups. *)

(* --- Fuel monotonicity helpers --- *)

Triviality step_inst_fuel_add:
  !f k ctx inst s.
    (!e. step_inst f ctx inst s <> Error e) ==>
    step_inst (f + k) ctx inst s = step_inst f ctx inst s
Proof
  rpt strip_tac >>
  irule step_inst_fuel_mono >> simp[] >>
  metis_tac[run_function_fuel_mono]
QED

Triviality run_block_fuel_add:
  !f k ctx bb s.
    (!e. run_block f ctx bb s <> Error e) ==>
    run_block (f + k) ctx bb s = run_block f ctx bb s
Proof
  rpt strip_tac >> irule run_block_fuel_mono >> simp[]
QED

(* ===== Context Agreement Simulation =====

   If lookup_function agrees on all names in two contexts,
   then run_function/run_block produce identical results.
   This is the foundation for remove_function correctness. *)

Triviality step_inst_ctx_agree:
  !fuel ctx ctx' inst s.
    (!name. lookup_function name ctx.ctx_functions =
            lookup_function name ctx'.ctx_functions) /\
    (!ctx1 ctx2 fn s'.
       (!name. lookup_function name ctx1.ctx_functions =
               lookup_function name ctx2.ctx_functions) ==>
       run_function fuel ctx1 fn s' = run_function fuel ctx2 fn s') ==>
    step_inst fuel ctx inst s = step_inst fuel ctx' inst s
Proof
  rpt strip_tac >>
  reverse (Cases_on `inst.inst_opcode = INVOKE`)
  >- simp[step_inst_non_invoke] >>
  `!fn' s'. run_function fuel ctx fn' s' = run_function fuel ctx' fn' s'`
    by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  (* Rewrite both ctx.ctx_functions and run_function fuel ctx
     to ctx' versions, making both sides identical *)
  PURE_ONCE_REWRITE_TAC[step_inst_def] >> simp[]
QED

Triviality run_block_ctx_agree_lem:
  !n fuel ctx ctx' bb s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    (!name. lookup_function name ctx.ctx_functions =
            lookup_function name ctx'.ctx_functions) /\
    (!ctx1 ctx2 fn s'.
       (!name. lookup_function name ctx1.ctx_functions =
               lookup_function name ctx2.ctx_functions) ==>
       run_function fuel ctx1 fn s' = run_function fuel ctx2 fn s') ==>
    run_block fuel ctx bb s = run_block fuel ctx' bb s
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `!inst. step_inst fuel ctx inst s = step_inst fuel ctx' inst s` by
    (rpt strip_tac >> match_mp_tac step_inst_ctx_agree >>
     simp[] >> metis_tac[]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (imp_res_tac run_block_no_inst >> gvs[])
  >> rename1 `_ = SOME inst` >>
  PURE_ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[]
  >- (
    rename1 `_ = OK s'` >>
    IF_CASES_TAC >> gvs[] >>
    `s'.vs_inst_idx = s.vs_inst_idx`
      by metis_tac[step_inst_preserves_inst_idx] >>
    `s.vs_inst_idx < LENGTH bb.bb_instructions` by
      (fs[get_instruction_def] >>
       Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[]) >>
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx`
      mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then irule >> simp[])
QED

Theorem run_function_ctx_agree:
  !fuel ctx ctx' fn s.
    (!name. lookup_function name ctx.ctx_functions =
            lookup_function name ctx'.ctx_functions) ==>
    run_function fuel ctx fn s = run_function fuel ctx' fn s
Proof
  completeInduct_on `fuel` >> rpt strip_tac >>
  Cases_on `fuel`
  >- simp[run_function_zero]
  >> rename1 `SUC f` >>
  simp[run_function_suc] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  rename1 `_ = SOME bb` >>
  `run_block f ctx bb s = run_block f ctx' bb s` by (
    qspecl_then [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
                 `f`, `ctx`, `ctx'`, `bb`, `s`]
      mp_tac run_block_ctx_agree_lem >>
    impl_tac >- (
      simp[] >> rpt strip_tac >>
      first_x_assum (qspec_then `f` mp_tac) >> simp[] >>
      metis_tac[]) >>
    simp[]) >>
  gvs[] >>
  Cases_on `run_block f ctx' bb s` >> gvs[] >>
  rename1 `_ = OK s'` >>
  IF_CASES_TAC >> gvs[]
QED

Theorem run_context_ctx_agree:
  !fuel ctx ctx' s.
    ctx.ctx_entry = ctx'.ctx_entry /\
    (!name. lookup_function name ctx.ctx_functions =
            lookup_function name ctx'.ctx_functions) ==>
    run_context fuel ctx s = run_context fuel ctx' s
Proof
  rw[run_context_def] >>
  CASE_TAC >> gvs[] >>
  CASE_TAC >> gvs[] >>
  CASE_TAC >> gvs[] >>
  irule run_function_ctx_agree >> simp[]
QED

(* ===== Remove Function Properties ===== *)

Theorem remove_function_entry_preserved:
  !name ctx. (remove_function name ctx).ctx_entry = ctx.ctx_entry
Proof
  rw[remove_function_def]
QED

Theorem lookup_function_remove_neq:
  !name name' fns.
    name' <> name ==>
    lookup_function name' (FILTER (\f. f.fn_name <> name) fns) =
    lookup_function name' fns
Proof
  Induct_on `fns` >> rpt strip_tac >>
  gvs[lookup_function_def, listTheory.FIND_thm] >>
  IF_CASES_TAC >> gvs[listTheory.FIND_thm]
QED

Theorem lookup_function_remove:
  !name name' ctx.
    name' <> name ==>
    lookup_function name' (remove_function name ctx).ctx_functions =
    lookup_function name' ctx.ctx_functions
Proof
  rw[remove_function_def] >>
  irule lookup_function_remove_neq >> simp[]
QED

(* If no INVOKE in the context targets 'name', then during execution
   lookup_function name is never called, so removing it is safe. *)

(* We don't need to track reachability — if the entry function
   is not 'name', and lookup_function agrees for all other names,
   then run_context is identical. The key insight: we just need
   to show that lookup_function name is never the name
   that step_inst looks up. *)

(* Simple version: if candidate ≠ entry and no lookup_function
   call within execution uses candidate_name, then removing is safe.
   We prove this using run_context_ctx_agree: if all lookups agree,
   execution is identical. For remove_function, lookups agree for
   all names except the removed one. So we need: during execution,
   lookup_function is only called with names ≠ candidate.

   Rather than tracking execution, we use a syntactic condition:
   no INVOKE instruction in any function targets candidate_name. *)

(* ===== No-invoke predicate ===== *)

(* An instruction targets callee_name if it's an INVOKE with
   first operand Label callee_name *)
Definition inst_targets_def:
  inst_targets callee_name inst <=>
    inst.inst_opcode = INVOKE /\
    case inst.inst_operands of
      Label l :: _ => l = callee_name
    | _ => F
End

(* No instruction in a function targets callee_name *)
Definition fn_no_invoke_def:
  fn_no_invoke callee_name fn <=>
    EVERY (\bb. EVERY (\inst. ~inst_targets callee_name inst)
                      bb.bb_instructions)
          fn.fn_blocks
End

(* No function in a context targets callee_name *)
Definition ctx_no_invoke_def:
  ctx_no_invoke callee_name ctx <=>
    EVERY (fn_no_invoke callee_name) ctx.ctx_functions
End

(* find_invoke_site = NONE iff no invoke targets callee_name *)
Theorem find_invoke_idx_none:
  !callee_name insts n.
    find_invoke_idx callee_name insts n = NONE <=>
    EVERY (\inst. ~inst_targets callee_name inst) insts
Proof
  Induct_on `insts` >>
  rw[find_invoke_idx_def, inst_targets_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >> metis_tac[]
QED

Theorem find_invoke_site_none:
  !callee_name bbs.
    find_invoke_site callee_name bbs = NONE <=>
    EVERY (\bb. EVERY (\inst. ~inst_targets callee_name inst)
                      bb.bb_instructions) bbs
Proof
  Induct_on `bbs` >>
  rw[find_invoke_site_def] >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >>
  gvs[find_invoke_idx_none] >>
  (* SOME case: find_invoke_idx ≠ NONE means ~EVERY *)
  `find_invoke_idx callee_name h.bb_instructions 0 <> NONE` by simp[] >>
  fs[find_invoke_idx_none, listTheory.NOT_EVERY]
QED

(* find_invoke_site result label is in the block list *)
Triviality find_invoke_site_label_mem:
  !callee_name bbs lbl idx.
    find_invoke_site callee_name bbs = SOME (lbl, idx) ==>
    MEM lbl (MAP (\b. b.bb_label) bbs)
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def] >>
  rpt gen_tac >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >>
  simp[] >> metis_tac[]
QED

(* inline_one_site = NONE iff find_invoke_site = NONE *)
Triviality inline_one_site_none:
  !caller callee ist.
    inline_one_site caller callee ist = NONE <=>
    find_invoke_site callee.fn_name caller.fn_blocks = NONE
Proof
  rw[inline_one_site_def] >>
  CASE_TAC >> gvs[] >> PairCases_on `x` >> gvs[]
QED

(* After inline_at_sites terminates with NONE, no invoke targets callee *)
Theorem inline_at_sites_no_invoke:
  !n caller callee ist caller' ist'.
    inline_at_sites n caller callee ist = (caller', ist') /\
    inline_one_site caller' callee ist' = NONE ==>
    fn_no_invoke callee.fn_name caller'
Proof
  rw[fn_no_invoke_def, inline_one_site_none, find_invoke_site_none]
QED

(* Count of INVOKE instructions targeting a specific function *)
Definition invoke_count_def:
  invoke_count name fn =
    LENGTH (FILTER (inst_targets name) (fn_insts fn))
End

(* invoke_count bounded by total instruction count *)
Triviality invoke_count_bound:
  invoke_count name fn <= LENGTH (fn_insts fn)
Proof
  rw[invoke_count_def, rich_listTheory.LENGTH_FILTER_LEQ]
QED

(* renumber preserves fn_no_invoke and invoke_count.
   inst_targets only checks inst_opcode and inst_operands, both preserved. *)
(* fn_insts_blocks = FLAT . MAP *)
Triviality fn_insts_blocks_flat:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* inst_targets factors through the instruction projection *)
Triviality inst_targets_proj:
  !name i1 i2.
    i1.inst_opcode = i2.inst_opcode /\
    i1.inst_operands = i2.inst_operands /\
    i1.inst_outputs = i2.inst_outputs ==>
    (inst_targets name i1 <=> inst_targets name i2)
Proof
  rw[inst_targets_def]
QED

Triviality invoke_count_renumber:
  !name func. invoke_count name (renumber_fn_inst_ids func) = invoke_count name func
Proof
  rw[invoke_count_def, fn_insts_def, fn_insts_blocks_flat] >>
  irule (INST_TYPE [beta |-> ``:opcode # operand list # string list``]
         filter_length_map_proj) >>
  qexists_tac `\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)` >>
  rw[renumber_fn_inst_ids_inst_proj] >>
  rw[inst_targets_proj]
QED

(* invoke_count = 0 iff fn_no_invoke *)
Triviality invoke_count_zero:
  invoke_count name fn = 0 <=> fn_no_invoke name fn
Proof
  rw[invoke_count_def, fn_no_invoke_def, fn_insts_def,
     fn_insts_blocks_flat, listTheory.LENGTH_NIL,
     listTheory.FILTER_EQ_NIL, listTheory.EVERY_FLAT,
     listTheory.EVERY_MAP, listTheory.EVERY_MEM]
QED

Triviality fn_no_invoke_renumber:
  !name func. fn_no_invoke name (renumber_fn_inst_ids func) <=> fn_no_invoke name func
Proof
  metis_tac[invoke_count_renumber, invoke_count_zero]
QED

(* find_invoke_idx SOME specification *)
Triviality find_invoke_idx_some:
  !name insts n idx.
    find_invoke_idx name insts n = SOME idx ==>
    idx >= n /\
    idx - n < LENGTH insts /\
    inst_targets name (EL (idx - n) insts) /\
    EVERY (\inst. ~inst_targets name inst) (TAKE (idx - n) insts)
Proof
  Induct_on `insts` >> simp[find_invoke_idx_def] >>
  rpt gen_tac >> IF_CASES_TAC >> strip_tac
  >- (gvs[inst_targets_def])
  >> first_x_assum drule >> strip_tac >>
  (`idx - n = SUC (idx - (n + 1))` by simp[]) >>
  gvs[listTheory.EL, listTheory.TAKE_def, inst_targets_def]
QED

(* FILTER over TAKE/EL/DROP decomposition *)
Triviality filter_take_el_drop:
  !P l i.
    i < LENGTH l /\ P (EL i l) /\ EVERY (\x. ~P x) (TAKE i l) ==>
    LENGTH (FILTER P l) =
    LENGTH (FILTER P (DROP (SUC i) l)) + 1
Proof
  Induct_on `l` >> simp[] >>
  rpt gen_tac >> Cases_on `i` >> simp[] >>
  simp[listTheory.TAKE_def, listTheory.DROP_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`P`, `n`] mp_tac) >> simp[]
QED

(* fn_insts_blocks distributes over append *)
Triviality fn_insts_blocks_append:
  !bbs1 bbs2.
    fn_insts_blocks (bbs1 ++ bbs2) =
    fn_insts_blocks bbs1 ++ fn_insts_blocks bbs2
Proof
  Induct_on `bbs1` >>
  simp[fn_insts_blocks_def, listTheory.APPEND_ASSOC]
QED

(* fn_insts_blocks over replace_block + appended blocks *)
Triviality fn_insts_blocks_replace_app:
  !lbl bb' bbs extra.
    fn_insts_blocks (replace_block lbl bb' bbs ++ extra) =
    fn_insts_blocks (replace_block lbl bb' bbs) ++ fn_insts_blocks extra
Proof
  Induct_on `bbs` >>
  simp[replace_block_def, fn_insts_blocks_def, fn_insts_blocks_append]
QED

(* FILTER over fn_insts_blocks distributes *)
Triviality filter_fn_insts_blocks_app:
  !P bbs1 bbs2.
    FILTER P (fn_insts_blocks (bbs1 ++ bbs2)) =
    FILTER P (fn_insts_blocks bbs1) ++ FILTER P (fn_insts_blocks bbs2)
Proof
  Induct_on `bbs1` >>
  simp[fn_insts_blocks_def, listTheory.FILTER_APPEND_DISTRIB]
QED

(* inst_targets is false when opcode <> INVOKE *)
Triviality inst_targets_not_invoke:
  !name inst. inst.inst_opcode <> INVOKE ==> ~inst_targets name inst
Proof
  rw[inst_targets_def]
QED

(* rewrite_inline_inst: every output satisfies ~inst_targets *)
Triviality rewrite_inline_inst_no_invoke:
  !ops outs ret inst pi insts pi' name.
    rewrite_inline_inst ops outs ret inst pi = (insts, pi') /\
    ~inst_targets name inst ==>
    EVERY (\i. ~inst_targets name i) insts
Proof
  rw[rewrite_inline_inst_def, LET_THM] >> gvs[] >>
  rw[listTheory.EVERY_APPEND, listTheory.EVERY_MEM,
     indexedListsTheory.MEM_MAPi] >>
  rw[inst_targets_not_invoke]
QED

(* rewrite_inline_insts preserves ~inst_targets *)
Triviality rewrite_inline_insts_no_invoke:
  !ops outs ret insts pi insts' pi' name.
    rewrite_inline_insts ops outs ret insts pi = (insts', pi') /\
    EVERY (\inst. ~inst_targets name inst) insts ==>
    EVERY (\inst. ~inst_targets name inst) insts'
Proof
  Induct_on `insts` >> simp[rewrite_inline_insts_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rpt strip_tac >> gvs[listTheory.EVERY_APPEND] >>
  imp_res_tac rewrite_inline_inst_no_invoke >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

(* rewrite_inline_blocks preserves fn_no_invoke when callee has no self-invoke *)
Triviality rewrite_inline_blocks_no_invoke:
  !ops outs ret_lbl blocks n blocks' n'.
    rewrite_inline_blocks ops outs ret_lbl blocks n = (blocks', n') /\
    EVERY (\bb. EVERY (\inst. ~inst_targets name inst) bb.bb_instructions)
      blocks ==>
    EVERY (\bb. EVERY (\inst. ~inst_targets name inst) bb.bb_instructions)
      blocks'
Proof
  Induct_on `blocks` >> simp[rewrite_inline_blocks_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rpt strip_tac >>
  gvs[rewrite_inline_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  metis_tac[rewrite_inline_insts_no_invoke]
QED

(* clone_instruction preserves opcode *)
Triviality clone_instruction_opcode:
  !prefix lbls inst.
    (clone_instruction prefix lbls inst).inst_opcode = inst.inst_opcode
Proof
  simp[clone_instruction_def]
QED

(* INVOKE targets in a function are external (not block labels).
   This is a basic well-formedness property: INVOKE's first operand
   is a function name, never an internal block label. *)
Definition invoke_targets_extern_def:
  invoke_targets_extern fn <=>
    EVERY (\inst.
      inst.inst_opcode = INVOKE ==>
      case inst.inst_operands of
        Label l :: _ => ~MEM l (fn_labels fn)
      | _ => T)
    (fn_insts fn)
End

(* Per-instruction: clone preserves ~inst_targets when targets are external *)
Triviality clone_instruction_no_invoke:
  !prefix lbls inst name.
    ~inst_targets name inst /\
    (inst.inst_opcode = INVOKE ==>
      case inst.inst_operands of
        Label l :: _ => ~MEM l lbls
      | _ => T) ==>
    ~inst_targets name (clone_instruction prefix lbls inst)
Proof
  rpt strip_tac
  \\ gvs[inst_targets_def, clone_instruction_def]
  \\ Cases_on `inst.inst_operands` \\ gvs[]
  \\ rename1 `clone_operand _ _ h`
  \\ Cases_on `h` \\ gvs[clone_operand_def]
  \\ Cases_on `MEM s lbls` \\ gvs[]
QED

(* clone_function preserves fn_no_invoke when INVOKE targets are external *)
Triviality clone_function_no_invoke:
  !prefix callee name.
    fn_no_invoke name callee /\
    invoke_targets_extern callee ==>
    fn_no_invoke name (clone_function prefix callee)
Proof
  rw[fn_no_invoke_def, clone_function_def, LET_THM,
     invoke_targets_extern_def, fn_insts_def,
     listTheory.EVERY_MAP, clone_basic_block_def,
     listTheory.EVERY_MEM, listTheory.EVERY_FLAT,
     listTheory.MEM_MAP, PULL_EXISTS]
  \\ rpt strip_tac
  \\ rename1 `MEM orig_bb callee.fn_blocks`
  \\ rename1 `MEM orig_inst orig_bb.bb_instructions`
  \\ `MEM orig_inst (fn_insts_blocks callee.fn_blocks)` by (
       simp[listTheory.MEM_FLAT, listTheory.MEM_MAP,
            fn_insts_blocks_flat] >>
       metis_tac[])
  \\ metis_tac[clone_instruction_no_invoke]
QED

(* subst_label_inst preserves ~inst_targets for non-INVOKE instructions *)
Triviality subst_label_inst_no_invoke:
  !old new inst name.
    inst.inst_opcode <> INVOKE ==>
    ~inst_targets name (subst_label_inst old new inst)
Proof
  rw[inst_targets_def, subst_label_inst_def]
QED

(* fix_inline_phis preserves fn_no_invoke:
   only modifies PHI instructions (changes operands via subst_label_inst),
   and PHI <> INVOKE so inst_targets is unchanged *)
Triviality fix_inline_phis_no_invoke:
  !orig new_lbl ret_bb func name.
    fn_no_invoke name func ==>
    fn_no_invoke name (fix_inline_phis orig new_lbl ret_bb func)
Proof
  rw[fn_no_invoke_def, fix_inline_phis_def, LET_THM,
     listTheory.EVERY_MAP, listTheory.EVERY_MEM,
     listTheory.MEM_MAP, PULL_EXISTS]
  \\ rpt strip_tac
  \\ rename1 `MEM orig_bb func.fn_blocks`
  \\ Cases_on `MEM orig_bb.bb_label (bb_succs ret_bb)` \\ gvs[]
  \\ TRY (metis_tac[])
  \\ gvs[listTheory.MEM_MAP]
  \\ rename1 `MEM orig_inst orig_bb.bb_instructions`
  \\ Cases_on `orig_inst.inst_opcode = PHI` \\ gvs[]
  \\ TRY (metis_tac[])
  \\ gvs[inst_targets_def, subst_label_inst_def]
QED

(* Non-INVOKE instructions: subst_label_inst preserves inst_targets *)
Triviality subst_label_inst_inst_targets:
  !old new inst name.
    inst.inst_opcode <> INVOKE ==>
    (inst_targets name (subst_label_inst old new inst) <=>
     inst_targets name inst)
Proof
  rw[inst_targets_def, subst_label_inst_def]
QED

(* Helper: MAP that conditionally applies subst_label_inst to PHI instructions
   preserves FILTER with inst_targets *)
Triviality filter_inst_targets_map_phi_subst:
  !insts old new name.
    FILTER (inst_targets name)
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                   else subst_label_inst old new inst) insts) =
    FILTER (inst_targets name) insts
Proof
  Induct >> simp[] >> rw[] >>
  gvs[inst_targets_def, subst_label_inst_def]
QED

(* fix_inline_phis preserves invoke_count: only modifies PHI operands,
   and PHI <> INVOKE so inst_targets is unaffected *)
Triviality fix_inline_phis_invoke_count:
  !orig new_lbl ret_bb func name.
    invoke_count name (fix_inline_phis orig new_lbl ret_bb func) =
    invoke_count name func
Proof
  rw[invoke_count_def, fn_insts_def, fix_inline_phis_def, LET_THM] >>
  AP_TERM_TAC >>
  qspec_tac (`func.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def, listTheory.FILTER_APPEND_DISTRIB] >>
  rw[] >> simp[filter_inst_targets_map_phi_subst]
QED

(* MAP with always-false condition is identity *)
Triviality map_cond_false_id:
  !P y l. EVERY (\x. ~P x) l ==>
          MAP (\x. if P x then y else x) l = l
Proof
  Induct_on `l` >> simp[]
QED

(* MAP with condition that's always false is identity *)
Triviality map_if_false_id:
  !lbl bb' bbs.
    EVERY (\b. b.bb_label <> lbl) bbs ==>
    MAP (\bb. if bb.bb_label = lbl then bb' else bb) bbs = bbs
Proof
  Induct_on `bbs` >> simp[]
QED

(* Replacing a block with one that has no P-matches can only decrease
   the total FILTER count. No ALL_DISTINCT needed. *)
Triviality filter_fn_insts_replace_block_mono:
  !P lbl (bb':basic_block) bbs.
    EVERY (\inst. ~P inst) bb'.bb_instructions ==>
    LENGTH (FILTER P (fn_insts_blocks (replace_block lbl bb' bbs))) <=
    LENGTH (FILTER P (fn_insts_blocks bbs))
Proof
  ntac 3 gen_tac >> Induct >>
  simp[replace_block_def, fn_insts_blocks_def,
       listTheory.FILTER_APPEND_DISTRIB, listTheory.LENGTH_APPEND] >>
  rpt strip_tac >>
  `LENGTH (FILTER P bb'.bb_instructions) = 0`
    by simp[listTheory.LENGTH_NIL, listTheory.FILTER_EQ_NIL] >>
  Cases_on `h.bb_label = lbl` >>
  gvs[replace_block_def]
QED

(* When a block with label lbl is a MEM of bbs, replacing all blocks
   with that label by a no-P-match block decreases count by at least
   bb's contribution. No ALL_DISTINCT needed. *)
Triviality filter_fn_insts_replace_block_le:
  !P lbl (bb':basic_block) bbs bb.
    MEM bb bbs /\ bb.bb_label = lbl /\
    EVERY (\inst. ~P inst) bb'.bb_instructions ==>
    LENGTH (FILTER P (fn_insts_blocks (replace_block lbl bb' bbs))) +
    LENGTH (FILTER P bb.bb_instructions) <=
    LENGTH (FILTER P (fn_insts_blocks bbs))
Proof
  ntac 3 gen_tac >> Induct >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[replace_block_def, fn_insts_blocks_def,
       listTheory.FILTER_APPEND_DISTRIB, listTheory.LENGTH_APPEND] >>
  `LENGTH (FILTER P bb'.bb_instructions) = 0`
    by simp[listTheory.LENGTH_NIL, listTheory.FILTER_EQ_NIL]
  >- (* bb = head: use mono on tail *)
     (simp[GSYM replace_block_def] >>
      qspecl_then [`P`, `bb.bb_label`, `bb'`, `bbs`]
        mp_tac filter_fn_insts_replace_block_mono >>
      simp[])
  >> (* MEM bb bbs *)
  Cases_on `h.bb_label = bb.bb_label` >> gvs[] >>
  simp[GSYM replace_block_def] >>
  first_x_assum (qspecl_then [`bb`] mp_tac) >> simp[]
QED

(* lookup_block returns a block with the matching label *)
Triviality lookup_block_label:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  rw[lookup_block_def] >>
  Induct_on `bbs` >> gvs[listTheory.FIND_thm] >> rw[] >> gvs[] >> metis_tac[]
QED

(* Core lemma: inline_call_site decreases invoke count. *)
Triviality inline_call_site_invoke_count:
  !prefix ret_lbl fn callee bb_lbl idx call_bb name.
    name = callee.fn_name /\
    fn_no_invoke name callee /\
    invoke_targets_extern callee /\
    lookup_block bb_lbl fn.fn_blocks = SOME call_bb /\
    find_invoke_idx name call_bb.bb_instructions 0 = SOME idx ==>
    invoke_count name (inline_call_site prefix ret_lbl fn callee bb_lbl idx)
    < invoke_count name fn
Proof
  rw[invoke_count_def, fn_insts_def, inline_call_site_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  (* Decompose fn_insts_blocks over concatenated blocks *)
  simp[filter_fn_insts_blocks_app, fn_insts_blocks_def,
       listTheory.FILTER_APPEND_DISTRIB, listTheory.LENGTH_APPEND] >>
  (* Get properties from find_invoke_idx *)
  imp_res_tac find_invoke_idx_some >> gvs[] >>
  (* Use MEM-based _le: lookup_block gives MEM and label match *)
  imp_res_tac lookup_block_MEM >>
  imp_res_tac lookup_block_label >>
  `LENGTH (FILTER (inst_targets callee.fn_name) (fn_insts_blocks
      (replace_block bb_lbl
        (call_bb with bb_instructions :=
           TAKE idx call_bb.bb_instructions ++
           [<|inst_id := 0; inst_opcode := JMP;
              inst_operands :=
                [Label (case (clone_function prefix callee).fn_blocks
                        of [] => "" | eb::v1 => eb.bb_label)];
              inst_outputs := []|>])
        fn.fn_blocks))) +
   LENGTH (FILTER (inst_targets callee.fn_name) call_bb.bb_instructions) <=
   LENGTH (FILTER (inst_targets callee.fn_name) (fn_insts_blocks fn.fn_blocks))` by (
    irule filter_fn_insts_replace_block_le >> simp[] >>
    simp[listTheory.EVERY_APPEND, inst_targets_def,
         listTheory.EVERY_MEM] >>
    rpt strip_tac >>
    imp_res_tac rich_listTheory.MEM_TAKE >> res_tac) >>
  (* Use filter_take_el_drop on call_bb *)
  `LENGTH (FILTER (inst_targets callee.fn_name) call_bb.bb_instructions) =
   LENGTH (FILTER (inst_targets callee.fn_name)
     (DROP (SUC idx) call_bb.bb_instructions)) + 1` by (
    irule filter_take_el_drop >> simp[]) >>
  (* Rewritten blocks have no inst_targets *)
  `fn_no_invoke callee.fn_name (clone_function prefix callee)` by
    metis_tac[clone_function_no_invoke] >>
  `EVERY (\b. EVERY (\inst. ~inst_targets callee.fn_name inst)
              b.bb_instructions) rewritten_blocks` by (
    mp_tac (rewrite_inline_blocks_no_invoke |> Q.GEN `name`
            |> Q.SPEC `callee.fn_name`) >>
    gvs[fn_no_invoke_def] >> metis_tac[]) >>
  `LENGTH (FILTER (inst_targets callee.fn_name)
     (fn_insts_blocks rewritten_blocks)) = 0` by (
    simp[listTheory.LENGTH_NIL, listTheory.FILTER_EQ_NIL,
         fn_insts_blocks_flat, listTheory.EVERY_FLAT, listTheory.EVERY_MAP] >>
    gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `SUC idx = idx + 1` by simp[] >>
  gvs[]
QED

(* find_invoke_site SOME gives a block and index (needs unique labels) *)
Triviality find_invoke_site_some:
  !callee_name bbs lbl idx.
    find_invoke_site callee_name bbs = SOME (lbl, idx) /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    ?bb. lookup_block lbl bbs = SOME bb /\
         find_invoke_idx callee_name bb.bb_instructions 0 = SOME idx
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def] >>
  rpt gen_tac >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >> simp[] >>
  strip_tac >> gvs[] >| [
    first_x_assum drule >> strip_tac >>
    qexists_tac `bb` >>
    simp[lookup_block_def, listTheory.FIND_thm] >>
    imp_res_tac find_invoke_site_label_mem >>
    Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def],
    qexists_tac `h` >> simp[lookup_block_def, listTheory.FIND_thm]
  ]
QED

(* inline_one_site with non-self-invoking callee decreases invoke count *)
Triviality inline_one_site_decreases_invocations:
  !fn callee ist fn' ist'.
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels fn) /\
    inline_one_site fn callee ist = SOME (fn', ist') ==>
    invoke_count callee.fn_name fn' < invoke_count callee.fn_name fn
Proof
  rw[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name fn.fn_blocks` >> gvs[] >>
  PairCases_on `x` >> gvs[LET_THM, invoke_count_renumber] >>
  rename1 `find_invoke_site _ _ = SOME (bb_lbl, idx)` >>
  (* fix_inline_phis preserves invoke_count *)
  CASE_TAC >> gvs[fix_inline_phis_invoke_count] >>
  TRY (PairCases_on `x` >> gvs[fix_inline_phis_invoke_count]) >>
  (* Use inline_call_site_invoke_count *)
  irule inline_call_site_invoke_count >>
  imp_res_tac find_invoke_site_some >>
  gvs[fn_labels_def]
QED

Triviality inline_one_site_is_inline_count:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') ==>
    ist'.is_inline_count = ist.is_inline_count + 1
Proof
  rw[inline_one_site_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[]
QED

(* Combined invariant for inline_at_sites:
   fn_no_invoke, ALL_DISTINCT, labels_fresh_above preserved,
   and is_inline_count only increases *)
Triviality inline_at_sites_fn_no_invoke:
  !n fn callee ist fn' ist'.
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    labels_fresh_above ist.is_inline_count fn /\
    invoke_count callee.fn_name fn <= n /\
    inline_at_sites n fn callee ist = (fn', ist') ==>
    fn_no_invoke callee.fn_name fn' /\
    ALL_DISTINCT (fn_labels fn') /\
    labels_fresh_above ist'.is_inline_count fn' /\
    ist.is_inline_count <= ist'.is_inline_count
Proof
  Induct >>
  rpt gen_tac >> strip_tac >>
  fs[inline_at_sites_def]
  (* Base case: inline_at_sites 0 = id, invoke_count = 0 *)
  >- (imp_res_tac invoke_count_zero >> simp[])
  (* Step case *)
  >> Cases_on `inline_one_site fn callee ist` >> gvs[]
  (* NONE: fn unchanged, invoke_one_site_none => fn_no_invoke *)
  >- (gvs[inline_one_site_none, find_invoke_site_none, fn_no_invoke_def])
  (* SOME: inline_one_site succeeded *)
  >> PairCases_on `x` >> gvs[] >>
  rename1 `inline_one_site fn callee ist = SOME (fn1, ist1)` >>
  `ist1.is_inline_count = ist.is_inline_count + 1`
    by metis_tac[inline_one_site_is_inline_count] >>
  (* Derive the 3 non-trivial IH prerequisites *)
  `ALL_DISTINCT (fn_labels fn1)` by
    metis_tac[inline_one_site_all_distinct, ret_lbl_not_in_mapped_callee_weak] >>
  `labels_fresh_above ist1.is_inline_count fn1` by
    metis_tac[labels_fresh_above_inline_one_site] >>
  `invoke_count callee.fn_name fn1 <= n` by (
    imp_res_tac inline_one_site_decreases_invocations >> simp[]) >>
  (* Apply IH *)
  first_x_assum (qspecl_then [`fn1`, `callee`, `ist1`, `fn'`, `ist'`]
    mp_tac) >>
  simp[]
QED

(* FOLDL of inline_at_sites preserves fn_no_invoke *)
Triviality foldl_inline_fn_no_invoke:
  !fns0 acc ist0 callee result ist1.
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) fns0 /\
    EVERY (\f. labels_fresh_above ist0.is_inline_count f) fns0 /\
    FOLDL (\(fns_acc, st) caller_fn.
      let max_sites = LENGTH (fn_insts caller_fn) in
      let (caller', st') = inline_at_sites max_sites caller_fn callee st in
      (SNOC caller' fns_acc, st'))
      (acc, ist0) fns0 = (result, ist1) /\
    EVERY (fn_no_invoke callee.fn_name) acc ==>
    EVERY (fn_no_invoke callee.fn_name) result
Proof
  Induct >- (rw[] >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  gvs[LET_THM] >>
  pairarg_tac >> gvs[] >>
  `fn_no_invoke callee.fn_name caller' /\
   ALL_DISTINCT (fn_labels caller') /\
   labels_fresh_above st'.is_inline_count caller' /\
   ist0.is_inline_count <= st'.is_inline_count` by
    metis_tac[inline_at_sites_fn_no_invoke, invoke_count_bound] >>
  first_x_assum irule >> simp[] >>
  MAP_EVERY qexists_tac [`SNOC caller' acc`, `st'`, `ist1`] >>
  simp[listTheory.EVERY_SNOC] >>
  irule listTheory.MONO_EVERY >>
  qexists_tac `\f. labels_fresh_above ist0.is_inline_count f` >>
  simp[] >> rpt strip_tac >>
  irule labels_fresh_above_mono >>
  qexists_tac `ist0.is_inline_count` >> simp[]
QED

(* inline_candidate establishes ctx_no_invoke for the callee *)
Theorem inline_candidate_no_invoke:
  !ctx callee ist ctx' ist'.
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
    EVERY (\f. labels_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    inline_candidate ctx callee ist = (ctx', ist') ==>
    ctx_no_invoke callee.fn_name ctx'
Proof
  rw[inline_candidate_def, LET_THM, ctx_no_invoke_def] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`ctx.ctx_functions`, `[]`, `ist`, `callee`, `fns'`, `ist'`]
    mp_tac foldl_inline_fn_no_invoke >>
  simp[LET_THM]
QED


(* ===== Partial context agreement =====
   If two contexts agree on all function lookups EXCEPT name,
   and ALL functions reachable from ctx satisfy fn_no_invoke name,
   then execution is identical.

   Key insight: fn_no_invoke guarantees lookup_function name is never
   used during execution, so the disagreement doesn't matter. *)

(* Helper: get_instruction returns an element of bb_instructions *)
Triviality get_instruction_mem:
  !bb idx inst.
    get_instruction bb idx = SOME inst ==>
    MEM inst bb.bb_instructions
Proof
  rw[get_instruction_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  metis_tac[rich_listTheory.EL_MEM]
QED

(* ===== step_inst partial agreement =====
   Extracted from the repeated INVOKE case analysis pattern.
   If ~inst_targets name inst, lookups agree except name,
   EVERY fn_no_invoke name ctx.ctx_functions, and an IH for
   run_function, then step_inst is identical in both contexts. *)
Triviality step_inst_partial_agree:
  !fuel ctx ctx' name inst s.
    ~inst_targets name inst /\
    (!name'. name' <> name ==>
       lookup_function name' ctx.ctx_functions =
       lookup_function name' ctx'.ctx_functions) /\
    EVERY (fn_no_invoke name) ctx.ctx_functions /\
    (!ctx1 ctx2 fn s'.
       (!name'. name' <> name ==>
          lookup_function name' ctx1.ctx_functions =
          lookup_function name' ctx2.ctx_functions) /\
       EVERY (fn_no_invoke name) ctx1.ctx_functions /\
       fn_no_invoke name fn ==>
       run_function fuel ctx1 fn s' = run_function fuel ctx2 fn s') ==>
    step_inst fuel ctx inst s = step_inst fuel ctx' inst s
Proof
  rpt strip_tac >>
  reverse (Cases_on `inst.inst_opcode = INVOKE`)
  >- simp[step_inst_non_invoke] >>
  simp[step_inst_invoke_expand] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  (* SOME case: extract callee name and args *)
  rename1 `_ = SOME ca` >> PairCases_on `ca` >>
  rename1 `decode_invoke inst = SOME (cn, ao)` >>
  (* cn <> name from ~inst_targets *)
  `cn <> name` by (
    gvs[inst_targets_def, decode_invoke_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[]) >>
  (* Replace ctx.ctx_functions lookups with ctx' using the agree hyp *)
  `lookup_function cn ctx.ctx_functions =
   lookup_function cn ctx'.ctx_functions` by metis_tac[] >>
  simp[] >>
  Cases_on `lookup_function cn ctx'.ctx_functions` >> gvs[] >>
  rename1 `lookup_function cn ctx'.ctx_functions = SOME cfn` >>
  Cases_on `eval_operands ao s` >> gvs[] >>
  rename1 `eval_operands ao s = SOME args` >>
  Cases_on `setup_callee cfn args s` >> gvs[] >>
  rename1 `setup_callee cfn args s = SOME cs` >>
  `fn_no_invoke name cfn` by (
    `lookup_function cn ctx.ctx_functions = SOME cfn` by gvs[] >>
    gvs[listTheory.EVERY_MEM] >>
    metis_tac[lookup_function_MEM]) >>
  `run_function fuel ctx cfn cs = run_function fuel ctx' cfn cs` by (
    first_x_assum irule >> simp[]) >>
  simp[]
QED

(* run_block with partial agreement —
   Mirrors run_block_ctx_agree_lem but with partial lookup agreement. *)
Triviality run_block_partial_agree_lem:
  !n fuel ctx ctx' name bb s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    (!name'. name' <> name ==>
       lookup_function name' ctx.ctx_functions =
       lookup_function name' ctx'.ctx_functions) /\
    EVERY (fn_no_invoke name) ctx.ctx_functions /\
    EVERY (\inst. ~inst_targets name inst) bb.bb_instructions /\
    (!ctx1 ctx2 fn s'.
       (!name'. name' <> name ==>
          lookup_function name' ctx1.ctx_functions =
          lookup_function name' ctx2.ctx_functions) /\
       EVERY (fn_no_invoke name) ctx1.ctx_functions /\
       fn_no_invoke name fn ==>
       run_function fuel ctx1 fn s' = run_function fuel ctx2 fn s') ==>
    run_block fuel ctx bb s = run_block fuel ctx' bb s
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (imp_res_tac run_block_no_inst >> gvs[])
  >> rename1 `_ = SOME inst` >>
  `~inst_targets name inst` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[get_instruction_mem]) >>
  `step_inst fuel ctx inst s = step_inst fuel ctx' inst s` by
    (irule step_inst_partial_agree >>
     qexists_tac `name` >> simp[]) >>
  (* Expand run_block on both sides *)
  PURE_ONCE_REWRITE_TAC[run_block_def] >>
  ASM_REWRITE_TAC[] >>
  Cases_on `step_inst fuel ctx' inst s` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  (`s.vs_inst_idx < LENGTH bb.bb_instructions` by
     (gvs[get_instruction_def] >>
      Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[])) >>
  first_x_assum irule >>
  simp[] >> qexists_tac `name` >> simp[]
QED

(* run_function with partial agreement *)
Theorem run_function_partial_agree:
  !fuel ctx ctx' name fn s.
    (!name'. name' <> name ==>
       lookup_function name' ctx.ctx_functions =
       lookup_function name' ctx'.ctx_functions) /\
    EVERY (fn_no_invoke name) ctx.ctx_functions /\
    fn_no_invoke name fn ==>
    run_function fuel ctx fn s = run_function fuel ctx' fn s
Proof
  completeInduct_on `fuel` >> rpt strip_tac >>
  Cases_on `fuel`
  >- simp[run_function_zero]
  >> rename1 `SUC f` >>
  simp[run_function_suc] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  rename1 `_ = SOME bb` >>
  `EVERY (\inst. ~inst_targets name inst) bb.bb_instructions` by (
    imp_res_tac lookup_block_MEM >>
    gvs[fn_no_invoke_def, listTheory.EVERY_MEM] >> res_tac) >>
  `run_block f ctx bb s = run_block f ctx' bb s` by (
    irule run_block_partial_agree_lem >> simp[] >>
    qexists_tac `name` >> simp[] >>
    rpt strip_tac >>
    first_x_assum (qspec_then `f` mp_tac) >> simp[] >>
    metis_tac[]) >>
  gvs[] >>
  Cases_on `run_block f ctx' bb s` >> gvs[] >>
  rename1 `_ = OK s'` >>
  IF_CASES_TAC >> gvs[] >>
  first_x_assum (qspec_then `f` mp_tac) >> simp[] >>
  metis_tac[]
QED

(* run_context with partial agreement *)
Theorem run_context_partial_agree:
  !fuel ctx ctx' name s.
    ctx.ctx_entry = ctx'.ctx_entry /\
    ctx.ctx_entry <> SOME name /\
    (!name'. name' <> name ==>
       lookup_function name' ctx.ctx_functions =
       lookup_function name' ctx'.ctx_functions) /\
    EVERY (fn_no_invoke name) ctx.ctx_functions ==>
    run_context fuel ctx s = run_context fuel ctx' s
Proof
  rw[run_context_def] >>
  CASE_TAC >> gvs[] >>
  rename1 `_ = SOME en` >>
  `en <> name` by (CCONTR_TAC >> gvs[]) >>
  `lookup_function en ctx.ctx_functions =
   lookup_function en ctx'.ctx_functions` by simp[] >>
  CASE_TAC >> gvs[] >>
  rename1 `_ = SOME efn` >>
  CASE_TAC >> gvs[] >>
  irule run_function_partial_agree >>
  qexists_tac `name` >> simp[] >>
  `lookup_function en ctx.ctx_functions = SOME efn` by metis_tac[] >>
  imp_res_tac lookup_function_MEM >>
  gvs[listTheory.EVERY_MEM, fn_no_invoke_def] >>
  metis_tac[]
QED

(* remove_function_correct: if ctx_no_invoke name and name ≠ entry,
   then removing doesn't change execution *)
Theorem remove_function_correct:
  !name ctx fuel s.
    ctx.ctx_entry <> SOME name /\
    EVERY (fn_no_invoke name) ctx.ctx_functions ==>
    run_context fuel (remove_function name ctx) s =
    run_context fuel ctx s
Proof
  rpt strip_tac >>
  irule EQ_SYM >>
  irule run_context_partial_agree >>
  simp[remove_function_entry_preserved] >>
  qexists_tac `name` >>
  simp[] >>
  rpt strip_tac >> simp[lookup_function_remove]
QED

val _ = export_theory();
