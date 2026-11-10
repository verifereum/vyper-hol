(*
 * Memory-safe fragment execution
 *
 * frag_exec_mem is frag_exec that also tracks memory safety
 * (mem_safe_run): every instruction the run executes, callee frames
 * included, reads and writes memory below the allocation frontier.  Where
 * the fragment ends normally, a run from its end that is memory-safe is a
 * run from its start that is memory-safe; where it exits, the run to the
 * exit is memory-safe.  frag_exec_mem gives frag_exec, so a lemma proved in
 * this form also gives its frag_exec version.
 *
 * TOP-LEVEL:
 *   frag_exec_mem             — the judgment
 *   frag_exec_mem_frag_exec   — it gives frag_exec
 *   mem_safe_run_fuel_mono_up — more fuel, when run_from does not fail
 *   frag_exec_mem_seq, frag_exec_mem_seq_pointwise, frag_exec_mem_then
 *                             — sequencing
 *   frag_exec_mem_conseq, frag_exec_mem_refl, frag_exec_mem_pointwise,
 *   frag_exec_mem_false_pre, frag_exec_mem_exit_prefix,
 *   frag_exec_mem_weaken, frag_exec_mem_pre_exit(_c)
 *                             — as for frag_exec
 *   frag_exec_mem_step        — one straight-line instruction
 *   frag_exec_mem_step_abort, frag_exec_mem_assert_fail, stop_frag_mem
 *                             — abort and halt lifting
 *   revert_forward_frag_mem   — the exempt RETURNDATACOPY/REVERT pair
 *   mstore_alloca_frag_mem    — an MSTORE into an ALLOCA'd buffer
 *   run_inst_seq_mem_ok       — every instruction of a straight-line
 *                               sequence is below the frontier where it runs
 *   run_inst_seq_mem_ok_last, run_inst_seq_mem_ok_cons,
 *   run_inst_seq_mem_ok_append
 *                             — unfolding and composing it
 *   frag_exec_mem_run_inst_seq
 *                             — a straight-line fragment, by run_inst_seq
 *
 * Helpers:
 *   run_from_step_exit        — a step that does not continue ends the run
 *   mem_safe_run_inst_seq     — run_inst_seq_mem_ok lifts to mem_safe_run
 *)

Theory fragExecMem
Ancestors
  list rich_list compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomExecProofs venomInst venomInstProofs venomState
  venomMemDefs codegenRel contextCodegenRel unitTransformDefs fragExec memSafeRun
  instIdxIndep instMemFrontier

(* ===== Definition ===== *)

(* frag_exec, where a run from the end transfers to a run from the start
   that is memory-safe whenever the run from the end is, and the run to an
   exit is memory-safe. *)
Definition frag_exec_mem_def:
  frag_exec_mem ctx (st : compile_state) (st' : compile_state) P Q R <=>
    !fn s.
      fn_has_code st st' fn /\ P s /\ ~s.vs_halted /\
      s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      (?s'. Q s' /\ ~s'.vs_halted /\
            s'.vs_current_bb = st'.cs_current_bb /\
            s'.vs_inst_idx = LENGTH st'.cs_current_insts /\
            !fuel r. run_from fuel ctx fn s' = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn s = r /\
                             (mem_safe_run fuel ctx fn s' ==>
                              mem_safe_run fuel' ctx fn s)) \/
      (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
                mem_safe_run fuel ctx fn s)
End

Theorem frag_exec_mem_frag_exec:
  !ctx st st' P Q R.
    frag_exec_mem ctx st st' P Q R ==> frag_exec ctx st st' P Q R
Proof
  rw[frag_exec_mem_def, frag_exec_def] >>
  first_x_assum (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> qexists_tac `s'` >> simp[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

(* ===== Fuel ===== *)

Theorem mem_safe_run_fuel_mono_up:
  !n m ctx fn s.
    mem_safe_run n ctx fn s /\ (!e. run_from n ctx fn s <> Error e) /\
    n <= m ==> mem_safe_run m ctx fn s
Proof
  rpt gen_tac >> simp[mem_safe_run_def, run_from_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >> rpt strip_tac >>
  `!e. exec_block n ctx bb s <> Error e` by (rpt strip_tac >> gvs[]) >>
  `exec_block m ctx bb s = exec_block n ctx bb s` by
    (qspecl_then [`n`, `m`, `ctx`, `bb`, `s`, `exec_block n ctx bb s`]
       mp_tac (cj 2 fuel_mono) >> simp[]) >>
  pop_assum SUBST1_TAC
  >- metis_tac[mem_safe_fuel_mono_up] >>
  Cases_on `exec_block n ctx bb s` >> gvs[] >> rw[] >> gvs[] >>
  metis_tac[mem_safe_fuel_mono_up]
QED

(* A safe terminating continuation covers every smaller prefix and every
   larger fuel budget.  A fragment's conditional transfer needs such a
   continuation; it does not establish one by itself. *)
Theorem mem_safe_run_all_fuel:
  !fuel ctx fn s.
    mem_safe_run fuel ctx fn s /\ (!e. run_from fuel ctx fn s <> Error e) ==>
    !m. mem_safe_run m ctx fn s
Proof
  rpt strip_tac >> Cases_on `m <= fuel`
  >- metis_tac[mem_safe_run_fuel_mono_down] >>
  irule mem_safe_run_fuel_mono_up >> qexists_tac `fuel` >> simp[]
QED

(* Entry/halt composition supplies a safe terminal continuation at every
   normal body landing.  Exits already carry their own terminal witness. *)
Theorem frag_exec_mem_complete:
  !ctx sa sb P Q R fn s0.
    frag_exec_mem ctx sa sb P Q R /\ fn_has_code sa sb fn /\
    P s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!s. Q s /\ ~s.vs_halted /\
         s.vs_current_bb = sb.cs_current_bb /\
         s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
         ?fuel r. run_from fuel ctx fn s = r /\ (!e. r <> Error e) /\
                  mem_safe_run fuel ctx fn s) ==>
    !fuel. mem_safe_run fuel ctx fn s0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [frag_exec_mem_def]) >>
  disch_then (qspecl_then [`fn`, `s0`] mp_tac) >> simp[] >> strip_tac
  >- (qpat_x_assum `!s. Q s /\ _ ==> _`
        (qspec_then `s'` mp_tac) >> simp[] >> strip_tac >>
      metis_tac[mem_safe_run_all_fuel]) >>
  metis_tac[exit_result_not_error, mem_safe_run_all_fuel]
QED

(* ===== Judgment rules ===== *)

Theorem frag_exec_mem_conseq:
  !ctx st st' P Q R P' Q' R'.
    frag_exec_mem ctx st st' P Q R /\
    (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\ (!r. R r ==> R' r) ==>
    frag_exec_mem ctx st st' P' Q' R'
Proof
  rw[frag_exec_mem_def] >>
  first_x_assum (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem frag_exec_mem_refl:
  !ctx st P Q R. (!s. P s ==> Q s) ==> frag_exec_mem ctx st st P Q R
Proof
  rw[frag_exec_mem_def] >> disj1_tac >> qexists_tac `s` >> simp[] >>
  metis_tac[]
QED

Theorem frag_exec_mem_pointwise:
  !ctx st st' P Q R.
    (!s0. P s0 ==> frag_exec_mem ctx st st' (\s. s = s0) Q R) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rw[frag_exec_mem_def] >> first_x_assum drule >> simp[frag_exec_mem_def] >>
  metis_tac[]
QED

Theorem frag_exec_mem_seq:
  !ctx st1 st2 st3 P Q Q2 R.
    frag_exec_mem ctx st1 st2 P Q R /\ frag_exec_mem ctx st2 st3 Q Q2 R /\
    cs_extends st1 st2 /\ cs_extends st2 st3 ==>
    frag_exec_mem ctx st1 st3 P Q2 R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_mem_def] >> rpt strip_tac >>
  `fn_has_code st1 st2 fn /\ fn_has_code st2 st3 fn` by
    metis_tac[fn_has_code_split] >>
  qpat_x_assum `frag_exec_mem ctx st1 st2 P Q R`
    (mp_tac o SIMP_RULE std_ss [frag_exec_mem_def]) >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >> strip_tac
  >- (rename1 `Q s2` >>
      qpat_x_assum `frag_exec_mem ctx st2 st3 Q Q2 R`
        (mp_tac o SIMP_RULE std_ss [frag_exec_mem_def]) >>
      disch_then (qspecl_then [`fn`, `s2`] mp_tac) >> simp[] >> strip_tac
      >- (disj1_tac >> rename1 `Q2 s3` >> qexists_tac `s3` >> simp[] >>
          rpt strip_tac >> metis_tac[])
      >> disj2_tac >> metis_tac[exit_result_not_error]) >>
  disj2_tac >> metis_tac[]
QED

Theorem frag_exec_mem_false_pre:
  !ctx st st' Q R. frag_exec_mem ctx st st' (\s. F) Q R
Proof
  rw[frag_exec_mem_def]
QED

Theorem frag_exec_mem_exit_prefix:
  !ctx st1 st2 st3 P Q R.
    frag_exec_mem ctx st1 st2 P (\s. F) R /\ cs_extends st1 st2 /\
    cs_extends st2 st3 ==>
    frag_exec_mem ctx st1 st3 P Q R
Proof
  rpt strip_tac >> irule frag_exec_mem_seq >> qexistsl_tac [`\s. F`, `st2`] >>
  simp[frag_exec_mem_false_pre]
QED

Theorem frag_exec_mem_seq_pointwise:
  !ctx st1 st2 st3 P Q1 Q R.
    frag_exec_mem ctx st1 st2 P Q1 R /\
    (!t. Q1 t ==> frag_exec_mem ctx st2 st3 (\s. s = t) Q R) /\
    cs_extends st1 st2 /\ cs_extends st2 st3 ==>
    frag_exec_mem ctx st1 st3 P Q R
Proof
  rpt strip_tac >> irule frag_exec_mem_seq >> qexistsl_tac [`Q1`, `st2`] >>
  simp[] >> irule frag_exec_mem_pointwise >> simp[]
QED

Theorem frag_exec_mem_then:
  !ctx st1 st2 P Q1 R.
    frag_exec_mem ctx st1 st2 P Q1 R ==>
    !st3 Q.
      (!t. Q1 t ==> frag_exec_mem ctx st2 st3 (\s. s = t) Q R) /\
      cs_extends st1 st2 /\ cs_extends st2 st3 ==>
      frag_exec_mem ctx st1 st3 P Q R
Proof
  metis_tac[frag_exec_mem_seq_pointwise]
QED

Theorem frag_exec_mem_weaken:
  !ctx st st' P Q R.
    frag_exec_mem ctx st st' P Q R ==>
    !P' Q' R'.
      (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\ (!r. R r ==> R' r) ==>
      frag_exec_mem ctx st st' P' Q' R'
Proof
  metis_tac[frag_exec_mem_conseq]
QED

Theorem frag_exec_mem_pre_exit:
  !ctx st st' P Q R P' R'.
    frag_exec_mem ctx st st' P Q R /\ (!s. P' s ==> P s) /\
    (!r. R r ==> R' r) ==>
    frag_exec_mem ctx st st' P' Q R'
Proof
  rpt strip_tac >> irule frag_exec_mem_conseq >>
  qexistsl_tac [`P`, `Q`, `R`] >> simp[]
QED

Theorem frag_exec_mem_pre_exit_c:
  !ctx st st' P Q R.
    frag_exec_mem ctx st st' P Q R ==>
    !P' R'. (!s. P' s ==> P s) /\ (!r. R r ==> R' r) ==>
            frag_exec_mem ctx st st' P' Q R'
Proof
  metis_tac[frag_exec_mem_pre_exit]
QED

(* ===== One instruction ===== *)

(* A step that does not continue the block is the result of the run, and
   the run is memory-safe when the step is. *)
Theorem run_from_step_exit:
  !fuel ctx fn s bb inst r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = r /\ (!s'. r <> OK s') ==>
    run_from fuel ctx fn s = r /\
    (mem_safe_step fuel ctx inst s ==> mem_safe_run fuel ctx fn s)
Proof
  rpt gen_tac >> strip_tac >>
  `exec_block fuel ctx bb s = r` by
    (simp[Once exec_block_def] >> Cases_on `r` >> gvs[]) >>
  simp[run_from_def, mem_safe_run_def, Once mem_safe_block_def] >>
  Cases_on `r` >> gvs[]
QED

(* One straight-line instruction that is memory-safe where it runs, and
   either finishes in a state satisfying Q or aborts. *)
Theorem frag_exec_mem_step:
  !ctx st st' inst P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [inst] /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    (!s. P s ==>
       inst_mem_below_frontier inst s /\ inst_dload_in_section inst s /\
       ((?s1. step_inst_base inst s = OK s1 /\
              Q (s1 with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
        (?a s1. step_inst_base inst s = Abort a s1 /\ R (Abort a s1)))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rw[frag_exec_mem_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `!fuel. mem_safe_step fuel ctx inst s` by
    (first_x_assum drule >> simp[mem_safe_step_non_invoke]) >>
  first_x_assum drule >> strip_tac
  >- (disj1_tac >>
      `!fuel. step_inst fuel ctx inst s = OK s1` by
        simp[step_inst_non_invoke] >>
      `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted` by
        metis_tac[step_preserves_control_flow, step_preserves_halted] >>
      qexists_tac `s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
      gvs[arithmeticTheory.ADD1] >> rpt strip_tac >>
      qexists_tac `fuel` >>
      metis_tac[run_from_step, mem_safe_run_step, arithmeticTheory.ADD1]) >>
  disj2_tac >>
  `step_inst 0 ctx inst s = Abort a s1` by simp[step_inst_non_invoke] >>
  qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `inst`, `Abort a s1`] mp_tac
    run_from_step_exit >> simp[] >> strip_tac >>
  qexists_tac `0` >> simp[exit_result_def]
QED

(* ===== Abort and halt lifting ===== *)

Theorem frag_exec_mem_step_abort:
  !ctx st st' inst P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [inst] /\
    (!s. P s ==>
       ?fuel a s'. step_inst fuel ctx inst s = Abort a s' /\
                   mem_safe_step fuel ctx inst s /\ R (Abort a s')) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rw[frag_exec_mem_def] >> disj2_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH st.cs_current_insts) = SOME inst` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  qspecl_then [`fuel`, `ctx`, `fn`, `s`, `bb`, `inst`, `Abort a s'`] mp_tac
    run_from_step_exit >> gvs[] >> strip_tac >>
  qexists_tac `fuel` >> simp[exit_result_def]
QED

Theorem frag_exec_mem_assert_fail:
  !ctx st op x st' P Q R.
    emit_void ASSERT [op] st = (x, st') /\
    (!s. P s ==>
       eval_operand op s = SOME 0w /\
       R (Abort Revert_abort (revert_state (set_returndata [] s)))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt strip_tac >> irule frag_exec_mem_step_abort >>
  gvs[emit_void_assert_inst] >>
  `(mk_inst st.cs_next_id ASSERT [op] []).inst_opcode <> INVOKE` by
    simp[mk_inst_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[step_inst_non_invoke, assert_false_correct, mem_safe_step_non_invoke,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def]
QED

Theorem stop_frag_mem:
  !ctx st st' id P Q R.
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++ [mk_inst id STOP [] []] /\
    (!s. P s ==> R (Halt (halt_state (s with vs_returndata := [])))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rw[frag_exec_mem_def] >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH st.cs_current_insts) =
   SOME (mk_inst id STOP [] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `(mk_inst id STOP [] []).inst_opcode = STOP` by simp[mk_inst_def] >>
  `step_inst 0 ctx (mk_inst id STOP [] []) s =
   Halt (halt_state (s with vs_returndata := []))` by
    (simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  `mem_safe_step 0 ctx (mk_inst id STOP [] []) s` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         mk_inst_def] >>
  qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `mk_inst id STOP [] []`,
               `Halt (halt_state (s with vs_returndata := []))`] mp_tac
    run_from_step_exit >> gvs[] >> strip_tac >>
  qexists_tac `0` >> simp[exit_result_def]
QED

(* ===== Revert forwarding ===== *)

(* A step that ends the run at a revert-forwarding instruction: the run is
   memory-safe whatever the instruction touches. *)
Theorem run_from_step_exit_forward[local]:
  !fuel ctx fn s bb inst r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = r /\ (!s'. r <> OK s') /\
    revert_forward_at bb s.vs_inst_idx ==>
    run_from fuel ctx fn s = r /\ mem_safe_run fuel ctx fn s
Proof
  rpt gen_tac >> strip_tac >>
  `exec_block fuel ctx bb s = r` by
    (simp[Once exec_block_def] >> Cases_on `r` >> gvs[]) >>
  simp[run_from_def, mem_safe_run_def, Once mem_safe_block_def] >>
  Cases_on `r` >> gvs[]
QED

Theorem same_after_assigns_refl[local]:
  !l op. same_after_assigns l op op
Proof
  Cases >> simp[same_after_assigns_def]
QED

(* Adjacent RETURNDATACOPY [p; 0; rds] and REVERT [p; rds] form a pair. *)
Theorem revert_forward_pair_adjacent[local]:
  !bb i id1 id2 p rds.
    get_instruction bb i = SOME (mk_inst id1 RETURNDATACOPY [p; Lit 0w; rds] []) /\
    get_instruction bb (SUC i) = SOME (mk_inst id2 REVERT [p; rds] []) ==>
    revert_forward_at bb i /\ revert_forward_at bb (SUC i)
Proof
  rpt gen_tac >> strip_tac >>
  `revert_forward_pair bb i (SUC i)` suffices_by
    (rw[revert_forward_at_def] >> metis_tac[]) >>
  `i < LENGTH bb.bb_instructions /\
   EL i bb.bb_instructions = mk_inst id1 RETURNDATACOPY [p; Lit 0w; rds] []` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `TAKE (SUC i) bb.bb_instructions =
   SNOC (mk_inst id1 RETURNDATACOPY [p; Lit 0w; rds] [])
        (TAKE i bb.bb_instructions)` by
    metis_tac[rich_listTheory.SNOC_EL_TAKE] >>
  gvs[revert_forward_pair_def, listTheory.REVERSE_SNOC,
      resolve_block_assigns_def, same_after_assigns_refl, mk_inst_def] >>
  rpt strip_tac >>
  `~(k < SUC i)` by (qpat_x_assum `i < k` mp_tac >> simp[]) >>
  gvs[]
QED

(* RETURNDATACOPY [p; 0; rds] then REVERT [p; rds], the lowering's revert
   forwarding after a failed call.  raw_unit_memory_ok exempts the pair
   (revert_forward_pair), so it is memory-safe wherever p points; the run exits
   at the copy's abort or at the REVERT. *)
Theorem revert_forward_frag_mem:
  !ctx st st' id1 id2 p rds P Q R.
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst id1 RETURNDATACOPY [p; Lit 0w; rds] [];
       mk_inst id2 REVERT [p; rds] []] /\
    (!s. P s ==>
       (?a s1.
          step_inst_base (mk_inst id1 RETURNDATACOPY [p; Lit 0w; rds] []) s =
            Abort a s1 /\ R (Abort a s1)) \/
       (?s1 a s2.
          step_inst_base (mk_inst id1 RETURNDATACOPY [p; Lit 0w; rds] []) s =
            OK s1 /\
          step_inst_base (mk_inst id2 REVERT [p; rds] [])
            (s1 with vs_inst_idx := SUC s.vs_inst_idx) = Abort a s2 /\
          R (Abort a s2))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rw[frag_exec_mem_def] >> disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `i1 = mk_inst id1 RETURNDATACOPY [p; Lit 0w; rds] []` >>
  qabbrev_tac `i2 = mk_inst id2 REVERT [p; rds] []` >>
  `get_instruction bb s.vs_inst_idx = SOME i1 /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME i2` by
    (qpat_x_assum `!i. _` (fn th =>
       qspec_then `0` mp_tac th >> qspec_then `1` mp_tac th) >>
     simp[arithmeticTheory.ADD1]) >>
  `revert_forward_at bb s.vs_inst_idx /\ revert_forward_at bb (SUC s.vs_inst_idx)` by
    (unabbrev_all_tac >> drule_all revert_forward_pair_adjacent >> simp[]) >>
  `i1.inst_opcode = RETURNDATACOPY /\ i2.inst_opcode = REVERT` by
    (unabbrev_all_tac >> simp[mk_inst_def]) >>
  first_x_assum drule >> strip_tac
  >- (`step_inst 0 ctx i1 s = Abort a s1` by simp[step_inst_non_invoke] >>
      qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`, `i1`, `Abort a s1`] mp_tac
        run_from_step_exit_forward >>
      gvs[] >> strip_tac >>
      qexists_tac `0` >> simp[exit_result_def]) >>
  `step_inst 0 ctx i1 s = OK s1` by simp[step_inst_non_invoke] >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, is_terminator_def] >>
  qabbrev_tac `t = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst 0 ctx i2 t = Abort a s2` by simp[step_inst_non_invoke] >>
  `run_from 0 ctx fn s = run_from 0 ctx fn t` by
    (unabbrev_all_tac >> irule run_from_step >> gvs[is_terminator_def]) >>
  `mem_safe_run 0 ctx fn s <=>
   (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step 0 ctx i1 s) /\
   mem_safe_run 0 ctx fn t` by
    (unabbrev_all_tac >> irule mem_safe_run_step >> gvs[is_terminator_def]) >>
  qspecl_then [`0`, `ctx`, `fn`, `t`, `bb`, `i2`, `Abort a s2`] mp_tac
    run_from_step_exit_forward >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx` by
    simp[Abbr `t`] >>
  gvs[] >> strip_tac >>
  qexists_tac `0` >> simp[exit_result_def]
QED

(* ===== Leaf template ===== *)

(* An MSTORE whose 32 bytes end no later than an ALLOCA'd region does (a
   store into the region, or below it).  alloca_next_valid (half of
   alloca_inv) puts every region at or below the frontier, which is all
   inst_mem_below_frontier needs.  w2n only shrinks a wrapped address, so the address may be
   computed with word arithmetic. *)
Theorem mstore_alloca_frag_mem:
  !ctx sa sb dst src s0 d w aid b sz R.
    emit_void MSTORE [dst; src] sa = ((), sb) /\
    eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME w /\
    alloca_next_valid s0 /\ FLOOKUP s0.vs_allocas aid = SOME (b, sz) /\
    w2n d + 32 <= b + sz ==>
    frag_exec_mem ctx sa sb (\s. s = s0)
      (\s. s = mstore (w2n d) w s0 with
                 vs_inst_idx := LENGTH sb.cs_current_insts) R
Proof
  rpt strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
        comp_ignore_bind_def, comp_return_def] >>
  irule frag_exec_mem_step >> simp[] >>
  simp[mk_inst_def, is_terminator_def] >>
  `b + sz <= s0.vs_alloca_next` by metis_tac[alloca_next_valid_def] >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [dst; src] []) s0 =
   OK (mstore (w2n d) w s0)` by (irule step_MSTORE >> simp[]) >>
  fs[mk_inst_def] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, fixed_source_write_range_def]
QED

(* ===== Straight-line sequences ===== *)

(* Every instruction of a straight-line sequence is below the frontier,
   and reads the data section from within it, in the state it runs in. *)
Definition run_inst_seq_mem_ok_def:
  run_inst_seq_mem_ok [] s = T /\
  run_inst_seq_mem_ok (i::is) s =
    (inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
     case step_inst_base i s of
       OK s' => run_inst_seq_mem_ok is s'
     | _ => T)
End

Theorem run_inst_seq_mem_ok_inst_idx[simp]:
  !is s n.
    EVERY (\i. ~is_terminator i.inst_opcode) is ==>
    (run_inst_seq_mem_ok is (s with vs_inst_idx := n) <=>
     run_inst_seq_mem_ok is s)
Proof
  Induct >> rw[run_inst_seq_mem_ok_def] >>
  simp[step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base h s` >> gvs[exec_result_map_def]
QED

(* Successful prefixes supply exactly the state-dependent checks needed by
   the recursive straight-line memory-safety predicate, for a sequence
   without data-section reads. *)
Theorem run_inst_seq_mem_ok_of_prefix_safe:
  !xs s.
    EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) xs /\
    (!pre i post u. xs = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      inst_mem_below_frontier i u) ==>
    run_inst_seq_mem_ok xs s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >> rpt strip_tac
  >- (first_x_assum irule >>
      qexistsl_tac [`xs`, `[]`] >> simp[run_inst_seq_def]) >>
  Cases_on `step_inst_base h s` >> simp[] >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  qexistsl_tac [`post`, `h::pre`] >> simp[run_inst_seq_def]
QED

Theorem run_inst_seq_mem_ok_every:
  !code s.
    EVERY (\i. !t. inst_mem_below_frontier i t /\ inst_dload_in_section i t)
      code ==>
    run_inst_seq_mem_ok code s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >>
  rpt strip_tac >> Cases_on `step_inst_base h s` >> simp[]
QED

Theorem run_inst_seq_mem_ok_last:
  run_inst_seq_mem_ok [i] s <=>
  inst_mem_below_frontier i s /\ inst_dload_in_section i s
Proof
  Cases_on `step_inst_base i s` >> simp[run_inst_seq_mem_ok_def]
QED

(* The cons clause, only where a next instruction follows: with
   run_inst_seq_mem_ok_last it unfolds a known sequence to its per-step
   frontier checks. *)
Theorem run_inst_seq_mem_ok_cons:
  run_inst_seq_mem_ok (i::j::is) s <=>
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  case step_inst_base i s of
    OK s' => run_inst_seq_mem_ok (j::is) s'
  | _ => T
Proof
  simp[run_inst_seq_mem_ok_def]
QED

Theorem run_inst_seq_mem_ok_append:
  !is1 is2 s.
    run_inst_seq_mem_ok is1 s /\
    (!s'. run_inst_seq is1 s = OK s' ==> run_inst_seq_mem_ok is2 s') ==>
    run_inst_seq_mem_ok (is1 ++ is2) s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def, run_inst_seq_def] >>
  rpt strip_tac >> Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum irule >> fs[]
QED

Theorem DROP_EQ_CONS[local]:
  !l n h rest.
    DROP n l = h :: rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

(* A straight-line prefix of the block whose instructions are below the
   frontier: a memory-safe run from past it is a memory-safe run from its
   start, and a run that aborts in it is memory-safe. *)
Theorem mem_safe_run_inst_seq:
  !is s fuel ctx fn bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
    run_inst_seq_mem_ok is s ==>
    (!s'. run_inst_seq is s = OK s' /\
          mem_safe_run fuel ctx fn
            (s' with vs_inst_idx := s.vs_inst_idx + LENGTH is) ==>
          mem_safe_run fuel ctx fn s) /\
    (!a s'. run_inst_seq is s = Abort a s' ==> mem_safe_run fuel ctx fn s)
Proof
  Induct >> simp[run_inst_seq_def, run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX is rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  drule DROP_EQ_CONS >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  `!fuel. mem_safe_step fuel ctx h s` by simp[mem_safe_step_non_invoke] >>
  `!fuel. step_inst fuel ctx h s = step_inst_base h s` by
    simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base h s` >> gvs[]
  >~ [`step_inst_base h s = OK s1`]
  >- (`s1.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
      `mem_safe_run fuel ctx fn s <=>
       mem_safe_run fuel ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qspecl_then [`fuel`, `ctx`, `fn`, `s`, `bb`, `h`, `s1`] mp_tac
           mem_safe_run_step >> simp[]) >>
      simp[] >>
      first_x_assum (qspecl_then [`s1 with vs_inst_idx := SUC s.vs_inst_idx`,
                                  `fuel`, `ctx`, `fn`, `bb`] mp_tac) >>
      simp[run_inst_seq_inst_idx] >>
      Cases_on `run_inst_seq is s1` >> simp[exec_result_map_def] >>
      simp[arithmeticTheory.ADD1]) >>
  rename1 `step_inst_base h s = Abort a s1` >>
  qspecl_then [`fuel`, `ctx`, `fn`, `s`, `bb`, `h`, `Abort a s1`] mp_tac
    run_from_step_exit >> simp[]
QED

Theorem run_inst_seq_preserves_halted[local]:
  !is s s'.
    run_inst_seq is s = OK s' /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is ==>
    s'.vs_halted = s.vs_halted
Proof
  rpt strip_tac >>
  drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. s.vs_halted` run_inst_seq_preserves_field) >>
  simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[step_preserves_halted, step_inst_non_invoke]
QED

(* frag_exec_run_inst_seq with memory safety: the straight-line fragment
   is memory-safe when its instructions are below the frontier where they
   run. *)
Theorem frag_exec_mem_run_inst_seq:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    (!s. P s ==>
       run_inst_seq_mem_ok (emitted_insts st st') s /\
       ((?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
              Q (s' with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
        (?a s'. run_inst_seq (emitted_insts st st') s = Abort a s' /\
                !n. R (Abort a (s' with vs_inst_idx := n))))) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rw[frag_exec_mem_def] >>
  `?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?t. st'.cs_current_insts = st.cs_current_insts ++ t /\
       emitted_insts st st' = t` by
    (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `isPREFIX t (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  qpat_x_assum `emitted_insts st st' = t` (fn th => fs[th]) >>
  first_x_assum drule >> strip_tac
  >- (disj1_tac >>
      `!fuel. s'.vs_current_bb = s.vs_current_bb /\
              exec_block fuel ctx bb s =
              exec_block fuel ctx bb
                (s' with vs_inst_idx := s.vs_inst_idx + LENGTH t)` by
        (gen_tac >>
         qspecl_then [`t`, `s`, `fuel`, `ctx`, `bb`] mp_tac
           exec_block_run_inst_seq >> simp[]) >>
      `s'.vs_halted = s.vs_halted` by
        metis_tac[run_inst_seq_preserves_halted] >>
      qexists_tac `s' with vs_inst_idx := LENGTH st'.cs_current_insts` >>
      gvs[] >> rpt strip_tac >>
      qexists_tac `fuel` >> gvs[run_from_def] >>
      qspecl_then [`t`, `s`, `fuel`, `ctx`, `fn`, `bb`] mp_tac
        mem_safe_run_inst_seq >> simp[]) >>
  disj2_tac >>
  `?n. exec_block 0 ctx bb s = Abort a (s' with vs_inst_idx := n)` by
    (qspecl_then [`t`, `s`, `0`, `ctx`, `bb`] mp_tac
       exec_block_run_inst_seq >> simp[]) >>
  qexists_tac `0` >> simp[run_from_def, exit_result_def] >>
  qspecl_then [`t`, `s`, `0`, `ctx`, `fn`, `bb`] mp_tac
    mem_safe_run_inst_seq >> simp[]
QED


(* A raw actual jump with a non-error continuation enters a zero-PHI target. *)
Theorem mem_safe_run_jump_result:
  !a fuel ctx fn s bb inst lbl out.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst a ctx inst s = OK (jump_to lbl s) /\
    (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step a ctx inst s) /\
    run_from fuel ctx fn (jump_to lbl s) = out /\ (!e. out <> Error e) ==>
    run_from (SUC fuel) ctx fn s = out /\
    (mem_safe_run fuel ctx fn (jump_to lbl s) ==>
     mem_safe_run (SUC fuel) ctx fn s)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst_base inst s = OK (jump_to lbl s)` by
    gvs[step_inst_non_invoke] >>
  conj_tac >- (irule run_from_jump_result >> metis_tac[]) >>
  strip_tac >>
  `?target. lookup_block lbl fn.fn_blocks = SOME target /\
            phi_prefix_length target.bb_instructions = 0` by
    (irule run_from_jump_target >> simp[] >> metis_tac[]) >>
  `eval_phis (jump_to lbl s) target.bb_instructions = OK (jump_to lbl s)` by
    simp[eval_phis_no_phi] >>
  `mem_safe_blocks (SUC fuel) ctx fn (jump_to lbl s)` by
    (drule_at Any mem_safe_blocks_run >>
     disch_then (qspecl_then [`fuel`, `ctx`, `fn`] mp_tac) >>
     gvs[jump_to_def]) >>
  `revert_forward_at bb s.vs_inst_idx \/ mem_safe_step (SUC fuel) ctx inst s` by
    metis_tac[mem_safe_step_non_invoke] >>
  simp[mem_safe_run_def, Once mem_safe_block_def, Once exec_block_def,
       step_inst_non_invoke, jump_to_def] >>
  fs[jump_to_def]
QED
