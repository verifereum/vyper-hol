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
 *   mstore_alloca_frag_mem    — an MSTORE into an ALLOCA'd buffer
 *
 * Helpers:
 *   run_from_step_exit        — a step that does not continue ends the run
 *)

Theory fragExecMem
Ancestors
  list rich_list compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomExecProofs venomInst venomInstProofs venomState
  venomMemDefs codegenRel contextCodegenRel unitTransformDefs fragExec memSafeRun

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
       inst_mem_below_frontier inst s /\
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
