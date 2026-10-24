(*
 * Running code from a state with extra variables bound (#636)
 *
 * An instruction that steps to OK or aborts from a state also does so from
 * the same state with more variables bound, with the same effects, ending
 * in a state that again has at least the variables of the first run's
 * result bound (vars_ext: a SUBMAP of the variables, every other field
 * equal).  A sequence of such instructions likewise.
 *
 * The lowering's run-level lemmas (emitHelperProps, arithmeticProps, ...)
 * assume fresh_vars_wrt: no compiler variable at or above the compile
 * state's counter is bound.  That fails where a loop body runs again with
 * the last iteration's temporaries still bound, so stmt_state_rel does not
 * carry it.  drop_fresh removes those temporaries; a lemma applied to the
 * cleaned state then carries over to the actual one through
 * run_inst_seq_vars_ext, and to a fragment through
 * frag_exec_run_inst_seq_drop_fresh.
 *
 * Three kinds of instruction are left out:
 *   - terminators: they leave the block, and run_inst_seq and
 *     frag_exec_run_inst_seq cover straight-line code only;
 *   - INVOKE: step_inst_base does not run it (step_inst runs the callee
 *     with run_blocks), so a call enters a fragment through its own
 *     frag_exec lemma, with the callee's run as a hypothesis, not through
 *     run_inst_seq;
 *   - the external-call ops (CALL, STATICCALL, DELEGATECALL, CREATE,
 *     CREATE2): their steps go through the call and create oracles
 *     (consume_call_outcome, ...), whose frame lemmas over the variables
 *     are not proved yet; with them the ops can join
 *     step_inst_base_vars_ext.
 *
 * TOP-LEVEL:
 *   vars_ext, vars_ext_result — a state, and a result, with more variables
 *                               bound
 *   step_inst_base_vars_ext, step_inst_base_vars_ext_state — one
 *                               instruction
 *   run_inst_seq_vars_ext     — a straight-line sequence
 *   drop_fresh                — a state without the variables fresh at a
 *                               compile state
 *   fresh_vars_wrt_drop_fresh, vars_ext_drop_fresh, lookup_var_drop_fresh
 *   frag_exec_run_inst_seq_drop_fresh — a straight-line fragment, given by
 *                               its run from the state without the
 *                               temporaries fresh at its start, as the
 *                               fresh_vars_wrt lemmas state it
 *
 * Helpers: SUBMAP_FUPDATE_both, eval_operand_vars_ext,
 *   eval_operands_vars_ext, vars_ext_with, update_var_vars_ext,
 *   exec_pure1_vars_ext, exec_pure2_vars_ext,
 *   exec_pure3_vars_ext, exec_read0_vars_ext, exec_read1_vars_ext,
 *   exec_write2_vars_ext
 *)

Theory varsExt
Ancestors
  list rich_list finite_map pred_set
  venomExecSemantics venomState venomInst exprLoweringProps compileEnv
  fragExec

(* ===== More variables bound ===== *)

(* t' is t with more variables bound. *)
Definition vars_ext_def:
  vars_ext (t:venom_state) (t':venom_state) <=>
    t.vs_vars SUBMAP t'.vs_vars /\ t' = t with vs_vars := t'.vs_vars
End

(* r' is what r becomes from a state with more variables bound: the same
   OK or abort, in a state with more variables bound.  Nothing is said of
   the other results. *)
Definition vars_ext_result_def:
  (vars_ext_result (OK t) r' <=> ?t'. r' = OK t' /\ vars_ext t t') /\
  (vars_ext_result (Abort a t) r' <=> ?t'. r' = Abort a t' /\ vars_ext t t') /\
  (vars_ext_result _ r' <=> T)
End

Theorem SUBMAP_FUPDATE_both:
  !f g k v. f SUBMAP g ==> f |+ (k, v) SUBMAP g |+ (k, v)
Proof
  rw[SUBMAP_DEF, FAPPLY_FUPDATE_THM] >> rw[]
QED

Theorem eval_operand_vars_ext:
  !op s V.
    s.vs_vars SUBMAP V /\ eval_operand op s <> NONE ==>
    eval_operand op (s with vs_vars := V) = eval_operand op s
Proof
  Cases >> rw[eval_operand_def, lookup_var_def] >>
  gvs[FLOOKUP_DEF, SUBMAP_DEF]
QED

Theorem eval_operands_vars_ext:
  !ops s V.
    s.vs_vars SUBMAP V /\ eval_operands ops s <> NONE ==>
    eval_operands ops (s with vs_vars := V) = eval_operands ops s
Proof
  Induct >> rw[eval_operands_def] >>
  Cases_on `eval_operand h s` >> gvs[] >>
  Cases_on `eval_operands ops s` >> gvs[] >>
  simp[eval_operand_vars_ext]
QED

(* ===== One instruction ===== *)

val ext_simps =
  [vars_ext_result_def, vars_ext_def, eval_operand_vars_ext,
   eval_operands_vars_ext, update_var_def, SUBMAP_FUPDATE_both,
   mload_def, sload_def, tload_def, contract_storage_def,
   contract_transient_def, sstore_def, tstore_def, mstore_def,
   mstore8_def, mcopy_def, istore_def, write_memory_with_expansion_def,
   read_memory_def, halt_state_def, revert_state_def,
   set_returndata_def, LET_THM];

(* Split on the result from the smaller state (the left one) only: casing
   both sides multiplies the goals. *)
val ext_tac =
  qmatch_goalsub_abbrev_tac `vars_ext_result r _` >>
  qpat_x_assum `Abbrev (r = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  Cases_on `r` >> gvs[vars_ext_result_def, AllCaseEqs()] >>
  asm_simp_tac (srw_ss()) ext_simps;

Theorem vars_ext_with:
  !t V. t.vs_vars SUBMAP V ==> vars_ext t (t with vs_vars := V)
Proof
  rw[vars_ext_def]
QED

Theorem update_var_vars_ext:
  !out w s V.
    s.vs_vars SUBMAP V ==>
    vars_ext (update_var out w s) (update_var out w (s with vs_vars := V))
Proof
  rw[vars_ext_def, update_var_def, SUBMAP_FUPDATE_both]
QED

(* The exec_* helpers: split on the result from the smaller state, read off
   its operands, and rerun from the larger one.  Going through the two
   lemmas above keeps simp off the venom_state record. *)
val exec_simps = [eval_operand_vars_ext, update_var_vars_ext, vars_ext_with];

Theorem exec_pure1_vars_ext:
  !f inst s V.
    s.vs_vars SUBMAP V ==>
    vars_ext_result (exec_pure1 f inst s)
      (exec_pure1 f inst (s with vs_vars := V))
Proof
  rpt strip_tac >> Cases_on `exec_pure1 f inst s` >>
  gvs[vars_ext_result_def, exec_pure1_def, AllCaseEqs()] >>
  simp exec_simps
QED

Theorem exec_pure2_vars_ext:
  !f inst s V.
    s.vs_vars SUBMAP V ==>
    vars_ext_result (exec_pure2 f inst s)
      (exec_pure2 f inst (s with vs_vars := V))
Proof
  rpt strip_tac >> Cases_on `exec_pure2 f inst s` >>
  gvs[vars_ext_result_def, exec_pure2_def, AllCaseEqs()] >>
  simp exec_simps
QED

Theorem exec_pure3_vars_ext:
  !f inst s V.
    s.vs_vars SUBMAP V ==>
    vars_ext_result (exec_pure3 f inst s)
      (exec_pure3 f inst (s with vs_vars := V))
Proof
  rpt strip_tac >> Cases_on `exec_pure3 f inst s` >>
  gvs[vars_ext_result_def, exec_pure3_def, AllCaseEqs()] >>
  simp exec_simps
QED

Theorem exec_read0_vars_ext:
  !f inst s V.
    s.vs_vars SUBMAP V /\ f (s with vs_vars := V) = f s ==>
    vars_ext_result (exec_read0 f inst s)
      (exec_read0 f inst (s with vs_vars := V))
Proof
  rpt strip_tac >> Cases_on `exec_read0 f inst s` >>
  gvs[vars_ext_result_def, exec_read0_def, AllCaseEqs()] >>
  simp exec_simps
QED

Theorem exec_read1_vars_ext:
  !f inst s V.
    s.vs_vars SUBMAP V /\ (!w. f w (s with vs_vars := V) = f w s) ==>
    vars_ext_result (exec_read1 f inst s)
      (exec_read1 f inst (s with vs_vars := V))
Proof
  rpt strip_tac >> Cases_on `exec_read1 f inst s` >>
  gvs[vars_ext_result_def, exec_read1_def, AllCaseEqs()] >>
  simp exec_simps
QED

Theorem exec_write2_vars_ext:
  !f inst s V.
    s.vs_vars SUBMAP V /\
    (!w1 w2. f w1 w2 (s with vs_vars := V) = f w1 w2 s with vs_vars := V) /\
    (!w1 w2. (f w1 w2 s).vs_vars = s.vs_vars) ==>
    vars_ext_result (exec_write2 f inst s)
      (exec_write2 f inst (s with vs_vars := V))
Proof
  rpt strip_tac >> Cases_on `exec_write2 f inst s` >>
  gvs[vars_ext_result_def, exec_write2_def, AllCaseEqs()] >>
  simp exec_simps
QED

Theorem step_inst_base_vars_ext:
  !inst s V.
    s.vs_vars SUBMAP V /\ ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\ ~is_ext_call_op inst.inst_opcode ==>
    vars_ext_result (step_inst_base inst s)
      (step_inst_base inst (s with vs_vars := V))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_terminator_def, is_ext_call_op_def] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs]
  >>~- ([`vars_ext_result (exec_pure1 _ _ _) _`],
        irule exec_pure1_vars_ext >> simp[])
  >>~- ([`vars_ext_result (exec_pure2 _ _ _) _`],
        irule exec_pure2_vars_ext >> simp[])
  >>~- ([`vars_ext_result (exec_pure3 _ _ _) _`],
        irule exec_pure3_vars_ext >> simp[])
  >>~- ([`vars_ext_result (exec_read0 _ _ _) _`],
        irule exec_read0_vars_ext >> asm_simp_tac (srw_ss()) ext_simps)
  >>~- ([`vars_ext_result (exec_read1 _ _ _) _`],
        irule exec_read1_vars_ext >> asm_simp_tac (srw_ss()) ext_simps)
  >>~- ([`vars_ext_result (exec_write2 _ _ _) _`],
        irule exec_write2_vars_ext >> asm_simp_tac (srw_ss()) ext_simps) >>
  simp[exec_alloca_def]
  (* one step per opcode: together they run past the step limit *)
  >>~- ([`inst.inst_opcode = MCOPY`], ext_tac)
  >>~- ([`inst.inst_opcode = CALLDATACOPY`], ext_tac)
  >>~- ([`inst.inst_opcode = RETURNDATACOPY`], ext_tac)
  >>~- ([`inst.inst_opcode = CODECOPY`], ext_tac)
  >>~- ([`inst.inst_opcode = EXTCODECOPY`], ext_tac)
  >>~- ([`inst.inst_opcode = DLOADBYTES`], ext_tac)
  >>~- ([`inst.inst_opcode = SHA3`], ext_tac)
  >>~- ([`inst.inst_opcode = ISTORE`], ext_tac)
  >>~- ([`inst.inst_opcode = LOG`], ext_tac)
  >>~- ([`inst.inst_opcode = ALLOCA`], ext_tac)
  >>~- ([`inst.inst_opcode = DALLOCA`], ext_tac)
  >>~- ([`inst.inst_opcode = BUMP`], ext_tac)
  >>~- ([`inst.inst_opcode = ASSERT`], ext_tac)
  >>~- ([`inst.inst_opcode = PARAM`], ext_tac)
  >>~- ([`inst.inst_opcode = FMP_PARAM`], ext_tac) >>
  ext_tac
QED

Theorem step_inst_base_vars_ext_state:
  !inst s s'.
    vars_ext s s' /\ ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\ ~is_ext_call_op inst.inst_opcode ==>
    vars_ext_result (step_inst_base inst s) (step_inst_base inst s')
Proof
  rw[vars_ext_def] >>
  qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule step_inst_base_vars_ext >> simp[]
QED

(* ===== A straight-line sequence ===== *)

Theorem run_inst_seq_vars_ext:
  !is s s'.
    vars_ext s s' /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               ~is_ext_call_op i.inst_opcode) is ==>
    vars_ext_result (run_inst_seq is s) (run_inst_seq is s')
Proof
  Induct >- simp[run_inst_seq_def, vars_ext_result_def] >>
  rw[run_inst_seq_def] >>
  `vars_ext_result (step_inst_base h s) (step_inst_base h s')` by
    (irule step_inst_base_vars_ext_state >> simp[]) >>
  Cases_on `step_inst_base h s` >> gvs[vars_ext_result_def] >>
  first_x_assum irule >> simp[]
QED

(* ===== Dropping the variables fresh at a compile state ===== *)

Definition drop_fresh_def:
  drop_fresh (st:compile_state) (s:venom_state) =
    s with vs_vars := DRESTRICT s.vs_vars (\x. not_fresh_at st x)
End

Theorem fresh_vars_wrt_drop_fresh:
  !st s. fresh_vars_wrt st (drop_fresh st s)
Proof
  rw[fresh_vars_wrt_def, drop_fresh_def, FDOM_DRESTRICT, IN_INTER] >>
  simp[IN_DEF, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.GREATER_EQ]
QED

Theorem vars_ext_drop_fresh:
  !st s. vars_ext (drop_fresh st s) s
Proof
  rw[vars_ext_def, drop_fresh_def, DRESTRICT_SUBMAP] >>
  simp[venom_state_component_equality]
QED

Theorem lookup_var_drop_fresh:
  !st s x.
    not_fresh_at st x ==> lookup_var x (drop_fresh st s) = lookup_var x s
Proof
  rw[lookup_var_def, drop_fresh_def, FLOOKUP_DRESTRICT, IN_DEF]
QED

(* ===== Straight-line fragments from the cleaned state ===== *)

(* frag_exec_run_inst_seq where the run is known from drop_fresh st s, as
   the fresh_vars_wrt lemmas give it, and the fragment's end is wanted in
   any state with more variables bound.  The emitted code is straight-line
   and has no INVOKE or external call, as run_inst_seq_vars_ext needs (see
   the header). *)
Theorem frag_exec_run_inst_seq_drop_fresh:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode) (emitted_insts st st') /\
    (!s. P s ==>
       (?t0. run_inst_seq (emitted_insts st st') (drop_fresh st s) = OK t0 /\
             !t. vars_ext t0 t ==>
                 Q (t with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
       (?a t0. run_inst_seq (emitted_insts st st') (drop_fresh st s) =
                 Abort a t0 /\
               !t n. vars_ext t0 t ==> R (Abort a (t with vs_inst_idx := n))))
    ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >> irule frag_exec_run_inst_seq >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`emitted_insts st st'`, `drop_fresh st s`, `s`] mp_tac
    run_inst_seq_vars_ext >>
  (impl_tac >- simp[vars_ext_drop_fresh, EVERY_MEM]) >>
  simp[vars_ext_result_def] >> strip_tac >> metis_tac[]
QED
