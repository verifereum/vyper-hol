(* Allocation frames for the actual selected dispatch and entry-check paths. *)
Theory actualEntryAllocationFrame
Ancestors
  moduleLoweringProps entryDispatchProps fragExec

Theorem vars_pc_only_allocas:
  !s t. vars_pc_only s t ==> t.vs_allocas = s.vs_allocas
Proof
  rw[vars_pc_only_def] >> pop_assum (SUBST1_TAC o SYM) >> simp[]
QED

Theorem compile_selector_dispatch_linear_allocas:
  !selectors fallback_lbl st st' ctx fn ss.
      compile_selector_dispatch_linear selectors fallback_lbl st = ((), st') /\
      fn_has_code st st' fn /\
      EVERY (\(sel, lbl). sel < 2 ** 32) selectors /\
      LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256) /\
      fresh_vars_wrt st ss /\ ~ss.vs_halted /\
      ss.vs_current_bb = st.cs_current_bb /\
      ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
      ?tt. runs_through ctx fn ss tt /\ vars_pc_only ss tt /\
           fresh_vars_wrt st' tt /\
           (!x. not_fresh_at st x ==> lookup_var x tt = lookup_var x ss) /\
           tt.vs_current_bb =
             linear_dispatch_target ss.vs_call_ctx.cc_calldata selectors
               fallback_lbl /\
           tt.vs_inst_idx = 0 /\ tt.vs_allocas = ss.vs_allocas
Proof
  rpt strip_tac >> drule_all compile_selector_dispatch_linear_correct >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum $ drule_at Any >>
  simp[] >> metis_tac[vars_pc_only_allocas]
QED

Theorem payable_check_frag_allocas:
  emit_op CALLVALUE [] st0 = (cv, st1) /\
  emit_op ISZERO [cv] st1 = (nv, st2) /\
  emit_void ASSERT [nv] st2 = ((), st3) /\
  fresh_vars_wrt st0 s0 ==>
  frag_exec ctx st0 st3 (\s. s = s0)
    (\t. vars_pc_only s0 t /\ fresh_vars_wrt st3 t /\
         (!x. not_fresh_at st0 x ==> lookup_var x t = lookup_var x s0) /\
         s0.vs_call_ctx.cc_callvalue = 0w /\
         t.vs_allocas = s0.vs_allocas)
    (\r. ?t. r = Abort Revert_abort t /\
              s0.vs_call_ctx.cc_callvalue <> 0w)
Proof
  strip_tac >> drule_all payable_check_frag >>
  disch_then (assume_tac o SPEC_ALL) >>
  irule frag_exec_conseq >> goal_assum $ drule_at Any >>
  simp[] >> metis_tac[vars_pc_only_allocas]
QED
