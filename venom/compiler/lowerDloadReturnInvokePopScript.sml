(* Returned shared state is retained; caller-local state is restored. *)
Theory lowerDloadReturnInvokePop
Ancestors
  lowerDloadReturnInvokePush lowerDloadSafetyKernel venomExecSemantics
  finite_map pred_set list o1LowerDloadJointRestore venomState ptrDiscipline
  lowerDloadSafetyUpdates
Libs
  lowerDloadReturnPackageLib

Theorem ld_merge_return_memory[local]:
  ld_memory lo A tnr sc tc ==>
  ld_memory lo A tnr (merge_callee_state s sc) (merge_callee_state t tc)
Proof
  simp[ld_memory_def, merge_callee_state_def] >> metis_tac[]
QED

Theorem ld_merge_return_nonghost[local]:
  ld_nonghost tn s t /\ ld_nonghost tnr sc tc /\
  sc.vs_call_ctx = s.vs_call_ctx ==>
  ld_nonghost tnr (merge_callee_state s sc) (merge_callee_state t tc)
Proof
  simp[ld_nonghost_def, merge_callee_state_def] >> rpt strip_tac >>
  gvs[]
QED

Theorem ld_return_shared_restore:
  ld_memory lo A tnr sc tc /\
  ld_nonghost tn s t /\ ld_nonghost tnr sc tc /\
  sc.vs_call_ctx = s.vs_call_ctx /\
  bind_outputs outs vals (merge_callee_state s sc) = SOME sr /\
  bind_outputs outs vals (merge_callee_state t tc) = SOME tr ==>
  ld_memory lo (DRESTRICT A keep) (tnr with t_var := tv)
    (sr with vs_inst_idx := si) (tr with vs_inst_idx := ti) /\
  ld_nonghost (tnr with t_var := tv)
    (sr with vs_inst_idx := si) (tr with vs_inst_idx := ti)
Proof
  strip_tac >>
  `sr = (merge_callee_state s sc) with vs_vars := sr.vs_vars` by
    (irule o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only >>
     goal_assum drule) >>
  `tr = (merge_callee_state t tc) with vs_vars := tr.vs_vars` by
    (irule o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only >>
     goal_assum drule) >>
  `ld_memory lo (DRESTRICT A keep) tnr
     (merge_callee_state s sc) (merge_callee_state t tc)` by
    (irule ld_memory_restrict >> irule ld_merge_return_memory >> simp[]) >>
  `ld_nonghost tnr (merge_callee_state s sc) (merge_callee_state t tc)` by
    (irule ld_merge_return_nonghost >> simp[] >> qexists_tac `tn` >> simp[]) >>
  qpat_x_assum `sr = _` SUBST_ALL_TAC >>
  qpat_x_assum `tr = _` SUBST_ALL_TAC >>
  qpat_x_assum `ld_memory lo (DRESTRICT A keep) _ _ _` mp_tac >>
  qpat_x_assum `ld_nonghost tnr (merge_callee_state _ _) _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[ld_memory_def, ld_nonghost_def] >> metis_tac[]
QED

Theorem ld_vars_bind_outputs:
  !outs vals f sr tr.
    ld_vars P A f /\ set outs SUBSET set (fn_ir_vars f.lf_fn) /\
    bind_outputs outs vals f.lf_src = SOME sr /\
    bind_outputs outs vals f.lf_tgt = SOME tr ==>
    ld_vars P A (f with <|lf_src := sr; lf_tgt := tr;
      lf_H := DRESTRICT f.lf_H (COMPL (set outs));
      lf_tv := DRESTRICT f.lf_tv (COMPL (set outs))|>)
Proof
  Induct
  >- (Cases_on `vals` >> simp[bind_outputs_def, DRESTRICT_UNIV] >>
      rpt strip_tac >> gvs[]) >>
  Cases_on `vals` >- simp[bind_outputs_def] >>
  simp[bind_outputs_def] >> rpt strip_tac >>
  rename1 `MEM out (fn_ir_vars f.lf_fn)` >>
  rename1 `LENGTH outs = LENGTH rest` >>
  rename1 `update_var out value f.lf_src` >>
  `ld_vars P A (f with <|
     lf_src := update_var out value f.lf_src;
     lf_tgt := update_var out value f.lf_tgt;
     lf_H := DRESTRICT f.lf_H (COMPL {out});
     lf_tv := DRESTRICT f.lf_tv (COMPL {out})|>)` by
    (simp[update_var_def] >>
     irule (SRULE[ptrDisciplineTheory.set_prov_def]
       (Q.INST [`q` |-> `NONE`] lowerDloadSafetyUpdatesTheory.ld_vars_write)) >>
     simp[FLOOKUP_DRESTRICT, word_agree_except_def]) >>
  first_x_assum drule >>
  disch_then (qspec_then `rest` mp_tac) >>
  `COMPL (set outs) INTER COMPL {out} = COMPL (out INSERT set outs)` by
    simp[EXTENSION, CONJ_COMM] >>
  simp[bind_outputs_def, DRESTRICT_DRESTRICT, INTER_COMM]
QED

Theorem ld_vars_alloc_agree:
  ld_vars P A f /\
  (!a. a IN FRANGE f.lf_H \/ MEM (SOME a) f.lf_Q ==>
    FLOOKUP B a = FLOOKUP A a) ==>
  ld_vars P B f
Proof
  simp[ld_vars_def] >> strip_tac >> simp[] >> conj_tac >> rpt strip_tac
  >- (qpat_x_assum `!v x y. _` (qspecl_then [`v`, `x`, `y`] mp_tac) >>
      Cases_on `retpc_var f.lf_fn v` >> simp[] >>
      Cases_on `FLOOKUP f.lf_H v` >> simp[] >> strip_tac >>
      `x' IN FRANGE f.lf_H` by
        (simp[FRANGE_FLOOKUP] >> goal_assum drule) >>
      fs[ld_wordrel_SOME]) >>
  first_x_assum (qspec_then `j` mp_tac) >>
  Cases_on `j < LENGTH f.lf_Q` >> simp[] >>
  Cases_on `EL j f.lf_Q` >> simp[ld_wordrel_SOME] >>
  `MEM (SOME x) f.lf_Q` by metis_tac[MEM_EL] >> simp[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
        else raise Fail "return restoration boundary has kernel hypotheses")
  [ld_return_shared_restore, ld_vars_bind_outputs, ld_vars_alloc_agree];
