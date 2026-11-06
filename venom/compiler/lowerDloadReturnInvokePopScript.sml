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

Theorem ld_maps_alloc_agree:
  ld_maps A f /\
  (!a. a IN ld_slots A [f] ==> FLOOKUP B a = FLOOKUP A a) ==>
  ld_maps B f
Proof
  simp[ld_maps_def] >> strip_tac >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      first_x_assum drule >> strip_tac >> qexists_tac `c` >> simp[] >>
      `((f.lf_serial,aid) IN ld_slots A [f])` by
        (simp[ld_slots_def] >> metis_tac[]) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac
      >- (simp[] >>
          `((f.lf_serial,ai) IN ld_slots A [f])` by
            (simp[ld_slots_def] >> metis_tac[]) >> simp[]) >>
      disj2_tac >> simp[] >> qexists_tac `d` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem ld_slots_restrict_domain:
  FDOM (DRESTRICT A (ld_slots A frames)) =
    ld_slots (DRESTRICT A (ld_slots A frames)) frames
Proof
  simp[FDOM_DRESTRICT, ld_slots_restrict, EXTENSION] >>
  gen_tac >> eq_tac >- simp[] >>
  simp[ld_slots_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_saved_alloc_restore:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  ld_global lo A frames /\
  (!a. a IN ld_slots A frames ==> FLOOKUP Ar a = FLOOKUP A a) ==>
  EVERY (\f. ld_maps (DRESTRICT Ar (ld_slots Ar frames)) f /\
    ld_vars P (DRESTRICT Ar (ld_slots Ar frames)) f) frames /\
  FDOM (DRESTRICT Ar (ld_slots Ar frames)) =
    ld_slots (DRESTRICT Ar (ld_slots Ar frames)) frames
Proof
  strip_tac >> conj_tac >- (
    `FDOM A = ld_slots A frames /\
     EVERY (\f. ld_maps A f /\ ld_vars P A f) frames` by
      (qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
       rpt (pop_assum kall_tac) >> simp[ld_sync_def, EVERY_MEM] >> metis_tac[]) >>
    `ld_slots A frames SUBSET ld_slots Ar frames` by
      (irule lowerDloadReturnInvokeStackTheory.ld_slots_agree_subset >> simp[]) >>
    `!a. a IN ld_slots A frames ==>
       FLOOKUP (DRESTRICT Ar (ld_slots Ar frames)) a = FLOOKUP A a` by
      (simp[FLOOKUP_DRESTRICT] >> fs[SUBSET_DEF]) >>
    simp[EVERY_MEM] >> gen_tac >> strip_tac >>
    `ld_maps A f /\ ld_vars P A f` by fs[EVERY_MEM] >> conj_tac
    >- (irule ld_maps_alloc_agree >> qexists_tac `A` >> simp[] >> rpt strip_tac >>
        first_x_assum irule >> fs[ld_slots_def] >> metis_tac[]) >>
    irule ld_vars_alloc_agree >> qexists_tac `A` >> simp[] >> rpt strip_tac >>
    first_x_assum irule >>
    `a IN FDOM A` by (irule ld_global_selected >> metis_tac[]) >>
    metis_tac[]) >>
  irule ld_slots_restrict_domain
QED

Theorem ld_call_saved_alloc_restore:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ^ld_probe_stable lo P Sigma names (f::fs) fc A Ar fr ==>
  EVERY (\g. ld_maps (DRESTRICT Ar (ld_slots Ar (f::fs))) g /\
    ld_vars P (DRESTRICT Ar (ld_slots Ar (f::fs))) g) (f::fs) /\
  FDOM (DRESTRICT Ar (ld_slots Ar (f::fs))) =
    ld_slots (DRESTRICT Ar (ld_slots Ar (f::fs))) (f::fs)
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
  `!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a` by
    (fs[Abbr `Stable`] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     fs[ld_slots_def, FLOOKUP_DEF]) >>
  drule_all ld_saved_alloc_restore >> simp[]
QED

Theorem ld_vars_merge_callee:
  ld_vars P A f ==>
  ld_vars P A (f with <|
    lf_src := merge_callee_state f.lf_src sc;
    lf_tgt := merge_callee_state f.lf_tgt tc|>)
Proof
  simp[ld_vars_def, merge_callee_state_def]
QED

Theorem ld_vars_resume:
  ld_vars P A f ==>
  ld_vars P A (f with <|
    lf_src := f.lf_src with vs_inst_idx := si;
    lf_tgt := f.lf_tgt with vs_inst_idx := ti|>)
Proof
  simp[ld_vars_def]
QED

val _ = List.app (fn th => if null (hyp th) then ()
        else raise Fail "saved-frame restoration has kernel hypotheses")
  [ld_maps_alloc_agree, ld_slots_restrict_domain, ld_saved_alloc_restore,
   ld_call_saved_alloc_restore, ld_vars_merge_callee, ld_vars_resume];

Theorem ld_vars_return_restore:
  ld_vars P A f /\ set outs SUBSET set (fn_ir_vars f.lf_fn) /\
  bind_outputs outs vals (merge_callee_state f.lf_src sc) = SOME sr /\
  bind_outputs outs vals (merge_callee_state f.lf_tgt tc) = SOME tr ==>
  ld_vars P A (f with <|
    lf_src := sr with vs_inst_idx := si;
    lf_tgt := tr with vs_inst_idx := ti;
    lf_H := DRESTRICT f.lf_H (COMPL (set outs));
    lf_tv := DRESTRICT f.lf_tv (COMPL (set outs))|>)
Proof
  strip_tac >>
  `ld_vars P A (f with <|lf_src := merge_callee_state f.lf_src sc;
     lf_tgt := merge_callee_state f.lf_tgt tc|>)` by
    (irule ld_vars_merge_callee >> simp[]) >>
  drule ld_vars_bind_outputs >>
  disch_then (qspecl_then [`outs`, `vals`, `sr`, `tr`] mp_tac) >>
  simp[] >> strip_tac >>
  drule ld_vars_resume >> simp[]
QED

val _ = if null (hyp ld_vars_return_restore) then ()
        else raise Fail "resumed variable restoration has kernel hypotheses";
