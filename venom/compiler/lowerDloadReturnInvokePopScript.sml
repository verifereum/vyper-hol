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

Theorem ld_return_frame_geometry:
  bind_outputs outs vals (merge_callee_state f.lf_src sc) = SOME sr /\
  bind_outputs outs vals (merge_callee_state f.lf_tgt tc) = SOME tr /\
  g = (f with <|lf_src := sr with vs_inst_idx := si;
    lf_tgt := tr with vs_inst_idx := ti;
    lf_H := DRESTRICT f.lf_H keep;
    lf_tv := DRESTRICT f.lf_tv keep|>) ==>
  g.lf_src.vs_allocas = f.lf_src.vs_allocas /\
  g.lf_tgt.vs_allocas = f.lf_tgt.vs_allocas /\
  g.lf_src.vs_alloca_next = f.lf_src.vs_alloca_next /\
  g.lf_tgt.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
  g.lf_src.vs_current_bb = f.lf_src.vs_current_bb /\
  g.lf_tgt.vs_current_bb = f.lf_tgt.vs_current_bb /\
  g.lf_src.vs_prev_bb = f.lf_src.vs_prev_bb /\
  g.lf_tgt.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
  g.lf_serial = f.lf_serial /\ g.lf_E = f.lf_E /\
  g.lf_fn = f.lf_fn /\ g.lf_supply = f.lf_supply /\
  g.lf_Q = f.lf_Q /\ FRANGE g.lf_H SUBSET FRANGE f.lf_H
Proof
  strip_tac >>
  `sr = (merge_callee_state f.lf_src sc) with vs_vars := sr.vs_vars` by
    (irule o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only >>
     goal_assum drule) >>
  `tr = (merge_callee_state f.lf_tgt tc) with vs_vars := tr.vs_vars` by
    (irule o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only >>
     goal_assum drule) >>
  qpat_x_assum `sr = _` SUBST_ALL_TAC >>
  qpat_x_assum `tr = _` SUBST_ALL_TAC >>
  gvs[merge_callee_state_def] >>
  simp[SUBSET_DEF, FRANGE_FLOOKUP, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_global_return_restore:
  ld_global lo A (f::fs) /\ FDOM A = ld_slots A (f::fs) /\
  (!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a) /\
  bind_outputs outs vals (merge_callee_state f.lf_src sc) = SOME sr /\
  bind_outputs outs vals (merge_callee_state f.lf_tgt tc) = SOME tr /\
  g = (f with <|lf_src := sr with vs_inst_idx := si;
    lf_tgt := tr with vs_inst_idx := ti;
    lf_H := DRESTRICT f.lf_H keep;
    lf_tv := DRESTRICT f.lf_tv keep|>) ==>
  ld_global lo (DRESTRICT Ar (ld_slots Ar (f::fs))) (g::fs)
Proof
  strip_tac >>
  drule_all ld_return_frame_geometry >> strip_tac >>
  qpat_x_assum `g = _` kall_tac >>
  `ld_global lo A ((g with lf_H := f.lf_H)::fs)` by
    (irule ld_global_head_cong >> qexists_tac `f` >> simp[]) >>
  `FDOM A SUBSET FDOM (DRESTRICT Ar (ld_slots Ar (f::fs)))` by
    (`ld_slots A (f::fs) SUBSET ld_slots Ar (f::fs)` by
      (irule lowerDloadReturnInvokeStackTheory.ld_slots_agree_subset >> simp[]) >>
     simp[FDOM_DRESTRICT, SUBSET_DEF] >> rpt strip_tac >>
     `x IN ld_slots A (f::fs)` by metis_tac[] >>
     `FLOOKUP Ar x = FLOOKUP A x` by metis_tac[] >>
     Cases_on `x IN FDOM Ar` >> fs[SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[]) >>
  `!source. ld_sites ((g with lf_H := f.lf_H)::fs) source =
    ld_sites (g::fs) source` by
    (gen_tac >> simp[ld_sites_def, EXTENSION] >>
     gen_tac >> PairCases_on `x` >> simp[] >> Cases_on `x0` >> simp[]) >>
  qpat_x_assum `ld_global lo A ((g with lf_H := _)::fs)` mp_tac >>
  qpat_x_assum `!source. ld_sites _ source = _` (fn th => rewrite_tac[ld_global_def,th]) >>
  qpat_x_assum `FRANGE g.lf_H SUBSET _` mp_tac >>
  qpat_x_assum `FDOM A SUBSET _` mp_tac >>
  qpat_x_assum `g.lf_src.vs_alloca_next = _` mp_tac >>
  qpat_x_assum `g.lf_tgt.vs_alloca_next = _` mp_tac >>
  qpat_x_assum `g.lf_Q = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[ld_global_def, SUBSET_DEF] >> ntac 6 strip_tac >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!source j aid b n. _ ==> _ /\ _` drule >> simp[]) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> disch_tac >>
  Cases_on `f' = g`
  >- (gvs[] >>
      qpat_x_assum `!h a. (_ \/ MEM h fs) /\ _ ==> _`
        (qspec_then `g with lf_H := f.lf_H` mp_tac) >>
      simp[] >> strip_tac >> metis_tac[]) >>
  fs[] >> metis_tac[]
QED

Theorem ld_return_stack_geometry:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  EVERY (\h. h.lf_supply = Sigma h.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
      (EL k (f::fs)).lf_fn.fn_name names) /\
  bind_outputs outs vals (merge_callee_state f.lf_src sc) = SOME sr /\
  bind_outputs outs vals (merge_callee_state f.lf_tgt tc) = SOME tr /\
  g = (f with <|lf_src := sr with vs_inst_idx := si;
    lf_tgt := tr with vs_inst_idx := ti;
    lf_H := DRESTRICT f.lf_H keep;
    lf_tv := DRESTRICT f.lf_tv keep|>) ==>
  LENGTH (g::fs) = SUC (LENGTH stk) /\
  ALL_DISTINCT (MAP (\h. h.lf_serial) (g::fs)) /\
  EVERY (\h. h.lf_serial < N /\ h.lf_supply = Sigma h.lf_fn.fn_name /\
    MEM h.lf_fn C.ctx_functions /\ ld_intervals lo h.lf_src /\
    ld_intervals lo h.lf_tgt /\
    h.lf_src.vs_prev_bb = h.lf_tgt.vs_prev_bb /\
    h.lf_src.vs_current_bb = h.lf_tgt.vs_current_bb) (g::fs) /\
  (!j k. j < k /\ k < LENGTH (g::fs) ==>
    list_precedes (EL j (g::fs)).lf_fn.fn_name
      (EL k (g::fs)).lf_fn.fn_name names) /\
  ld_charge (g::fs) = ld_charge (f::fs) /\
  ld_charge (g::fs) <= ctx_dload_count C /\
  (!j. j < LENGTH (g::fs) ==>
    (EL j (g::fs)).lf_tgt.vs_alloca_next =
    (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))) /\
  (!j. j < LENGTH fs ==>
    ?X p. ld_envelope (EL j fs).lf_supply (EL j fs).lf_fn
      (EL j fs).lf_src (EL j fs).lf_src.vs_inst_idx X p /\
      (EL j fs).lf_tgt.vs_inst_idx = p) /\
  (!j. j < LENGTH stk ==>
    (EL j stk).cf_fn = (EL j fs).lf_fn /\
    (EL j stk).cf_state = (EL j fs).lf_src /\
    (EL j stk).cf_prov = ld_erase A o_f (EL j fs).lf_H /\
    (EL j stk).cf_params = MAP (OPTION_MAP (ld_erase A)) (EL j fs).lf_Q /\
    (EL j stk).cf_tvar = (EL j fs).lf_tv)
Proof
  strip_tac >> drule_all ld_return_frame_geometry >> strip_tac >>
  qpat_x_assum `g = _` kall_tac >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ld_sync_def, ld_charge_def] >> strip_tac >>
  qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `active_inst _ _ _` kall_tac >>
  qpat_x_assum `ld_memory _ _ _ _ _` kall_tac >>
  qpat_x_assum `ld_nonghost _ _ _` kall_tac >>
  ntac 2 (qpat_x_assum `bind_outputs _ _ _ = _` kall_tac) >>
  qpat_x_assum `f.lf_src = s` kall_tac >>
  qpat_x_assum `f.lf_tgt = t` kall_tac >>
  `ld_intervals lo g.lf_src /\ ld_intervals lo g.lf_tgt` by
    (simp[ld_intervals_def] >>
     qpat_assum `ld_intervals lo f.lf_src` mp_tac >>
     qpat_assum `ld_intervals lo f.lf_tgt` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ld_intervals_def] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> rpt conj_tac
  >- (rpt gen_tac >>
      qpat_x_assum `!j k. _ ==> list_precedes _ _ _`
        (qspecl_then [`j`, `k`] mp_tac) >>
      map_every Cases_on [`j`, `k`] >> simp[])
  >- (gen_tac >>
      qpat_x_assum `!j. _ ==> _ = _` (qspec_then `j` mp_tac) >>
      Cases_on `j` >> simp[ld_charge_def])
  >> rpt strip_tac >>
  qpat_x_assum `!j. _ ==> ?X. _`
    (qspec_then `SUC j` mp_tac) >> simp[]
QED

Theorem ld_call_global_return_restore:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ^ld_probe_stable lo P Sigma names (f::fs) fc A Ar fr /\
  bind_outputs outs vals (merge_callee_state f.lf_src sc) = SOME sr /\
  bind_outputs outs vals (merge_callee_state f.lf_tgt tc) = SOME tr /\
  g = (f with <|lf_src := sr with vs_inst_idx := si;
    lf_tgt := tr with vs_inst_idx := ti;
    lf_H := DRESTRICT f.lf_H keep;
    lf_tv := DRESTRICT f.lf_tv keep|>) ==>
  ld_global lo (DRESTRICT Ar (ld_slots Ar (f::fs))) (g::fs)
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
  `FDOM A = ld_slots A (f::fs)` by fs[ld_sync_def] >>
  `!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a` by
    (fs[Abbr `Stable`] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     fs[ld_slots_def, FLOOKUP_DEF]) >>
  drule_all ld_global_return_restore >> simp[]
QED

Theorem ld_saved_stack_alloc_agree:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  (!a. a IN ld_slots A (f::fs) ==> FLOOKUP B a = FLOOKUP A a) ==>
  !j. j < LENGTH stk ==>
    (EL j stk).cf_fn = (EL j fs).lf_fn /\
    (EL j stk).cf_state = (EL j fs).lf_src /\
    (EL j stk).cf_prov = ld_erase B o_f (EL j fs).lf_H /\
    (EL j stk).cf_params = MAP (OPTION_MAP (ld_erase B)) (EL j fs).lf_Q /\
    (EL j stk).cf_tvar = (EL j fs).lf_tv
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `FDOM A = ld_slots A (f::fs)` by fs[ld_sync_def] >>
  `MEM (EL j fs) (f::fs)` by
    (`LENGTH fs = LENGTH stk` by fs[ld_sync_def] >> simp[EL_MEM]) >>
  `!a. a IN FRANGE (EL j fs).lf_H \/ MEM (SOME a) (EL j fs).lf_Q ==>
    FLOOKUP B a = FLOOKUP A a` by
    (rpt strip_tac >>
     qpat_x_assum `!a. a IN ld_slots A (f::fs) ==> _` irule >>
     `a IN FDOM A` by (irule ld_global_selected >> metis_tac[]) >>
     metis_tac[]) >>
  `ld_erase B o_f (EL j fs).lf_H = ld_erase A o_f (EL j fs).lf_H` by
    (simp[fmap_eq_flookup, FLOOKUP_o_f] >> gen_tac >>
     Cases_on `FLOOKUP (EL j fs).lf_H x` >> simp[] >>
     `FLOOKUP B x' = FLOOKUP A x'` by
       (first_x_assum irule >> simp[FRANGE_FLOOKUP] >> metis_tac[]) >>
     simp[ld_erase_def]) >>
  `MAP (OPTION_MAP (ld_erase B)) (EL j fs).lf_Q =
    MAP (OPTION_MAP (ld_erase A)) (EL j fs).lf_Q` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     Cases_on `x` >> simp[ld_erase_def]) >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ld_sync_def] >> strip_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _` (qspec_then `j` mp_tac) >> simp[]
QED

Theorem ld_call_saved_stack_return:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ^ld_probe_stable lo P Sigma names (f::fs) fc A Ar fr ==>
  !j. j < LENGTH stk ==>
    (EL j stk).cf_fn = (EL j fs).lf_fn /\
    (EL j stk).cf_state = (EL j fs).lf_src /\
    (EL j stk).cf_prov =
      ld_erase (DRESTRICT Ar (ld_slots Ar (f::fs))) o_f (EL j fs).lf_H /\
    (EL j stk).cf_params = MAP
      (OPTION_MAP (ld_erase (DRESTRICT Ar (ld_slots Ar (f::fs))))) (EL j fs).lf_Q /\
    (EL j stk).cf_tvar = (EL j fs).lf_tv
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
  `!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a` by
    (fs[Abbr `Stable`] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     fs[ld_slots_def, FLOOKUP_DEF]) >>
  `ld_slots A (f::fs) SUBSET ld_slots Ar (f::fs)` by
    (irule lowerDloadReturnInvokeStackTheory.ld_slots_agree_subset >> simp[]) >>
  `!a. a IN ld_slots A (f::fs) ==>
    FLOOKUP (DRESTRICT Ar (ld_slots Ar (f::fs))) a = FLOOKUP A a` by
    (simp[FLOOKUP_DRESTRICT] >> fs[SUBSET_DEF]) >>
  rpt strip_tac >> drule_all ld_saved_stack_alloc_agree >> simp[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
        else raise Fail "structural return restoration has kernel hypotheses")
  [ld_return_frame_geometry, ld_global_return_restore, ld_return_stack_geometry,
   ld_call_global_return_restore, ld_saved_stack_alloc_agree,
   ld_call_saved_stack_return];
