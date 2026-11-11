(* Returned shared state is retained; caller-local state is restored. *)
Theory lowerDloadReturnInvokePop
Ancestors
  lowerDloadReturnInvokePush lowerDloadSafetyKernel venomExecSemantics
  finite_map pred_set list o1LowerDloadJointRestore venomState ptrDiscipline
  lowerDloadSafetyUpdates lowerDloadReturnCallContext lowerDloadOracleCallAssembly
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

(* The actual source return supplies reachability of the resumed caller;
   the old caller continuation, not the callee entry, is retained. *)
Theorem ld_return_caller_frame_reachable:
  o1_ctx_shape C /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  run_blocks sf C callee cs = IntRet rs sc /\
  ld_sync lo P C vs0
    (<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
       cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    PGr Gr tnr callee rinst se te Ar fr Nr /\
  step_inst 0 C rinst se = IntRet rs sc /\
  bind_outputs inst.inst_outputs rs.iret_values
    (adopt_return_fmp rs (merge_callee_state s sc)) = SOME sr /\
  active_inst fn next (sr with vs_inst_idx := SUC s.vs_inst_idx) ==>
  frame_reachable vs0 C stk PG
    (DRESTRICT G (COMPL (set inst.inst_outputs)))
    (tnr with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
    fn next (sr with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  qpat_assum `ld_sync _ _ _ _ (_::_) _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o MATCH_MP ld_sync_source) >>
  drule frame_reachable_ret >> simp[] >> metis_tac[]
QED

Theorem ld_return_caller_reachable:
  o1_ctx_shape C /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_return_cont C fn caller_cs s /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  run_blocks sf C callee cs = IntRet rs sc /\
  ld_sync lo P C vs0
    (<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
       cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    PGr Gr tnr callee rinst se te Ar fr Nr /\
  step_inst 0 C rinst se = IntRet rs sc /\
  bind_outputs inst.inst_outputs rs.iret_values
    (adopt_return_fmp rs (merge_callee_state s sc)) = SOME sr /\
  active_inst fn next (sr with vs_inst_idx := SUC s.vs_inst_idx) ==>
  frame_reachable vs0 C stk PG
    (DRESTRICT G (COMPL (set inst.inst_outputs)))
    (tnr with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
    fn next (sr with vs_inst_idx := SUC s.vs_inst_idx) /\
  ld_return_cont C fn caller_cs (sr with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> conj_tac
  >- (drule_all ld_return_caller_frame_reachable >> simp[]) >>
  irule ld_return_cont_next >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (qpat_x_assum `ld_sync _ _ _ _ (_::_) _ _ _ _ _ _ _ _ _ _` kall_tac >>
    drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  qexistsl_tac [`inst`, `sf`] >>
  simp[venomInstTheory.is_terminator_def] >>
  conj_tac >- simp[Once step_inst_def] >>
  metis_tac[ld_sync_source]
QED

Theorem ld_invoke_pop_core:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  fn' = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  inst.inst_opcode = INVOKE /\ 
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ^ld_probe_terminal lo P C C' vs0
    (<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
       cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    callee cs (f::fs) fc A Sigma names rt u /\
  bind_outputs inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t u)) = SOME q /\
  active_inst fn' nexti (q with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^ld_transfer_point lo P C C' vs0 stk fn fn' s fs0 f0 A0 Sigma names bb
    (q with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qabbrev_tac `Ambient = ^ld_covered_ambient` >>
  qabbrev_tac `Stable = ^ld_probe_stable` >>
  qabbrev_tac `Terminal = ^ld_probe_terminal` >>
  qabbrev_tac `Point = ^ld_transfer_point` >>
  qabbrev_tac `Guard = ^ld_probe_guard` >> fs[] >> strip_tac >>
  `?sr. bind_outputs inst.inst_outputs rs.iret_values
      (adopt_return_fmp rs (merge_callee_state s cs')) = SOME sr /\
      step_inst sf C inst s = OK sr` by
    (irule lowerDloadReturnInterfaceProbeTheory.ld_invoke_from_return >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `o1_ctx_shape C` by fs[Abbr `Ambient`] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (qpat_x_assum `ld_sync _ _ _ _ (_::_) _ _ _ _ _ _ _ _ _ _` kall_tac >>
     drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `EVERY inst_wf (fn_insts fn)` by
    (qpat_x_assum `ld_sync _ _ _ _ (_::_) _ _ _ _ _ _ _ _ _ _` kall_tac >>
     drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >>
     simp[venomWfTheory.fn_inst_wf_def, EVERY_MEM, venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (qpat_assum `ld_sync _ _ _ _ stk _ _ _ _ _ _ _ _ (f::fs) _`
       (strip_assume_tac o MATCH_MP ld_sync_active) >> fs[]) >>
  `lower_dload_function_supply f.lf_supply fn =
    (fn', SND (lower_dload_function_supply f.lf_supply fn))` by
    fs[ld_image_def] >>
  `sr.vs_current_bb = s.vs_current_bb /\ q.vs_current_bb = t.vs_current_bb` by
    metis_tac[o1LowerDloadRunnerBoundaryTheory.ld_invoke_bind_control] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn'.fn_blocks)` by
    (drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     simp[venomInstTheory.fn_labels_def]) >>
  `?ti. get_instruction bb (SUC t.vs_inst_idx) = SOME ti` by
    (drule_all lowerDloadSafetyAmbientTheory.ld_active_lookup >>
     simp[] >> strip_tac >>
     gvs[venomInstTheory.get_instruction_def]) >>
  `?next Y. active_inst fn next (sr with vs_inst_idx := SUC s.vs_inst_idx) /\
    ld_envelope f.lf_supply fn (sr with vs_inst_idx := SUC s.vs_inst_idx)
      (SUC s.vs_inst_idx) Y (p+1)` by
    (irule (SRULE [] (Q.INST [`X` |-> `[inst]`,
       `q` |-> `q with vs_inst_idx := SUC t.vs_inst_idx`]
       lowerDloadSafetyLocationsTheory.ld_envelope_successor_location)) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`bb`, `inst`, `q with vs_inst_idx := SUC t.vs_inst_idx`,
       `s`, `t`, `ti`] >> simp[] >>
     metis_tac[ld_sync_control, pairTheory.FST]) >>
  drule_all ld_return_caller_frame_reachable >> strip_tac >>
  `!caller_cs. ld_return_cont C fn caller_cs s ==>
    ld_return_cont C fn caller_cs (sr with vs_inst_idx := SUC s.vs_inst_idx)` by
    (rpt strip_tac >> irule ld_return_cont_next >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`inst`, `sf`] >>
     simp[venomInstTheory.is_terminator_def] >> metis_tac[ld_sync_source]) >>
  `cs'.vs_call_ctx = s.vs_call_ctx` by
    (drule_all ld_setup_return_call_ctx >> simp[]) >>
  `bind_outputs inst.inst_outputs rt.iret_values (merge_callee_state s cs') = SOME sr /\
   bind_outputs inst.inst_outputs rt.iret_values (merge_callee_state t u) = SOME q` by
    gvs[adopt_return_fmp_def] >>
  qabbrev_tac `B = DRESTRICT Ar (ld_slots Ar (f::fs))` >>
  qabbrev_tac `keep = COMPL (set inst.inst_outputs)` >>
  qabbrev_tac `g = f with <|lf_src := sr with vs_inst_idx := SUC s.vs_inst_idx;
    lf_tgt := q with vs_inst_idx := SUC t.vs_inst_idx;
    lf_H := DRESTRICT f.lf_H keep; lf_tv := DRESTRICT f.lf_tv keep|>` >>
  qabbrev_tac `tn1 = tnr with t_var := DRESTRICT tn.t_var keep` >>
  `ld_memory lo B tn1 (sr with vs_inst_idx := SUC s.vs_inst_idx)
      (q with vs_inst_idx := SUC t.vs_inst_idx) /\
   ld_nonghost tn1 (sr with vs_inst_idx := SUC s.vs_inst_idx)
      (q with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qunabbrev_tac `B` >> qunabbrev_tac `tn1` >>
     irule ld_return_shared_restore >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[ld_sync_memory]) >>
  `EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs) /\
   FDOM B = ld_slots B (f::fs)` by
    (qunabbrev_tac `B` >> qunabbrev_tac `Stable` >>
     drule_all ld_call_saved_alloc_restore >> simp[]) >>
  `bind_outputs inst.inst_outputs rt.iret_values (merge_callee_state f.lf_src cs') = SOME sr /\
   bind_outputs inst.inst_outputs rt.iret_values (merge_callee_state f.lf_tgt u) = SOME q` by
    simp[] >>
  `g = (f with <|lf_src := sr with vs_inst_idx := SUC s.vs_inst_idx;
    lf_tgt := q with vs_inst_idx := SUC t.vs_inst_idx;
    lf_H := DRESTRICT f.lf_H keep; lf_tv := DRESTRICT f.lf_tv keep|>)` by
    simp[Abbr `g`] >>
  `ld_global lo B (g::fs)` by
    (qunabbrev_tac `B` >> qunabbrev_tac `Stable` >>
     drule_all ld_call_global_return_restore >> simp[]) >>
  `EVERY (\h. h.lf_supply = Sigma h.lf_fn.fn_name) (f::fs) /\
   (!i k. i < k /\ k < LENGTH (f::fs) ==>
      list_precedes (EL i (f::fs)).lf_fn.fn_name
        (EL k (f::fs)).lf_fn.fn_name names)` by fs[Abbr `Stable`] >>
  drule_all ld_return_stack_geometry >> strip_tac >>
  `!i. i < LENGTH stk ==>
    (EL i stk).cf_fn = (EL i fs).lf_fn /\
    (EL i stk).cf_state = (EL i fs).lf_src /\
    (EL i stk).cf_prov = ld_erase B o_f (EL i fs).lf_H /\
    (EL i stk).cf_params = MAP (OPTION_MAP (ld_erase B)) (EL i fs).lf_Q /\
    (EL i stk).cf_tvar = (EL i fs).lf_tv` by
    (rpt strip_tac >> qunabbrev_tac `B` >> qunabbrev_tac `Stable` >>
     drule_all ld_call_saved_stack_return >> simp[]) >>
  `set inst.inst_outputs SUBSET set (fn_ir_vars f.lf_fn)` by
    (simp[SUBSET_DEF] >> rpt strip_tac >> irule ld_inst_output_ir >>
     qexists_tac `inst` >> simp[] >>
     metis_tac[ld_sync_source, ld_active_inst_member]) >>
  `ld_vars P B g` by
    (qpat_assum `EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs)`
       (strip_assume_tac o SRULE []) >>
     drule_all ld_vars_return_restore >> simp[Abbr `g`, Abbr `keep`]) >>
  drule_all ld_return_frame_geometry >> strip_tac >>
  `ld_maps B g` by
    (qpat_assum `EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs)`
       (strip_assume_tac o SRULE []) >>
     `!d ai. ld_private g d ai = ld_private f d ai` by
       simp[ld_private_def] >>
     qpat_x_assum `ld_maps B f` mp_tac >>
     simp[ld_maps_def] >> strip_tac >> simp[]) >>
  `FDOM B = ld_slots B (g::fs)` by
    (qpat_x_assum `FDOM B = _` SUBST1_TAC >>
     qpat_x_assum `g.lf_serial = _` mp_tac >>
     qpat_x_assum `g.lf_src.vs_allocas = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rpt strip_tac >> simp[ld_slots_def, EXTENSION] >> metis_tac[]) >>
  `!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a` by
    (fs[Abbr `Stable`] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     fs[ld_slots_def, FLOOKUP_DEF]) >>
  `ld_slots A (f::fs) SUBSET ld_slots Ar (f::fs)` by
    (irule lowerDloadReturnInvokeStackTheory.ld_slots_agree_subset >> simp[]) >>
  `!a. a IN FRANGE f.lf_H \/ MEM (SOME a) f.lf_Q ==>
    FLOOKUP B a = FLOOKUP A a` by
    (rpt strip_tac >>
     `a IN FDOM A` by
       (`ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
        irule ld_global_selected >> goal_assum (drule_at Any) >>
        qexists_tac `f` >> simp[]) >>
     `a IN ld_slots A (f::fs)` by metis_tac[ld_sync_def] >>
     simp[Abbr `B`, FLOOKUP_DRESTRICT] >> fs[SUBSET_DEF]) >>
  `ld_erase B o_f f.lf_H = ld_erase A o_f f.lf_H` by
    (simp[fmap_eq_flookup, FLOOKUP_o_f] >> gen_tac >>
     Cases_on `FLOOKUP f.lf_H x` >> simp[] >>
     `FLOOKUP B x' = FLOOKUP A x'` by
       (first_x_assum irule >> simp[FRANGE_FLOOKUP] >> metis_tac[]) >>
     simp[ld_erase_def]) >>
  `MAP (OPTION_MAP (ld_erase B)) f.lf_Q =
    MAP (OPTION_MAP (ld_erase A)) f.lf_Q` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     Cases_on `x` >> simp[ld_erase_def]) >>
  `PG = MAP (OPTION_MAP (ld_erase B)) g.lf_Q /\
   DRESTRICT G keep = ld_erase B o_f g.lf_H` by
    (qpat_assum `ld_sync _ _ _ _ stk _ _ _ _ _ _ _ _ (f::fs) _`
       (strip_assume_tac o SRULE [ld_sync_def]) >>
     `G = ld_erase B o_f f.lf_H` by metis_tac[] >>
     simp[Abbr `g`, Abbr `keep`, lowerDloadSafetyBoundaryTheory.provenance_return_erasure]) >>
  `EVERY (\h. h.lf_serial < N /\ ld_maps B h /\ ld_vars P B h /\
      ld_intervals lo h.lf_src /\ ld_intervals lo h.lf_tgt /\
      h.lf_src.vs_prev_bb = h.lf_tgt.vs_prev_bb /\
      h.lf_src.vs_current_bb = h.lf_tgt.vs_current_bb /\
      MEM h.lf_fn C.ctx_functions) (g::fs)` by
    (qpat_x_assum `EVERY (\h. h.lf_serial < N /\ _) (g::fs)` mp_tac >>
     qpat_x_assum `EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs)` mp_tac >>
     qpat_x_assum `ld_maps B g` mp_tac >>
     qpat_x_assum `ld_vars P B g` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH (g::fs) ==>
    ?X p. ld_envelope (EL i (g::fs)).lf_supply (EL i (g::fs)).lf_fn
      (EL i (g::fs)).lf_src (EL i (g::fs)).lf_src.vs_inst_idx X p /\
      (EL i (g::fs)).lf_tgt.vs_inst_idx = p` by
    (qpat_x_assum `!j. j < LENGTH fs ==> ?X p. _` mp_tac >>
     qpat_x_assum `ld_envelope _ _ (sr with vs_inst_idx := _) _ Y _` mp_tac >>
     qpat_x_assum `t.vs_inst_idx = p` mp_tac >>
     qpat_x_assum `f.lf_fn = fn` mp_tac >>
     qunabbrev_tac `g` >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `i` >> gvs[arithmeticTheory.ADD1] >> metis_tac[]) >>
  `ld_sync lo P C vs0 stk PG (DRESTRICT G keep) tn1 fn next
    (sr with vs_inst_idx := SUC s.vs_inst_idx)
    (q with vs_inst_idx := SUC t.vs_inst_idx) B (g::fs) N` by
    (qpat_assum `ld_sync _ _ _ _ stk _ _ _ _ _ _ _ _ (f::fs) _`
       (strip_assume_tac o SRULE [ld_sync_def]) >>
     qpat_x_assum `!a. a IN FRANGE f.lf_H \/ _ ==> _` kall_tac >>
     qpat_x_assum `!a. a IN ld_slots A (f::fs) ==> _` kall_tac >>
     qpat_x_assum `Abbrev (Ambient = _)` kall_tac >>
     qpat_x_assum `Abbrev (Terminal = _)` kall_tac >>
     qpat_x_assum `Abbrev (Point = _)` kall_tac >>
     qpat_x_assum `Abbrev (Stable = _)` kall_tac >>
     qpat_x_assum `Abbrev (Guard = _)` kall_tac >>
     pure_rewrite_tac[ld_sync_def, listTheory.HD] >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (simp[NoAsms, Abbr `g`, Abbr `tn1`])] >>
     FIRST [first_assum ACCEPT_TAC,
       (qpat_x_assum `f.lf_tv = tn.t_var` (fn th => rewrite_tac[th]))]) >>
  `fs0 = fs` by
    (qpat_assum `Stable lo P Sigma names fs0 f0 A0 A (f::fs)` mp_tac >>
     qunabbrev_tac `Stable` >> rpt (pop_assum kall_tac) >> simp[]) >>
  `fr = HD fr::f::fs` by
    (qpat_assum `Stable lo P Sigma names (f::fs) fc A Ar fr` mp_tac >>
     qunabbrev_tac `Stable` >> rpt (pop_assum kall_tac) >>
     Cases_on `fr` >> simp[] >> metis_tac[]) >>
  `Stable lo P Sigma names (f::fs) fc A Ar (HD fr::f::fs)` by metis_tac[] >>
  `(!a. a IN FDOM A0 INTER ld_slots A0 fs0 ==> FLOOKUP B a = FLOOKUP A0 a) /\
   (!h. MEM h fs0 ==> FRANGE h.lf_H SUBSET ld_slots Ar (f::fs) /\
      (!a. MEM (SOME a) h.lf_Q ==> a IN ld_slots Ar (f::fs)))` by
    (qunabbrev_tac `Stable` >> drule_all lowerDloadReturnInvokeStackTheory.ld_saved_slots_restore >>
     strip_tac >> qpat_x_assum `fs0 = fs` SUBST_ALL_TAC >>
     simp[Abbr `B`] >> rpt strip_tac >>
     qpat_assum `!h. MEM h fs ==> FRANGE h.lf_H SUBSET _ /\ _` drule >> simp[]) >>
  `ld_slots A fs0 SUBSET ld_slots B fs0` by
    (irule lowerDloadReturnInvokeStackTheory.ld_slots_agree_subset >>
     rpt strip_tac >>
     `a IN ld_slots A (f::fs)` by
       (qpat_x_assum `fs0 = fs` SUBST_ALL_TAC >>
        qpat_x_assum `a IN ld_slots A fs` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[Once ld_slots_cons]) >>
     qunabbrev_tac `B` >>
     qpat_assum `!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a` mp_tac >>
     qpat_assum `ld_slots A (f::fs) SUBSET ld_slots Ar (f::fs)` mp_tac >>
     qpat_assum `a IN ld_slots A (f::fs)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[SUBSET_DEF, FLOOKUP_DRESTRICT]) >>
  `Stable lo P Sigma names fs0 f0 A0 B (g::fs)` by
    (qpat_assum `Stable lo P Sigma names fs0 f0 A0 A (f::fs)` mp_tac >>
     qunabbrev_tac `Stable` >> BETA_TAC >>
     pure_rewrite_tac [listTheory.HD, listTheory.TL, listTheory.NOT_CONS_NIL] >>
     strip_tac >>
     conj_tac >- simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[Abbr `g`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `EVERY (\h. h.lf_supply = _) (f::fs)` mp_tac >>
         qunabbrev_tac `g` >> rpt (pop_assum kall_tac) >> simp[]) >>
     conj_tac
     >- (qpat_assum `EVERY (\h. !j a. _) (f::fs)` mp_tac >>
         qunabbrev_tac `g` >> rpt (pop_assum kall_tac) >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `!h. MEM h fs0 ==> FRANGE h.lf_H SUBSET ld_slots A fs0 /\ _` mp_tac >>
         qpat_assum `ld_slots A fs0 SUBSET ld_slots B fs0` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[SUBSET_DEF] >> metis_tac[]) >>
     qpat_assum `!a. a IN FDOM A0 INTER _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qunabbrev_tac `Point` >> BETA_TAC >>
  qexistsl_tac [`PG`, `DRESTRICT G keep`, `tn1`, `next`,
    `sr with vs_inst_idx := SUC s.vs_inst_idx`,
    `q with vs_inst_idx := SUC t.vs_inst_idx`, `B`, `g::fs`, `N`, `Y`, `p+1`, `0`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qunabbrev_tac `Stable` >> first_assum ACCEPT_TAC) >>
  simp[NoAsms, listTheory.HD] >>
  conj_tac >- simp[Abbr `g`, ld_image_def] >>
  conj_tac >- simp[Abbr `g`] >>
  conj_tac
  >- (`active_inst fn' ti (q with vs_inst_idx := SUC t.vs_inst_idx)` by
        (irule contextCodegenRelPropsTheory.lookup_instruction_active >>
         qexists_tac `bb` >>
         qpat_assum `lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb` mp_tac >>
         qpat_assum `get_instruction bb (SUC t.vs_inst_idx) = SOME ti` mp_tac >>
         qpat_assum `q.vs_current_bb = t.vs_current_bb` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[]) >>
      `0 < LENGTH Y /\ ti = EL 0 Y` by
        (qpat_assum `ld_envelope _ _ (sr with vs_inst_idx := SUC s.vs_inst_idx) _ Y _` mp_tac >>
         qpat_assum `active_inst fn' ti _` mp_tac >>
         qpat_assum `fn' = ld_image f` mp_tac >>
         qpat_assum `ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N` mp_tac >>
         qpat_assum `q.vs_current_bb = t.vs_current_bb` mp_tac >>
         qpat_assum `sr.vs_current_bb = s.vs_current_bb` mp_tac >>
         qpat_assum `t.vs_inst_idx = p` mp_tac >>
         qpat_assum `f.lf_fn = fn` mp_tac >>
         qpat_assum `ALL_DISTINCT (MAP _ fn.fn_blocks)` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt disch_tac >>
         drule ld_sync_control >> strip_tac >>
         gvs[ld_image_def] >>
         drule_at (Pat `ld_envelope _ _ _ _ _ _`)
           lowerDloadSafetyLocationsTheory.ld_envelope_active_head >>
         simp[] >>
         disch_then (qspecl_then [`ti`, `q with vs_inst_idx := SUC t.vs_inst_idx`] mp_tac) >>
         simp[]) >>
      simp[ld_prefix_zero] >>
      qpat_assum `active_inst fn' ti _` mp_tac >>
      qpat_assum `ti = EL 0 Y` mp_tac >>
      qpat_assum `fn' = ld_image f` mp_tac >>
      qpat_assum `t.vs_inst_idx = p` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[]) >>
  simp[] >>
  qpat_assum `lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb` mp_tac >>
  qpat_assum `fn' = ld_image f` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[]
QED

Theorem ld_invoke_active_pop:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  fn' = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  ld_return_cont C fn caller_cs s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ^ld_probe_terminal lo P C C' vs0
    (<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
       cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    callee cs (f::fs) fc A Sigma names rt u /\
  bind_outputs inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t u)) = SOME q /\
  active_inst fn' nexti (q with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^ld_probe_point lo P C C' vs0 stk fn fn' caller_cs fs0 f0 A0 Sigma names bb
    (q with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >>
  drule_all ld_invoke_pop_core >> simp[] >> strip_tac >>
  simp[NoAsms, Abbr `Goal`] >>
  qexistsl_tac [`PG'`,`G'`,`tn'`,`inst'`,`s''`,`t0`,`A'`,`frames`,`N'`,`X`,`p'`,`h`] >>
  gvs[] >> metis_tac[]
QED

Theorem ld_invoke_guarded_pop:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  fn' = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  ld_return_cont C fn caller_cs s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ^ld_probe_terminal lo P C C' vs0
    (<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
       cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    callee cs (f::fs) fc A Sigma names rt u /\
  bind_outputs inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t u)) = SOME q /\
  ^ld_probe_guard C' j bb (q with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^ld_probe_point lo P C C' vs0 stk fn fn' caller_cs fs0 f0 A0 Sigma names bb
    (q with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qabbrev_tac `Ambient = ^ld_covered_ambient` >>
  qabbrev_tac `Stable = ^ld_probe_stable` >>
  qabbrev_tac `Terminal = ^ld_probe_terminal` >>
  qabbrev_tac `Point = ^ld_probe_point` >>
  qabbrev_tac `Guard = ^ld_probe_guard` >> strip_tac >>
  `q.vs_current_bb = t.vs_current_bb` by
    metis_tac[o1LowerDloadRunnerBoundaryTheory.ld_invoke_bind_control] >>
  `?ti. get_instruction bb (SUC t.vs_inst_idx) = SOME ti` by
    (mp_tac (Q.INST [`C` |-> `C'`, `k` |-> `j`,
      `t` |-> `q with vs_inst_idx := SUC t.vs_inst_idx`]
      lowerDloadReturnAlignmentTheory.ld_successful_body_fetch) >>
     fs[Abbr `Guard`] >> metis_tac[]) >>
  `active_inst fn' ti (q with vs_inst_idx := SUC t.vs_inst_idx)` by
    (simp[contextCodegenRelTheory.active_inst_def] >>
     qexists_tac `bb` >>
     gvs[venomInstTheory.get_instruction_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       venomExecPropsTheory.lookup_block_label]) >>
  qunabbrev_tac `Ambient` >> qunabbrev_tac `Stable` >>
  qunabbrev_tac `Terminal` >> qunabbrev_tac `Point` >>
  drule_all ld_invoke_active_pop >> simp[NoAsms]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "caller pop has kernel hypotheses")
  [ld_invoke_active_pop, ld_invoke_guarded_pop];
