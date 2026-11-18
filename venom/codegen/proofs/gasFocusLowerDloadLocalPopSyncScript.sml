(* An operational local pop keeps current shared stores and resumes saved locals. *)
Theory gasFocusLowerDloadLocalPopSync
Ancestors
  lowerDloadReturnInvokePop lowerDloadPtrCall lowerDloadSafetyRelation
  lowerDloadSafetyKernel o1LowerDloadJointRestore venomExecSemantics
  venomState ptrDiscipline finite_map pred_set list

Theorem ld_focus_pop_shared[local]:
  ld_memory lo A tn s t /\ ld_nonghost tn s t /\
  ld_dyn_agree fl tn.t_mem s.vs_memory t.vs_memory /\
  c.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  bind_outputs outs vals (merge_callee_state c s) = SOME sr /\
  bind_outputs outs vals (merge_callee_state d t) = SOME tr /\
  dload_equal_environment (sr with vs_inst_idx := si) (tr with vs_inst_idx := ti) ==>
  ld_memory lo (DRESTRICT A keep) (tn with t_var := tv)
    (sr with vs_inst_idx := si) (tr with vs_inst_idx := ti) /\
  ld_nonghost (tn with t_var := tv)
    (sr with vs_inst_idx := si) (tr with vs_inst_idx := ti) /\
  ld_dyn_agree fl (tn with t_var := tv).t_mem
    (sr with vs_inst_idx := si).vs_memory (tr with vs_inst_idx := ti).vs_memory
Proof
  strip_tac >>
  `ld_memory lo (DRESTRICT A keep) tn s t` by simp[ld_memory_restrict] >>
  qpat_x_assum `dload_equal_environment _ _` mp_tac >>
  qpat_assum `bind_outputs _ _ _ = SOME sr`
    (assume_tac o MATCH_MP ld_bind_outputs_vars_only) >>
  qpat_assum `bind_outputs _ _ _ = SOME tr`
    (assume_tac o MATCH_MP ld_bind_outputs_vars_only) >>
  ntac 2 (pop_assum (fn th => once_rewrite_tac[th])) >>
  qpat_x_assum `ld_memory lo (DRESTRICT A keep) tn s t` mp_tac >>
  qpat_x_assum `ld_nonghost tn s t` mp_tac >>
  simp[dload_equal_environment_def, ld_memory_def, ld_nonghost_def,
       merge_callee_state_def, venom_state_component_equality] >>
  rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem ld_focus_pop_maps[local]:
  ld_maps B f /\ g.lf_serial = f.lf_serial /\ g.lf_E = f.lf_E /\
  g.lf_supply = f.lf_supply /\ g.lf_fn = f.lf_fn /\
  g.lf_src.vs_allocas = f.lf_src.vs_allocas /\
  g.lf_tgt.vs_allocas = f.lf_tgt.vs_allocas ==>
  ld_maps B g
Proof
  strip_tac >>
  `!x a. ld_private g x a = ld_private f x a` by simp[ld_private_def] >>
  qpat_x_assum `ld_maps B f` mp_tac >> simp[ld_maps_def] >> metis_tac[]
QED

Theorem ld_focus_pop_ghost[local]:
  ld_ghost_ok fl A H G ==>
  ld_ghost_ok fl A (DRESTRICT H keep) (DRESTRICT G keep)
Proof
  rw[ld_ghost_ok_def, FLOOKUP_DRESTRICT] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_focus_local_pop_sync:
  let fl = dyn_floor C vs;
      outs = c.cf_inst.inst_outputs;
      K = COMPL (set outs);
      s1 = sr with vs_inst_idx := SUC c.cf_state.vs_inst_idx;
      t1 = tr with vs_inst_idx := SUC d.cf_state.vs_inst_idx;
      tn1 = tn with t_var := DRESTRICT c.cf_tvar K;
      g = f with <|lf_src := s1; lf_tgt := t1;
                    lf_H := DRESTRICT f.lf_H K; lf_tv := DRESTRICT f.lf_tv K|>
  in
    ld_sync lo P C vs (c::cs) PG G tn fn ri s t A (child::f::fs) N /\
    B = DRESTRICT A (ld_slots A (f::fs)) /\ FDOM B = ld_slots B (g::fs) /\
    EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs) /\
    (!j. j < LENGTH (c::cs) ==>
      let cc = EL j (c::cs); h = EL j (f::fs) in
        cc.cf_fn = h.lf_fn /\ cc.cf_state = h.lf_src /\
        ld_ghost_ok fl B h.lf_H cc.cf_prov /\
        ld_params_ok fl B h.lf_Q cc.cf_params /\ cc.cf_tvar = h.lf_tv) /\
    ALL_DISTINCT (MAP (\h. h.lf_serial) (g::fs)) /\
    EVERY (\h. h.lf_serial < N /\ ld_intervals lo h.lf_src /\ ld_intervals lo h.lf_tgt /\
      h.lf_src.vs_prev_bb = h.lf_tgt.vs_prev_bb /\
      h.lf_src.vs_current_bb = h.lf_tgt.vs_current_bb /\ MEM h.lf_fn C.ctx_functions) (g::fs) /\
    (!j. j < LENGTH (g::fs) ==>
      (EL j (g::fs)).lf_tgt.vs_alloca_next =
      (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))) /\
    ld_charge (g::fs) <= ctx_dload_count C /\
    c.cf_state = f.lf_src /\ d.cf_state = f.lf_tgt /\ c.cf_fn = f.lf_fn /\
    set outs SUBSET set (fn_ir_vars f.lf_fn) /\
    bind_outputs outs vals (merge_callee_state c.cf_state s) = SOME sr /\
    bind_outputs outs vals (merge_callee_state d.cf_state t) = SOME tr /\
    frame_reachable vs C cs c.cf_params (DRESTRICT c.cf_prov K) tn1 c.cf_fn next s1 /\
    active_inst c.cf_fn next s1 /\
    ld_envelope f.lf_supply c.cf_fn s1 s1.vs_inst_idx Y t1.vs_inst_idx /\
    dload_equal_environment s1 t1 /\ c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address ==>
    ld_sync lo P C vs cs c.cf_params (DRESTRICT c.cf_prov K) tn1 c.cf_fn next s1 t1 B (g::fs) N
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `s1 = sr with vs_inst_idx := SUC c.cf_state.vs_inst_idx` >>
  qabbrev_tac `t1 = tr with vs_inst_idx := SUC d.cf_state.vs_inst_idx` >>
  qabbrev_tac `keep = COMPL (set c.cf_inst.inst_outputs)` >>
  qabbrev_tac `tn1 = tn with t_var := DRESTRICT c.cf_tvar keep` >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := t1;
                             lf_H := DRESTRICT f.lf_H keep; lf_tv := DRESTRICT f.lf_tv keep|>` >>
  strip_tac >>
  `ld_maps B f /\ ld_vars P B f /\ EVERY (\h. ld_maps B h /\ ld_vars P B h) fs` by
    fs[] >>
  `ld_vars P B g` by
    ((simp[Abbr `g`, Abbr `s1`, Abbr `t1`, Abbr `keep`] >>
     irule ld_vars_return_restore >> goal_assum (drule_at Any) >> fs[] >> (metis_tac[Abbr `g`, Abbr `s1`, Abbr `t1`, Abbr `keep`, ld_vars_return_restore]))) >>
  `ld_maps B g` by
    (irule ld_focus_pop_maps >> qexists_tac `f` >>
     simp[Abbr `g`, Abbr `s1`, Abbr `t1`] >>
     qpat_assum `bind_outputs _ _ _ = SOME sr`
       (once_rewrite_tac o single o MATCH_MP ld_bind_outputs_vars_only) >>
     qpat_assum `bind_outputs _ _ _ = SOME tr`
       (once_rewrite_tac o single o MATCH_MP ld_bind_outputs_vars_only) >>
     simp[merge_callee_state_def]) >>
  suspend "assemble"
QED

Resume ld_focus_local_pop_sync[assemble]:
  qpat_x_assum `!j. j < LENGTH (c::cs) ==> _ /\ _ /\ ld_ghost_ok _ B _ _ /\ _`
    (mk_asm "saved") >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[ld_sync_def]) >>
  `LENGTH fs = LENGTH cs` by fs[] >>
  `ld_memory lo B tn1 s1 t1 /\ ld_nonghost tn1 s1 t1 /\
   ld_dyn_agree (dyn_floor C vs) tn1.t_mem s1.vs_memory t1.vs_memory` by
    (map_every (fn v => qpat_x_assum v (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]))
       [`Abbrev (tn1 = _)`, `Abbrev (s1 = _)`, `Abbrev (t1 = _)`] >>
     drule_all ld_focus_pop_shared >>
     disch_then (qspec_then `DRESTRICT c.cf_tvar keep` mp_tac) >> simp[]) >>
  qpat_x_assum `B = DRESTRICT A _` kall_tac >>
  asm "saved" (qspec_then `0`
    (strip_assume_tac o REWRITE_RULE[LENGTH, EL, HD, prim_recTheory.LESS_0])) >>
  `g.lf_fn = c.cf_fn /\ g.lf_src = s1 /\ g.lf_tgt = t1 /\
   g.lf_tv = tn1.t_var /\ g.lf_Q = f.lf_Q /\
   g.lf_H = DRESTRICT f.lf_H keep` by simp[Abbr `g`, Abbr `tn1`] >>
  `ld_ghost_ok (dyn_floor C vs) B g.lf_H (DRESTRICT c.cf_prov keep) /\
   ld_params_ok (dyn_floor C vs) B g.lf_Q c.cf_params` by
    simp[ld_focus_pop_ghost] >>
  `ld_envelope g.lf_supply g.lf_fn g.lf_src g.lf_src.vs_inst_idx Y g.lf_tgt.vs_inst_idx` by
    (simp[Abbr `g`] >> metis_tac[]) >>
  `!j. j < LENGTH (g::fs) ==>
    ?X p. ld_envelope (EL j (g::fs)).lf_supply (EL j (g::fs)).lf_fn
      (EL j (g::fs)).lf_src (EL j (g::fs)).lf_src.vs_inst_idx X p /\
      (EL j (g::fs)).lf_tgt.vs_inst_idx = p` by
    (qpat_x_assum `!j. j < LENGTH (child::f::fs) ==> ?X p. _` (mk_asm "old_envelopes") >>
     Cases >> simp[NoAsms]
     >- (qexists_tac `Y` >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >> asm "old_envelopes" (qspec_then `SUC (SUC n)` mp_tac) >> simp[]) >>
  pure_rewrite_tac[ld_sync_def, HD] >>
  rpt conj_tac >> simp[EVERY_CONJ]
  >- fs[EVERY_CONJ] >>
  rpt strip_tac >>
  asm "saved" (qspec_then `SUC j`
    (mp_tac o REWRITE_RULE[LENGTH, EL, TL, prim_recTheory.LESS_MONO_EQ])) >>
  disch_then drule >> strip_tac >> asm_rewrite_tac[]
QED

Finalise ld_focus_local_pop_sync
