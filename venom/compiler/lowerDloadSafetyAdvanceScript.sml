(* Conditional sequential reconstruction: effect and next-location premises explicit. *)
Theory lowerDloadSafetyAdvance
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline finite_map pred_set list arithmetic

Theorem ld_sync_head_update:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  g = f with <|lf_src := s'; lf_tgt := t'; lf_H := H'; lf_tv := tn'.t_var|> /\
  frame_reachable vs0 C stk PG G' tn' fn next s' /\ active_inst fn next s' /\
  G' = ld_erase A o_f H' /\ ld_vars P A g /\
  ld_memory lo A tn' s' t' /\ ld_nonghost tn' s' t' /\
  s'.vs_current_bb = t'.vs_current_bb /\ s'.vs_prev_bb = t'.vs_prev_bb /\
  s'.vs_allocas = s.vs_allocas /\ t'.vs_allocas = t.vs_allocas /\
  s'.vs_alloca_next = s.vs_alloca_next /\ t'.vs_alloca_next = t.vs_alloca_next /\
  (?X. ld_envelope f.lf_supply fn s' s'.vs_inst_idx X t'.vs_inst_idx) /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) ==>
  ld_sync lo P C vs0 stk PG G' tn' fn next s' t' A (g::fs) N /\
  ld_global lo A (g::fs)
Proof
  strip_tac >>
  `f.lf_src = s /\ f.lf_tgt = t` by
    (drule ld_sync_active >> simp[]) >>
  `ld_maps A g = ld_maps A f` by
    (simp[ld_maps_def, ld_private_def] >> gvs[]) >>
  `ld_slots A (g::fs) = ld_slots A (f::fs)` by
    (irule ld_slots_head_cong >> gvs[]) >>
  `!source. ld_sites (g::fs) source = ld_sites (f::fs) source` by
    (gen_tac >> simp[ld_sites_def, EXTENSION] >>
     qx_gen_tac `x` >> PairCases_on `x` >> simp[] >>
     Cases_on `x0` >> gvs[]) >>
  `!xs. ld_charge (g::xs) = ld_charge (f::xs)` by simp[ld_charge_def] >>
  reverse conj_tac
  >- (qpat_x_assum `ld_global lo A (f::fs)` mp_tac >>
      simp[ld_global_def] >> strip_tac >>
      conj_tac >- (gvs[] >> metis_tac[]) >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N` mp_tac >>
  simp[ld_sync_def] >> strip_tac >> simp[] >>
  conj_tac >- (gvs[ld_intervals_def] >> metis_tac[]) >>
  conj_tac >- (gen_tac >> Cases_on `j`
    >- (qpat_x_assum `!j. _ ==> (EL j (f::fs)).lf_tgt.vs_alloca_next = _`
          (qspec_then `0` mp_tac) >> gvs[ld_charge_def]) >>
    qpat_x_assum `!j. _ ==> (EL j (f::fs)).lf_tgt.vs_alloca_next = _`
      (qspec_then `SUC n` mp_tac) >> gvs[]) >>
  gen_tac >> Cases_on `j`
  >- (simp[] >> metis_tac[]) >>
  qpat_x_assum `!j. _ ==> ?X. ld_envelope _ _ _ _ X _`
    (qspec_then `SUC n` mp_tac) >> gvs[]
QED

Theorem ld_sync_ordinary_advance:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  f.lf_src = s /\ f.lf_tgt = t /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\
  step_inst fuel C' inst t = OK ts /\
  step_inst fuel C inst s = OK ss /\
  tn' = step_taint inst s ss tn /\
  G' = step_prov PG G inst ss /\
  f' = f with <| lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                 lf_tgt := ts with vs_inst_idx := SUC p;
                 lf_H := H'; lf_tv := tn'.t_var |> /\
  G' = ld_erase A o_f H' /\ ld_vars P A f' /\
  ld_memory lo A tn' ss ts /\ ld_nonghost tn' ss ts /\
  active_inst fn next (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
  (?Y. ld_envelope f.lf_supply fn
         (ss with vs_inst_idx := SUC s.vs_inst_idx)
         (SUC s.vs_inst_idx) Y (SUC p)) /\
  ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
  ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) ==>
  ld_sync lo P C vs0 stk PG G' tn' fn next
    (ss with vs_inst_idx := SUC s.vs_inst_idx)
    (ts with vs_inst_idx := SUC p) A (f'::fs) N /\
  ld_global lo A (f'::fs)
Proof
  strip_tac >>
  `frame_reachable vs0 C stk PG G' tn' fn next
    (ss with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gvs[] >> irule frame_reachable_next >>
     drule ld_sync_source >> metis_tac[]) >>
  irule ld_sync_head_update >>
  drule ld_sync_control >> strip_tac >>
  simp[] >>
  gvs[ld_memory_def, ld_nonghost_def] >> metis_tac[]
QED

Theorem ld_vars_inst_indices:
  ld_vars P A (f with <|lf_src := f.lf_src with vs_inst_idx := i;
                       lf_tgt := f.lf_tgt with vs_inst_idx := j|>) <=>
  ld_vars P A f
Proof
  simp[ld_vars_def]
QED
