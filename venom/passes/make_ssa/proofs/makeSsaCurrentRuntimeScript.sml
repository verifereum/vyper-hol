Theory makeSsaCurrentRuntime
Ancestors
  o1FrameLockstep venomExecSemantics venomState

Definition current_output_slots_def:
  current_output_slots sg outs outs' sg1 <=>
    LENGTH outs = LENGTH outs' /\ ALL_DISTINCT outs /\ ALL_DISTINCT outs' /\
    !n v. FLOOKUP sg1 n = SOME v ==>
      (?k. k < LENGTH outs /\ EL k outs = v /\ EL k outs' = n) \/
      (~MEM v outs /\ ~MEM n outs' /\ FLOOKUP sg n = SOME v)
End

Theorem current_output_slots_out_rename:
  current_output_slots sg outs outs' sg1 ==> out_rename_ok sg outs outs' sg1
Proof
  simp[current_output_slots_def, out_rename_ok_def] >>
  metis_tac[listTheory.EL_MEM]
QED

Theorem current_runtime_fold_lookup_unwritten:
  !pairs st x. ~MEM x (MAP FST pairs) ==>
    lookup_var x (FOLDL (\s (k,v). update_var k v s) st pairs) = lookup_var x st
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem current_runtime_fold_lookup_slot:
  !outs vals st k. ALL_DISTINCT outs /\ LENGTH outs = LENGTH vals /\ k < LENGTH outs ==>
    lookup_var (EL k outs)
      (FOLDL (\s (n,v). update_var n v s) st (ZIP (outs,vals))) = SOME (EL k vals)
Proof
  Induct >> simp[] >> Cases_on `vals` >> simp[] >> rpt strip_tac >>
  Cases_on `k` >> simp[] >- (
    rename1 `lookup_var key (FOLDL _ (update_var key value st) _) = SOME value` >>
    `lookup_var key (FOLDL (\s (n,v). update_var n v s)
       (update_var key value st) (ZIP (outs,t))) =
       lookup_var key (update_var key value st)` by
      (irule current_runtime_fold_lookup_unwritten >> simp[listTheory.MAP_ZIP]) >>
    fs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]) >>
  first_x_assum irule >> simp[]
QED

Theorem current_runtime_fold_frame:
  !pairs st. execution_frame (FOLDL (\s (n,v). update_var n v s) st pairs) =
    execution_frame st /\
    (FOLDL (\s (n,v). update_var n v s) st pairs).vs_current_bb = st.vs_current_bb /\
    (FOLDL (\s (n,v). update_var n v s) st pairs).vs_prev_bb = st.vs_prev_bb
Proof
  Induct >> simp[] >> Cases_on `h` >> rpt gen_tac >>
  first_x_assum (qspec_then `update_var q r st` mp_tac) >>
  simp[venomStateTheory.update_var_def, stateFrameTheory.execution_frame_def]
QED

Theorem current_runtime_bind_lookup_slot:
  ALL_DISTINCT outs /\ bind_outputs outs vals st = SOME t /\ k < LENGTH outs ==>
  lookup_var (EL k outs) t = SOME (EL k vals)
Proof
  simp[bind_outputs_def] >> rpt strip_tac >> gvs[] >>
  irule current_runtime_fold_lookup_slot >> simp[]
QED

Theorem current_runtime_bind_lookup_unwritten:
  bind_outputs outs vals st = SOME t /\ ~MEM x outs ==>
  lookup_var x t = lookup_var x st
Proof
  simp[bind_outputs_def] >> rpt strip_tac >> gvs[] >>
  irule current_runtime_fold_lookup_unwritten >> simp[listTheory.MAP_ZIP]
QED

Theorem current_runtime_bind_slots:
  state_rel sg st st' /\ current_output_slots sg outs outs' sg1 /\
  bind_outputs outs' vals st' = SOME t' ==>
  ?t. bind_outputs outs vals st = SOME t /\ state_rel sg1 t t'
Proof
  simp[bind_outputs_def, current_output_slots_def] >> rpt strip_tac >> gvs[] >>
  simp[] >>
  qpat_x_assum `state_rel sg st st'` mp_tac >>
  pure_rewrite_tac[state_rel_def] >> strip_tac >>
  pure_rewrite_tac[current_runtime_fold_frame] >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[vars_rel_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac
  >- (`lookup_var (EL k outs)
        (FOLDL (\s (n,v). update_var n v s) st (ZIP (outs,vals))) = SOME (EL k vals)` by
        (irule current_runtime_fold_lookup_slot >> simp[]) >>
      `lookup_var (EL k outs')
        (FOLDL (\s (n,v). update_var n v s) st' (ZIP (outs',vals))) = SOME (EL k vals)` by
        (irule current_runtime_fold_lookup_slot >> simp[]) >> metis_tac[]) >>
  `lookup_var x' (FOLDL (\s (n,v). update_var n v s) st' (ZIP (outs',vals))) =
     lookup_var x' st'` by
    (irule current_runtime_fold_lookup_unwritten >> simp[listTheory.MAP_ZIP]) >>
  `lookup_var x (FOLDL (\s (n,v). update_var n v s) st (ZIP (outs,vals))) =
     lookup_var x st` by
    (irule current_runtime_fold_lookup_unwritten >> simp[listTheory.MAP_ZIP]) >>
  fs[vars_rel_def]
QED

Theorem current_runtime_bind_lookup_written:
  ALL_DISTINCT outs /\ bind_outputs outs vals st = SOME t /\ MEM x outs ==>
  IS_SOME (lookup_var x t)
Proof
  rpt strip_tac >>
  `?k. k < LENGTH outs /\ EL k outs = x` by metis_tac[listTheory.MEM_EL] >>
  `lookup_var (EL k outs) t = SOME (EL k vals)` by
    (irule current_runtime_bind_lookup_slot >> simp[] >> metis_tac[]) >>
  gvs[]
QED
