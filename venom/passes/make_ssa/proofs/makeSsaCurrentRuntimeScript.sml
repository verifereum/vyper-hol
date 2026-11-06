Theory makeSsaCurrentRuntime
Ancestors
  o1FrameLockstep venomExecSemantics venomState venomWf simplifyCfgPhiSemantics tailMergeStep
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
      (irule scfg_snapshot_lookup >> simp[listTheory.MAP_ZIP]) >>
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
    (irule scfg_snapshot_lookup >> simp[listTheory.MAP_ZIP]) >>
  `lookup_var x (FOLDL (\s (n,v). update_var n v s) st (ZIP (outs,vals))) =
     lookup_var x st` by
    (irule scfg_snapshot_lookup >> simp[listTheory.MAP_ZIP]) >>
  fs[vars_rel_def]
QED

Theorem current_runtime_bind_lookup_written:
  ALL_DISTINCT outs /\ bind_outputs outs vals st = SOME t /\ MEM x outs ==>
  IS_SOME (lookup_var x t)
Proof
  rpt strip_tac >>
  `?k. k < LENGTH outs /\ EL k outs = x` by metis_tac[listTheory.MEM_EL] >>
  `lookup_var (EL k outs) t = SOME (EL k vals)` by
    (irule bind_outputs_lookup_position >> simp[] >> metis_tac[]) >>
  gvs[]
QED

(* The source IR contract allows repeated INVOKE destinations. *)
Theorem current_runtime_invoke_duplicate_outputs_probe:
  inst_wf (inst with <| inst_opcode := INVOKE;
    inst_operands := [Label "callee"]; inst_outputs := ["x"; "x"] |>) /\
  ~current_output_slots sg ["x"; "x"] outs' sg1
Proof
  simp[venomWfTheory.inst_wf_def, current_output_slots_def]
QED

Definition current_last_output_slots_def:
  current_last_output_slots sg outs outs' sg1 <=>
    LENGTH outs = LENGTH outs' /\ ALL_DISTINCT outs' /\
    !n v. FLOOKUP sg1 n = SOME v ==>
      (?k. k < LENGTH outs /\ EL k outs = v /\ EL k outs' = n /\
        ~MEM v (DROP (SUC k) outs)) \/
      (~MEM v outs /\ ~MEM n outs' /\ FLOOKUP sg n = SOME v)
End

Theorem current_last_output_slots_out_rename:
  current_last_output_slots sg outs outs' sg1 ==> out_rename_ok sg outs outs' sg1
Proof
  simp[current_last_output_slots_def, out_rename_ok_def] >>
  metis_tac[listTheory.EL_MEM]
QED

Theorem current_runtime_fold_lookup_last:
  !outs vals st k. LENGTH outs = LENGTH vals /\ k < LENGTH outs /\
    ~MEM (EL k outs) (DROP (SUC k) outs) ==>
    lookup_var (EL k outs)
      (FOLDL (\s (n,v). update_var n v s) st (ZIP (outs,vals))) = SOME (EL k vals)
Proof
  Induct >> simp[] >> Cases_on `vals` >> simp[] >> rpt strip_tac >>
  Cases_on `k` >> gvs[]
  >- (rename1 `lookup_var key (FOLDL _ (update_var key value st) _) = SOME value` >>
      `lookup_var key (FOLDL (\s (n,v). update_var n v s)
         (update_var key value st) (ZIP (outs,t))) =
       lookup_var key (update_var key value st)` by
        (irule scfg_snapshot_lookup >> simp[listTheory.MAP_ZIP]) >>
      fs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE]) >>
  first_x_assum irule >> simp[]
QED

Theorem current_runtime_bind_last_slots:
  state_rel sg st st' /\ current_last_output_slots sg outs outs' sg1 /\
  bind_outputs outs' vals st' = SOME t' ==>
  ?t. bind_outputs outs vals st = SOME t /\ state_rel sg1 t t'
Proof
  simp[bind_outputs_def, current_last_output_slots_def] >> rpt strip_tac >> gvs[] >>
  simp[] >>
  qpat_x_assum `state_rel sg st st'` mp_tac >>
  pure_rewrite_tac[state_rel_def] >> strip_tac >>
  pure_rewrite_tac[current_runtime_fold_frame] >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[vars_rel_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac
  >- (`lookup_var (EL k outs)
        (FOLDL (\s (n,v). update_var n v s) st (ZIP (outs,vals))) = SOME (EL k vals)` by
        (irule current_runtime_fold_lookup_last >> simp[]) >>
      `lookup_var (EL k outs')
        (FOLDL (\s (n,v). update_var n v s) st' (ZIP (outs',vals))) = SOME (EL k vals)` by
        (irule current_runtime_fold_lookup_slot >> simp[]) >> metis_tac[]) >>
  `lookup_var x' (FOLDL (\s (n,v). update_var n v s) st' (ZIP (outs',vals))) =
     lookup_var x' st'` by
    (irule scfg_snapshot_lookup >> simp[listTheory.MAP_ZIP]) >>
  `lookup_var x (FOLDL (\s (n,v). update_var n v s) st (ZIP (outs,vals))) =
     lookup_var x st` by
    (irule scfg_snapshot_lookup >> simp[listTheory.MAP_ZIP]) >>
  fs[vars_rel_def]
QED

Theorem current_runtime_bind_lookup_last:
  bind_outputs outs vals st = SOME t /\ k < LENGTH outs /\
    ~MEM (EL k outs) (DROP (SUC k) outs) ==>
  lookup_var (EL k outs) t = SOME (EL k vals)
Proof
  simp[bind_outputs_def] >> rpt strip_tac >> gvs[] >>
  irule current_runtime_fold_lookup_last >> simp[]
QED

Theorem current_runtime_last_position:
  !outs x. MEM x outs ==>
    ?k. k < LENGTH outs /\ EL k outs = x /\ ~MEM x (DROP (SUC k) outs)
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `MEM x outs`
  >- (disch_tac >> first_x_assum drule >> strip_tac >>
      qexists_tac `SUC k` >> simp[]) >>
  simp[] >> strip_tac >> gvs[] >> qexists_tac `0` >> simp[]
QED

Theorem current_runtime_bind_lookup_written_general:
  bind_outputs outs vals st = SOME t /\ MEM x outs ==>
  IS_SOME (lookup_var x t)
Proof
  rpt strip_tac >> drule current_runtime_last_position >> strip_tac >>
  `lookup_var (EL k outs) t = SOME (EL k vals)` by
    (irule current_runtime_bind_lookup_last >> metis_tac[]) >>
  gvs[]
QED

Theorem current_runtime_last_duplicate_probe:
  !st. ?post. bind_outputs ["x"; "x"] [1w; 2w] st = SOME post /\
    lookup_var "x" post = SOME 2w
Proof
  simp[bind_outputs_def, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
