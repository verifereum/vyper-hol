Theory dftPacketEntryReplay
Ancestors
  dftIndexedExec dftGasToListReplay gasOracleReplay venomExecSemantics
  venomInst venomState stateEquiv list rich_list

Theorem dft_packet_pseudo_fold_gas:
  !zs s t.
    EVERY (\i. is_pseudo i.inst_opcode) zs /\
    FOLDR (dft_exec_cons f C) OK zs s = OK t ==>
    FOLDR (dft_exec_cons g D) OK zs (s with vs_gas_readings := gs) =
      OK (t with vs_gas_readings := gs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> GAS /\
   ~is_terminator h.inst_opcode` by
    (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
  gvs[FOLDR, dft_exec_cons_def, step_inst_non_invoke] >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst_base h (s with vs_gas_readings := gs) =
     OK (u with vs_gas_readings := gs)` by
    (drule gas_base_non_gas >>
     disch_then (qspec_then `s` mp_tac) >>
     simp[gas_replay_at_def, gas_prefix_def] >>
     disch_then (qspec_then `gs` mp_tac) >>
     Cases_on `step_inst_base h (s with vs_gas_readings := gs)` >>
     simp[lift_result_def]) >>
  simp[] >>
  first_x_assum drule >>
  simp[venom_state_component_equality]
QED

Theorem dft_packet_body_entry_replay:
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis entry (ps ++ ys) = OK sp /\
  FOLDR (dft_exec_cons f C) OK
    (DROP (phi_prefix_length (ps ++ ys)) ps)
    (sp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be ==>
  ?sp'. eval_phis (entry with vs_gas_readings := gs) (ps ++ xs) = OK sp' /\
    FOLDR (dft_exec_cons g D) OK
      (DROP (phi_prefix_length (ps ++ xs)) ps)
      (sp' with vs_inst_idx := phi_prefix_length (ps ++ xs)) =
        OK (be with vs_gas_readings := gs)
Proof
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  gvs[dft_phi_prefix_append, dft_eval_phis_append] >>
  qspec_then `ps` (qspec_then `entry` (qspec_then `gs` mp_tac)) replay_phis >>
  simp[] >> strip_tac >>
  qpat_x_assum `FOLDR _ _ _ _ = OK be`
    (mp_then Any mp_tac dft_packet_pseudo_fold_gas) >>
  simp[EVERY_DROP]
QED
