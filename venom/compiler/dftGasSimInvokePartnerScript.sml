Theory dftGasSimInvokePartner
Ancestors
  dftGasSimLocalBoundary dftGasSimInvokeFrame dftGasSimBoundary
  dftRunRel dftCommutation dftBlockSim dftGasOracleDefs
  venomExecSemantics venomState venomInst venomWf venomEffects opcodeClass
  venomInstProofs1 list pair pred_set finite_map
Libs
  stepInstBaseLib

Theorem ev_invoke_partner_updates:
  dft_gas_swap_pair i x /\ inst_wf i /\ inst_wf x /\
  i.inst_opcode = INVOKE /\ x.inst_opcode <> GAS /\
  ev_step orc p d fuel C i s = OK t /\
  ((?r. ev_step orc p d fuel C x s = OK r) \/
   (?r. ev_step orc p d fuel C x t = OK r)) ==>
  ?us. EVERY (\q. MEM (FST q) x.inst_outputs) us /\
    ev_step orc p d fuel C x s =
      OK (FOLDL (\u q. update_var (FST q) (SND q) u) s us) /\
    ev_step orc p d fuel C x t =
      OK (FOLDL (\u q. update_var (FST q) (SND q) u) t us)
Proof
  strip_tac >>
  drule_all dft_swap_invoke_partner_class >> strip_tac >>
  `x.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[opcode_fail_class_def]) >>
  `read_effects x.inst_opcode = empty_effects` by
    (Cases_on `x.inst_opcode` >>
     gvs[dft_gas_swap_pair_def, effects_independent_def,
         read_effects_def, write_effects_def, all_effects_def, empty_effects_def]) >>
  `(!v. ~MEM v i.inst_outputs ==> lookup_var v t = lookup_var v s) /\
   t.vs_prev_bb = s.vs_prev_bb /\ t.vs_params = s.vs_params /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
   t.vs_block_ctx = s.vs_block_ctx /\
   t.vs_data_section = s.vs_data_section /\ t.vs_code = s.vs_code /\
   t.vs_labels = s.vs_labels /\ t.vs_prev_hashes = s.vs_prev_hashes /\
   t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_return_pc_token = s.vs_return_pc_token` by
    (qpat_x_assum `ev_step _ _ _ _ _ i s = OK t` mp_tac >>
     simp[ev_step_def, AllCaseEqs()] >> disch_then strip_assume_tac >>
     gvs[AllCaseEqs()] >>
     conj_tac
     >- (rpt strip_tac >>
         `!us a. EVERY (\q. FST q <> v) us ==>
           lookup_var v (FOLDL (\u q. update_var (FST q) (SND q) u) a us) =
           lookup_var v a` by
           (Induct >- simp[] >> simp[] >> rpt strip_tac >>
            first_x_assum drule >>
            disch_then (qspec_then `update_var (FST h) (SND h) a` mp_tac) >>
            Cases_on `h` >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
         qpat_x_assum `bind_outputs _ _ _ = SOME t` mp_tac >>
         simp[bind_outputs_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
         `EVERY (\q. FST q <> v) (ZIP (i.inst_outputs,ret.iret_values))` by
           (simp[EVERY_MEM] >> rpt strip_tac >>
            drule MEM_ZIP >> strip_tac >> gvs[] >> metis_tac[MEM_EL]) >>
         `(\st (out,value). update_var out value st) =
          (\u q. update_var (FST q) (SND q) u)` by
           (simp[FUN_EQ_THM, pairTheory.FORALL_PROD]) >>
         simp[] >> Cases_on `ret.iret_adopt_fmp` >>
         simp[adopt_return_fmp_def, merge_callee_state_def, lookup_var_def]) >>
     qpat_x_assum `bind_outputs _ _ _ = SOME t` mp_tac >>
     simp[bind_outputs_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
     Cases_on `ret.iret_adopt_fmp` >>
     simp[foldl_update_var_preserves, update_var_def,
          adopt_return_fmp_def, merge_callee_state_def]) >>
  `!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def] >>
     first_x_assum irule >>
     metis_tac[dft_swap_output_frame]) >>
  gvs[ev_step_ordinary, step_inst_non_invoke] >>
  Cases_on `x.inst_opcode` >>
  gvs[dft_gas_swap_pair_def, is_pseudo_def, is_terminator_def,
      is_alloca_op_def, read_effects_def, write_effects_def,
      empty_effects_def, all_effects_def, opcode_fail_class_def] >>
  with_opcode_clause gvs >>
  qpat_x_assum `ev_step _ _ _ _ _ i s = _` kall_tac >>
  qpat_x_assum `inst_wf i` kall_tac >>
  qpat_x_assum `!v. ~MEM v i.inst_outputs ==> _` kall_tac >>
  all_tac >>~- ([`exec_pure2 _ x _ = OK _`],
    qpat_x_assum `exec_pure2 _ _ _ = OK _`
      (strip_assume_tac o SRULE [exec_pure2_def, AllCaseEqs()]) >>
    gvs[] >>
    rename1 `x.inst_operands = [aa;bb]` >>
    `eval_operand aa t = eval_operand aa s /\
     eval_operand bb t = eval_operand bb s` by metis_tac[] >>
    qpat_x_assum `!op. _` kall_tac >>
    qmatch_goalsub_abbrev_tac `update_var out vv _` >>
    qexists_tac `[(out,vv)]` >>
    simp[exec_pure2_def, Abbr `vv`]) >>
  all_tac >>~- ([`exec_pure3 _ x _ = OK _`],
    qpat_x_assum `exec_pure3 _ _ _ = OK _`
      (strip_assume_tac o SRULE [exec_pure3_def, AllCaseEqs()]) >>
    gvs[] >> rename1 `x.inst_operands = [aa;bb;cc]` >>
    `eval_operand aa t = eval_operand aa s /\
     eval_operand bb t = eval_operand bb s /\
     eval_operand cc t = eval_operand cc s` by metis_tac[] >>
    qpat_x_assum `!op. _` kall_tac >>
    qmatch_goalsub_abbrev_tac `update_var out vv _` >>
    qexists_tac `[(out,vv)]` >> simp[exec_pure3_def, Abbr `vv`]) >>
  all_tac >>~- ([`exec_pure1 _ x _ = OK _`],
    qpat_x_assum `exec_pure1 _ _ _ = OK _`
      (strip_assume_tac o SRULE [exec_pure1_def, AllCaseEqs()]) >>
    gvs[] >> rename1 `x.inst_operands = [aa]` >>
    `eval_operand aa t = eval_operand aa s` by metis_tac[] >>
    qmatch_goalsub_abbrev_tac `update_var out vv _` >>
    qexists_tac `[(out,vv)]` >>
    Cases_on `eval_operand aa s` >> gvs[exec_pure1_def, Abbr `vv`]) >>
  all_tac >>~- ([`exec_read0 _ x _ = OK _`],
    qpat_x_assum `exec_read0 _ _ _ = OK _`
      (strip_assume_tac o SRULE [exec_read0_def, AllCaseEqs()]) >>
    gvs[] >> qpat_x_assum `!op. _` kall_tac >>
    qmatch_goalsub_abbrev_tac `update_var out vv _` >>
    qexists_tac `[(out,vv)]` >> simp[exec_read0_def, Abbr `vv`]) >>
  all_tac >>~- ([`exec_read1 _ x _ = OK _`],
    qpat_x_assum `exec_read1 _ _ _ = OK _`
      (strip_assume_tac o SRULE [exec_read1_def, AllCaseEqs()]) >>
    gvs[] >> rename1 `x.inst_operands = [aa]` >>
    `eval_operand aa t = eval_operand aa s` by metis_tac[] >>
    qmatch_goalsub_abbrev_tac `update_var out vv _` >>
    qexists_tac `[(out,vv)]` >>
    Cases_on `eval_operand aa s` >> gvs[exec_read1_def, Abbr `vv`]) >>
  all_tac >>~- ([`x.inst_opcode = ASSIGN`],
    qpat_x_assum `_ = OK r`
      (strip_assume_tac o SRULE [AllCaseEqs()]) >>
    gvs[] >> rename1 `x.inst_operands = [aa]` >>
    `eval_operand aa t = eval_operand aa s` by metis_tac[] >>
    qmatch_goalsub_abbrev_tac `update_var out vv _` >>
    qexists_tac `[(out,vv)]` >>
    Cases_on `eval_operand aa s` >> gvs[Abbr `vv`]) >>
  all_tac >>~- ([`x.inst_opcode = NOP`], qexists_tac `[]` >> simp[]) >>
  qpat_x_assum `_ = OK r` (strip_assume_tac o SRULE [AllCaseEqs()]) >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var next value2 (update_var ptr value1 _)` >>
  qexists_tac `[(ptr,value1);(next,value2)]` >> simp[]
QED
