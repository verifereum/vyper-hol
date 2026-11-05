Theory dftGasSimSwapSuccess
Ancestors
  dftGasSimLocalBoundary dftGasSimInvokeFrame dftGasSimBoundary
  dftGasSimInvokePartner
  dftRunRel dftBlockSim dftCommutation dftGasOracleDefs
  venomExecSemantics venomState venomInst venomWf venomEffects list pair

Theorem ev_step_independent_update_ok_iff:
  inst_wf i /\
  (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
  ~MEM out i.inst_outputs ==>
  (ev_step orc p d fuel C i (update_var out value s) = OK u <=>
   ?t. ev_step orc p d fuel C i s = OK t /\
       u = update_var out value t)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (drule_all ev_step_invoke_update_var >>
      Cases_on `ev_step orc p d fuel C i s` >> simp[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = GAS`
  >- (`?gout. i.inst_outputs = [gout]` by metis_tac[ev_step_gas_shape] >>
      `!st. ev_step orc p d fuel C i st =
        OK (update_var gout (orc (p,d,i.inst_id)) st)` by
        (gen_tac >> drule_all ev_step_gas_shape >> simp[] >> metis_tac[]) >>
      gvs[] >> simp[update_var_commutes, EQ_SYM_EQ]) >>
  simp[ev_step_ordinary] >>
  drule_all step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `value`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[map_result_state_def] >> metis_tac[]
QED

Theorem ev_gas_pair_success_iff:
  dft_gas_swap_pair g i /\ g.inst_opcode = GAS /\
  inst_wf g /\ inst_wf i ==>
  ((?sg. ev_step orc p d fuel C g s = OK sg /\
         ev_step orc p d fuel C i sg = OK t) <=>
   (?si. ev_step orc p d fuel C i s = OK si /\
         ev_step orc p d fuel C g si = OK t))
Proof
  strip_tac >>
  `?gout. g.inst_outputs = [gout]` by metis_tac[ev_step_gas_shape] >>
  `!st. ev_step orc p d fuel C g st =
    OK (update_var gout (orc (p,d,g.inst_id)) st)` by
    (gen_tac >> drule_all ev_step_gas_shape >> simp[] >> metis_tac[]) >>
  drule_all dft_independent_gas_output >> strip_tac >>
  simp[] >> drule_all ev_step_independent_update_ok_iff >>
  simp[] >> metis_tac[]
QED

Theorem ev_pair_success:
  dft_gas_swap_pair a b /\ inst_wf a /\ inst_wf b /\
  ev_step orc p d fuel C a s = OK sa /\
  ev_step orc p d fuel C b sa = OK sab ==>
  ?sb. ev_step orc p d fuel C b s = OK sb /\
       ev_step orc p d fuel C a sb = OK sab
Proof
  strip_tac >>
  `dft_gas_swap_pair b a` by metis_tac[dft_gas_swap_pair_sym] >>
  Cases_on `a.inst_opcode = GAS`
  >- (drule_all ev_gas_pair_success_iff >> metis_tac[]) >>
  Cases_on `b.inst_opcode = GAS`
  >- (drule_all ev_gas_pair_success_iff >> metis_tac[]) >>
  Cases_on `a.inst_opcode = INVOKE`
  >- (`?us. EVERY (\q. MEM (FST q) b.inst_outputs) us /\
         ev_step orc p d fuel C b s =
           OK (FOLDL (\u q. update_var (FST q) (SND q) u) s us) /\
         ev_step orc p d fuel C b sa =
           OK (FOLDL (\u q. update_var (FST q) (SND q) u) sa us)` by
        (irule ev_invoke_partner_updates >> metis_tac[]) >>
      `EVERY (\q. ~MEM (Var (FST q)) a.inst_operands /\
                  ~MEM (FST q) a.inst_outputs) us` by
        (gvs[listTheory.EVERY_MEM] >> metis_tac[dft_swap_output_frame]) >>
      qexists_tac `FOLDL (\u q. update_var (FST q) (SND q) u) s us` >>
      simp[] >> drule_all ev_step_invoke_update_fold >> gvs[]) >>
  Cases_on `b.inst_opcode = INVOKE`
  >- (`?us. EVERY (\q. MEM (FST q) a.inst_outputs) us /\
         sa = FOLDL (\u q. update_var (FST q) (SND q) u) s us` by
        (`write_effects a.inst_opcode = empty_effects /\
          read_effects a.inst_opcode = empty_effects` by
           (Cases_on `a.inst_opcode` >>
            gvs[dft_gas_swap_pair_def, effects_independent_def,
                venomEffectsTheory.read_effects_def,
                venomEffectsTheory.write_effects_def,
                venomEffectsTheory.all_effects_def,
                venomEffectsTheory.empty_effects_def]) >>
         `~is_terminator a.inst_opcode /\ ~is_alloca_op a.inst_opcode /\
          ~is_ext_call_op a.inst_opcode` by
           (Cases_on `a.inst_opcode` >>
            gvs[dft_gas_swap_pair_def, venomEffectsTheory.write_effects_def,
                venomEffectsTheory.all_effects_def,
                venomEffectsTheory.empty_effects_def,
                is_terminator_def, is_alloca_op_def, is_ext_call_op_def]) >>
         `step_inst_base a s = OK sa` by
           gvs[ev_step_ordinary, step_inst_non_invoke] >>
         fs[empty_effects_def] >> drule_all pure_step_structure >> strip_tac >>
         qexists_tac `pairs` >>
         `(\st (out,value). update_var out value st) =
           (\u q. update_var (FST q) (SND q) u)` by
           simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
         gvs[EVERY_MEM] >> metis_tac[listTheory.MEM_MAP]) >>
      `EVERY (\q. ~MEM (Var (FST q)) b.inst_operands /\
                  ~MEM (FST q) b.inst_outputs) us` by
        (gvs[listTheory.EVERY_MEM] >> metis_tac[dft_swap_output_frame]) >>
      drule_all ev_step_invoke_update_fold >>
      disch_then (qspecl_then [`p`, `orc`, `fuel`, `d`, `C`, `s`] mp_tac) >>
      Cases_on `ev_step orc p d fuel C b s` >> gvs[] >>
      strip_tac >> rename1 `ev_step orc p d fuel C b s = OK sb` >>
      `?vs. EVERY (\q. MEM (FST q) a.inst_outputs) vs /\
         ev_step orc p d fuel C a s =
           OK (FOLDL (\u q. update_var (FST q) (SND q) u) s vs) /\
         ev_step orc p d fuel C a sb =
           OK (FOLDL (\u q. update_var (FST q) (SND q) u) sb vs)` by
        (irule ev_invoke_partner_updates >> metis_tac[]) >>
      `EVERY (\q. ~MEM (Var (FST q)) b.inst_operands /\
                  ~MEM (FST q) b.inst_outputs) vs` by
        (gvs[listTheory.EVERY_MEM] >> metis_tac[dft_swap_output_frame]) >>
      drule_all ev_step_invoke_update_fold >>
      disch_then (qspecl_then [`p`, `orc`, `fuel`, `d`, `C`, `s`] mp_tac) >>
      gvs[]) >>
  gvs[ev_step_ordinary] >>
  irule dft_nongas_pair_success >> simp[gas_pair_def] >> metis_tac[]
QED
