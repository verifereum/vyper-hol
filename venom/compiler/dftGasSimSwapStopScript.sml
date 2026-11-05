Theory dftGasSimSwapStop
Ancestors
  dftGasSimLocalBoundary dftGasSimInvokeFrame dftGasSimBoundary
  dftRunRel dftCommutation dftBlockSim dftGasOracleDefs dftIndexedExec dftPermSim
  venomExecSemantics venomState venomInst venomWf venomEffects opcodeClass
  list pair pred_set
Libs
  stepInstBaseLib

Theorem ev_invoke_partner_stopping:
  dft_gas_swap_pair i x /\ i.inst_opcode = INVOKE /\
  ev_step orc p d fuel C x s = OK t /\ (!u. r <> OK u) ==>
  (ev_step orc p d fuel C i t = r <=>
   ev_step orc p d fuel C i s = r)
Proof
  strip_tac >>
  drule_all dft_swap_invoke_partner_class >> strip_tac >>
  `x.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[opcode_fail_class_def]) >>
  `read_effects x.inst_opcode = empty_effects` by
    (Cases_on `x.inst_opcode` >>
     gvs[dft_gas_swap_pair_def, effects_independent_def,
         read_effects_def, write_effects_def, all_effects_def, empty_effects_def]) >>
  `?us. EVERY (\q. MEM (FST q) x.inst_outputs) us /\
    t = FOLDL (\u q. update_var (FST q) (SND q) u) s us` by
    (Cases_on `x.inst_opcode = GAS`
     >- (gvs[ev_step_def, ev_gas_def, AllCaseEqs()] >>
         qexists_tac `[(out,orc (p,d,x.inst_id))]` >> simp[]) >>
     gvs[ev_step_ordinary] >>
     Cases_on `x.inst_opcode` >>
     gvs[dft_gas_swap_pair_def, is_pseudo_def, is_terminator_def,
         is_alloca_op_def, read_effects_def, write_effects_def,
         empty_effects_def, all_effects_def] >>
     gvs[step_inst_non_invoke] >> with_opcode_clause gvs >>
     gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
         exec_read0_def, exec_read1_def, AllCaseEqs()] >>
     all_tac
     >>~- ([`EVERY (\q. FST q = out) _`],
       qmatch_goalsub_abbrev_tac `update_var out value s` >>
       qexists_tac `[(out,value)]` >> simp[])
     >>~- ([`x.inst_opcode = BUMP`],
       qexists_tac `[(ptr_out,base_val); (next_out,base_val + sz)]` >> simp[]) >>
     qexists_tac `[]` >> simp[]) >>
  `dft_gas_swap_pair x i` by metis_tac[dft_gas_swap_pair_sym] >>
  `EVERY (\q. ~MEM (Var (FST q)) i.inst_operands /\
              ~MEM (FST q) i.inst_outputs) us` by
    (gvs[EVERY_MEM] >> metis_tac[dft_swap_output_frame]) >>
  gvs[] >> drule_all ev_step_invoke_update_fold >>
  disch_then assume_tac >>
  Cases_on `ev_step orc p d fuel C i s` >> simp[] >> metis_tac[]
QED

Theorem ev_invoke_partner_no_abort:
  dft_gas_swap_pair i x /\ i.inst_opcode = INVOKE ==>
  ev_step orc p d fuel C x s <> Abort a t
Proof
  strip_tac >> drule_all dft_swap_invoke_partner_class >> strip_tac >>
  `x.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[opcode_fail_class_def]) >>
  Cases_on `x.inst_opcode = GAS`
  >- simp[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  simp[ev_step_ordinary, step_inst_non_invoke] >> strip_tac >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[opcode_fail_class_def, write_effects_def, empty_effects_def, all_effects_def,
      dft_gas_swap_pair_def, is_terminator_def]
QED

Theorem ev_pair_abort_iff:
  dft_gas_swap_pair x y /\ ev_step orc p d fuel C x s = OK t ==>
  ((?u. ev_step orc p d fuel C y t = Abort a u) <=>
   (?u. ev_step orc p d fuel C y s = Abort a u))
Proof
  strip_tac >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  Cases_on `y.inst_opcode = INVOKE`
  >- metis_tac[ev_invoke_partner_stopping, exec_result_distinct] >>
  Cases_on `x.inst_opcode = INVOKE`
  >- metis_tac[ev_invoke_partner_no_abort] >>
  Cases_on `y.inst_opcode = GAS`
  >- simp[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  Cases_on `x.inst_opcode = GAS`
  >- (qpat_x_assum `ev_step _ _ _ _ _ x s = _`
        (strip_assume_tac o SRULE [ev_step_def, ev_gas_def, AllCaseEqs()]) >> gvs[] >>
      drule_all dft_independent_gas_output >> strip_tac >>
      simp[ev_step_ordinary] >>
      drule_all step_inst_frame >>
      disch_then (qspecl_then [`fuel`, `C`, `s`, `orc (p,d,x.inst_id)`] mp_tac) >>
      Cases_on `step_inst fuel C y s` >> simp[map_result_state_def] >> metis_tac[]) >>
  gvs[ev_step_ordinary] >> irule dft_nongas_pair_abort_iff >>
  simp[gas_pair_def] >> metis_tac[]
QED

Theorem ev_suffix_second_abort:
  dft_gas_swap_pair x y /\ ev_step orc p d fuel C x s = OK sx /\
  ev_step orc p d fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  ev_suffix orc p d fuel C (x::y::tail) s = Abort a t /\
  ?u. ev_suffix orc p d fuel C (y::x::tail) s = Abort a u
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `?u. ev_step orc p d fuel C y sx = Abort a u` by
    metis_tac[ev_step_nonterminator_abort_idx_iff] >>
  `?u. ev_step orc p d fuel C y s = Abort a u` by
    metis_tac[ev_pair_abort_iff] >>
  simp[ev_suffix_def]
QED

Theorem ev_suffix_first_abort:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~s.vs_call_ctx.cc_static /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  ev_step orc p d fuel C x s = Abort a t ==>
  ev_suffix orc p d fuel C (x::y::tail) s = Abort a t /\
  ?u. ev_suffix orc p d fuel C (y::x::tail) s = Abort a u
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  simp[ev_suffix_def] >>
  Cases_on `x.inst_opcode = GAS`
  >- gvs[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  Cases_on `y.inst_opcode = GAS`
  >- (`?sy. ev_step orc p d fuel C y s = OK sy` by
        (drule_all ev_step_gas_shape >> metis_tac[]) >>
      `?u. ev_step orc p d fuel C x sy = Abort a u` by
        metis_tac[ev_pair_abort_iff] >>
      `?u. ev_step orc p d fuel C x
             (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort a u` by
        metis_tac[ev_step_nonterminator_abort_idx_iff] >>
      simp[ev_suffix_def]) >>
  Cases_on `y.inst_opcode = INVOKE`
  >- metis_tac[ev_invoke_partner_no_abort] >>
  Cases_on `x.inst_opcode = INVOKE`
  >- (drule_all dft_swap_invoke_partner_class >> strip_tac >>
      `y.inst_opcode <> CODECOPY` by
        (strip_tac >> gvs[write_effects_def, empty_effects_def]) >>
      `~is_pseudo y.inst_opcode /\ y.inst_opcode <> ALLOCA` by
        (gvs[dft_gas_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
      `?sy. step_inst fuel C y s = OK sy` by
        metis_tac[dft_swap_guarded_nofail_total] >>
      `ev_step orc p d fuel C y s = OK sy` by simp[ev_step_ordinary] >>
      `?u. ev_step orc p d fuel C x sy = Abort a u` by
        metis_tac[ev_pair_abort_iff] >>
      `?u. ev_step orc p d fuel C x
             (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort a u` by
        metis_tac[ev_step_nonterminator_abort_idx_iff] >>
      simp[ev_suffix_def]) >>
  `~gas_pair x.inst_opcode y.inst_opcode` by simp[gas_pair_def] >>
  gvs[ev_step_ordinary] >>
  drule_at (Pat `step_inst _ _ _ _ = Abort _ _`) dft_nongas_suffix_first_abort >>
  simp[] >>
  disch_then (qspecl_then [`y`, `[]`] mp_tac) >> simp[] >>
  Cases_on `step_inst fuel C y s` >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def] >>
  Cases_on `step_inst fuel C x (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
  simp[dft_exec_suffix_def]
QED

Theorem ev_suffix_swap_halt:
  dft_gas_swap_pair x y /\ inst_wf y /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  (ev_step orc p d fuel C x s = Halt t \/
   (?sx. ev_step orc p d fuel C x s = OK sx /\
     ev_step orc p d fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Halt t)) ==>
  ev_suffix orc p d fuel C (x::y::tail) s = Halt t /\
  ev_suffix orc p d fuel C (y::x::tail) s = Halt t
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo y.inst_opcode /\ y.inst_opcode <> ALLOCA` by
    (gvs[dft_gas_swap_pair_def] >> metis_tac[is_alloca_op_def])
  >- (`x.inst_opcode = INVOKE` by metis_tac[ev_step_nonterminator_halt_invoke] >>
      drule_all dft_swap_invoke_partner_class >> strip_tac >>
      `y.inst_opcode <> INVOKE` by (strip_tac >> gvs[opcode_fail_class_def]) >>
      `y.inst_opcode <> CODECOPY` by
        (strip_tac >> gvs[write_effects_def, empty_effects_def]) >>
      `?sy. ev_step orc p d fuel C y s = OK sy` by
        (Cases_on `y.inst_opcode = GAS`
         >- (drule_all ev_step_gas_shape >> metis_tac[]) >>
         simp[ev_step_ordinary] >> metis_tac[dft_swap_guarded_nofail_total]) >>
      `ev_step orc p d fuel C x sy = Halt t` by
        metis_tac[ev_invoke_partner_stopping, exec_result_distinct] >>
      `ev_step orc p d fuel C x
         (sy with vs_inst_idx := SUC s.vs_inst_idx) = Halt t` by
        metis_tac[ev_step_invoke_inst_idx_non_ok, exec_result_distinct] >>
      simp[ev_suffix_def]) >>
  `y.inst_opcode = INVOKE` by metis_tac[ev_step_nonterminator_halt_invoke] >>
  `ev_step orc p d fuel C y sx = Halt t` by
    (qpat_x_assum `ev_step _ _ _ _ _ y (_ with vs_inst_idx := _) = _` mp_tac >>
     simp[ev_step_invoke_inst_idx] >>
     Cases_on `ev_step orc p d fuel C y sx` >> simp[]) >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  `ev_step orc p d fuel C y s = Halt t` by
    metis_tac[ev_invoke_partner_stopping, exec_result_distinct] >>
  simp[ev_suffix_def]
QED
