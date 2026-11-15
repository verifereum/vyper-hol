Theory dftGasSimSwap
Ancestors
  dftGasSimSwapSuccess dftGasSimSwapStop dftGasSimLocalBoundary
  dftGasSimBoundary dftRunRel dftGasOracleDefs venomState venomInst
  venomExecSemantics venomEffects list

Theorem ev_indexed_pair_success:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ev_step orc p d fuel C x s = OK sx /\
  ev_step orc p d fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
  ?sy sxy. ev_step orc p d fuel C y s = OK sy /\
    ev_step orc p d fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
    (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (syx with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `ev_step orc p d fuel C y sx =
    OK (syx with vs_inst_idx := sx.vs_inst_idx)` by
    (qpat_assum `ev_step _ _ _ _ _ y (_ with vs_inst_idx := _) = _`
       (mp_then Any mp_tac ev_step_nonterminator_ok_idx) >> simp[] >>
     disch_then (qspec_then `sx.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all ev_pair_success >> strip_tac >>
  rename1 `ev_step orc p d fuel C x sb = OK (_ with vs_inst_idx := _)` >>
  qpat_assum `ev_step _ _ _ _ _ x sb = _`
    (mp_then Any mp_tac ev_step_nonterminator_ok_idx) >>
  simp[] >> disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ev_suffix_pair_success:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ev_step orc p d fuel C x s = OK sx /\
  ev_step orc p d fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
  ev_suffix orc p d fuel C (x::y::tail) s =
  ev_suffix orc p d fuel C (y::x::tail) s
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  drule_all ev_indexed_pair_success >> strip_tac >> simp[ev_suffix_def]
QED

Theorem ev_suffix_swap_success_back:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  (ev_suffix orc p d fuel C (y::x::tail) s = OK t \/
   ev_suffix orc p d fuel C (y::x::tail) s = IntRet vals t) ==>
  ev_suffix orc p d fuel C (x::y::tail) s =
  ev_suffix orc p d fuel C (y::x::tail) s
Proof
  strip_tac >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  Cases_on `ev_step orc p d fuel C y s` >>
  gvs[ev_suffix_def] >>
  imp_res_tac ev_step_nonterminator_no_intret >>
  rename1 `ev_step orc p d fuel C y s = OK sy` >>
  Cases_on `ev_step orc p d fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx)` >>
  gvs[ev_suffix_def] >>
  imp_res_tac ev_step_nonterminator_no_intret >>
  drule_all ev_indexed_pair_success >> strip_tac >> simp[]
QED

Theorem ev_suffix_swap:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~s.vs_call_ctx.cc_static /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  dft_res_rel (ev_suffix orc p d fuel C (x::y::tail) s)
              (ev_suffix orc p d fuel C (y::x::tail) s)
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  Cases_on `ev_step orc p d fuel C x s`
  >- (rename1 `ev_step orc p d fuel C x s = OK sx` >>
      Cases_on `ev_step orc p d fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx)`
      >- (drule_all ev_suffix_pair_success >>
          disch_then (qspec_then `tail` assume_tac) >> simp[] >>
          Cases_on `ev_suffix orc p d fuel C (y::x::tail) s` >>
          simp[dft_res_rel_def])
      >- (`ev_suffix orc p d fuel C (x::y::tail) s = Halt v /\
          ev_suffix orc p d fuel C (y::x::tail) s = Halt v` by
           (irule ev_suffix_swap_halt >> simp[] >> metis_tac[]) >>
         simp[dft_res_rel_def])
      >- (drule_all ev_suffix_second_abort >> strip_tac >>
          simp[dft_res_rel_def] >> metis_tac[])
      >- metis_tac[ev_step_nonterminator_no_intret] >>
      rename1 `ev_step orc p d fuel C y _ = Error err` >>
      `ev_suffix orc p d fuel C (x::y::tail) s = Error err` by
        simp[ev_suffix_def] >>
      simp[Once dft_res_rel_def] >>
      metis_tac[ev_suffix_swap_success_back, exec_result_distinct])
  >- (`ev_suffix orc p d fuel C (x::y::tail) s = Halt v /\
          ev_suffix orc p d fuel C (y::x::tail) s = Halt v` by
           (irule ev_suffix_swap_halt >> simp[] >> metis_tac[]) >>
         simp[dft_res_rel_def])
  >- (drule_all ev_suffix_first_abort >> strip_tac >>
      simp[dft_res_rel_def] >> metis_tac[])
  >- metis_tac[ev_step_nonterminator_no_intret] >>
  rename1 `ev_step orc p d fuel C x s = Error err` >>
  `ev_suffix orc p d fuel C (x::y::tail) s = Error err` by
    simp[ev_suffix_def] >>
  simp[Once dft_res_rel_def] >>
  metis_tac[ev_suffix_swap_success_back, exec_result_distinct]
QED

Theorem ev_suffix_swap_revert_empty:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~s.vs_call_ctx.cc_static /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  ev_suffix orc p d fuel C (x::y::tail) s = Abort Revert_abort t /\
  t.vs_returndata = [] ==>
  ?u. ev_suffix orc p d fuel C (y::x::tail) s = Abort Revert_abort u /\
      u.vs_returndata = []
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  Cases_on `ev_step orc p d fuel C x s`
  >- (rename1 `ev_step orc p d fuel C x s = OK sx` >>
      Cases_on `ev_step orc p d fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx)`
      >- (drule_all ev_suffix_pair_success >>
          disch_then (qspec_then `tail` assume_tac) >> metis_tac[])
      >- gvs[ev_suffix_def]
      >- (gvs[ev_suffix_def] >>
          drule_all ev_suffix_second_abort >> strip_tac >>
          Cases_on `y.inst_opcode = INVOKE`
          >- (`ev_step orc p d fuel C y sx = Abort Revert_abort t` by
                (qpat_x_assum `ev_step _ _ _ _ _ y (_ with vs_inst_idx := _) = _` mp_tac >>
                 simp[dftGasSimInvokeFrameTheory.ev_step_invoke_inst_idx] >>
                 Cases_on `ev_step orc p d fuel C y sx` >> simp[]) >>
              `ev_step orc p d fuel C y s = Abort Revert_abort t` by
                metis_tac[ev_invoke_partner_stopping, exec_result_distinct] >>
              simp[]) >>
          `?u. ev_step orc p d fuel C y sx = Abort Revert_abort u` by
            metis_tac[ev_step_nonterminator_abort_idx_iff] >>
          `?u. ev_step orc p d fuel C y s = Abort Revert_abort u` by
            metis_tac[ev_pair_abort_iff] >>
          simp[] >> metis_tac[ev_step_noninvoke_abort_empty])
      >- metis_tac[ev_step_nonterminator_no_intret] >>
      gvs[ev_suffix_def])
  >- gvs[ev_suffix_def]
  >- (drule_all ev_suffix_first_abort >>
      disch_then (qspec_then `tail` strip_assume_tac) >>
      gvs[ev_suffix_def] >>
      Cases_on `x.inst_opcode = INVOKE`
      >- (Cases_on `ev_step orc p d fuel C y s` >> gvs[]
          >- (rename1 `ev_step orc p d fuel C y s = OK sy` >>
              `ev_step orc p d fuel C x sy = Abort Revert_abort t` by
                metis_tac[ev_invoke_partner_stopping, exec_result_distinct] >>
              `ev_step orc p d fuel C x
                 (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort Revert_abort t` by
                metis_tac[dftGasSimInvokeFrameTheory.ev_step_invoke_inst_idx_non_ok,
                          exec_result_distinct] >> gvs[]) >>
          metis_tac[ev_invoke_partner_no_abort]) >>
      `y.inst_opcode <> INVOKE` by metis_tac[ev_invoke_partner_no_abort] >>
      Cases_on `ev_step orc p d fuel C y s` >> gvs[]
      >- (rename1 `ev_step orc p d fuel C y s = OK sy` >>
          Cases_on `ev_step orc p d fuel C x
            (sy with vs_inst_idx := SUC s.vs_inst_idx)` >> gvs[]
          >- metis_tac[ev_indexed_pair_success, exec_result_distinct] >>
          metis_tac[ev_step_noninvoke_abort_empty]) >>
      metis_tac[ev_step_noninvoke_abort_empty])
  >- metis_tac[ev_step_nonterminator_no_intret] >>
  gvs[ev_suffix_def]
QED
