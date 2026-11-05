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
