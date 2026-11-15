Theory dftStaticSwap
Ancestors
  dftStaticEventAbort dftGasSimSwap dftGasSimSwapStop dftGasSimLocalBoundary
  dftGasSimBoundary dftRunRel dftGasOracleDefs venomState venomInst
  venomExecSemantics venomEffects list

(* Full operand readiness includes CODECOPY labels.  Static abort replay
   preserves the asymmetric abort class, not the abort state or kind. *)
Theorem ev_suffix_swap_ready:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE ==>
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
  >- (drule_all ev_suffix_first_abort_static >> strip_tac >>
      simp[dft_res_rel_def] >> metis_tac[])
  >- metis_tac[ev_step_nonterminator_no_intret] >>
  rename1 `ev_step orc p d fuel C x s = Error err` >>
  `ev_suffix orc p d fuel C (x::y::tail) s = Error err` by
    simp[ev_suffix_def] >>
  simp[Once dft_res_rel_def] >>
  metis_tac[ev_suffix_swap_success_back, exec_result_distinct]
QED
