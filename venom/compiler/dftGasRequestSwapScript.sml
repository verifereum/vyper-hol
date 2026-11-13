(* Directional request observations at an adjacent DFT crossing. *)
Theory dftGasRequestSwap
Ancestors
  dftGasRequestRel dftGasRequestObservation dftGasRequestPartner
  dftGasSimSwap dftGasSimSwapStop dftGasSimLocalBoundary dftGasSimInvokeFrame
  dftRunRel dftGasSimBoundary dftGasOracleDefs o1RequestContract venomExecSemantics
  venomState venomInst venomEffects list rich_list

Theorem ev_suffix_second_abort_requests:
  dft_gas_swap_pair x y /\
  ev_step orc p d fuel C x s = OK sx /\
  ev_step orc p d fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t /\
  ev_suffix orc p d fuel C (y::x::tail) s = Abort b u ==>
  request_prefix_rel D t.vs_requests u.vs_requests
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  Cases_on `y.inst_opcode = INVOKE`
  >- (`ev_step orc p d fuel C y sx = Abort a t` by
        (gvs[ev_step_invoke_inst_idx, AllCaseEqs()]) >>
      `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
      `ev_step orc p d fuel C y s = Abort a t` by
        metis_tac[ev_invoke_partner_stopping, exec_result_distinct] >>
      gvs[ev_suffix_def] >> simp[request_prefix_rel_refl]) >>
  `x.inst_opcode <> INVOKE` by
    metis_tac[ev_invoke_partner_no_abort] >>
  `t.vs_requests = sx.vs_requests` by
    (drule_all ev_step_abort_requests >> simp[]) >>
  `s.vs_requests <<= sx.vs_requests` by metis_tac[ev_step_requests_prefix] >>
  drule_all ev_suffix_second_abort >> strip_tac >>
  `?v. ev_step orc p d fuel C y s = Abort a v` by
    metis_tac[ev_pair_abort_iff, ev_step_nonterminator_abort_idx_iff] >>
  `u.vs_requests = s.vs_requests` by
    (gvs[ev_suffix_def] >> metis_tac[ev_step_abort_requests]) >>
  metis_tac[isPREFIX_imp_request_prefix_rel]
QED

Theorem ev_suffix_first_abort_requests:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~s.vs_call_ctx.cc_static /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  ev_step orc p d fuel C x s = Abort a t /\
  ev_suffix orc p d fuel C (y::x::tail) s = Abort b u ==>
  request_prefix_rel D t.vs_requests u.vs_requests
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  Cases_on `x.inst_opcode = INVOKE`
  >- (Cases_on `ev_step orc p d fuel C y s` >>
      gvs[ev_suffix_def]
      >- (rename1 `ev_step orc p d fuel C y s = OK sy` >>
          `ev_step orc p d fuel C x sy = Abort a t` by
            metis_tac[ev_invoke_partner_stopping, exec_result_distinct] >>
          `ev_step orc p d fuel C x
             (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t` by
            metis_tac[ev_step_invoke_inst_idx_non_ok, exec_result_distinct] >>
          gvs[] >> simp[request_prefix_rel_refl]) >>
      metis_tac[ev_invoke_partner_no_abort]) >>
  `~MEM y.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` by
    metis_tac[ev_abort_partner_request_free] >>
  `t.vs_requests = s.vs_requests` by metis_tac[ev_step_abort_requests] >>
  drule_all ev_suffix_first_abort >> disch_then (qspec_then `[]` strip_assume_tac) >>
  Cases_on `ev_step orc p d fuel C y s` >> gvs[ev_suffix_def]
  >- (rename1 `ev_step orc p d fuel C y s = OK sy` >>
      `sy.vs_requests = s.vs_requests` by
        (irule ev_step_request_free >> simp[] >> metis_tac[]) >>
      Cases_on `ev_step orc p d fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx)` >>
      gvs[] >>
      drule_all ev_step_abort_requests >> simp[request_prefix_rel_refl]) >>
  metis_tac[ev_step_abort_requests, request_prefix_rel_refl]
QED

(* The old result contract supplies all non-abort observations. *)
Theorem ev_suffix_swap_rq:
  dead_wf D /\ dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~s.vs_call_ctx.cc_static /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  dft_rq_res_rel D (ev_suffix orc p d fuel C (x::y::tail) s)
                  (ev_suffix orc p d fuel C (y::x::tail) s)
Proof
  strip_tac >> simp[dft_rq_res_rel_def] >> conj_tac
  >- (irule ev_suffix_swap >> fs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ev_suffix _ _ _ _ _ (y::x::tail) s = _` (mk_asm "target") >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  Cases_on `ev_step orc p d fuel C x s`
  >- (rename1 `ev_step orc p d fuel C x s = OK sx` >>
      Cases_on `ev_step orc p d fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx)`
      >- (drule_all ev_suffix_pair_success >>
          disch_then (qspec_then `tail` assume_tac) >>
          asm_x "target" assume_tac >> gvs[] >> simp[request_prefix_rel_refl]) >>
      gvs[ev_suffix_def] >> asm_x "target" assume_tac >>
      metis_tac[ev_suffix_second_abort_requests]) >>
  gvs[ev_suffix_def] >> asm_x "target" assume_tac >>
  metis_tac[ev_suffix_first_abort_requests]
QED
