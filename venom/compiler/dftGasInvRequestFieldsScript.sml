(* Preserve the operands and world state observed by an external request
   when DFT completes a scheduled prefix. *)
Theory dftGasInvRequestFields
Ancestors
  dftGasInvObservationOracle
  dftGasInvExtraction dftGasInvFlexibleTrace dftGasInvCrossingProbe
  dftGasOracleDefs dftSsaPreserve
  dftRunRel dftScheduleOrder dftGasSimBoundary venomEffects venomExecSemantics
  venomExecProps venomExecProofs venomInstProofs oracleExecProps opcodeClass venomState venomInst
  pred_set list rich_list venomCallOracleDefs dftGasInvInversion
  dftGasInvResidualTrace dftGasInvPrefixRun dftGasInvReachSlice
  dftStaticAbortExtension dftStructural dftCorrectness dftDefs passSharedDefs sorting
Libs
  stepInstBaseLib

Theorem ext_call_reads_all[local]:
  is_ext_call_op op ==> read_effects op = all_effects
Proof
  Cases_on `op` >> simp[is_ext_call_op_def, read_effects_def]
QED

Theorem inv_ev_step_request_fields[local]:
  is_ext_call_op obs.inst_opcode /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  (~dft_must_order inst obs \/ ~dft_must_order obs inst) /\
  ev_step orc p d fuel C inst s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ext_call_reads_all >> strip_tac >>
  `Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode` by
    (gvs[dftScheduleOrderTheory.dft_must_order_def, all_effects_def, IN_DISJOINT] >>
     metis_tac[]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- gvs[ev_step_def, ev_gas_def, update_var_def, AllCaseEqs()] >>
  `step_inst fuel C inst s = OK t` by gvs[ev_step_def, step_inst_def] >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  metis_tac[write_effects_sound_memory, write_effects_sound_accounts,
            write_effects_sound_transient, step_inst_ok_preserves_call_ctx]
QED

Theorem inv_ev_ftrace_request_fields[local]:
  !xs s t.
    is_ext_call_op obs.inst_opcode /\
    EVERY (\i. i.inst_opcode <> ALLOCA /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode /\
      (~dft_must_order i obs \/ ~dft_must_order obs i)) xs /\
    inv_ev_ftrace orc p d C xs s t ==>
    t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `?fuel u. _`
    (CHOOSE_THEN (CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  drule_all (Q.INST [`obs` |-> `obs`, `inst` |-> `h`] inv_ev_step_request_fields) >>
  strip_tac >>
  first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`, `t`] mp_tac) >>
  simp[]
QED

Theorem exec_ext_call_same_requests[local]:
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_requests = s.vs_requests /\ t.vs_outcomes = s.vs_outcomes /\
  exec_ext_call inst s gas addr value ao az ro rz static = OK post ==>
  ?u. exec_ext_call inst t gas addr value ao az ro rz static = OK u /\
      u.vs_requests = post.vs_requests /\ u.vs_outcomes = post.vs_outcomes
Proof
  strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[exec_ext_call_def] >>
  rename1 `out::outs` >> Cases_on `outs` >>
  gvs[exec_ext_call_def, AllCaseEqs(), update_var_def] >>
  simp[venom_call_request_def, venomStateTheory.read_memory_def]
QED

Theorem exec_delegatecall_same_requests[local]:
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_requests = s.vs_requests /\ t.vs_outcomes = s.vs_outcomes /\
  exec_delegatecall inst s gas addr ao az ro rz = OK post ==>
  ?u. exec_delegatecall inst t gas addr ao az ro rz = OK u /\
      u.vs_requests = post.vs_requests /\ u.vs_outcomes = post.vs_outcomes
Proof
  strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[exec_delegatecall_def] >>
  rename1 `out::outs` >> Cases_on `outs` >>
  gvs[exec_delegatecall_def, AllCaseEqs(), update_var_def] >>
  simp[venom_call_request_def, venomStateTheory.read_memory_def]
QED

Theorem exec_create_same_requests[local]:
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\
  t.vs_requests = s.vs_requests /\ t.vs_outcomes = s.vs_outcomes /\
  exec_create inst s value off sz salt = OK post ==>
  ?u. exec_create inst t value off sz salt = OK u /\
      u.vs_requests = post.vs_requests /\ u.vs_outcomes = post.vs_outcomes
Proof
  strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[exec_create_def] >>
  rename1 `out::outs` >> Cases_on `outs` >>
  gvs[exec_create_def, AllCaseEqs(), update_var_def] >>
  simp[venom_create_request_def, venomStateTheory.read_memory_def]
QED

Theorem request_step_same_fields:
  is_ext_call_op inst.inst_opcode /\
  (!op. MEM op inst.inst_operands ==> eval_operand op t = eval_operand op s) /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_requests = s.vs_requests /\ t.vs_outcomes = s.vs_outcomes /\
  step_inst fuel C inst s = OK post ==>
  ?u. step_inst fuel' C' inst t = OK u /\
      u.vs_requests = post.vs_requests /\ u.vs_outcomes = post.vs_outcomes
Proof
  strip_tac >>
  `eval_operands inst.inst_operands t = eval_operands inst.inst_operands s` by
    metis_tac[eval_operands_agree] >>
  Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def, step_inst_non_invoke] >>
  with_opcode_clause gvs >>
  qpat_x_assum `_ = OK post` mp_tac >>
  simp[AllCaseEqs()] >> rw[] >>
  gvs[MEM] >>
  FIRST [irule exec_ext_call_same_requests,
         irule exec_delegatecall_same_requests,
         irule exec_create_same_requests] >> qexists_tac `s` >> simp[]
QED

Theorem inv_external_call_invokes_ordered[local]:
  is_ext_call_op y.inst_opcode /\
  (~dft_must_order y x \/ ~dft_must_order x y) ==>
  x.inst_opcode <> INVOKE
Proof
  strip_tac >> spose_not_then assume_tac >>
  `Eff_MEMORY IN read_effects y.inst_opcode /\
   Eff_MEMORY IN write_effects x.inst_opcode` by
    simp[ext_call_reads_all, write_effects_def, all_effects_def] >>
  fs[dftScheduleOrderTheory.dft_must_order_def, IN_DISJOINT] >>
  metis_tac[IN_UNION]
QED

Theorem inv_completed_external_request_fields:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  is_ext_call_op obs.inst_opcode /\
  EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions /\
  EVERY (\i. inst_shape_ok i /\ ~is_terminator i.inst_opcode /\ ~dft_must_order i obs)
    (FILTER (\i. ~MEM i consumed) srcpre) /\
  s0.vs_inst_idx = LENGTH pseudos /\
  inv_ev_trace orc p d 0 ctx (FILTER (\i. ~MEM i consumed) srcpre) sT u /\
  (!op. MEM op obs.inst_operands ==> eval_operand op u = eval_operand op sT) /\
  inv_ev_ftrace orc p d ctx srcpre s0 sS /\
  inv_ev_ftrace orc p d ctx (FILTER (\i. MEM i consumed) srcpost) sS u ==>
  (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
  sS.vs_memory = sT.vs_memory /\ sS.vs_accounts = sT.vs_accounts /\
  sS.vs_transient = sT.vs_transient /\ sS.vs_call_ctx = sT.vs_call_ctx /\
  sS.vs_requests = sT.vs_requests /\ sS.vs_outcomes = sT.vs_outcomes
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> ALLOCA /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode /\
      (~dft_must_order i obs \/ ~dft_must_order obs i))
    (FILTER (\i. ~MEM i consumed) srcpre)` by
    (fs[EVERY_MEM, MEM_FILTER] >> metis_tac[MEM_APPEND, MEM, inv_external_call_invokes_ordered]) >>
  `EVERY (\z. MEM z bb.bb_instructions /\ ~is_pseudo z.inst_opcode /\
     id_before (MAP (\i. i.inst_id) bb.bb_instructions) obs.inst_id z.inst_id /\
     id_before (MAP (\i. i.inst_id) bb'.bb_instructions) z.inst_id obs.inst_id)
     (FILTER (\i. MEM i consumed) srcpost)` by
    (simp[EVERY_MEM, MEM_FILTER] >> gen_tac >> strip_tac >>
     `MEM z bb.bb_instructions /\ ~is_pseudo z.inst_opcode` by
       (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
     asm_rewrite_tac[MAP_APPEND] >>
     simp[dftSsaPreserveTheory.id_before_append,
          dftSsaPreserveTheory.id_before_cons, MEM_MAP] >> metis_tac[]) >>
  `MEM obs bb.bb_instructions /\ ~is_pseudo obs.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode /\
      (~dft_must_order i obs \/ ~dft_must_order obs i))
    (FILTER (\i. MEM i consumed) srcpost)` by
    (drule_all dftRunRelTheory.dft_fn_rel_lookup_order >> strip_tac >>
     simp[EVERY_MEM, MEM_FILTER] >> gen_tac >> strip_tac >>
     qpat_x_assum `EVERY _ (FILTER (\i. MEM i consumed) srcpost)`
       (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_MEM]) >> simp[MEM_FILTER] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `~dft_must_order obs i` by
       (irule dftRunRelTheory.dft_inversion_not_must_order >> simp[] >>
        qexistsl_tac [`bb`, `bb'`] >> simp[]) >>
     `i.inst_opcode <> ALLOCA` by
       (qpat_assum `EVERY _ bb.bb_instructions`
         (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
     `~is_terminator i.inst_opcode` by gvs[dftScheduleOrderTheory.dft_must_order_def] >>
     metis_tac[inv_external_call_invokes_ordered]) >>
  `u.vs_memory = sT.vs_memory /\ u.vs_accounts = sT.vs_accounts /\
    u.vs_transient = sT.vs_transient /\ u.vs_call_ctx = sT.vs_call_ctx` by
    (mp_tac (Q.SPECL [`FILTER (\i. ~MEM i consumed) srcpre`, `sT`, `u`]
       (Q.INST [`C` |-> `ctx`] inv_ev_ftrace_request_fields)) >>
     simp[] >> metis_tac[inv_ev_trace_ftrace]) >>
  `u.vs_memory = sS.vs_memory /\ u.vs_accounts = sS.vs_accounts /\
    u.vs_transient = sS.vs_transient /\ u.vs_call_ctx = sS.vs_call_ctx` by
    (mp_tac (Q.SPECL [`FILTER (\i. MEM i consumed) srcpost`, `sS`, `u`]
       (Q.INST [`C` |-> `ctx`] inv_ev_ftrace_request_fields)) >> simp[]) >>
  `inv_memory_observation obs.inst_opcode` by
    (Cases_on `obs.inst_opcode` >> gvs[inv_memory_observation_def, is_ext_call_op_def]) >>
  drule_all inv_completed_observation_oracle >> simp[] >> metis_tac[]
QED

Theorem inv_lookup_normalized_external_request_fields:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions /\
  dft_remaining_inv fn bb (srcpre ++ obs::srcpost) s0 /\
  s0.vs_inst_idx = LENGTH pseudos /\ is_ext_call_op obs.inst_opcode /\
  inv_ev_ftrace orc p d ctx consumed s0 sT /\
  inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS ==>
  (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
  sS.vs_memory = sT.vs_memory /\ sS.vs_accounts = sT.vs_accounts /\
  sS.vs_transient = sT.vs_transient /\ sS.vs_call_ctx = sT.vs_call_ctx /\
  sS.vs_requests = sT.vs_requests /\ sS.vs_outcomes = sT.vs_outcomes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `wf_function fn /\ wf_ssa fn` by metis_tac[dft_fn_rel_def] >>
  `ALL_DISTINCT (consumed ++ obs::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  `ALL_DISTINCT consumed /\ ~MEM obs consumed` by
    (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `EVERY (\i. MEM i (srcpre ++ srcpost)) consumed` by
    (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
     `i <> obs` by metis_tac[] >>
     drule PERM_MEM_EQ >> disch_then (qspec_then `i` mp_tac) >>
     simp[]) >>
  drule_all inv_lookup_block_contract >> strip_tac >>
  drule_all inv_lookup_missing_predecessors >> strip_tac >>
  `inv_memory_observation obs.inst_opcode` by
    (Cases_on `obs.inst_opcode` >> gvs[inv_memory_observation_def, is_ext_call_op_def]) >>
  `EVERY (\i. MEM i (srcpre ++ obs::srcpost)) consumed` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `dft_remaining_inv fn bb
    (FILTER (\i. ~MEM i consumed) srcpre ++ obs::FILTER (\i. ~MEM i consumed) srcpost) sT` by
    (drule_all inv_ftrace_remaining >> simp[FILTER_APPEND_DISTRIB]) >>
  `?u. inv_ev_trace orc p d 0 ctx (FILTER (\i. ~MEM i consumed) srcpre) sT u /\
    (!op. MEM op obs.inst_operands ==> eval_operand op u = eval_operand op sT)` by
    (Cases_on `sT.vs_call_ctx.cc_static`
     >- (`s0.vs_call_ctx.cc_static` by metis_tac[inv_ftrace_call_ctx] >>
         `inv_ev_ftrace orc p d ctx srcpre s0 sS` by
           (drule_at (Pat `inv_ev_prefix _ _ _ _ _ _ _ _`) inv_ev_prefix_ftrace >>
            simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG]) >>
         `EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG])
           (FILTER (\i. ~MEM i consumed) srcpre)` by
           (drule_all inv_static_ftrace_no_writes >> simp[EVERY_MEM, MEM_FILTER]) >>
         drule_at (Pat `dft_remaining_inv _ _ _ sT`)
           inv_remaining_trace_extension_no_static_writes >> simp[] >> metis_tac[]) >>
     drule_at (Pat `dft_remaining_inv _ _ _ sT`) inv_remaining_trace_extension >>
     simp[] >> metis_tac[]) >>
  `inv_ev_ftrace orc p d ctx
    (consumed ++ FILTER (\i. ~MEM i consumed) srcpre) s0 u` by
    metis_tac[inv_ev_trace_ftrace, inv_ev_ftrace_append] >>
  drule_all inv_lookup_completed_sort >> simp[inv_ev_ftrace_append] >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx srcpre s0 normalized` >>
  `inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 normalized` by
    (qspecl_then [`srcpre`, `pseudos`, `s0`, `normalized`] mp_tac
       (Q.INST [`b` |-> `obs::srcpost`] inv_ev_ftrace_slice) >>
     simp[APPEND_ASSOC]) >>
  `normalized = sS` by metis_tac[inv_ev_prefix_unique] >>
  qpat_x_assum `normalized = sS` SUBST_ALL_TAC >>
  drule_all inv_completed_external_request_fields >> simp[]
QED
