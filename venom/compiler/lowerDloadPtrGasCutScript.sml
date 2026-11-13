(* gas_cut transport for the LowerDload pointer chain.  Source and target of
   a boundary have equal gas readings, and a prefix of an expansion only
   drops readings, so a cut at the target carries to the source and to the
   boundary state t0.  A step of the frame-reachable relation only drops
   readings too, so a cut at its target carries to its source. *)
Theory lowerDloadPtrGasCut
Ancestors
  lowerDloadPtrAggregate lowerDloadPtrPhase lowerDloadPtrCall o1SafeUpto
  gasCount gasOracleReplay venomExecSemantics venomState contextCodegenRel venomInstProofs1
  list

Theorem dload_equal_environment_gas_readings:
  dload_equal_environment s t ==> s.vs_gas_readings = t.vs_gas_readings
Proof
  rw[dload_equal_environment_def] >>
  pop_assum (mp_tac o Q.AP_TERM `\x:venom_state. x.vs_gas_readings`) >>
  simp[]
QED

Theorem dload_boundary_core_gas_readings:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  s.vs_gas_readings = t.vs_gas_readings
Proof
  strip_tac >> irule dload_equal_environment_gas_readings >>
  fs[dload_boundary_core_def]
QED

Theorem dload_prefix_match_gas_le:
  !k t0 H0 un0 t H un.
    dload_prefix_match fuel C PG emitted k t0 H0 un0 t H un ==>
    LENGTH t.vs_gas_readings <= LENGTH t0.vs_gas_readings
Proof
  Induct_on `k` >> rw[dload_prefix_match_def] >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`fuel`,`C`,`EL k emitted`,`u`] mp_tac
    (cj 1 gasCountTheory.gas_count_suffix) >>
  simp[gasCountTheory.gas_count_suffix_def, listTheory.LENGTH_DROP]
QED

Theorem dload_prefix_gas_cut:
  dload_prefix_match fuel C PG emitted n t0 H0 un0 t H un /\
  gas_cut cut vs t ==> gas_cut cut vs t0
Proof
  rw[] >> imp_res_tac dload_prefix_match_gas_le >> gvs[gas_cut_def]
QED

Theorem dload_boundary_core_gas_cut:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  gas_cut cut vs t ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac dload_boundary_core_gas_readings >> gvs[gas_cut_def]
QED

Theorem dload_boundary_prefix_gas_cut:
  dload_boundary_core lo fs V Ws PG PH G H0 tn un0 s t0 cs ds /\
  dload_prefix_match fuel C' PH emitted n t0 H0 un0 t H un /\
  gas_cut cut vs t ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac dload_boundary_core_gas_readings >>
  imp_res_tac dload_prefix_match_gas_le >> gvs[gas_cut_def]
QED

Theorem gas_cut_le:
  LENGTH t.vs_gas_readings <= LENGTH s.vs_gas_readings /\
  gas_cut cut vs t ==> gas_cut cut vs s
Proof
  rw[gas_cut_def] >> decide_tac
QED

Theorem step_inst_gas_le:
  step_inst fuel ctx inst s = OK s' ==>
  LENGTH s'.vs_gas_readings <= LENGTH s.vs_gas_readings
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`fuel`,`ctx`,`inst`,`s`] (cj 1 gasCountTheory.gas_count_suffix)) >>
  gvs[gasCountTheory.gas_count_suffix_def]
QED

Theorem step_inst_int_ret_gas_le:
  step_inst fuel ctx inst s = IntRet ret s_end ==>
  LENGTH s_end.vs_gas_readings <= LENGTH s.vs_gas_readings
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`fuel`,`ctx`,`inst`,`s`] (cj 1 gasCountTheory.gas_count_suffix)) >>
  gvs[gasCountTheory.gas_count_suffix_def]
QED

Theorem enters_block_gas_le:
  enters_block fn s s1 ==>
  LENGTH s1.vs_gas_readings <= LENGTH s.vs_gas_readings
Proof
  rw[enters_block_def] >>
  mp_tac (INST [``insts:instruction list`` |-> ``bb.bb_instructions``]
            gasCountTheory.gas_count_phis) >>
  gvs[gasCountTheory.gas_count_suffix_def]
QED

(* Each rule of frame_reachable carries a cut at its target back to its
   source. *)
Theorem frame_next_gas_cut:
  step_inst fuel ctx inst s = OK s' /\
  gas_cut cut vs (s' with vs_inst_idx := k) ==> gas_cut cut vs s
Proof
  rw[] >> drule step_inst_gas_le >> strip_tac >>
  `LENGTH (s' with vs_inst_idx := k).vs_gas_readings <=
   LENGTH s.vs_gas_readings` by simp[] >>
  metis_tac[gas_cut_le]
QED

Theorem frame_block_gas_cut:
  step_inst fuel ctx inst s = OK s' /\ enters_block fn s' s1 /\
  gas_cut cut vs s1 ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac step_inst_gas_le >> imp_res_tac enters_block_gas_le >>
  `LENGTH s1.vs_gas_readings <= LENGTH s.vs_gas_readings` by decide_tac >>
  metis_tac[gas_cut_le]
QED

Theorem frame_call_gas_cut:
  setup_callee callee args s = SOME cs /\ enters_block callee cs s1 /\
  gas_cut cut vs s1 ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac gasOracleReplayTheory.gas_setup_callee_readings >>
  imp_res_tac enters_block_gas_le >>
  `LENGTH s1.vs_gas_readings <= LENGTH s.vs_gas_readings` by gvs[] >>
  metis_tac[gas_cut_le]
QED

Theorem frame_ret_gas_cut:
  step_inst fuel ctx rinst s = IntRet ret s_end /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state c s_end)) = SOME s' /\
  gas_cut cut vs (s' with vs_inst_idx := k) ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac step_inst_int_ret_gas_le >>
  imp_res_tac gasOracleReplayTheory.gas_bind_outputs_readings >>
  `(s' with vs_inst_idx := k).vs_gas_readings = s_end.vs_gas_readings` by
    (Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `gas_cut cut vs s_end` by gvs[gas_cut_def] >>
  metis_tac[gas_cut_le]
QED
