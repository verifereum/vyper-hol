(* Generated SHA256 calls retain the origin of their internal GAS on failure. *)
Theory bodyFullHashShaAbortOrigin
Ancestors
  bodyFullHashShaOrigin
  fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr gasCount ptrSafeRun
  bodyPtrHashBuiltinsShaTail bodyPtrHashBuiltinsShaTailSteps fragExecMem memSafeRun gasEvents
  venomExecProofs venomExecSemantics venomState venomInstProofs venomInst
  instIdxIndep fragExec exprLoweringProps fragGasSeqMem fragGasSeqAbort
  ptrDiscipline list rich_list arithmetic
  fragGasOriginPtrExec fragGasPath vyperStorageTrace vyperStorageFootprint

Theorem sha_setup_cannot_abort[local]:
  MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD] ==>
  step_inst_base i s <> Abort a t
Proof
  simp[] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_alloca_def, exec_pure2_def,
    exec_read1_def, exec_write2_def, AllCaseEqs()]
QED

Theorem sha_setup_nonterminators[local]:
  EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]) prefix ==>
  EVERY (\i. ~is_terminator i.inst_opcode) prefix
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> res_tac >>
  gvs[is_terminator_def]
QED

Theorem sha_setup_gas_origin_abort[local]:
  !prefix s t a G tn G' tn' ctx fn bb code id gv.
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (prefix ++ mk_inst id GAS [] [gv]::code)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]) prefix /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) code /\
  (fn.fn_name,id) NOTIN explicit /\
  run_inst_seq_mem_ok (prefix ++ mk_inst id GAS [] [gv]::code) s /\
  inst_seq_ptr D lo ctx fn PG G tn (prefix ++ mk_inst id GAS [] [gv]::code) s G' tn' /\
  run_inst_seq (prefix ++ mk_inst id GAS [] [gv]::code) s = Abort a t ==>
  ?j. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [F]
    (Abort a (t with vs_inst_idx := j),G',tn')
Proof
  Induct >- (simp_tac std_ss [APPEND, EVERY_DEF] >>
    rpt strip_tac >> drule_all sha_gas_head_origin_abort >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [APPEND, EVERY_DEF]) >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `MEM h.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD] /\ _` strip_assume_tac >>
  `h.inst_opcode <> GAS /\ h.inst_opcode <> INVOKE /\ ~is_terminator h.inst_opcode` by
    (qpat_assum `MEM h.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]` mp_tac >>
     simp[] >> strip_tac >> gvs[is_terminator_def]) >>
  `!a t. step_inst_base h s <> Abort a t` by
    (rpt gen_tac >> irule sha_setup_cannot_abort >> fs[]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[Once run_inst_seq_def, Once inst_seq_ptr_def, Once run_inst_seq_mem_ok_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (prefix ++ mk_inst id GAS [] [gv]::code)` by
    (simp[EVERY_APPEND, mk_inst_def, is_terminator_def] >> conj_tac
     >- (irule sha_setup_nonterminators >> simp[]) >>
     qpat_assum `EVERY _ code` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  disch_then (qspecl_then [`a`, `step_prov PG G h u`,
    `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `fn`, `bb`, `code`, `id`, `gv`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  strip_tac >> qexists_tac `j` >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G h u,step_taint h s u tn)` by
    (mp_tac (Q.INST [`i` |-> `h`, `u` |-> `u`, `func` |-> `fn`]
       (SPEC_ALL straight_line_origin_ptr_edge)) >>
     simp[inst_dload_in_section_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >> simp[]
QED

Theorem sha_origin_abort_endpoint_unique[local]:
  gas_origin_ptr_path (D1,lo,explicit,ctx,fn,PG) (s,G,tn) marks
    (Abort a t,G1,tn1) /\
  gas_origin_ptr_path (D2,lo,explicit,ctx,fn,PG) (s,G,tn) marks'
    (Abort a u,G2,tn2) ==> t = u
Proof
  strip_tac >>
  qpat_assum `gas_origin_ptr_path (D1,_,_,_,_,_) _ _ _`
    (mp_then Any mp_tac gas_origin_ptr_path_exec) >>
  simp[exit_result_def] >> disch_then (qx_choose_then `k` strip_assume_tac) >>
  qpat_assum `gas_origin_ptr_path (D2,_,_,_,_,_) _ _ _`
    (mp_then Any mp_tac gas_origin_ptr_path_exec) >>
  simp[exit_result_def] >> disch_then (qx_choose_then `l` strip_assume_tac) >>
  `run_from (k+l) ctx fn s = Abort a t` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `k` >> simp[]) >>
  `run_from (k+l) ctx fn s = Abort a u` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `l` >> simp[]) >>
  gvs[]
QED

Theorem sha_setup_gas_origin_abort_uniform:
  storage_trace_domain cx st0 obs /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (prefix ++ mk_inst id GAS [] [gv]::code)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]) prefix /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) code /\
  (fn.fn_name,id) NOTIN explicit /\
  run_inst_seq_mem_ok (prefix ++ mk_inst id GAS [] [gv]::code) s /\
  (!H. valid_horizon cx st0 H obs ==>
    inst_seq_ptr (DF H) lo ctx fn PG G tn
      (prefix ++ mk_inst id GAS [] [gv]::code) s G' tn') /\
  run_inst_seq (prefix ++ mk_inst id GAS [] [gv]::code) s = Abort a t ==>
  ?j. !H. valid_horizon cx st0 H obs ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [F]
      (Abort a (t with vs_inst_idx := j),G',tn')
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon obs) obs` by
    fs[storage_trace_domain_def] >>
  `inst_seq_ptr (DF (storage_trace_horizon obs)) lo ctx fn PG G tn
    (prefix ++ mk_inst id GAS [] [gv]::code) s G' tn'` by metis_tac[] >>
  drule_all (Q.INST [`D` |-> `DF (storage_trace_horizon obs)`]
    sha_setup_gas_origin_abort) >> strip_tac >> qexists_tac `j` >>
  rpt strip_tac >>
  `inst_seq_ptr (DF H) lo ctx fn PG G tn
    (prefix ++ mk_inst id GAS [] [gv]::code) s G' tn'` by metis_tac[] >>
  drule_all (Q.INST [`D` |-> `DF H`] sha_setup_gas_origin_abort) >>
  disch_then (qx_choose_then `k` assume_tac) >>
  `(t with vs_inst_idx := k) = (t with vs_inst_idx := j)` by
    (irule sha_origin_abort_endpoint_unique >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  metis_tac[]
QED

