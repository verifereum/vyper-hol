(* Shifted fresh allocation probe: concrete endpoint, ambient fields and ghost. *)
Theory ctorDeployMemoryRunPtrPrefixShiftAlloc
Ancestors
  ctorDeployMemoryRunPtrPrefixRegisterAlloc ctorDeployLoweringEntryAllocation
  ctorRegisterArgs fragExec abiDecoderLoop actualAllocExec
  entryArgPtrs localPtrsProps ctorAbiActualArrayRun loweringHalt
  ctorDeployMemoryFrontier allocaFrontierBound compileEnv moduleLowering
  venomState venomExecSemantics venomInst ptrSafeRun ptrDiscipline
  finite_map words arithmetic pred_set list

Theorem prefix_shift_alloc_actual:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
  n < dimword (:256) /\ alloca_inv initial /\
  alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?a H q.
    a = (update_var (STRING #"%" (toString st.cs_next_var))
      (n2w initial.vs_alloca_next)
      (initial with <|vs_allocas := initial.vs_allocas |+
        (st.cs_next_id,(initial.vs_alloca_next,n));
        vs_alloca_next := initial.vs_alloca_next+n|>))
      with vs_inst_idx := LENGTH sa.cs_current_insts /\
    H = G |+ (STRING #"%" (toString st.cs_next_var),(initial.vs_alloca_next,n)) /\
    q = tn with <|t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{});
      t_mem := tn.t_mem UNION {j | initial.vs_alloca_next <= j /\ j < initial.vs_alloca_next+n}|> /\
    alloca_inv a /\ alloca_frontier_inv_from k ctx func site a /\
    a.vs_alloca_next = initial.vs_alloca_next+n /\
    a.vs_alloca_next < dimword (:256) /\
    allocas_from lo a /\ lo <= a.vs_alloca_next /\
    ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
    a.vs_inst_idx = LENGTH sa.cs_current_insts /\
    a.vs_outcomes = initial.vs_outcomes /\ a.vs_tx_ctx = initial.vs_tx_ctx /\
    a.vs_block_ctx = initial.vs_block_ctx /\ a.vs_gas_readings = initial.vs_gas_readings /\
    abi_decode_sim ctx func initial a /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H q a) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> drule_all entry_alloc_buffer_inst >> strip_tac >>
  drule_at (Pat `MEM _ _`) deploy_ctor_literal_alloca_fresh_run >>
  disch_then (mp_tac o SRULE [mk_inst_def]) >>
  disch_then (qspecl_then [`site`,`initial`,`n`] mp_tac) >>
  disch_then (drule_all o SRULE []) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `exec_alloca _ initial _ = OK t` >>
  `alloca_inv t` by metis_tac[alloca_inv_exec_alloca] >>
  `alloca_frontier_inv_from k ctx func site t` by
    (irule deploy_ctor_alloca_frontier_preserved >>
     conj_tac >- metis_tac[ctor_actual_function_ids] >>
     goal_assum (drule_at Any) >> fs[mk_inst_def] >> metis_tac[]) >>
  `frag_exec ctx st sa (\u. u = initial)
     (\u. u = t with vs_inst_idx := LENGTH sa.cs_current_insts) (\r. F)` by
    (irule compile_alloc_buffer_fresh_frag >> qexistsl [`buf`,`n`] >> simp[Abbr `t`]) >>
  `abi_decode_sim ctx func initial (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
     simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
     simp[abi_decode_sim_def] >> metis_tac[]) >>
  `alloca_frontier_inv_from k ctx func site (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (irule deploy_ctor_alloca_frontier_fields >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all prefix_register_alloc_layout >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH sa.cs_current_insts` >> simp[] >>
  gvs[Abbr `t`, update_var_def] >>
  reverse conj_tac >-
    (`n < dimword (:256)` by decide_tac >>
     drule_all prefix_register_alloc_run_continuation >> simp[update_var_def] >> metis_tac[]) >>
  simp[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `st.cs_next_id = aid` >> gvs[allocas_from_def] >> metis_tac[]
QED
