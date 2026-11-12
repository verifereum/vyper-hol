(* Shifted allocation at an explicit machine/ghost endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixEntryRegisterAlloc
Ancestors
 ctorDeployMemoryRunPtrPrefixRegisterAlloc ctorDeployLoweringEntryRegisterRun
 ctorDeployLoweringEntryAllocation actualAllocCredit actualAllocExec
 allocaFrontierBound allocaBudgetProps entryArgPtrs loweringHalt fragExec
 ctorAbiActualSites ctorRegisterArgs emitHelperProps moduleLowering compileEnv
 venomExecSemantics venomState venomInst finite_map words arithmetic
 vyperCompiler localPtrsProps ctorAbiActualArrayRun abiDecoderLoop
 ptrSafeRun ptrDiscipline pred_set ctorDeployMemoryRunPtrPrefixAllocationFloor

Theorem prefix_entry_register_alloc_run[local]:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ alloca_inv initial /\
 alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?a. a = (update_var (STRING #"%" (toString st.cs_next_var))
     (n2w initial.vs_alloca_next)
     (initial with <| vs_allocas := initial.vs_allocas |+
       (st.cs_next_id,(initial.vs_alloca_next,n));
       vs_alloca_next := initial.vs_alloca_next+n |>))
     with vs_inst_idx := LENGTH sa.cs_current_insts /\
 alloca_inv a /\ alloca_frontier_inv_from k ctx func site a /\
 initial.vs_alloca_next+n < dimword (:256) /\
 ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
 abi_decode_sim ctx func initial a
Proof
 strip_tac >>
 `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
   [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
   (drule_all entry_alloc_buffer_inst >> simp[]) >>
 `initial.vs_alloca_next + n < dimword (:256)` by
   (drule deploy_ctor_alloca_frontier_credit >>
    disch_then drule >>
    simp[mk_inst_def, alloca_size_def, w2n_n2w] >> strip_tac >> decide_tac) >>
 qabbrev_tac `raw = update_var (STRING #"%" (toString st.cs_next_var))
   (n2w initial.vs_alloca_next)
   (initial with <|vs_allocas := initial.vs_allocas |+
     (st.cs_next_id,(initial.vs_alloca_next,n));
     vs_alloca_next := initial.vs_alloca_next+n |>)` >>
 `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) initial (n2w n : bytes32) = OK raw` by
   simp[exec_alloca_def, mk_inst_def, w2n_n2w, Abbr `raw`] >>
 `alloca_inv raw` by metis_tac[alloca_inv_exec_alloca] >>
 `alloca_frontier_inv_from k ctx func site raw` by
   (irule deploy_ctor_alloca_frontier_preserved >>
    conj_tac >- metis_tac[ctor_actual_function_ids] >>
    qexistsl [`mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString st.cs_next_var)]`, `initial`, `site`] >>
    fs[mk_inst_def, step_inst_base_def]) >>
 `frag_exec ctx st sa (\u. u = initial)
    (\u. u = raw with vs_inst_idx := LENGTH sa.cs_current_insts) (K F)` by
   (irule compile_alloc_buffer_fresh_frag >> qexistsl [`buf`, `n`] >>
    simp[Abbr `raw`]) >>
 qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
 simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
 simp[] >> strip_tac >>
 simp[abi_decode_sim_def] >>
 irule deploy_ctor_alloca_frontier_fields >>
 goal_assum (drule_at Any) >> simp[]
QED

Theorem prefix_entry_register_alloc_actual:
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
     (st.cs_next_id,(initial.vs_alloca_next,n)); vs_alloca_next := initial.vs_alloca_next+n|>))
   with vs_inst_idx := LENGTH sa.cs_current_insts /\
 H = G |+ (STRING #"%" (toString st.cs_next_var),(initial.vs_alloca_next,n)) /\
 q = tn with <|t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{});
   t_mem := tn.t_mem UNION {j | initial.vs_alloca_next <= j /\ j < initial.vs_alloca_next+n}|> /\
 alloca_inv a /\ alloca_frontier_inv_from k ctx func site a /\
 a.vs_alloca_next = initial.vs_alloca_next+n /\ a.vs_alloca_next < dimword (:256) /\
 allocas_from lo a /\ lo <= a.vs_alloca_next /\
 ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
 a.vs_inst_idx = LENGTH sa.cs_current_insts /\ abi_decode_sim ctx func initial a /\
 a.vs_code = initial.vs_code /\ a.vs_outcomes = initial.vs_outcomes /\
 a.vs_tx_ctx = initial.vs_tx_ctx /\ a.vs_block_ctx = initial.vs_block_ctx /\
 a.vs_gas_readings = initial.vs_gas_readings /\
 (!j. j < lo ==> read_byte j a.vs_memory = read_byte j initial.vs_memory) /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H q a) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 strip_tac >> drule_all prefix_entry_register_alloc_run >> strip_tac >>
 qexists `a` >> simp[] >>
 reverse conj_tac >-
   (drule_all prefix_register_alloc_run_continuation >> simp[]) >>
 gvs[update_var_def] >>
 simp[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
 Cases_on `st.cs_next_id = aid` >> gvs[allocas_from_def] >> metis_tac[]
QED

val _ = export_theory();
