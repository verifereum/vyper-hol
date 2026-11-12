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
  ctorDeployMemoryRunMemEntryRegistration


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
 strip_tac >> drule_all ctorDeployLoweringEntryRegisterRunTheory.deploy_ctor_register_alloc_run >> strip_tac >>
 qexists `a` >> simp[] >>
 reverse conj_tac >-
   (drule_all prefix_register_alloc_run_continuation >> simp[]) >>
 gvs[update_var_def] >>
 simp[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
 Cases_on `st.cs_next_id = aid` >> gvs[allocas_from_def] >> metis_tac[]
QED

(* Allocation has a literal machine endpoint, so checked execution attaches
   directly to that endpoint rather than to a second existential run. *)
Theorem prefix_entry_register_alloc_actual_mode:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ alloca_inv initial /\
 alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
 (checked ==> alloca_history func initial) ==>
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
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
 (checked ==> gas_path_mem ctx func initial 0 (OK a) /\ alloca_history func a)
Proof
 strip_tac >> drule_all prefix_entry_register_alloc_actual >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
 qexistsl [`a`,`H`,`q`] >> asm_rewrite_tac[] >> strip_tac >>
 metis_tac[ctor_checked_alloc_buffer_edge]
QED

val _ = export_theory();
