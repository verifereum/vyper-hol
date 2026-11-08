(* Actual allocation at the constructor's reserved-memory frontier. *)
Theory ctorDeployMemoryRunMemEntryShiftedAlloc
Ancestors
  ctorDeployLoweringEntryRegisterRun ctorDeployLoweringEntryAllocation
  ctorDeployMemoryRunMemEntryShiftedFrame
  ctorDeployMemoryRunMemEntryShiftedFrontier ctorDeployMemoryFrontier
  actualAllocExec allocaBudgetProps allocaFrontierBound venomExecSemantics venomState venomInst
  vyperCompiler ctorRegisterArgs ctorDeployMemoryRunMemEntryRegistration
  ctorAbiActualSites context emitHelper emitHelperProps exprLoweringProps
  loweringHalt fragExec abiDecoderReentry venomMemProps venomMemDefs
  entryArgPtrs fragGasPathMem allocaHistory localPtrsProps
  ctorAbiActualArrayRun abiDecoderLoop compileEnv abiEncoderRegisteredEffect abiEncoderProps
  finite_map pred_set list rich_list arithmetic words

Theorem actual_word_alloca_fresh_run_from:
  alloca_frontier_inv_from k ctx fn site s /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    t = update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (inst.inst_id,(s.vs_alloca_next,32));
        vs_alloca_next := s.vs_alloca_next + 32|>) /\
    s.vs_alloca_next + 32 < dimword (:256) /\
    t.vs_allocas = s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,32)) /\
    t.vs_alloca_next = s.vs_alloca_next + 32 /\
    (!j. j <> inst.inst_id ==> FLOOKUP t.vs_allocas j = FLOOKUP s.vs_allocas j)
Proof
  strip_tac >>
  `alloca_size inst = 32` by
    simp[alloca_size_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  `inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
  drule_all actual_word_alloca_no_wrap_from >> strip_tac >>
  simp[step_inst_base_def, exec_alloca_def] >>
  simp[update_var_def, FLOOKUP_UPDATE,
       dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem ctor_alloc_buffer_credit_from:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
  n < dimword (:256) /\ alloca_frontier_inv_from k ctx func site initial /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = NONE ==>
  initial.vs_alloca_next + n < dimword (:256)
Proof
  strip_tac >> drule_all entry_alloc_buffer_inst >> strip_tac >>
  drule_at (Pat `MEM _ _`) actual_alloca_no_wrap_from >>
  simp[mk_inst_def, FLOOKUP_DEF, alloca_size_def, w2n_n2w] >>
  disch_then (qspecl_then [`k`, `ctx`, `site`, `initial`] mp_tac) >>
  gvs[FLOOKUP_DEF]
QED

Theorem ctor_checked_alloc_buffer_run_from:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ alloca_inv initial /\
 alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ alloca_history func initial /\
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
   abi_decode_sim ctx func initial a /\
   gas_path_mem ctx func initial 0 (OK a) /\
   a.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func a
Proof
 strip_tac >>
 `initial.vs_alloca_next + n < dimword (:256)` by
   (drule_all ctor_alloc_buffer_credit_from >> simp[]) >>
 `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
   [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
   (drule_all entry_alloc_buffer_inst >> simp[]) >>
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
 `abi_decode_sim ctx func initial (raw with vs_inst_idx := LENGTH sa.cs_current_insts)` by
   (qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
    simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
    simp[abi_decode_sim_def]) >>
 `alloca_inv (raw with vs_inst_idx := LENGTH sa.cs_current_insts) /\
  alloca_frontier_inv_from k ctx func site (raw with vs_inst_idx := LENGTH sa.cs_current_insts)` by
   (conj_tac >- fs[alloca_inv_def] >>
    irule deploy_ctor_alloca_frontier_fields >>
    goal_assum (drule_at Any) >> simp[]) >>
 drule compile_alloc_buffer_parts >> strip_tac >>
 qexists `raw with vs_inst_idx := LENGTH sa.cs_current_insts` >>
 asm_rewrite_tac[] >>
 `raw = update_var (STRING #"%" (toString st.cs_next_var))
   (n2w initial.vs_alloca_next)
   (initial with <| vs_allocas := initial.vs_allocas |+
     (st.cs_next_id,(initial.vs_alloca_next,n));
     vs_alloca_next := initial.vs_alloca_next+n |>)` by simp[Abbr `raw`] >>
 drule_all ctor_checked_alloc_buffer_edge >>
 disch_then (qspec_then `ctx` mp_tac) >>
 simp[Abbr `raw`, update_var_def] >>
 drule compile_alloc_buffer_insts >> simp[]
QED

Theorem ctor_checked_alloc_buffer_actual_from:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ local_ptrs_rel func ce scopes initial /\
 fresh_vars_wrt st initial /\ alloca_inv initial /\ alloca_history func initial /\
 alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?a. buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
   local_ptrs_rel func ce scopes a /\
   lookup_var (STRING #"%" (toString st.cs_next_var)) a =
     SOME (n2w initial.vs_alloca_next) /\
   local_backed func (STRING #"%" (toString st.cs_next_var)) a initial.vs_alloca_next n /\
   FLOOKUP a.vs_allocas st.cs_next_id = SOME (initial.vs_alloca_next,n) /\
   a.vs_alloca_next = initial.vs_alloca_next+n /\
   a.vs_alloca_next < dimword (:256) /\
   alloca_inv a /\ alloca_frontier_inv_from k ctx func site a /\
   fresh_vars_wrt sa a /\ not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
   (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
   (!name b sz. local_region ce scopes a name b sz ==>
     compileEnv$regions_disjoint initial.vs_alloca_next n b sz) /\
   a.vs_memory = initial.vs_memory /\
   a.vs_data_section = initial.vs_data_section /\
   a.vs_call_ctx = initial.vs_call_ctx /\ a.vs_labels = initial.vs_labels /\
   (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
     lookup_var x a = SOME w) /\
   abi_encoder_registered_effect (frag_ids st sa) [] initial a /\
   ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
   a.vs_inst_idx = LENGTH sa.cs_current_insts /\
   abi_decode_sim ctx func initial a /\
   gas_path_mem ctx func initial 0 (OK a) /\
   a.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func a
Proof
 strip_tac >>
 `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >>
 drule_all ctor_checked_alloc_buffer_run_from >> strip_tac >>
 `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
 `not_scope_ptr ce scopes (STRING #"%" (toString st.cs_next_var))` by
   (irule local_ptrs_rel_fresh_not_scope_ptr >>
    qexistsl [`func`, `initial`, `st`] >> simp[GREATER_EQ]) >>
 `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) initial (n2w n : bytes32) =
    OK (a with vs_inst_idx := initial.vs_inst_idx)` by
   gvs[exec_alloca_def, mk_inst_def, update_var_def, w2n_n2w,
       venom_state_component_equality] >>
 drule local_ptrs_rel_exec_alloca_fresh >> simp[mk_inst_def, IgnAsm `a = _`] >>
 disch_then (qspecl_then [`func`, `ce`, `scopes`] mp_tac) >>
 simp[local_ptrs_rel_inst_idx, IgnAsm `a = _`] >> strip_tac >>
 `w = n2w initial.vs_alloca_next` by metis_tac[n2w_w2n] >>
 drule compile_alloc_buffer_parts >> strip_tac >>
 qexists `a` >> asm_rewrite_tac[] >>
 simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
 conj_tac
 >- (simp[local_backed_def] >> disj1_tac >>
     qexists `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString st.cs_next_var)]` >>
     drule_all entry_alloc_buffer_inst >> gvs[mk_inst_def]) >>
 conj_tac
 >- (fs[fresh_vars_wrt_def, update_var_def, GREATER_EQ] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 conj_tac
 >- (rpt strip_tac >>
     qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
     fs[local_region_def, lookup_var_def, update_var_def] >> metis_tac[]) >>
 conj_tac
 >- (rpt strip_tac >> IF_CASES_TAC >> gvs[lookup_var_def]) >>
 simp[abi_encoder_registered_effect_def, frag_ids_def, GSPECIFICATION,
      update_var_def, FLOOKUP_UPDATE] >>
 rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED
