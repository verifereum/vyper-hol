(* Shifted allocation at an explicit machine/ghost endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixEntryRegisterAlloc
Ancestors
  exprLoweringProps
  ctorDeployMemoryRunPtrPrefixRegisterAlloc ctorDeployLoweringEntryRegisterRun
  ctorDeployLoweringEntryAllocation actualAllocCredit actualAllocExec
  allocaFrontierBound allocaBudgetProps entryArgPtrs loweringHalt fragExec
  ctorAbiActualSites ctorRegisterArgs emitHelperProps moduleLowering compileEnv
  venomExecSemantics venomState venomInst finite_map words arithmetic
  vyperCompiler localPtrsProps ctorAbiActualArrayRun abiDecoderLoop
  ptrSafeRun ptrDiscipline pred_set ctorDeployMemoryRunPtrPrefixAllocationFloor
  ctorDeployMemoryRunMemEntryRegistration
  fragGasOriginPtr fragGasOriginPtrLoop memSafeRun unitTransformDefs contextCodegenRel codegenRel


Theorem prefix_entry_register_alloc_actual:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ alloca_inv initial /\
 alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp initial /\
    initial.vs_alloca_next + pending_alloca_size func initial <= w2n initial.vs_initial_fmp) ==>
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
 allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp initial /\
    initial.vs_alloca_next + pending_alloca_size func initial <= w2n initial.vs_initial_fmp) /\
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
 (ctx_has_dalloca ctx ==> allocas_below_fmp a /\
   a.vs_alloca_next + pending_alloca_size func a <= w2n a.vs_initial_fmp) /\
 ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
 a.vs_inst_idx = LENGTH sa.cs_current_insts /\ abi_decode_sim ctx func initial a /\
 a.vs_code = initial.vs_code /\ a.vs_outcomes = initial.vs_outcomes /\
 a.vs_tx_ctx = initial.vs_tx_ctx /\ a.vs_block_ctx = initial.vs_block_ctx /\
 a.vs_gas_readings = initial.vs_gas_readings /\
 (!j. j < lo ==> read_byte j a.vs_memory = read_byte j initial.vs_memory) /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H q a) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
 (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK a, H, q)) /\
 (checked ==> gas_path_mem ctx func initial 0 (OK a) /\ alloca_history func a)
Proof
 strip_tac >> drule_all prefix_entry_register_alloc_actual >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
 `(ctx_has_dalloca ctx ==> allocas_below_fmp a /\
   a.vs_alloca_next + pending_alloca_size func a <= w2n a.vs_initial_fmp)` by
   (strip_tac >>
    drule_all prefix_register_alloc_layout >> strip_tac >>
    qabbrev_tac `i = mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString st.cs_next_var)]` >>
    `MEM i (fn_insts func)` by
      (irule lookup_block_fn_insts >>
       qexistsl [`bb`,`initial.vs_current_bb`] >> asm_rewrite_tac[] >>
       qpat_assum `get_instruction bb _ = SOME _` mp_tac >>
       simp_tac bool_ss [Abbr `i`,get_instruction_def,AllCaseEqs(),optionTheory.SOME_11,optionTheory.NOT_NONE_SOME] >>
       strip_tac >> pure_rewrite_tac[listTheory.MEM_EL] >>
       qexists_tac `initial.vs_inst_idx` >> asm_rewrite_tac[]) >>
    qabbrev_tac `raw = update_var (STRING #"%" (toString st.cs_next_var))
      (n2w initial.vs_alloca_next)
      (initial with <|vs_allocas := initial.vs_allocas |+
        (st.cs_next_id,(initial.vs_alloca_next,n)); vs_alloca_next := initial.vs_alloca_next+n|>)` >>
    `exec_alloca i initial (n2w n:bytes32) = OK raw` by
      simp[Abbr `i`,Abbr `raw`,exec_alloca_def,mk_inst_def,wordsTheory.w2n_n2w,ADD_COMM] >>
    `raw.vs_alloca_next + pending_alloca_size func raw <=
     initial.vs_alloca_next + pending_alloca_size func initial` by
      (irule exec_alloca_static_charge >> qexistsl [`i`,`n2w n:bytes32`] >>
       simp[Abbr `i`]) >>
    `a.vs_alloca_next + pending_alloca_size func a =
      raw.vs_alloca_next + pending_alloca_size func raw` by
      simp[Abbr `raw`,update_var_def,pending_alloca_size_def] >>
    `a.vs_initial_fmp = initial.vs_initial_fmp` by simp[Abbr `raw`,update_var_def] >>
    `a.vs_alloca_next + pending_alloca_size func a <= w2n a.vs_initial_fmp` by
      (qpat_assum `ctx_has_dalloca ctx ==> _ /\ _`
         (fn room => qpat_assum `ctx_has_dalloca ctx`
           (mp_tac o CONJUNCT2 o MATCH_MP room)) >>
       qpat_assum `raw.vs_alloca_next + _ <= _` mp_tac >> asm_rewrite_tac[] >> decide_tac) >>
    conj_tac >-
      (`allocas_below_fmp initial` by simp[] >>
       `a.vs_alloca_next <= w2n a.vs_initial_fmp` by decide_tac >>
       fs[Abbr `raw`,allocas_below_fmp_def,update_var_def,FLOOKUP_UPDATE] >>
       rpt strip_tac >> Cases_on `aid = st.cs_next_id` >> gvs[] >> res_tac) >>
    first_assum ACCEPT_TAC) >>
 qexistsl [`a`,`H`,`q`] >> asm_rewrite_tac[] >>
 conj_tac >-
   (strip_tac >> qx_gen_tac `D'` >> gen_tac >>
    mp_tac (Q.INST [`s` |-> `initial`, `aid` |-> `st.cs_next_id`,
      `x` |-> `STRING #"%" (toString st.cs_next_var)`, `fuel` |-> `0`, `fn` |-> `func`, `D` |-> `D'`]
      prefix_register_alloc_pair) >>
    impl_tac >- simp[] >>
    pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
    drule_all prefix_register_alloc_layout >> strip_tac >>
    qpat_x_assum `LENGTH sa.cs_current_insts = _` SUBST1_TAC >>
    `(mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [STRING #"%" (toString st.cs_next_var)]).inst_opcode = ALLOCA` by simp[mk_inst_def] >>
    `inst_mem_below_frontier (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [STRING #"%" (toString st.cs_next_var)]) initial /\
     inst_dload_in_section (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [STRING #"%" (toString st.cs_next_var)]) initial` by
      simp[mk_inst_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
           source_memory_read_ranges_def, source_memory_write_ranges_def] >>
    irule (Q.INST [`s` |-> `initial`, `i` |-> `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [STRING #"%" (toString st.cs_next_var)]`] step_origin_ptr_path) >>
    asm_rewrite_tac[] >> qexistsl [`bb`, `n`, `st`] >>
    asm_simp_tac (srw_ss()) [step_inst_non_invoke, is_terminator_def] >> gvs[]) >>
 strip_tac >> metis_tac[ctor_checked_alloc_buffer_edge]
QED

val _ = export_theory();
