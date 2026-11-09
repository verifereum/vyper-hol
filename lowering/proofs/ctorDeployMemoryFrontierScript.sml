(* The memory, pointer and DLOAD invariants of a lowered unit whose run
 * starts with its alloca frontier at k rather than 0: the deployment unit
 * starts it above the immutables region, which it addresses as a fixed
 * region at offset 0.
 *
 * alloca_frontier_inv_from k is allocaFrontierBound's alloca_frontier_inv
 * with the budget raised by k, and is proved closed the same way.  The
 * other theorems take a unit that passed lowering_context_ok, with its
 * entry function, and give the S3 conjuncts the O1 pipeline's source
 * invariant asks for (o1_src_inv), from the run facts the unit's own
 * proofs provide: a memory-safe run, a pointer-safe run, and the
 * frontier's headroom.
 *
 * TOP-LEVEL:
 *   alloca_frontier_inv_from, alloca_frontier_inv_from_closed,
 *   alloca_frontier_inv_from_entry
 *   lowered_unit_raw_memory_ok_from, lowered_unit_dload_headroom_ok_from,
 *   lowered_unit_dload_offset_ok, lowered_unit_ptr_taint
 *   lowered_unit_entry_facts -- what lowering_context_ok gives the entry
 *   deploy_unit_run_entry -- the deployment unit's entry, at frontier
 *     imm_len
 *)
Theory ctorDeployMemoryFrontier
Ancestors
  allocaFrontierBound allocaBudgetProps contextCodegenRel
  contextCodegenRelProps fcgPostorder fcgCorrectnessProof fcgDefs
  vyperCompiler venomWf venomExecSemantics venomInst venomState
  memSafeRun ptrSafeRun ptrOkCheck ptrDiscipline unitMemInv
  unitTransformDefs lowerDloadDefs ctorDeployDefs deployUnitProducers
  o1PassContract
  finite_map list pred_set relation arithmetic

(* ===== The frontier from k ===== *)

Definition alloca_frontier_inv_from_def:
  alloca_frontier_inv_from k ctx fn (inst:instruction) s <=>
    lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
    (!g. TC (fn_directly_calls ctx) fn.fn_name g ==>
         ~TC (fn_directly_calls ctx) g g) /\
    s.vs_alloca_next + remaining_alloca_budget (fn_insts fn) s +
    CARD {g | TC (fn_directly_calls ctx) fn.fn_name g} *
      SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA)
        (FLAT (MAP fn_insts ctx.ctx_functions)))) <=
    k + unit_alloca_budget ctx
End

Theorem alloca_frontier_inv_from_step[local]:
  ctx_inst_ids_distinct ctx /\ alloca_frontier_inv_from k ctx fn inst s /\
  active_inst fn inst s /\ step_inst fuel ctx inst s = OK s' /\
  t.vs_allocas = s'.vs_allocas /\ t.vs_alloca_next = s'.vs_alloca_next ==>
  alloca_frontier_inv_from k ctx fn inst' t
Proof
  rpt strip_tac >> fs[alloca_frontier_inv_from_def] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule_all ctx_inst_ids_distinct_fn >> strip_tac >>
  drule_all step_inst_alloca_budget >> strip_tac >>
  `remaining_alloca_budget (fn_insts fn) t =
   remaining_alloca_budget (fn_insts fn) s'`
    by (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  decide_tac
QED

Theorem alloca_frontier_inv_from_callee_entry[local]:
  alloca_frontier_inv_from k ctx caller site s /\ active_inst caller site s /\
  site.inst_opcode = INVOKE /\ decode_invoke site = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  setup_callee callee args s = SOME cs ==>
  fn_entry_inv (alloca_frontier_inv_from k) ctx callee cs
Proof
  rw[fn_entry_inv_def] >>
  `fn_directly_calls ctx caller.fn_name nm` by
    (fs[fn_directly_calls_def, alloca_frontier_inv_from_def] >>
     qexistsl [`site`, `ops`] >>
     `site.inst_operands = Label nm :: ops` by
       (qpat_x_assum `decode_invoke _ = _` mp_tac >>
        rw[decode_invoke_def, AllCaseEqs()] >> gvs[]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `callee.fn_name = nm` by metis_tac[lookup_function_result_name] >>
  `MEM callee ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule enters_block_alloca_fields >> strip_tac >>
  `s1.vs_allocas = FEMPTY /\ s1.vs_alloca_next = s.vs_alloca_next`
    by gvs[setup_callee_def, AllCaseEqs()] >>
  gvs[alloca_frontier_inv_from_def] >>
  `~TC (fn_directly_calls ctx) callee.fn_name callee.fn_name`
    by metis_tac[TC_RULES] >>
  drule_all callee_targets_card_lt >> strip_tac >>
  conj_tac >- metis_tac[TC_RULES] >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  qmatch_asmsub_abbrev_tac `CARD below < CARD above` >>
  `remaining_alloca_budget (fn_insts callee) s1 <= frame`
    by simp[Abbr `frame`, remaining_alloca_budget_frame] >>
  `SUC (CARD below) * frame <= CARD above * frame`
    by (irule LESS_MONO_MULT >> simp[]) >>
  full_simp_tac bool_ss [MULT_CLAUSES] >> decide_tac
QED

Theorem alloca_frontier_inv_from_closed:
  ctx_inst_ids_distinct ctx ==>
  reachability_closed (alloca_frontier_inv_from k) ctx
Proof
  rw[reachability_closed_def]
  >- (irule alloca_frontier_inv_from_step >> simp[] >> metis_tac[])
  >- (drule enters_block_alloca_fields >> strip_tac >>
      irule alloca_frontier_inv_from_step >> simp[] >> metis_tac[])
  >> irule alloca_frontier_inv_from_callee_entry >> metis_tac[]
QED

(* From frontier k at the entry function's entry. *)
Theorem alloca_frontier_inv_from_entry:
  ctx_wf ctx /\ wf_invoke_targets ctx /\ reachable_call_graph_acyclic ctx /\
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  s.vs_alloca_next = k ==>
  fn_entry_inv (alloca_frontier_inv_from k) ctx fn s
Proof
  rw[fn_entry_inv_def] >>
  drule enters_block_alloca_fields >> strip_tac >>
  `fn.fn_name = name` by metis_tac[lookup_function_result_name] >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fcg_is_reachable (fcg_analyze ctx) name`
    by (irule fcg_analyze_reachable_complete_proof >>
        simp[fcg_path_def, ctx_fn_names_def] >>
        metis_tac[lookup_function_mem]) >>
  gvs[alloca_frontier_inv_from_def] >> conj_tac
  >- (rpt strip_tac >>
      `fcg_is_reachable (fcg_analyze ctx) g`
        by metis_tac[reachable_fcg_acyclic_tc_rank,
                     reachable_call_graph_acyclic_def] >>
      metis_tac[reachable_fcg_acyclic_no_reachable_cycle,
                reachable_call_graph_acyclic_def]) >>
  simp_tac bool_ss [unit_alloca_budget_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
                     (FLAT (MAP fn_insts ctx.ctx_functions)))` >>
  `remaining_alloca_budget (fn_insts fn) s1 <= frame /\ CARD below <= n`
    by simp[Abbr `below`, Abbr `frame`, Abbr `n`, call_targets_card,
            remaining_alloca_budget_frame] >>
  `CARD below * frame <= n * frame` by (irule LESS_MONO_MULT >> simp[]) >>
  full_simp_tac bool_ss [RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac
QED

(* ===== A unit that passed lowering_context_ok ===== *)

Theorem lowered_unit_entry_facts:
  lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn ==>
  ctx_wf ctx /\ wf_invoke_targets ctx /\ reachable_call_graph_acyclic ctx /\
  ctx_inst_ids_distinct ctx /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
  ALL_DISTINCT (fn_labels fn) /\
  ?lbl. fn_entry_label fn = SOME lbl
Proof
  strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  `MEM fn ctx.ctx_functions /\ fn.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_result_name] >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[EVERY_MEM] >>
  rpt conj_tac
  >- (simp[ctx_wf_def, ctx_has_entry_def] >>
      simp[ctx_fn_names_def, MEM_MAP] >> metis_tac[])
  >- simp[]
  >- simp[reachable_call_graph_acyclic_def]
  >- simp[]
  >- fs[EVERY_MEM]
  >- simp[] >>
  Cases_on `fn.fn_blocks` >>
  gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]
QED

(* Every reachable frontier, plus 32 bytes per DLOAD, stays below 2^256. *)
Theorem lowered_unit_dload_headroom_ok_from:
  !k ctx name fn vs.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    vs.vs_alloca_next = k /\
    k + unit_alloca_budget ctx + 32 * ctx_dload_count ctx < dimword (:256)
    ==> mem_inv dload_headroom_ok ctx vs
Proof
  rpt strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >>
  simp[mem_inv_def, codegen_reachability_package_def] >>
  qexists_tac `alloca_frontier_inv_from k` >> rpt conj_tac
  >- (irule alloca_frontier_inv_from_closed >> simp[])
  >- (irule alloca_frontier_inv_from_entry >> simp[] >> metis_tac[]) >>
  rw[dload_headroom_ok_def, alloca_frontier_inv_from_def] >>
  decide_tac
QED

(* raw_unit_memory_ok from a memory-safe run, with
   alloca_frontier_inv_from k as the frontier bound. *)
Theorem lowered_unit_raw_memory_ok_from:
  !k ctx name fn lbl vs.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    vs.vs_alloca_next = k /\ k + unit_alloca_budget ctx < dimword (:256) /\
    (!fuel. mem_safe_blocks fuel ctx fn
              (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                          vs_inst_idx := 0 |>))
    ==> raw_unit_memory_ok ctx vs
Proof
  rpt strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >> gvs[] >>
  qspecl_then [`ctx`, `vs`, `name`, `fn`, `lbl`,
               `alloca_frontier_inv_from vs.vs_alloca_next`] mp_tac
    mem_safe_raw_unit_memory_ok >>
  disch_then irule >> simp[] >> rpt conj_tac
  >~ [`reachability_closed _ _`]
  >- (irule alloca_frontier_inv_from_closed >> simp[])
  >~ [`fn_entry_inv _ _ _ _`]
  >- (irule alloca_frontier_inv_from_entry >> simp[] >> metis_tac[]) >>
  rw[alloca_frontier_inv_from_def] >> decide_tac
QED

(* Every reachable DLOAD/DLOADBYTES offset, added to the length of the code
   before the data section, stays below 2^256: the memory-safe run checks
   that each offset is at most the data section's length
   (inst_dload_in_section), the code and the data section never change, and
   code_layout_valid keeps the code within 2^255 bytes. *)
Theorem lowered_unit_dload_offset_ok:
  !ctx name fn lbl vs.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\ code_layout_valid vs /\
    (!fuel. mem_safe_blocks fuel ctx fn
              (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                          vs_inst_idx := 0 |>))
    ==> mem_inv dload_offset_ok ctx vs
Proof
  rpt strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >> gvs[] >>
  rewrite_tac[mem_inv_def, codegen_reachability_package_def] >>
  qexists_tac `\c f i s. mem_safe_point c f i s /\
                         s.vs_code = vs.vs_code /\
                         s.vs_data_section = vs.vs_data_section` >>
  rpt conj_tac
  >- (qspecl_then [`mem_safe_point`,
        `\c f i s. s.vs_code = vs.vs_code /\
                   s.vs_data_section = vs.vs_data_section`,
        `ctx`] mp_tac reachability_closed_conj >>
      simp[mem_safe_point_closed, code_data_closed])
  >- (qexistsl [`name`, `fn`, `lbl`] >> simp[] >>
      qspecl_then [`mem_safe_point`,
        `\c f i s. s.vs_code = vs.vs_code /\
                   s.vs_data_section = vs.vs_data_section`,
        `ctx`, `fn`,
        `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>`] mp_tac fn_entry_inv_conj >>
      impl_tac >- (
        conj_tac >- (irule mem_safe_point_entry >> simp[]) >>
        qspecl_then [`ctx`, `fn`,
          `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                      vs_inst_idx := 0 |>`] mp_tac code_data_entry >>
        simp[]) >>
      simp[]) >>
  rw[dload_offset_ok_def] >>
  `inst_dload_in_section inst s` by metis_tac[mem_safe_point_dload] >>
  `w2n off <= LENGTH s.vs_data_section` by
    (fs[inst_dload_in_section_def] >> metis_tac[]) >>
  gvs[code_layout_valid_def, wordsTheory.dimword_def]
QED

(* The pointer discipline and taint bound from a pointer-safe run, with
   the pointer parameters ptr_ok_check (in lowering_context_ok) finds. *)
Theorem lowered_unit_ptr_taint:
  !D lo ctx name fn lbl vs.
    lowering_context_ok ctx /\ ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\ lo <= vs.vs_alloca_next /\
    ~ctx_has_dalloca ctx /\
    (!fuel. ptr_safe_blocks D lo fuel ctx fn [] FEMPTY entry_taint
              (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                          vs_inst_idx := 0 |>))
    ==> ptr_discipline lo ctx vs /\ taint_within D ctx vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >> gvs[] >>
  `ptr_ok_check ctx` by fs[lowering_context_ok_def] >>
  drule_all ptr_ok_check_sound >> strip_tac >>
  qspecl_then [`D`, `lo`, `\nm. set (ctx_ptr_param_list ctx nm)`, `ctx`,
               `vs`, `name`, `fn`, `lbl`] mp_tac ptr_safe_ptr_discipline >>
  disch_then irule >> fs[EVERY_MEM]
QED

(* ===== The deployment unit ===== *)

(* The deployment unit passed lowering_context_ok, its entry is __deploy,
   and its run starts with the alloca frontier at imm_len. *)
Theorem deploy_unit_run_entry:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    gas_variant vs (deploy_entry_state prog cplan tops es)
    ==>
    lowering_context_ok dunit.cu_context /\
    dunit.cu_context.ctx_entry = SOME "__deploy" /\
    vs.vs_alloca_next = imm_len tops /\
    ?fn lbl. lookup_function "__deploy" dunit.cu_context.ctx_functions =
               SOME fn /\
             fn_entry_label fn = SOME lbl
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >>
  simp[] >>
  qpat_x_assum `gas_variant _ _` mp_tac >> simp[gas_variant_def] >>
  disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_alloca_next``) >>
  simp[deploy_entry_state_def]
QED
