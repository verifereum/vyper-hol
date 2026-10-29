(* The alloca frontier stays below 2**256 across internal calls.

   A frame allocates each of its function's ALLOCA sites at most once, and a
   returning INVOKE gives the caller its frontier back, so the frontier is at
   most one static frame per function on the current call chain.  On an
   acyclic call graph those functions are distinct call targets, of which
   there are at most as many as INVOKE sites; unit_alloca_budget charges one
   frame per INVOKE site plus the entry frame.

   alloca_frontier_inv is closed under the three reachability steps
   (reachability_closed), holds at the entry of the entry function from
   frontier 0, and implies the bound; all three are generic in ctx. *)
Theory allocaFrontierBound
Ancestors
  allocaBudgetProps contextCodegenRel fcgPostorder fcgCorrectnessProof
  fcgDefs vyperCompiler venomWf venomExecSemantics venomExecProofs
  venomInstProofs1 venomState venomInst
  finite_map list pred_set relation arithmetic

(* Every frame charged at the unit's whole static ALLOCA size bounds what one
   frame can still allocate (remaining_alloca_budget_le,
   static_alloca_function_le).  Each transitive callee of fn is charged one
   frame: none is on a call cycle, so each has at most one frame on any call
   chain below fn. *)
Definition alloca_frontier_inv_def:
  alloca_frontier_inv ctx fn (inst:instruction) s <=>
    lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
    (!g. TC (fn_directly_calls ctx) fn.fn_name g ==>
         ~TC (fn_directly_calls ctx) g g) /\
    s.vs_alloca_next + remaining_alloca_budget (fn_insts fn) s +
    CARD {g | TC (fn_directly_calls ctx) fn.fn_name g} *
      SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA)
        (FLAT (MAP fn_insts ctx.ctx_functions)))) <=
    unit_alloca_budget ctx
End

(* ===== Call targets ===== *)

(* Every transitive call target is the label of some INVOKE in the unit. *)
Theorem call_targets_card:
  FINITE {g | TC (fn_directly_calls ctx) a g} /\
  CARD {g | TC (fn_directly_calls ctx) a g} <=
    LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
      (FLAT (MAP fn_insts ctx.ctx_functions)))
Proof
  qabbrev_tac `invs = FILTER (\i. i.inst_opcode = INVOKE)
                        (FLAT (MAP fn_insts ctx.ctx_functions))` >>
  qabbrev_tac `targets = IMAGE (\i. case i.inst_operands of
                                       Label l :: _ => l
                                     | _ => ARB) (set invs)` >>
  `{g | TC (fn_directly_calls ctx) a g} SUBSET targets` by
    (rw[SUBSET_DEF] >>
     `?b. fn_directly_calls ctx b x` by metis_tac[TC_CASES2] >>
     gvs[fn_directly_calls_def] >>
     simp[Abbr `targets`, Abbr `invs`, MEM_FILTER, MEM_FLAT, MEM_MAP] >>
     qexists `inst` >> simp[] >>
     metis_tac[lookup_function_MEM]) >>
  `FINITE targets` by simp[Abbr `targets`] >>
  conj_tac >- metis_tac[SUBSET_FINITE] >>
  irule LESS_EQ_TRANS >> qexists `CARD targets` >>
  conj_tac >- (irule CARD_SUBSET >> simp[]) >>
  irule LESS_EQ_TRANS >> qexists `CARD (set invs)` >>
  simp[Abbr `targets`, CARD_IMAGE, CARD_LIST_TO_SET]
QED

(* Entering a callee off any cycle drops it from the pending targets. *)
Theorem callee_targets_card_lt:
  fn_directly_calls ctx a b /\ ~TC (fn_directly_calls ctx) b b ==>
  CARD {g | TC (fn_directly_calls ctx) b g} <
  CARD {g | TC (fn_directly_calls ctx) a g}
Proof
  strip_tac >> irule CARD_PSUBSET >>
  simp[call_targets_card, PSUBSET_MEMBER, SUBSET_DEF] >>
  metis_tac[TC_RULES]
QED

(* ===== Frame accounting across steps ===== *)

Theorem mem_fn_insts_blocks[local]:
  !bbs bb i. MEM bb bbs /\ MEM i bb.bb_instructions ==>
             MEM i (fn_insts_blocks bbs)
Proof
  Induct >> rw[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem active_inst_mem_fn_insts:
  active_inst fn inst s ==> MEM inst (fn_insts fn)
Proof
  rw[active_inst_def, fn_insts_def] >> irule mem_fn_insts_blocks >>
  metis_tac[EL_MEM]
QED

Theorem all_distinct_flat_mem[local]:
  !ls l. ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> rw[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem fn_insts_blocks_inst_ids[local]:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
        FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem ctx_inst_ids_distinct_fn:
  ctx_inst_ids_distinct ctx /\ MEM fn ctx.ctx_functions ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  rw[ctx_inst_ids_distinct_def] >> irule all_distinct_flat_mem >>
  first_x_assum (irule_at Any) >>
  simp[fn_insts_def, fn_insts_blocks_inst_ids, MEM_MAP] >>
  metis_tac[]
QED

Theorem enters_block_alloca_fields:
  enters_block fn s s1 ==>
  s1.vs_allocas = s.vs_allocas /\ s1.vs_alloca_next = s.vs_alloca_next
Proof
  rw[enters_block_def] >> drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem bind_outputs_alloca_fields[local]:
  bind_outputs outs vals t = SOME t' ==>
  t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `(\r:venom_state. (r.vs_allocas, r.vs_alloca_next)) t' =
   (\r:venom_state. (r.vs_allocas, r.vs_alloca_next)) t`
    suffices_by simp[] >>
  irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]
QED

Theorem adopt_return_fmp_alloca_next[local]:
  (adopt_return_fmp ir s).vs_alloca_next = s.vs_alloca_next
Proof
  Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

(* A returning INVOKE leaves the caller's frame as it was. *)
Theorem step_inst_invoke_alloca_fields:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  gvs[Once step_inst_def, AllCaseEqs()] >>
  drule bind_outputs_alloca_fields >>
  simp[adopt_return_fmp_alloca_next, merge_callee_state_def]
QED

Theorem step_inst_alloca_budget:
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\ MEM inst insts /\
  step_inst fuel ctx inst s = OK s' ==>
  s'.vs_alloca_next + remaining_alloca_budget insts s' =
  s.vs_alloca_next + remaining_alloca_budget insts s
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_alloca_fields >> strip_tac >>
      `remaining_alloca_budget insts s' = remaining_alloca_budget insts s`
        by (irule remaining_alloca_budget_domain_cong >> simp[]) >>
      simp[]) >>
  gvs[step_inst_non_invoke] >>
  drule_all step_inst_base_alloca_budget >> simp[]
QED

Theorem remaining_alloca_budget_frame:
  MEM func ctx.ctx_functions ==>
  remaining_alloca_budget (fn_insts func) s <=
    SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA)
      (FLAT (MAP fn_insts ctx.ctx_functions))))
Proof
  metis_tac[LESS_EQ_TRANS, remaining_alloca_budget_le,
            static_alloca_function_le]
QED

Theorem frame_charge_le[local]:
  r <= f /\ b < a ==> r + b * f <= a * f
Proof
  strip_tac >>
  `SUC b * f <= a * f` by (irule LESS_MONO_MULT >> simp[]) >>
  full_simp_tac bool_ss [MULT_CLAUSES] >> decide_tac
QED

Theorem frame_entry_le[local]:
  r <= f /\ b <= n ==> r + b * f <= (1 + n) * f
Proof
  strip_tac >>
  `b * f <= n * f` by (irule LESS_MONO_MULT >> simp[]) >>
  full_simp_tac bool_ss [RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac
QED

(* ===== The invariant ===== *)

Theorem alloca_frontier_inv_step[local]:
  ctx_inst_ids_distinct ctx /\ alloca_frontier_inv ctx fn inst s /\
  active_inst fn inst s /\ step_inst fuel ctx inst s = OK s' /\
  t.vs_allocas = s'.vs_allocas /\ t.vs_alloca_next = s'.vs_alloca_next ==>
  alloca_frontier_inv ctx fn inst' t
Proof
  rpt strip_tac >> fs[alloca_frontier_inv_def] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule_all ctx_inst_ids_distinct_fn >> strip_tac >>
  drule_all step_inst_alloca_budget >> strip_tac >>
  `remaining_alloca_budget (fn_insts fn) t =
   remaining_alloca_budget (fn_insts fn) s'`
    by (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  decide_tac
QED

Theorem decode_invoke_operands[local]:
  decode_invoke inst = SOME (nm, ops) ==> inst.inst_operands = Label nm :: ops
Proof
  rw[decode_invoke_def, AllCaseEqs()] >> gvs[]
QED

Theorem invoke_directly_calls[local]:
  alloca_frontier_inv ctx caller site s /\ active_inst caller site s /\
  site.inst_opcode = INVOKE /\ decode_invoke site = SOME (nm, ops) ==>
  fn_directly_calls ctx caller.fn_name nm
Proof
  rw[fn_directly_calls_def, alloca_frontier_inv_def] >>
  qexistsl [`site`, `ops`] >>
  metis_tac[active_inst_mem_fn_insts, decode_invoke_operands]
QED

Theorem alloca_frontier_inv_callee_entry[local]:
  alloca_frontier_inv ctx caller site s /\ active_inst caller site s /\
  site.inst_opcode = INVOKE /\ decode_invoke site = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  setup_callee callee args s = SOME cs ==>
  fn_entry_inv alloca_frontier_inv ctx callee cs
Proof
  rw[fn_entry_inv_def] >>
  drule_all invoke_directly_calls >> strip_tac >>
  `callee.fn_name = nm` by metis_tac[lookup_function_result_name] >>
  `MEM callee ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule enters_block_alloca_fields >> strip_tac >>
  `s1.vs_allocas = FEMPTY /\ s1.vs_alloca_next = s.vs_alloca_next`
    by gvs[setup_callee_def, AllCaseEqs()] >>
  gvs[alloca_frontier_inv_def] >>
  `~TC (fn_directly_calls ctx) callee.fn_name callee.fn_name`
    by metis_tac[TC_RULES] >>
  drule_all callee_targets_card_lt >> strip_tac >>
  conj_tac >- metis_tac[TC_RULES] >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  qmatch_asmsub_abbrev_tac `CARD below < CARD above` >>
  `remaining_alloca_budget (fn_insts callee) s1 <= frame`
    by simp[Abbr `frame`, remaining_alloca_budget_frame] >>
  `remaining_alloca_budget (fn_insts callee) s1 + CARD below * frame <=
   CARD above * frame` by (irule frame_charge_le >> fs[]) >>
  decide_tac
QED

Theorem alloca_frontier_inv_closed:
  ctx_inst_ids_distinct ctx ==>
  reachability_closed alloca_frontier_inv ctx
Proof
  rw[reachability_closed_def]
  >- (irule alloca_frontier_inv_step >> simp[] >> metis_tac[])
  >- (drule enters_block_alloca_fields >> strip_tac >>
      irule alloca_frontier_inv_step >> simp[] >> metis_tac[])
  >> irule alloca_frontier_inv_callee_entry >> metis_tac[]
QED

(* From frontier 0 at the entry function's entry. *)
Theorem alloca_frontier_inv_entry:
  ctx_wf ctx /\ wf_invoke_targets ctx /\ reachable_call_graph_acyclic ctx /\
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  s.vs_alloca_next = 0 ==>
  fn_entry_inv alloca_frontier_inv ctx fn s
Proof
  rw[fn_entry_inv_def] >>
  drule enters_block_alloca_fields >> strip_tac >>
  `fn.fn_name = name` by metis_tac[lookup_function_result_name] >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fcg_is_reachable (fcg_analyze ctx) name`
    by (irule fcg_analyze_reachable_complete_proof >>
        simp[fcg_path_def, ctx_fn_names_def] >>
        metis_tac[lookup_function_mem]) >>
  gvs[alloca_frontier_inv_def] >> conj_tac
  >- (rpt strip_tac >>
      `fcg_is_reachable (fcg_analyze ctx) g`
        by metis_tac[reachable_fcg_acyclic_tc_rank,
                     reachable_call_graph_acyclic_def] >>
      metis_tac[reachable_fcg_acyclic_no_reachable_cycle,
                reachable_call_graph_acyclic_def]) >>
  simp_tac bool_ss [unit_alloca_budget_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  `remaining_alloca_budget (fn_insts fn) s1 + CARD below * frame <=
   (1 + LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
          (FLAT (MAP fn_insts ctx.ctx_functions)))) * frame`
    by (irule frame_entry_le >>
        simp[Abbr `below`, Abbr `frame`, call_targets_card,
             remaining_alloca_budget_frame]) >>
  decide_tac
QED

Theorem alloca_frontier_inv_bound:
  alloca_frontier_inv ctx fn inst s /\
  unit_alloca_budget ctx < dimword (:256) ==>
  s.vs_alloca_next < dimword (:256)
Proof
  rw[alloca_frontier_inv_def] >> decide_tac
QED
