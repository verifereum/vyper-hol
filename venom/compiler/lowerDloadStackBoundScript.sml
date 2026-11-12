(* Live-stack static bounds for configured LowerDload. *)
Theory lowerDloadStackBound
Ancestors
  lowerDloadReachability lowerDloadDefs fcgBridge fcgDefs
  venomFnScheduleRunner o1PassContract venomInstProofs venomInst venomExecSemantics contextCodegenRel o1PassLift list

Theorem ld_stack_context_members:
  !vs C stk fn s0. ld_stack_origin vs C stk fn s0 ==>
    EVERY (\g. MEM g C.ctx_functions) (fn :: MAP (\f. f.cf_fn) stk)
Proof
  ho_match_mp_tac ld_stack_origin_ind >> rpt strip_tac >>
  gvs[] >> metis_tac[lookup_function_MEM]
QED

Theorem ld_active_invoke_target:
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) ==>
  MEM nm (fn_invoke_targets fn)
Proof
  simp[fn_invoke_targets_def, fcg_scan_function_def,
       mem_get_invoke_targets, active_inst_def, decode_invoke_def,
       AllCaseEqs()] >> rpt strip_tac >>
  qexists_tac `inst` >> simp[] >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >>
  qexists_tac `bb` >> simp[] >>
  metis_tac[MEM_EL]
QED

Theorem ld_precedes_trans[local]:
  list_precedes x y names /\ list_precedes y z names ==>
  list_precedes x z names
Proof
  simp[list_precedes_iff] >> rpt strip_tac >>
  gvs[] >> metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem ld_stack_order:
  !vs C stk fn s0. ld_stack_origin vs C stk fn s0 ==>
    !names. callee_first names C.ctx_functions ==>
      EVERY (\g. MEM g C.ctx_functions) (fn :: MAP (\f. f.cf_fn) stk) /\
      ALL_DISTINCT (fn.fn_name :: MAP (\f. f.cf_fn.fn_name) stk) /\
      EVERY (\nm. list_precedes fn.fn_name nm names)
        (MAP (\f. f.cf_fn.fn_name) stk)
Proof
  ho_match_mp_tac ld_stack_origin_ind >> rpt conj_tac
  >- (simp[] >> metis_tac[lookup_function_MEM]) >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
  first_x_assum (qspec_then `names` mp_tac) >> simp[] >> strip_tac >>
  `active_inst f.cf_fn f.cf_inst f.cf_state` by
    metis_tac[frame_reach_active] >>
  `MEM nm (fn_invoke_targets f.cf_fn)` by
    metis_tac[ld_active_invoke_target] >>
  `callee.fn_name = nm` by
    (qpat_x_assum `lookup_function nm _ = SOME callee` mp_tac >>
     qid_spec_tac `callee` >>
     qspec_tac (`C.ctx_functions`, `fns`) >>
     Induct_on `fns` >> simp[lookup_function_def, FIND_thm] >>
     rpt gen_tac >> Cases_on `h.fn_name = nm` >>
     gvs[lookup_function_def]) >>
  `list_precedes callee.fn_name f.cf_fn.fn_name names` by
    metis_tac[callee_first_def] >>
  `MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `!x. ~list_precedes x x names` by simp[list_precedes_iff] >>
  qpat_x_assum `EVERY (\nm. list_precedes _ nm names) _` mp_tac >>
  simp[EVERY_MEM] >> strip_tac >>
  conj_tac
  >- metis_tac[ld_precedes_trans] >>
  metis_tac[ld_precedes_trans]
QED

Theorem ld_sum_filter_le:
  !xs. SUM (MAP (w:'a -> num) (FILTER P xs)) <= SUM (MAP w xs)
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `P h` >> simp[]
QED

Theorem ld_sum_remove_member:
  !xs. MEM x xs ==>
    w x + SUM (MAP (w:'a -> num) (FILTER (\y. y <> x) xs)) <=
      SUM (MAP w xs)
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `h = x` >> simp[]
  >- simp[ld_sum_filter_le] >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem ld_weighted_subset_bound:
  !xs ys. ALL_DISTINCT xs /\ (!x. MEM x xs ==> MEM x ys) ==>
    SUM (MAP (w:'a -> num) xs) <= SUM (MAP w ys)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `FILTER (\y. y <> h) ys` mp_tac) >>
  simp[MEM_FILTER] >> strip_tac >>
  `MEM h ys` by metis_tac[] >>
  drule ld_sum_remove_member >>
  disch_then (qspec_then `w` mp_tac) >> decide_tac
QED

Theorem ld_stack_distinct_functions:
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 ==>
  ALL_DISTINCT (fn :: MAP (\f. f.cf_fn) stk)
Proof
  strip_tac >> irule (INST_TYPE [beta |-> ``:string``] ALL_DISTINCT_MAP) >>
  qexists_tac `\g. g.fn_name` >> simp[MAP_COMPOSE, combinTheory.o_DEF] >>
  drule ld_stack_order >>
  disch_then (qspec_then `names` mp_tac) >> simp[]
QED

Theorem ld_stack_dload_count_bound:
  callee_first names C.ctx_functions /\ ld_stack_origin vs C stk fn s0 ==>
  SUM (MAP (\g. LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
       (fn :: MAP (\f. f.cf_fn) stk)) <= ctx_dload_count C
Proof
  strip_tac >>
  `ALL_DISTINCT (fn :: MAP (\f. f.cf_fn) stk)` by
    metis_tac[ld_stack_distinct_functions] >>
  drule ld_stack_context_members >> rewrite_tac[EVERY_MEM] >> strip_tac >>
  pure_rewrite_tac[ctx_dload_count_def] >>
  irule ld_weighted_subset_bound >> simp[] >> metis_tac[MEM]
QED
