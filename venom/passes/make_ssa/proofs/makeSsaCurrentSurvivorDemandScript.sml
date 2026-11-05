Theory makeSsaCurrentSurvivorDemand
Ancestors makeSsaCurrentDemand makeSsaCurrentDemandDominance venomWf venomExecProps
  venomInst list

(* Semantic demands cross unwritten slots even if a slot mentions v as a
   PHI operand. This deliberately does not transport Python liveness. *)
Theorem current_demand_unwritten_interval:
  !k j. lookup_block h fn.fn_blocks = SOME bb /\
    j <= k /\ k <= LENGTH bb.bb_instructions /\
    current_demand fn v h k /\
    (!i. j <= i /\ i < k ==> ~MEM v (inst_defs (EL i bb.bb_instructions))) ==>
    current_demand fn v h j
Proof
  Induct >- (rpt strip_tac >> `j = 0` by decide_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `j = SUC k` >- gvs[] >>
  `j <= k /\ k < LENGTH bb.bb_instructions` by decide_tac >>
  `current_demand fn v h k` by
    (irule (cj 3 current_demand_rules) >> simp[] >>
     qexists_tac `bb` >> simp[] >> first_x_assum irule >> simp[]) >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem current_demand_unwritten_prefix:
  lookup_block h fn.fn_blocks = SOME bb /\
  k <= LENGTH bb.bb_instructions /\ current_demand fn v h k /\
  (!i. i < k ==> ~MEM v (inst_defs (EL i bb.bb_instructions))) ==>
  current_demand fn v h 0
Proof
  strip_tac >> irule current_demand_unwritten_interval >>
  qexistsl_tac [`bb`, `k`] >> simp[]
QED

Theorem current_demand_unwritten_edge:
  wf_function fn /\ lookup_block h fn.fn_blocks = SOME bb /\
  lookup_block p fn.fn_blocks = SOME pred /\ fn_cfg_edge fn p h /\
  k <= LENGTH bb.bb_instructions /\ current_demand fn v h k /\
  (!i. i < k ==> ~MEM v (inst_defs (EL i bb.bb_instructions))) ==>
  current_demand fn v p (LENGTH pred.bb_instructions)
Proof
  strip_tac >>
  `current_demand fn v h 0` by metis_tac[current_demand_unwritten_prefix] >>
  `MEM h (bb_succs pred)` by
    (gvs[fn_cfg_edge_def] >> metis_tac[MEM_lookup_block, optionTheory.SOME_11,
       wf_function_def, fn_labels_def]) >>
  metis_tac[current_demand_rules]
QED

Theorem current_live_post_phi_unwritten_edge_demand:
  wf_function fn /\ fn_inst_wf fn /\
  lookup_block h fn.fn_blocks = SOME bb /\
  lookup_block p fn.fn_blocks = SOME pred /\ fn_cfg_edge fn p h /\
  MEM v (live_vars_at (liveness_analyze fn) h
    (LENGTH (collect_phis bb.bb_instructions))) /\
  (!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_defs (EL i bb.bb_instructions))) ==>
  current_demand fn v p (LENGTH pred.bb_instructions)
Proof
  strip_tac >> irule current_demand_unwritten_edge >> simp[] >>
  qexistsl_tac [`bb`, `h`, `LENGTH (collect_phis bb.bb_instructions)`] >>
  simp[current_collect_phis_length] >>
  irule current_live_post_phi_demand >> simp[current_collect_phis_length]
QED
