Theory makeSsaCurrentGraphDemand
Ancestors makeSsaCurrentStaticCuts makeSsaCurrentStaticSuffix
  makeSsaCurrentStaticDemandProbe makeSsaCurrentStaticGraph
  makeSsaCurrentSimDefs makeSsaCurrentDefs venomWf cfgWf venomExecSemantics list

Definition current_graph_seed_def:
  current_graph_seed fn fn' H c x y <=>
    current_graph_admissible fn fn' c /\ current_static_seed fn fn' H c x y
End

Inductive current_graph_demand:
  (!fn fn' H c x y. current_graph_seed fn fn' H c x y ==>
    current_graph_demand fn fn' H c x y) /\
  (!fn fn' H c d kind x y u v.
    current_graph_demand fn fn' H d x y /\ current_graph_edge fn fn' c d kind /\
    current_graph_back fn fn' c kind x y (CurrentStaticRead u) (CurrentStaticRead v) ==>
    current_graph_demand fn fn' H c u v)
End

Theorem current_graph_demand_admissible:
  !fn fn' H c x y. current_graph_demand fn fn' H c x y ==>
    current_graph_admissible fn fn' c
Proof
  ho_match_mp_tac current_graph_demand_ind >>
  simp[current_graph_seed_def] >> metis_tac[current_graph_edge_endpoints]
QED

Theorem current_graph_demand_least:
  (!c x y. current_graph_seed fn fn' H c x y ==> R c x y) /\
  (!c d kind x y u v. R d x y /\ current_graph_edge fn fn' c d kind /\
    current_graph_back fn fn' c kind x y (CurrentStaticRead u) (CurrentStaticRead v) ==>
    R c u v) ==>
  !c x y. current_graph_demand fn fn' H c x y ==> R c x y
Proof
  strip_tac >>
  qsuff_tac `!f g hist c x y. current_graph_demand f g hist c x y ==>
    f = fn /\ g = fn' /\ hist = H ==> R c x y`
  >- metis_tac[] >>
  ho_match_mp_tac current_graph_demand_ind >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_graph_demand_ordinary_seed:
  current_graph_edge fn fn' (CurrentStaticCut p h i j) d 2 /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
  MEM (x,y) (ZIP ((EL i old.bb_instructions).inst_operands,
                 (EL j out.bb_instructions).inst_operands)) ==>
  current_graph_demand fn fn' H (CurrentStaticCut p h i j) x y
Proof
  strip_tac >> irule (cj 1 current_graph_demand_rules) >>
  simp[current_graph_seed_def] >> conj_tac
  >- metis_tac[current_graph_edge_endpoints] >>
  simp[current_static_seed_def] >> metis_tac[current_graph_edge_def]
QED

Theorem current_graph_demand_copy_seed:
  current_graph_edge fn fn' (CurrentStaticCut p h i j) d 1 /\
  lookup_block h fn'.fn_blocks = SOME out /\
  (EL j out.bb_instructions).inst_opcode = ASSIGN /\
  (EL j out.bb_instructions).inst_outputs = [n] /\
  (EL j out.bb_instructions).inst_operands = [y] /\
  current_static_owner fn H h n v ==>
  current_graph_demand fn fn' H (CurrentStaticCut p h i j) (Var v) y
Proof
  strip_tac >> irule (cj 1 current_graph_demand_rules) >>
  simp[current_graph_seed_def] >> conj_tac
  >- metis_tac[current_graph_edge_endpoints] >>
  simp[current_static_seed_def] >> metis_tac[current_graph_edge_def]
QED

Theorem current_graph_demand_phi_seed:
  current_graph_admissible fn fn' (CurrentStaticCut p h 0 0) /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
  MEM inst (TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions) /\
  inst.inst_outputs = [n] /\ resolve_phi p inst.inst_operands = SOME y /\
  ((current_actual_inserted fn v h /\
    current_token_name H (CurrentInserted v h) = SOME n /\ x = Var v) \/
   (?i. i < phi_prefix_length old.bb_instructions /\
    current_token_name H (CurrentOriginal h i 0) = SOME n /\
    resolve_phi p (EL i old.bb_instructions).inst_operands = SOME x)) ==>
  current_graph_demand fn fn' H (CurrentStaticCut p h 0 0) x y
Proof
  strip_tac >> irule (cj 1 current_graph_demand_rules) >>
  simp[current_graph_seed_def, current_static_seed_def] >> metis_tac[]
QED

Theorem current_graph_demand_ordinary_coverage:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_graph_predecessor fn p h /\ lookup_block h fn.fn_blocks = SOME old /\
  phi_prefix_length old.bb_instructions <= i /\ i < LENGTH old.bb_instructions /\
  k < LENGTH (EL i old.bb_instructions).inst_operands ==>
  ?out. lookup_block h fn'.fn_blocks = SOME out /\
    k < LENGTH (EL (current_static_body_start old.bb_instructions out.bb_instructions +
      (i - phi_prefix_length old.bb_instructions)) out.bb_instructions).inst_operands /\
    current_graph_demand fn fn' H
      (CurrentStaticCut p h i (current_static_body_start old.bb_instructions out.bb_instructions +
        (i - phi_prefix_length old.bb_instructions)))
      (EL k (EL i old.bb_instructions).inst_operands)
      (EL k (EL (current_static_body_start old.bb_instructions out.bb_instructions +
        (i - phi_prefix_length old.bb_instructions)) out.bb_instructions).inst_operands)
Proof
  strip_tac >> drule_all current_graph_certificate_ordinary_fields >> strip_tac >>
  drule_all current_graph_certificate_ordinary_edge >> strip_tac >> gvs[] >>
  irule current_graph_demand_ordinary_seed >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`old`, `out`] >> simp[MEM_ZIP] >>
  qexists_tac `k` >> simp[]
QED

Theorem current_graph_demand_probe_copy:
  (p = "E" \/ p = "D") /\ current_static_owner current_probe_loop H "D" "v" "v" ==>
  current_graph_demand current_probe_loop
    (FST (make_ssa_current_fn current_probe_supply current_probe_loop)) H
    (CurrentStaticCut p "D" 1 1) (Var "v") (Var "formal_var_0")
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule current_graph_demand_copy_seed >>
  conj_tac >- metis_tac[current_graph_probe_arrival_return] >>
  qexistsl_tac [`"v"`, `THE (lookup_block "D"
    (FST (make_ssa_current_fn current_probe_supply current_probe_loop)).fn_blocks)`] >>
  simp[] >> EVAL_TAC
QED

Theorem current_graph_demand_probe_batch:
  (p = "E" \/ p = "D") /\ current_static_owner current_probe_loop H "D" "v" "v" ==>
  current_graph_demand current_probe_loop
    (FST (make_ssa_current_fn current_probe_supply current_probe_loop)) H
    (CurrentStaticCut p "D" 0 0)
    (Var (if p = "E" then "a" else "b"))
    (Var (if p = "E" then "a" else "b"))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_graph_demand_probe_copy >> strip_tac >>
  irule (cj 2 current_graph_demand_rules) >>
  qexistsl_tac [`CurrentStaticCut p "D" 1 1`, `0`, `Var "v"`, `Var "formal_var_0"`] >>
  simp[] >> conj_tac >- metis_tac[current_graph_probe_arrival_return] >>
  gvs[] >> simp[current_graph_back_def, current_graph_admissible_def] >>
  EVAL_TAC >> simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED
