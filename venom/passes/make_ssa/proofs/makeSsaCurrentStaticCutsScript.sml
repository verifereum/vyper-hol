Theory makeSsaCurrentStaticCuts
Ancestors makeSsaCurrentStaticSuffix makeSsaCurrentStaticGraph
  makeSsaCurrentStaticDemandProbe makeSsaCurrentSimDefs makeSsaCurrentDefs
  venomWf cfgWf venomExecSemantics list

Definition current_graph_predecessor_def:
  current_graph_predecessor fn p h <=>
    fn_cfg_edge fn p h \/
    (?eb. entry_block fn = SOME eb /\ eb.bb_label = h)
End

Definition current_graph_admissible_def:
  current_graph_admissible fn fn' c <=>
    ?p h i j old out. c = CurrentStaticCut p h i j /\
      current_graph_predecessor fn p h /\
      lookup_block h fn.fn_blocks = SOME old /\
      lookup_block h fn'.fn_blocks = SOME out /\
      ((i = 0 /\ j = 0) \/
       (i = phi_prefix_length old.bb_instructions /\
        phi_prefix_length out.bb_instructions <= j /\
        j <= current_static_body_start old.bb_instructions out.bb_instructions) \/
       (phi_prefix_length old.bb_instructions <= i /\ i <= LENGTH old.bb_instructions /\
        j = current_static_body_start old.bb_instructions out.bb_instructions +
          (i - phi_prefix_length old.bb_instructions)))
End

Definition current_graph_edge_def:
  current_graph_edge fn fn' c d kind <=>
    current_static_edge fn fn' c d kind /\
    current_graph_admissible fn fn' c /\ current_graph_admissible fn fn' d
End

Definition current_graph_back_def:
  current_graph_back fn fn' c kind x y a b <=>
    current_graph_admissible fn fn' c /\
    ?p h i j old out. c = CurrentStaticCut p h i j /\
      lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
      ((kind = 0 /\
        current_static_phi_subst p
          (TAKE (phi_prefix_length old.bb_instructions) old.bb_instructions) x = SOME a /\
        current_static_phi_subst p
          (TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions) y = SOME b) \/
       (kind = 1 /\ a = CurrentStaticRead x /\
        current_static_copy_subst (EL j out.bb_instructions) y = SOME b) \/
       (kind = 2 /\ a = current_graph_inst_subst (EL i old.bb_instructions) x /\
                    b = current_graph_inst_subst (EL j out.bb_instructions) y) \/
       (kind = 3 /\ a = CurrentStaticRead x /\ b = CurrentStaticRead y))
End

Theorem current_graph_edge_endpoints:
  current_graph_edge fn fn' c d kind ==>
  current_graph_admissible fn fn' c /\ current_graph_admissible fn fn' d
Proof
  simp[current_graph_edge_def]
QED

Theorem current_graph_cleanup_bound:
  current_graph_edge fn fn' (CurrentStaticCut p h i j) d 1 /\
  lookup_block h fn'.fn_blocks = SOME out ==>
  j < LENGTH out.bb_instructions
Proof
  simp[current_graph_edge_def, current_static_edge_def] >> rpt strip_tac >>
  gvs[current_static_body_start_def] >> decide_tac
QED

Theorem current_graph_ordinary_bounds:
  current_graph_edge fn fn' (CurrentStaticCut p h i j) d 2 /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h fn'.fn_blocks = SOME out ==>
  i < LENGTH old.bb_instructions /\ j < LENGTH out.bb_instructions
Proof
  simp[current_graph_edge_def, current_static_edge_def] >> rpt strip_tac >> gvs[]
QED

Theorem current_graph_transfer_predecessor:
  current_graph_edge fn fn' c (CurrentStaticCut p h i j) 3 ==>
  fn_cfg_edge fn p h /\ i = 0 /\ j = 0 /\ current_graph_predecessor fn p h
Proof
  simp[current_graph_edge_def, current_static_edge_def] >> rpt strip_tac >>
  gvs[current_graph_predecessor_def]
QED

Theorem current_graph_entry_predecessor:
  entry_block fn = SOME eb ==>
  current_graph_predecessor fn p eb.bb_label
Proof
  simp[current_graph_predecessor_def]
QED

Theorem current_graph_ordinary_cut:
  current_graph_predecessor fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h fn'.fn_blocks = SOME out /\
  phi_prefix_length old.bb_instructions <= i /\ i <= LENGTH old.bb_instructions /\
  j = current_static_body_start old.bb_instructions out.bb_instructions +
    (i - phi_prefix_length old.bb_instructions) ==>
  current_graph_admissible fn fn' (CurrentStaticCut p h i j)
Proof
  simp[current_graph_admissible_def] >> metis_tac[]
QED

Theorem current_graph_ordinary_edge:
  current_graph_predecessor fn p h /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h fn'.fn_blocks = SOME out /\
  phi_prefix_length old.bb_instructions <= i /\ i < LENGTH old.bb_instructions /\
  j = current_static_body_start old.bb_instructions out.bb_instructions +
    (i - phi_prefix_length old.bb_instructions) /\ j < LENGTH out.bb_instructions ==>
  current_graph_edge fn fn' (CurrentStaticCut p h i j)
    (CurrentStaticCut p h (SUC i) (SUC j)) 2
Proof
  strip_tac >> rewrite_tac[current_graph_edge_def] >> conj_tac
  >- (simp[current_static_edge_def] >> metis_tac[]) >>
  conj_tac >> irule current_graph_ordinary_cut >>
  goal_assum $ drule_at Any >> simp[] >> decide_tac
QED

Theorem current_graph_certificate_ordinary_edge:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_graph_predecessor fn p h /\ lookup_block h fn.fn_blocks = SOME old /\
  phi_prefix_length old.bb_instructions <= i /\ i < LENGTH old.bb_instructions ==>
  ?out. lookup_block h fn'.fn_blocks = SOME out /\
    current_graph_edge fn fn'
      (CurrentStaticCut p h i (current_static_body_start old.bb_instructions out.bb_instructions +
        (i - phi_prefix_length old.bb_instructions)))
      (CurrentStaticCut p h (SUC i) (SUC (current_static_body_start old.bb_instructions out.bb_instructions +
        (i - phi_prefix_length old.bb_instructions)))) 2
Proof
  strip_tac >> drule_all current_graph_certificate_ordinary_fields >> strip_tac >>
  qexists_tac `out` >> simp[] >> irule current_graph_ordinary_edge >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem current_graph_probe_arrival_return:
  !p. p = "E" \/ p = "D" ==>
    current_graph_edge current_probe_loop
      (FST (make_ssa_current_fn current_probe_supply current_probe_loop))
      (CurrentStaticCut p "D" 0 0) (CurrentStaticCut p "D" 1 1) 0 /\
    current_graph_edge current_probe_loop
      (FST (make_ssa_current_fn current_probe_supply current_probe_loop))
      (CurrentStaticCut p "D" 1 1) (CurrentStaticCut p "D" 1 2) 1 /\
    current_graph_edge current_probe_loop
      (FST (make_ssa_current_fn current_probe_supply current_probe_loop))
      (CurrentStaticCut p "D" 1 2) (CurrentStaticCut p "D" 2 3) 2
Proof
  rpt strip_tac >> gvs[] >>
  simp[current_graph_edge_def, current_static_edge_def, current_graph_admissible_def] >>
  EVAL_TAC >> simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem current_graph_probe_zero_cleanup:
  current_graph_edge current_probe_loop
    (FST (make_ssa_current_fn current_probe_supply current_probe_loop))
    (CurrentStaticCut "D" "X" 0 0) (CurrentStaticCut "D" "X" 0 0) 0 /\
  current_graph_edge current_probe_loop
    (FST (make_ssa_current_fn current_probe_supply current_probe_loop))
    (CurrentStaticCut "D" "X" 0 0) (CurrentStaticCut "D" "X" 1 1) 2 /\
  ~current_graph_edge current_probe_loop
    (FST (make_ssa_current_fn current_probe_supply current_probe_loop))
    (CurrentStaticCut "D" "X" 0 0) (CurrentStaticCut "D" "X" 0 1) 1
Proof
  simp[current_graph_edge_def, current_static_edge_def, current_graph_admissible_def] >>
  EVAL_TAC >> simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED
