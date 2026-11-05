Theory makeSsaCurrentInsertedValue
Ancestors makeSsaCurrentRetainedRead makeSsaCurrentInsertedNonself makeSsaCurrentPhiRuntime
  makeSsaCurrentSimDefs makeSsaCurrentEdgeTrace makeSsaCurrentAnalysis
  makeSsaCurrentMergeSeed makeSsaCurrentFinalSlots makeSsaCurrentPhaseShape
  makeSsaCurrentRetainedNonclobber dfAnalyzeProofs venomExecProps
  makeSsaCurrentReinsertionNames makeSsaCurrentReinsertionSlots makeSsaCurrentDefs venomExecSemantics venomState venomInst venomWf livenessDefs list rich_list

Theorem current_inserted_slots_resolve:
  !ps. MEM p ps ==>
  resolve_phi p (current_phi_slots (MAP (\q. (q,v)) ps)) = SOME (Var v)
Proof
  rewrite_tac[current_resolve_phi_slots] >>
  Induct >> simp[FIND_thm] >> gen_tac >>
  Cases_on `h = p` >> simp[FIND_thm] >> gvs[optionTheory.OPTION_MAP_EQ_SOME]
QED

Theorem current_certificate_inserted_edge_resolve:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  ps = (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps0 => ps0) ==>
  resolve_phi p
    (FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
      (current_phi_slots (MAP (\q. (q,v)) ps)) events) =
    SOME (Var (latest_current_name (current_event_exit_rs ev) v))
Proof
  strip_tac >>
  `MEM p (fn_labels fn) /\ MEM h (fn_labels fn)` by
    (fs[fn_cfg_edge_def, wf_function_def, fn_succs_closed_def, fn_labels_def, MEM_MAP] >>
     metis_tac[]) >>
  `MEM p ps` by gvs[ALOOKUP_current_pred_map, current_cfg_edge_preds] >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_certificate_event_labels_distinct] >>
  `MEM h (case ALOOKUP (current_succ_map fn) p of NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  irule current_event_fold_selected_slot >>
  metis_tac[current_inserted_slots_resolve]
QED

Theorem current_certificate_inserted_replay_occurrence:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  first_block_no_preds fn /\
  current_actual_inserted fn v h /\ current_token_name H (CurrentInserted v h) = SOME n ==>
  ?old pre renamed final k.
    lookup_block h fn.fn_blocks = SOME old /\
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\
    EVERY (\j. j.inst_opcode = PHI) pre /\ k < LENGTH pre /\
    current_phi_view final.bb_instructions =
      FOLDL (\view ev. current_event_slot_action (current_succ_map fn) h ev view)
        (current_phi_view (pre ++ old.bb_instructions)) events /\
    k < LENGTH final.bb_instructions /\
    (EL k final.bb_instructions).inst_opcode = PHI /\
    (EL k final.bb_instructions).inst_outputs = [n] /\
    (EL k final.bb_instructions).inst_operands =
      FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
        (current_phi_slots (MAP (\p. (p,v))
          (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps => ps))) events
Proof
  strip_tac >>
  `MEM h (fn_labels fn)` by metis_tac[current_actual_inserted_support] >>
  `?old. lookup_block h fn.fn_blocks = SOME old` by
    metis_tac[lookup_block_exists, fn_labels_def] >>
  drule_all current_certificate_block_replay >> strip_tac >>
  `EVERY (\j. j.inst_opcode = PHI) pre` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     strip_tac >> simp[build_phi_inst_supply_def]) >>
  `?k. k < LENGTH pre /\ MEM v (EL k pre).inst_outputs` by metis_tac[MEM_EL] >>
  `?id. EL k pre = build_phi_inst_supply id v
    (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps => ps)` by
    (qpat_assum `EVERY (\inst. ?id v. _) pre` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `EL k pre` mp_tac) >>
     simp[EL_MEM] >> strip_tac >> gvs[build_phi_inst_supply_def]) >>
  `k < LENGTH (pre ++ old.bb_instructions) /\
    (EL k (pre ++ old.bb_instructions)).inst_opcode = PHI` by
    simp[EL_APPEND_EQN, build_phi_inst_supply_def] >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  `?name. (EL k final.bb_instructions).inst_outputs = [name] /\
    current_token_name H (CurrentInserted v h) = SOME name` by
    (qpat_x_assum `!k v. k < LENGTH pre /\ _ ==> _`
       (qspecl_then [`k`, `v`] mp_tac) >>
     simp[build_phi_inst_supply_def]) >>
  qexistsl_tac [`old`, `pre`, `renamed`, `final`, `k`] >>
  gvs[EL_APPEND_EQN, build_phi_inst_supply_def] >>
  simp[current_phi_slots_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem current_certificate_inserted_replayed_eval:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  first_block_no_preds fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_actual_inserted fn v h /\ current_token_name H (CurrentInserted v h) = SOME n /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  st'.vs_prev_bb = SOME p /\
  current_name_agree (current_event_exit_rs ev) [v] st st' /\ lookup_var v st = SOME value ==>
  ?old pre renamed final k.
    lookup_block h fn.fn_blocks = SOME old /\
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\
    EVERY (\j. j.inst_opcode = PHI) pre /\ k < LENGTH pre /\
    current_phi_view final.bb_instructions =
      FOLDL (\view ev. current_event_slot_action (current_succ_map fn) h ev view)
        (current_phi_view (pre ++ old.bb_instructions)) events /\
    k < LENGTH final.bb_instructions /\
    (EL k final.bb_instructions).inst_opcode = PHI /\
    (EL k final.bb_instructions).inst_outputs = [n] /\
    eval_one_phi st' (EL k final.bb_instructions) = SOME (n,value)
Proof
  strip_tac >> drule_all current_certificate_inserted_replay_occurrence >> strip_tac >>
  `resolve_phi p (EL k final.bb_instructions).inst_operands =
    SOME (Var (latest_current_name (current_event_exit_rs ev) v))` by
    (asm_rewrite_tac[] >> irule current_certificate_inserted_edge_resolve >>
     metis_tac[]) >>
  `lookup_var (latest_current_name (current_event_exit_rs ev) v) st' = SOME value` by
    fs[current_name_agree_def] >>
  qexistsl_tac [`old`, `pre`, `renamed`, `final`, `k`] >>
  asm_rewrite_tac[] >> simp[eval_one_phi_def, eval_operand_def] >> gvs[eval_operand_def]
QED

Theorem current_simplify_phi_surviving_identity:
  inst.inst_opcode = PHI /\ (simplify_current_phi inst).inst_opcode = PHI ==>
  simplify_current_phi inst = inst
Proof
  strip_tac >>
  Cases_on `EVERY (\v. MEM v (inst_ir_vars inst))
    (inst_ir_vars (simplify_current_phi_raw inst))`
  >- (gvs[simplify_current_phi_def, keep_current_phi_vars_def] >>
      Cases_on `current_phi_output inst.inst_outputs` >>
      gvs[simplify_current_phi_raw_def] >>
      Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >>
      gvs[simplify_current_phi_raw_def] >>
      Cases_on `x'` >> gvs[simplify_current_phi_raw_def] >>
      IF_CASES_TAC >> gvs[]) >>
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem current_collect_phi_split:
  !insts. insts = collect_phis insts ++ DROP (LENGTH (collect_phis insts)) insts /\
    EVERY (\j. j.inst_opcode = PHI) (collect_phis insts) /\
    (DROP (LENGTH (collect_phis insts)) insts = [] \/
      (HD (DROP (LENGTH (collect_phis insts)) insts)).inst_opcode <> PHI)
Proof
  Induct >> simp[collect_phis_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[collect_phis_def]
QED

Theorem current_collect_phi_prefix_bound:
  !insts prefix tail. insts = prefix ++ tail /\
    EVERY (\j. j.inst_opcode = PHI) prefix ==>
    LENGTH prefix <= LENGTH (collect_phis insts)
Proof
  Induct_on `prefix` >> simp[] >> rpt strip_tac >>
  gvs[collect_phis_def]
QED

Theorem current_replay_inserted_leading_bound:
  current_phi_view insts =
    FOLDL (\view ev. current_event_slot_action sm h ev view)
      (current_phi_view (pre ++ old)) events /\
  EVERY (\j. j.inst_opcode = PHI) pre /\ k < LENGTH pre ==>
  k < LENGTH (collect_phis insts)
Proof
  strip_tac >>
  qspec_then `old` (map_every assume_tac o CONJUNCTS) current_collect_phi_split >>
  `current_phi_view insts =
    FOLDL (\view ev. current_event_slot_action sm h ev view)
      (current_phi_view ((pre ++ collect_phis old) ++
        DROP (LENGTH (collect_phis old)) old)) events` by
    metis_tac[APPEND_ASSOC] >>
  drule_at (Pat `current_phi_view _ = _`) current_replay_phase_split >>
  simp[EVERY_APPEND] >> strip_tac >>
  drule_all current_collect_phi_prefix_bound >> simp[] >> decide_tac
QED

Theorem current_replay_surviving_phi_eval:
  fn'.fn_blocks = simplify_current_phis_if enabled renamed /\
  lookup_block h renamed = SOME final /\
  k < LENGTH (collect_phis final.bb_instructions) /\
  (EL k final.bb_instructions).inst_opcode = PHI /\
  (simplify_current_phi (EL k final.bb_instructions)).inst_opcode = PHI /\
  (EL k final.bb_instructions).inst_outputs = [n] /\
  eval_one_phi st (EL k final.bb_instructions) = SOME (n,value) ==>
  ?out r. lookup_block h fn'.fn_blocks = SOME out /\
    r < LENGTH (collect_phis out.bb_instructions) /\
    (EL r out.bb_instructions).inst_outputs = [n] /\
    eval_one_phi st (EL r out.bb_instructions) = SOME (n,value)
Proof
  strip_tac >>
  qspec_then `final.bb_instructions` (map_every assume_tac o CONJUNCTS)
    current_collect_phi_split >>
  `EL k final.bb_instructions = EL k (collect_phis final.bb_instructions)` by
    (qpat_assum `final.bb_instructions = _`
       (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
     simp[EL_APPEND_EQN]) >>
  `simplify_current_phi (EL k (collect_phis final.bb_instructions)) =
    EL k (collect_phis final.bb_instructions)` by
    (irule current_simplify_phi_surviving_identity >>
     metis_tac[EL_APPEND_EQN]) >>
  drule_all current_replay_retained_leading_position >> strip_tac >>
  `batch <= LENGTH (collect_phis out.bb_instructions)` by
    (qspec_then `out.bb_instructions` (qspecl_then
      [`TAKE batch out.bb_instructions`, `DROP batch out.bb_instructions`] mp_tac)
      current_collect_phi_prefix_bound >> simp[]) >>
  qexistsl_tac [`out`, `r`] >>
  imp_res_tac current_no_id_fields >>
  gvs[EL_APPEND_EQN, eval_one_phi_def] >> decide_tac
QED

(* The classification premise is scoped to the actual replay witness, not an
   arbitrary caller-supplied instruction. Eliminated copies are not executed here. *)
Theorem current_certificate_inserted_retained_eval:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  first_block_no_preds fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_actual_inserted fn v h /\ current_token_name H (CurrentInserted v h) = SOME n /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  st'.vs_prev_bb = SOME p /\
  current_name_agree (current_event_exit_rs ev) [v] st st' /\ lookup_var v st = SOME value ==>
  ?renamed final k.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\
    k < LENGTH (collect_phis final.bb_instructions) /\
    (EL k final.bb_instructions).inst_opcode = PHI /\
    (EL k final.bb_instructions).inst_outputs = [n] /\
    eval_one_phi st' (EL k final.bb_instructions) = SOME (n,value) /\
    ((simplify_current_phi (EL k final.bb_instructions)).inst_opcode = PHI ==>
      ?out r. lookup_block h fn'.fn_blocks = SOME out /\
        r < LENGTH (collect_phis out.bb_instructions) /\
        (EL r out.bb_instructions).inst_outputs = [n] /\
        eval_one_phi st' (EL r out.bb_instructions) = SOME (n,value))
Proof
  strip_tac >> drule_all current_certificate_inserted_replayed_eval >> strip_tac >>
  `k < LENGTH (collect_phis final.bb_instructions)` by
    (drule_all current_replay_inserted_leading_bound >> simp[]) >>
  qexistsl_tac [`renamed`, `final`, `k`] >> asm_rewrite_tac[] >> strip_tac >>
  drule_all current_replay_surviving_phi_eval >> simp[]
QED
