Theory makeSsaCurrentSemanticHistory
Ancestors makeSsaCurrentWriteFootprint venomExecSemantics venomInst venomState
  finite_map list rich_list pair

Datatype:
  current_history_phase = CurrentBatch string (instruction list)
    | CurrentOrdinary string num instruction | CurrentControl
End

(* Results are retained: only OK may precede another phase. *)
Definition current_state_result_def:
  (current_state_result (OK st) after <=> after = st) /\
  (current_state_result (Halt st) after <=> after = st) /\
  (current_state_result (Abort reason st) after <=> after = st) /\
  (current_state_result (IntRet ret st) after <=> after = st) /\
  (current_state_result (Error msg) after <=> F)
End

Definition current_semantic_phase_def:
  (current_semantic_phase fuel ctx (CurrentBatch l phis) before writes result after <=>
    before.vs_current_bb = l /\ EVERY (\inst. inst.inst_opcode = PHI) phis /\
    eval_phis before phis = OK after /\ result = OK after /\
    ?pairs. LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs /\
      writes = REVERSE pairs) /\
  (current_semantic_phase fuel ctx (CurrentOrdinary l i inst) before writes result after <=>
    before.vs_current_bb = l /\ before.vs_inst_idx = i /\
    result = step_inst fuel ctx inst before /\ current_state_result result after /\
    EVERY (\dv. MEM (FST dv) inst.inst_outputs) writes /\
    after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars writes) /\
  (current_semantic_phase fuel ctx CurrentControl before writes result after <=>
    after.vs_vars = before.vs_vars /\ writes = [] /\ result = OK after)
End

(* Control transports only the variable store.  It is not a reachability rule.
   Real CFG and certificate occurrence admissibility is a separate obligation. *)
Inductive current_semantic_history:
  (!st. current_semantic_history fuel ctx [] st [] (OK st) st) /\
  (!phase before writes result after.
    current_semantic_phase fuel ctx phase before writes result after ==>
    current_semantic_history fuel ctx [phase] before writes result after) /\
  (!phase phases before writes middle rest result after.
    current_semantic_phase fuel ctx phase before writes (OK middle) middle /\
    current_semantic_history fuel ctx phases middle rest result after ==>
    current_semantic_history fuel ctx (phase::phases) before (writes ++ rest) result after)
End

Theorem current_eval_phis_witness:
  !phis after. EVERY (\inst. inst.inst_opcode = PHI) phis /\
    eval_phis before phis = OK after ==>
  ?pairs. LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs /\
    after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars (REVERSE pairs)
Proof
  Induct >- simp[eval_phis_def] >> rpt gen_tac >>
  simp[eval_phis_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  qexists_tac `(out,v)::pairs` >> simp[REVERSE_DEF, FOLDL_APPEND, update_var_def]
QED

Theorem current_phi_pairs_unique:
  !phis pairs pairs'.
    LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs /\
    LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs' ==>
    pairs = pairs'
Proof
  Induct >> Cases_on `pairs` >> Cases_on `pairs'` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem current_semantic_batch:
  before.vs_current_bb = l /\ EVERY (\inst. inst.inst_opcode = PHI) phis /\
  eval_phis before phis = OK after ==>
  ?writes. current_semantic_phase fuel ctx (CurrentBatch l phis) before writes (OK after) after
Proof
  strip_tac >> drule_all current_eval_phis_witness >> strip_tac >>
  qexists_tac `REVERSE pairs` >> simp[current_semantic_phase_def] >> metis_tac[]
QED

Theorem current_semantic_phase_fold:
  current_semantic_phase fuel ctx phase before writes result after ==>
  after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars writes
Proof
  Cases_on `phase` >> simp[current_semantic_phase_def] >> rpt strip_tac >>
  drule_all current_eval_phis_witness >> strip_tac >>
  metis_tac[current_phi_pairs_unique]
QED

Theorem current_semantic_history_fold:
  !phases before writes result after. current_semantic_history fuel ctx phases before writes result after ==>
  after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars writes
Proof
  ho_match_mp_tac current_semantic_history_ind >> rpt strip_tac >>
  simp[FOLDL_APPEND] >> metis_tac[current_semantic_phase_fold]
QED

Theorem current_semantic_history_append:
  !phases before writes result0 middle.
  current_semantic_history fuel ctx phases before writes result0 middle ==>
  result0 = OK middle ==>
  !rest more result after. current_semantic_history fuel ctx rest middle more result after ==>
  current_semantic_history fuel ctx (phases ++ rest) before (writes ++ more) result after
Proof
  ho_match_mp_tac current_semantic_history_ind >> rpt strip_tac >>
  gvs[] >> metis_tac[current_semantic_history_rules, APPEND_ASSOC]
QED

Definition current_phase_outputs_def:
  (current_phase_outputs (CurrentBatch l phis) = FLAT (MAP (\inst. inst.inst_outputs) phis)) /\
  (current_phase_outputs (CurrentOrdinary l i inst) = inst.inst_outputs) /\
  (current_phase_outputs CurrentControl = [])
End

Theorem current_eval_one_phi_output:
  eval_one_phi before inst = SOME dv ==> MEM (FST dv) inst.inst_outputs
Proof
  simp[eval_one_phi_def] >> strip_tac >> gvs[AllCaseEqs()]
QED

Theorem current_phi_pairs_outputs:
  !phis pairs. LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs ==>
  EVERY (\dv. MEM (FST dv) (FLAT (MAP (\inst. inst.inst_outputs) phis))) pairs
Proof
  Induct >> Cases_on `pairs` >> simp[] >> rpt strip_tac
  >- metis_tac[current_eval_one_phi_output] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_semantic_phase_outputs:
  current_semantic_phase fuel ctx phase before writes result after ==>
  EVERY (\dv. MEM (FST dv) (current_phase_outputs phase)) writes
Proof
  Cases_on `phase` >> simp[current_semantic_phase_def, current_phase_outputs_def] >>
  rpt strip_tac >> gvs[EVERY_REVERSE] >>
  irule current_phi_pairs_outputs >> metis_tac[]
QED

Theorem current_semantic_ordinary:
  before.vs_current_bb = l /\ before.vs_inst_idx = i /\
  current_state_result (step_inst fuel ctx inst before) after /\
  current_result_output_writes inst.inst_outputs before (step_inst fuel ctx inst before) ==>
  ?writes. current_semantic_phase fuel ctx (CurrentOrdinary l i inst)
    before writes (step_inst fuel ctx inst before) after
Proof
  simp[current_semantic_phase_def] >>
  Cases_on `step_inst fuel ctx inst before` >>
  simp[current_state_result_def, current_result_output_writes_def, current_output_writes_def]
QED

Theorem current_semantic_noninvoke:
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  before.vs_current_bb = l /\ before.vs_inst_idx = i /\
  current_state_result (step_inst fuel ctx inst before) after ==>
  ?writes. current_semantic_phase fuel ctx (CurrentOrdinary l i inst)
    before writes (step_inst fuel ctx inst before) after
Proof
  strip_tac >> irule current_semantic_ordinary >> simp[] >>
  simp[Once step_inst_def, current_step_inst_base_output_writes]
QED

(* The first of duplicate PHI destinations wins; all reads use the snapshot. *)
Theorem current_semantic_duplicate_phi_probe:
  eval_phis (st with vs_prev_bb := SOME "p")
    [mk_inst 0 PHI [Label "p"; Lit 1w] ["x"];
     mk_inst 1 PHI [Label "p"; Lit 2w] ["x"]] =
  OK (update_var "x" 1w (update_var "x" 2w (st with vs_prev_bb := SOME "p")))
Proof
  simp[eval_phis_def, eval_one_phi_def, resolve_phi_def, phi_pairs_def,
    eval_operand_def, mk_inst_def]
QED

(* Cleanup copies are sequential: the second reads the first's write. *)
Theorem current_semantic_sequential_copy_probe:
  step_inst_base (mk_inst 1 ASSIGN [Var "x"] ["y"])
    (update_var "x" 7w st) =
  OK (update_var "y" 7w (update_var "x" 7w st))
Proof
  simp[step_inst_base_def, eval_operand_def, lookup_var_def,
    update_var_def, mk_inst_def, FLOOKUP_UPDATE]
QED
