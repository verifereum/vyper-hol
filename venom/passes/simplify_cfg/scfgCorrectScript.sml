(*
 * Simplify-CFG Correctness
 *
 * This theory proves basic correctness lemmas for simplify-cfg steps.
 *)

Theory scfgCorrect
Ancestors
  scfgDefs scfgTransform list relation stateEquiv venomSem venomState venomInst finite_map

(* ===== Equivalence Basics ===== *)

Theorem state_equiv_cfg_refl:
  !s. state_equiv_cfg s s
Proof
  rw[state_equiv_cfg_def, var_equiv_def]
QED

Theorem state_equiv_cfg_sym:
  !s1 s2. state_equiv_cfg s1 s2 ==> state_equiv_cfg s2 s1
Proof
  rw[state_equiv_cfg_def, var_equiv_def]
QED

Theorem state_equiv_cfg_trans:
  !s1 s2 s3.
    state_equiv_cfg s1 s2 /\ state_equiv_cfg s2 s3 ==> state_equiv_cfg s1 s3
Proof
  rw[state_equiv_cfg_def, var_equiv_def] >> metis_tac[]
QED

Theorem result_equiv_cfg_refl:
  !r. result_equiv_cfg r r
Proof
  Cases >> rw[result_equiv_cfg_def, state_equiv_cfg_refl]
QED

Theorem result_equiv_cfg_trans:
  !r1 r2 r3. result_equiv_cfg r1 r2 /\ result_equiv_cfg r2 r3 ==> result_equiv_cfg r1 r3
Proof
  Cases >> Cases >> Cases >>
  simp[result_equiv_cfg_def] >> metis_tac[state_equiv_cfg_trans]
QED

(* ===== Operand Evaluation under state_equiv_cfg ===== *)

Theorem eval_operand_state_equiv_cfg:
  !op s1 s2.
    state_equiv_cfg s1 s2 ==> eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, state_equiv_cfg_def, var_equiv_def]
QED

(* ===== State Operations Preserve state_equiv_cfg ===== *)

Theorem update_var_state_equiv_cfg:
  !x v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem mstore_state_equiv_cfg:
  !offset v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (mstore offset v s1) (mstore offset v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, mstore_def, lookup_var_def]
QED

Theorem sstore_state_equiv_cfg:
  !key v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (sstore key v s1) (sstore key v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, sstore_def, lookup_var_def]
QED

Theorem tstore_state_equiv_cfg:
  !key v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (tstore key v s1) (tstore key v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, tstore_def, lookup_var_def]
QED

Theorem write_memory_with_expansion_state_equiv_cfg:
  !offset bytes s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (write_memory_with_expansion offset bytes s1)
                    (write_memory_with_expansion offset bytes s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem jump_to_state_equiv_cfg:
  !lbl1 lbl2 s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (jump_to lbl1 s1) (jump_to lbl2 s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, revert_state_def, lookup_var_def]
QED

(* ===== resolve_phi under Label Rewriting ===== *)

Theorem resolve_phi_replace_label:
  !old new ops val.
    old <> new /\
    ~MEM (Label new) ops /\
    resolve_phi old ops = SOME val ==>
    resolve_phi new (MAP (replace_label_operand old new) ops) =
    SOME (replace_label_operand old new val)
Proof
  cheat
QED

(* TODO: proof attempt
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- simp[resolve_phi_def] >>
  Cases_on `t` >- simp[resolve_phi_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >>
  fs[resolve_phi_def, replace_label_operand_def] >>
  TRY (
    Cases_on `s = old` >> fs[] >>
    first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
    strip_tac >> simp[]
  ) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  strip_tac >> simp[]
QED
*)

Theorem resolve_phi_remove_non_preds:
  !preds prev ops val.
    MEM prev preds /\
    resolve_phi prev ops = SOME val ==>
    resolve_phi prev (phi_remove_non_preds preds ops) = SOME val
Proof
  cheat
QED

(* TODO: proof attempt
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- simp[resolve_phi_def, phi_remove_non_preds_def] >>
  Cases_on `t` >- simp[resolve_phi_def, phi_remove_non_preds_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >>
  fs[resolve_phi_def, phi_remove_non_preds_def] >>
  TRY (
    Cases_on `s = prev` >> fs[] >>
    first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
    strip_tac >> simp[]
  ) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  strip_tac >> simp[]
QED
*)

(* ===== PHI Simplification Preserves Step ===== *)

Theorem step_inst_simplify_phi_inst:
  !preds inst s prev out val_op.
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev /\
    MEM prev preds /\
    resolve_phi prev inst.inst_operands = SOME val_op
  ==>
    step_inst (simplify_phi_inst preds inst) s = step_inst inst s
Proof
  cheat
QED

(* TODO: proof attempt
Proof
  rpt strip_tac >>
  simp[simplify_phi_inst_def] >>
  qabbrev_tac `ops = phi_remove_non_preds preds inst.inst_operands` >>
  `resolve_phi prev ops = SOME val_op` by (
    fs[Abbr`ops`] >>
    irule resolve_phi_remove_non_preds >> simp[]
  ) >>
  Cases_on `ops` >- fs[resolve_phi_def] >>
  Cases_on `t` >- fs[resolve_phi_def] >>
  Cases_on `t'`
  >- (
    fs[step_inst_def, Abbr`ops`] >>
    Cases_on `h` >> fs[resolve_phi_def] >>
    Cases_on `s' = prev` >> fs[resolve_phi_def] >>
    simp[eval_operand_def]
  ) >>
  fs[step_inst_def]
QED
*)

(* ===== Simplify-PHI preserves block labels ===== *)

Theorem simplify_phi_block_label:
  !preds bb. (simplify_phi_block preds bb).bb_label = bb.bb_label
Proof
  rw[simplify_phi_block_def]
QED

(* ===== Simplify-PHI preserves step_in_block ===== *)

Theorem step_in_block_simplify_phi:
  !fn bb s preds res is_term.
    step_in_block fn bb s = (res, is_term) /\
    s.vs_prev_bb <> NONE /\
    preds = pred_labels fn bb.bb_label /\
    (!idx inst prev out val_op.
       get_instruction bb idx = SOME inst /\
       inst.inst_opcode = PHI /\
       inst.inst_outputs = [out] /\
       s.vs_prev_bb = SOME prev /\
       MEM prev preds /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       step_inst (simplify_phi_inst preds inst) s = step_inst inst s)
  ==>
    step_in_block fn (simplify_phi_block preds bb) s = (res, is_term)
Proof
  cheat
QED

(* TODO: proof attempt
Proof
  rpt strip_tac >>
  fs[step_in_block_def, simplify_phi_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `get_instruction (bb with bb_instructions := MAP (simplify_phi_inst preds) bb.bb_instructions) s.vs_inst_idx =
   SOME (simplify_phi_inst preds inst)` by (
    rw[get_instruction_def] >> simp[EL_MAP]
  ) >>
  simp[] >>
  Cases_on `step_inst inst s` >> fs[] >>
  simp[step_inst_def] >>
  (* Non-PHI instructions are unchanged *)
  Cases_on `inst.inst_opcode = PHI` >> fs[] >>
  first_x_assum (qspecl_then [`s.vs_inst_idx`, `inst`] mp_tac) >> simp[] >>
  strip_tac >> simp[]
QED
*)

(* ===== run_block equivalence for simplify_phi_block ===== *)

Theorem run_block_simplify_phi:
  !fn bb s preds.
    s.vs_prev_bb <> NONE /\
    preds = pred_labels fn bb.bb_label /\
    (!idx inst prev out val_op.
       get_instruction bb idx = SOME inst /\
       inst.inst_opcode = PHI /\
       inst.inst_outputs = [out] /\
       s.vs_prev_bb = SOME prev /\
       MEM prev preds /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       step_inst (simplify_phi_inst preds inst) s = step_inst inst s)
  ==>
    run_block fn (simplify_phi_block preds bb) s = run_block fn bb s
Proof
  cheat
QED

(* TODO: proof attempt
Proof
  ho_match_mp_tac run_block_ind >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >> Cases_on `q` >> simp[] >>
  strip_tac >>
  drule step_in_block_simplify_phi >>
  disch_then (qspecl_then [`preds`] mp_tac) >> simp[] >>
  disch_then (fn th => simp[th]) >>
  simp[Once run_block_def]
QED
*)

(* ===== Simplify-CFG Step Correctness (Skeletons) ===== *)

Theorem remove_unreachable_blocks_correct:
  !fn s fuel.
    fn.fn_blocks <> [] /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE ==>
    result_equiv_cfg (run_function fuel fn s)
                     (run_function fuel (remove_unreachable_blocks fn) s)
Proof
  cheat
QED

Theorem merge_blocks_correct:
  !fn a_lbl b_lbl s fuel.
    merge_blocks_cond fn a_lbl b_lbl /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE ==>
    result_equiv_cfg (run_function fuel fn s)
                     (run_function fuel (merge_blocks fn a_lbl b_lbl) s)
Proof
  cheat
QED

Theorem merge_jump_correct:
  !fn a_lbl b_lbl s fuel.
    merge_jump_cond fn a_lbl b_lbl /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE ==>
    result_equiv_cfg (run_function fuel fn s)
                     (run_function fuel (merge_jump fn a_lbl b_lbl) s)
Proof
  cheat
QED

Theorem simplify_cfg_step_correct:
  !fn fn' s fuel.
    simplify_cfg_step fn fn' /\
    fn.fn_blocks <> [] /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE ==>
    result_equiv_cfg (run_function fuel fn s)
                     (run_function fuel fn' s)
Proof
  cheat
QED

Theorem simplify_cfg_correct:
  !fn fn' s fuel.
    simplify_cfg fn fn' /\
    fn.fn_blocks <> [] /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE ==>
    result_equiv_cfg (run_function fuel fn s)
                     (run_function fuel fn' s)
Proof
  cheat
QED

val _ = export_theory();
