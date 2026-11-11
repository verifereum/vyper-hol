Theory algebraicOptCmpChunkProofs
Ancestors
  algebraicOptCmpStepProofs algebraicOptCmpCoherenceProofs
  algebraicOptCmpSimulationProofs algebraicOptCmpLocalProofs
  venomExecSemantics venomState stateFrame stateEquiv execEquivProps
  algebraicOptCmpScanProofs venomInst passSharedDefs pred_set venomFnScheduleRunner irSupply alist

(* This evaluator is used only at nonterminating instruction boundaries. *)
Definition ao_cmp_exec_chunk_def:
  (ao_cmp_exec_chunk fuel ctx [] s = OK s) /\
  (ao_cmp_exec_chunk fuel ctx (i::is) s =
    case step_inst fuel ctx i s of
      OK u => ao_cmp_exec_chunk fuel ctx is
        (u with vs_inst_idx := SUC s.vs_inst_idx)
    | Halt u => Halt u
    | Abort a u => Abort a u
    | IntRet r u => IntRet r u
    | Error e => Error e)
End

Theorem ao_cmp_exec_chunk_single:
  ao_cmp_exec_chunk fuel ctx [i] s =
    case step_inst fuel ctx i s of
      OK u => OK (u with vs_inst_idx := SUC s.vs_inst_idx)
    | Halt u => Halt u
    | Abort a u => Abort a u
    | IntRet r u => IntRet r u
    | Error e => Error e
Proof
  simp[ao_cmp_exec_chunk_def]
QED

Theorem ao_cmp_exec_chunk_two:
  step_inst fuel ctx i s = OK u ==>
  ao_cmp_exec_chunk fuel ctx [i;j] s =
    ao_cmp_exec_chunk fuel ctx [j] (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[ao_cmp_exec_chunk_def]
QED

Theorem ao_cmp_exec_chunk_append:
  !xs ys s.
    ao_cmp_exec_chunk fuel ctx (xs ++ ys) s =
      case ao_cmp_exec_chunk fuel ctx xs s of
        OK u => ao_cmp_exec_chunk fuel ctx ys u
      | Halt u => Halt u
      | Abort a u => Abort a u
      | IntRet r u => IntRet r u
      | Error e => Error e
Proof
  Induct >> simp[ao_cmp_exec_chunk_def] >> rpt gen_tac >>
  Cases_on `step_inst fuel ctx h s` >> simp[ao_cmp_exec_chunk_def]
QED

Theorem ao_cmp_state_rel_indices:
  !ignored flipped s t n m.
  ao_cmp_state_rel ignored flipped (s with vs_inst_idx := n) (t with vs_inst_idx := m) <=>
  ao_cmp_state_rel ignored flipped s t
Proof
  simp[ao_cmp_state_rel_def, execution_frame_updates, lookup_var_def]
QED

Theorem ao_cmp_removed_chunk:
  !ignored flipped fuel ctx inst v out s t.
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    inst.inst_opcode = ISZERO /\ inst.inst_operands = [Var v] /\
    inst.inst_outputs = [out] /\ v IN flipped /\ v NOTIN ignored /\
    out NOTIN flipped ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result
      (\u w. ao_cmp_state_rel ignored flipped u w /\
        u.vs_current_bb = w.vs_current_bb /\ u.vs_prev_bb = w.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx inst s)
      (ao_cmp_exec_chunk fuel ctx [inst with inst_opcode := ASSIGN] t)
Proof
  rpt gen_tac >> strip_tac >>
  ` (lookup_var v s = NONE /\ lookup_var v t = NONE) \/
    (?b. lookup_var v s = SOME (bool_to_word b) /\
         lookup_var v t = SOME (bool_to_word (~b)))` by
    (qpat_assum `ao_cmp_state_rel _ _ _ _` mp_tac >>
     pure_rewrite_tac[ao_cmp_state_rel_def] >> strip_tac >>
     first_x_assum (qspec_then `v` mp_tac) >> simp[])
  >- (disj1_tac >> metis_tac[ao_cmp_iszero_unwritten]) >>
  drule_all ao_cmp_iszero_compensation >> strip_tac >>
  `ao_cmp_state_rel ignored flipped
    (update_var out (bool_to_word (~b)) s)
    (update_var out (bool_to_word (~b)) t)` by
    (irule ao_cmp_state_rel_write >> simp[]) >>
  simp[ao_cmp_exec_chunk_single, lift_result_def] >>
  gvs[ao_cmp_state_rel_def, execution_frame_updates, lookup_var_def,
      update_var_def]
QED

Theorem ao_cmp_assert_chunk:
  !ignored flipped fuel ctx inst iz v fresh s t.
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [Var v] /\
    iz.inst_opcode = ISZERO /\ iz.inst_operands = [Var v] /\
    iz.inst_outputs = [fresh] /\ fresh IN ignored /\
    v IN flipped /\ v NOTIN ignored ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result
      (\u w. ao_cmp_state_rel ignored flipped u w /\
        u.vs_current_bb = w.vs_current_bb /\ u.vs_prev_bb = w.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx inst s)
      (ao_cmp_exec_chunk fuel ctx [iz; inst with inst_operands := [Var fresh]] t)
Proof
  rpt gen_tac >> strip_tac >>
  `(lookup_var v s = NONE /\ lookup_var v t = NONE) \/
    (?b. lookup_var v s = SOME (bool_to_word b) /\
         lookup_var v t = SOME (bool_to_word (~b)))` by
    (qpat_assum `ao_cmp_state_rel _ _ _ _` mp_tac >>
     pure_rewrite_tac[ao_cmp_state_rel_def] >> strip_tac >>
     first_x_assum (qspec_then `v` mp_tac) >> simp[])
  >- (disj1_tac >> qexists_tac `"undefined operand"` >>
      simp[step_inst_non_invoke] >> asm_rewrite_tac[step_inst_base_def] >>
      simp[eval_operand_def]) >>
  `ao_cmp_state_rel ignored flipped s (update_var fresh (bool_to_word b) t)` by
    (irule ao_cmp_state_rel_ignored_write >> simp[]) >>
  disj2_tac >> Cases_on `b` >>
  simp[ao_cmp_exec_chunk_def, step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def] >>
  simp[exec_pure1_def, eval_operand_def, bool_to_word_def,
       lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       lift_result_def] >>
  gvs[ao_cmp_state_rel_def, execution_frame_updates, lookup_var_def,
      update_var_def, bool_to_word_def, execution_equiv_def,
      revert_state_def, set_returndata_def]
QED

Theorem ao_cmp_producer_chunk:
  !ignored flipped fuel ctx inst op out s t w signed is_gt lo never hi.
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    inst.inst_opcode =
      (if signed then (if is_gt then SGT else SLT)
       else (if is_gt then GT else LT)) /\
    inst.inst_operands = [op; Lit w] /\ inst.inst_outputs = [out] /\
    out IN flipped /\
    (!v. op = Var v ==> v NOTIN ignored /\ v NOTIN flipped) /\
    (if signed then ao_signed_boundaries is_gt
     else ao_unsigned_boundaries is_gt) = (lo,never,hi) /\ w <> never ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result
      (\u v. ao_cmp_state_rel ignored flipped u v /\
        u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx inst s)
      (ao_cmp_exec_chunk fuel ctx
        [inst with <|inst_opcode := flip_comparison_opcode inst.inst_opcode;
          inst_operands := [op; Lit (if is_gt then w + 1w else w - 1w)]|>] t)
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand op s = eval_operand op t` by
    (irule ao_cmp_state_rel_operand >> qexistsl_tac [`flipped`, `ignored`] >> simp[]) >>
  Cases_on `eval_operand op s`
  >- (disj1_tac >> qexists_tac `"undefined operand"` >>
      Cases_on `signed` >> Cases_on `is_gt` >>
      simp[step_inst_non_invoke] >> asm_rewrite_tac[step_inst_base_def] >>
      gvs[exec_pure2_def, eval_operand_def]) >>
  `?b. step_inst fuel ctx inst s = OK (update_var out (bool_to_word b) s) /\
    step_inst fuel ctx
      (inst with <|inst_opcode := flip_comparison_opcode inst.inst_opcode;
        inst_operands := [op; Lit (if is_gt then w + 1w else w - 1w)]|>) t =
      OK (update_var out (bool_to_word (~b)) t)` by
    (irule ao_cmp_producer_refresh >> metis_tac[]) >>
  `ao_cmp_state_rel ignored flipped (update_var out (bool_to_word b) s)
    (update_var out (bool_to_word (~b)) t)` by
    (irule ao_cmp_state_rel_write >> simp[] >> metis_tac[]) >>
  simp[ao_cmp_exec_chunk_single, lift_result_def] >>
  gvs[ao_cmp_state_rel_def, execution_frame_updates, lookup_var_def, update_var_def]
QED

Theorem ao_cmp_selected_chunk_shape:
  !fn fs rs ins sup ns sup' inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    ao_name_inserts_supply sup ins = (ns,sup') /\ ir_supply_inst_ok sup /\
    MEM inst (fn_insts fn) /\
    (ALOOKUP fs inst.inst_id <> NONE \/ MEM inst.inst_id rs \/
      ALOOKUP ns inst.inst_id <> NONE) ==>
    ~is_terminator inst.inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (ao_cmp_flip_apply_inst fs rs ns inst) /\
    0 < LENGTH (ao_cmp_flip_apply_inst fs rs ns inst)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `ALOOKUP fs inst.inst_id`
  >- (Cases_on `MEM inst.inst_id rs`
      >- (drule_all ao_cmp_remove_lookup_cert >> strip_tac >>
          drule_all ao_cmp_remove_apply >> strip_tac >>
          simp[is_terminator_def]) >>
      `ALOOKUP ns inst.inst_id <> NONE` by metis_tac[] >>
      Cases_on `ALOOKUP ns inst.inst_id` >> gvs[] >>
      PairCases_on `x` >> drule_all ao_cmp_insert_apply >> strip_tac >>
      simp[is_terminator_def]) >>
  rename1 `ALOOKUP fs inst.inst_id = SOME action` >>
  PairCases_on `action` >> drule_all ao_cmp_producer_apply >>
  disch_then (qspec_then `ns` strip_assume_tac) >>
  qpat_x_assum `ao_cmp_flip_cert _ _ _` mp_tac >>
  simp[ao_cmp_flip_cert_def, ao_cmp_source_def] >> strip_tac >>
  gvs[is_comparator_def] >>
  simp[passSharedDefsTheory.flip_comparison_opcode_def, is_terminator_def]
QED

Theorem ao_cmp_selected_chunk:
  !fn fs rs ins sup ns sup' inst ignored flipped fuel ctx s t.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    ao_name_inserts_supply sup ins = (ns,sup') /\
    ir_supply_inst_ok sup /\ ir_supply_covers_fn sup fn /\
    ignored = set sup'.irs_used_vars DIFF set sup.irs_used_vars /\
    flipped = ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs /\
    MEM inst (fn_insts fn) /\
    ((inst.inst_opcode = ISZERO \/ inst.inst_opcode = ASSERT) ==>
      LENGTH inst.inst_operands = 1) /\
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    (ALOOKUP fs inst.inst_id <> NONE \/ MEM inst.inst_id rs \/
      ALOOKUP ns inst.inst_id <> NONE) ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result
      (\u v. ao_cmp_state_rel ignored flipped u v /\
        u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx inst s)
      (ao_cmp_exec_chunk fuel ctx (ao_cmp_flip_apply_inst fs rs ns inst) t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `DISJOINT (set (inst_ir_vars inst)) ignored` by
    (asm_rewrite_tac[] >> irule ao_cmp_ignored_inst_vars >> metis_tac[]) >>
  Cases_on `ALOOKUP fs inst.inst_id`
  >- (Cases_on `MEM inst.inst_id rs`
      >- suspend "removed"
      >> suspend "assert") >>
  suspend "producer"
QED

Resume ao_cmp_selected_chunk[removed]:
  drule_all ao_cmp_remove_lookup_cert >> strip_tac >>
  `LENGTH inst.inst_operands = 1` by metis_tac[] >>
  drule_all ao_cmp_removed_shape >> strip_tac >>
  drule_all ao_cmp_remove_apply >> strip_tac >>
  asm_rewrite_tac[] >> irule ao_cmp_removed_chunk >>
  gvs[DISJOINT_ALT, inst_ir_vars_def, inst_uses_def,
      venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
      venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]
QED

Resume ao_cmp_selected_chunk[assert]:
  Cases_on `ALOOKUP ns inst.inst_id` >- gvs[] >>
  rename1 `ALOOKUP ns inst.inst_id = SOME action` >> PairCases_on `action` >>
  drule_all ao_cmp_insert_apply >> strip_tac >>
  `LENGTH inst.inst_operands = 1` by metis_tac[] >>
  drule_all ao_cmp_named_shape >> strip_tac >>
  asm_rewrite_tac[] >> irule ao_cmp_assert_chunk >>
  gvs[DISJOINT_ALT, inst_ir_vars_def, inst_uses_def,
      venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
      venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]
QED

Resume ao_cmp_selected_chunk[producer]:
  rename1 `ALOOKUP fs inst.inst_id = SOME action` >> PairCases_on `action` >>
  drule_all ao_cmp_producer_apply >>
  disch_then (qspec_then `ns` strip_assume_tac) >>
  `?out. inst.inst_outputs = [out] /\ out IN flipped` by
    (drule ALOOKUP_MEM >> strip_tac >>
     qpat_assum `ao_cmp_flip_cert _ _ _` mp_tac >>
     pure_rewrite_tac[ao_cmp_flip_cert_def, ao_cmp_source_def] >> strip_tac >>
     qexists_tac `v` >> asm_rewrite_tac[] >>
     simp[ao_cmp_flipped_def] >> qexistsl_tac [`inst`, `(inst.inst_id,action0,action1,action2)`] >>
     simp[] >> gvs[ao_cmp_flip_cert_def, ao_cmp_source_def]) >>
  drule_all ao_cmp_flip_cert_origin >> strip_tac >>
  `inst.inst_opcode <> ISZERO /\ inst.inst_opcode <> ASSERT` by
    gvs[is_comparator_def] >>
  `DISJOINT (set (operand_vars inst.inst_operands)) flipped` by
    (drule_all ao_cmp_flipped_nonconsumer_reads >>
     disch_then (qspec_then `fs` mp_tac) >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> irule ao_cmp_producer_chunk >>
  gvs[is_comparator_def, DISJOINT_ALT, inst_ir_vars_def, inst_uses_def,
      venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
      venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >>
  metis_tac[]
QED

Finalise ao_cmp_selected_chunk
