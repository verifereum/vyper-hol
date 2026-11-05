Theory makeSsaCurrentChronologicalTransition
Ancestors
  makeSsaCurrentPairedRuntime makeSsaCurrentPairedWrites makeSsaCurrentJointRuntime
  makeSsaCurrentSimDefs makeSsaCurrentDefs venomInst venomState
  list rich_list alist pair arithmetic

Theorem current_origin_ordinal_bound[local]:
  !M. ?n:num. !a visit l i k. MEM (a,(visit,l,i,k)) M ==> k < n
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  pop_assum strip_assume_tac >> qexists_tac `SUC (n + h4)` >>
  rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem current_shared_origin_ordinal_fresh:
  ?n:num. !k. n <= k ==> current_origin_absent (visit,l,i,k) M /\
    current_origin_absent (visit,l,i,k) N
Proof
  Q.ISPEC_THEN `M` (qx_choose_then `m` assume_tac) current_origin_ordinal_bound >>
  Q.ISPEC_THEN `N` (qx_choose_then `n` assume_tac) current_origin_ordinal_bound >>
  qexists_tac `m+n` >> simp[current_origin_absent_def] >>
  rpt strip_tac >> imp_res_tac ALOOKUP_MEM >> res_tac >> decide_tac
QED

Definition current_event_reconnect_def:
  current_event_reconnect M N rt D outs outs' events <=>
  !v. MEM v D ==>
    (!k value. MEM (k,value) events ==>
      (EL k outs = v <=> EL k outs' = latest_current_name rt v)) /\
    ((~?k value. MEM (k,value) events /\ EL k outs = v) ==>
      ALOOKUP M v = ALOOKUP N (latest_current_name rt v))
End

Theorem current_event_lookup_reconnect[local]:
  !events M N n.
    (!k value. MEM (k,value) events ==> (EL k outs = v <=> EL k outs' = w)) /\
    ((~?k value. MEM (k,value) events /\ EL k outs = v) ==>
      ALOOKUP M v = ALOOKUP N w) ==>
    ALOOKUP (current_event_origins outs M visit l i n events) v =
    ALOOKUP (current_event_origins outs' N visit l i n events) w
Proof
  Induct >- simp[current_event_origins_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  simp[current_event_origins_def] >> first_x_assum irule >>
  conj_tac >- metis_tac[MEM] >>
  strip_tac >> gvs[MEM] >> Cases_on `EL h0 outs = v` >> gvs[] >> metis_tac[]
QED

Theorem current_event_reconnect_origins:
  current_event_reconnect M N rt D outs outs' events ==>
  !v. MEM v D ==>
    ALOOKUP (current_event_origins outs M visit l i n events) v =
    ALOOKUP (current_event_origins outs' N visit l i n events) (latest_current_name rt v)
Proof
  simp[current_event_reconnect_def] >> rpt strip_tac >>
  irule current_event_lookup_reconnect >> metis_tac[]
QED

Theorem current_step_inst_base_chronological:
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  current_joint_rel V M N rs (venomInst$operand_vars inst.inst_operands) st st' /\
  step_inst_base inst st = OK after ==>
  !rt D. ?n events after'.
    step_inst_base inst' st' = OK after' /\
    current_indexed_writes inst.inst_outputs events st after /\
    current_indexed_writes inst'.inst_outputs events st' after' /\
    current_origin_realizes (current_event_valuation V visit l i n events)
      (current_event_origins inst.inst_outputs M visit l i n events) after /\
    current_origin_realizes (current_event_valuation V visit l i n events)
      (current_event_origins inst'.inst_outputs N visit l i n events) after' /\
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb /\
    (current_event_reconnect M N rt D inst.inst_outputs inst'.inst_outputs events ==>
      current_joint_rel (current_event_valuation V visit l i n events)
        (current_event_origins inst.inst_outputs M visit l i n events)
        (current_event_origins inst'.inst_outputs N visit l i n events) rt D after after')
Proof
  rpt strip_tac >>
  `current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st'` by
    (irule current_joint_name_agree >> goal_assum $ drule_at Any) >>
  `?n:num. !k. n <= k ==> current_origin_absent (visit,l,i,k) M /\
    current_origin_absent (visit,l,i,k) N` by
    (irule current_shared_origin_ordinal_fresh) >>
  pop_assum strip_assume_tac >>
  `current_paired_origin_result V M N visit l i n inst.inst_outputs inst'.inst_outputs
     st st' (step_inst_base inst st) (step_inst_base inst' st')` by
    (irule current_step_inst_base_origins >> simp[] >>
     gvs[current_joint_rel_def] >> metis_tac[]) >>
  Cases_on `step_inst_base inst' st'` >>
  gvs[current_paired_origin_result_def, current_paired_origin_after_def] >>
  qexistsl_tac [`n`, `events`] >> simp[] >> strip_tac >>
  simp[current_joint_rel_def] >> rpt strip_tac >>
  drule current_event_reconnect_origins >> simp[]
QED
