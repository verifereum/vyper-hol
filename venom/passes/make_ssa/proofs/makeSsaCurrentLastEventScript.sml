Theory makeSsaCurrentLastEvent
Ancestors makeSsaCurrentChronologicalTransition makeSsaCurrentPairedRuntime
  makeSsaCurrentJointRuntime makeSsaCurrentDefs makeSsaCurrentSimDefs
  venomWf venomExecSemantics alist list arithmetic

Definition current_last_event_hit_def:
  (current_last_event_hit outs [] v = NONE : num option) /\
  (current_last_event_hit outs ((k,value)::events) v =
    case current_last_event_hit outs events v of
      SOME j => SOME (SUC j)
    | NONE => if EL k outs = v then SOME 0 else NONE)
End

Theorem current_event_origins_last_hit:
  !events M n.
    ALOOKUP (current_event_origins outs M visit l i n events) v =
    case current_last_event_hit outs events v of
      NONE => ALOOKUP M v
    | SOME j => SOME (visit,l,i,n+j)
Proof
  Induct >- simp[current_event_origins_def, current_last_event_hit_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[current_event_origins_def, current_last_event_hit_def] >>
  Cases_on `current_last_event_hit outs events v` >> simp[] >>
  Cases_on `EL h0 outs = v` >> simp[ADD_CLAUSES]
QED

Theorem current_last_hit_lookup_equal:
  current_last_event_hit outs events v = current_last_event_hit outs' events w /\
  (current_last_event_hit outs events v = NONE ==> ALOOKUP M v = ALOOKUP N w) ==>
  ALOOKUP (current_event_origins outs M visit l i n events) v =
  ALOOKUP (current_event_origins outs' N visit l i n events) w
Proof
  strip_tac >> simp[current_event_origins_last_hit] >>
  Cases_on `current_last_event_hit outs' events w` >> gvs[]
QED

Definition current_last_event_reconnect_def:
  current_last_event_reconnect M N rt D outs outs' events <=>
    !v. MEM v D ==>
      current_last_event_hit outs events v =
        current_last_event_hit outs' events (latest_current_name rt v) /\
      (current_last_event_hit outs events v = NONE ==>
        ALOOKUP M v = ALOOKUP N (latest_current_name rt v))
End

Theorem current_last_event_reconnect_origins:
  current_last_event_reconnect M N rt D outs outs' events ==>
  !v. MEM v D ==>
    ALOOKUP (current_event_origins outs M visit l i n events) v =
    ALOOKUP (current_event_origins outs' N visit l i n events) (latest_current_name rt v)
Proof
  simp[current_last_event_reconnect_def] >> rpt strip_tac >>
  irule current_last_hit_lookup_equal >> metis_tac[]
QED

Theorem current_last_event_repeated_probe:
  current_last_event_hit ["x";"x"] [(0,3n);(1,7)] "x" = SOME 1 /\
  current_last_event_hit ["x";"fresh"] [(0,3n);(1,7)] "fresh" = SOME 1 /\
  current_last_event_hit ["x"] [] "x" = NONE
Proof
  EVAL_TAC
QED

Theorem current_last_event_hit_none:
  !events. current_last_event_hit outs events v = NONE <=>
    !k. k < LENGTH events ==> EL (FST (EL k events)) outs <> v
Proof
  Induct >- simp[current_last_event_hit_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[current_last_event_hit_def] >>
  Cases_on `current_last_event_hit outs events v`
  >- (gvs[] >> eq_tac
      >- (rpt strip_tac >> Cases_on `k` >> gvs[]) >>
      disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >> spose_not_then assume_tac >>
  first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]
QED


Theorem current_step_inst_base_last_event:
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
    (current_last_event_reconnect M N rt D inst.inst_outputs inst'.inst_outputs events ==>
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
  drule current_last_event_reconnect_origins >> simp[]
QED
