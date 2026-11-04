Theory makeSsaCurrentPairedRuntime
Ancestors makeSsaCurrentPairedWrites makeSsaCurrentJointRuntime
  makeSsaCurrentDefs makeSsaCurrentSimDefs venomState venomExecSemantics stateFrame
  finite_map alist list pair combin

(* Each event gets its ordinal, not its destination name or output index.
   Repeated destinations and repeated output indices are therefore harmless. *)
Definition current_event_valuation_def:
  (current_event_valuation V visit l i n [] = V) /\
  (current_event_valuation V visit l i n ((k,value)::events) =
    current_event_valuation (((visit,l,i,n) =+ SOME value) V)
      visit l i (SUC n) events)
End

Definition current_event_origins_def:
  (current_event_origins outs M visit l i n [] = M) /\
  (current_event_origins outs M visit l i n ((k,value)::events) =
    current_event_origins outs ((EL k outs,(visit,l,i,n))::M)
      visit l i (SUC n) events)
End

Theorem current_origin_realizes_vars:
  current_origin_realizes V M st /\ after.vs_vars = st.vs_vars ==>
  current_origin_realizes V M after
Proof
  simp[current_origin_realizes_def, lookup_var_def]
QED

Theorem current_event_fold_vars:
  !events st. (FOLDL (\s kv. update_var (EL (FST kv) outs) (SND kv) s) st events).vs_vars =
    FOLDL (\m kv. m |+ (EL (FST kv) outs,SND kv)) st.vs_vars events
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[update_var_def]
QED

Theorem current_event_origins_realize:
  !events V M N st st' n.
  current_origin_realizes V M st /\ current_origin_realizes V N st' /\
  (!k. n <= k ==> current_origin_absent (visit,l,i,k) M /\
                    current_origin_absent (visit,l,i,k) N) ==>
  current_origin_realizes (current_event_valuation V visit l i n events)
    (current_event_origins outs M visit l i n events)
    (FOLDL (\s kv. update_var (EL (FST kv) outs) (SND kv) s) st events) /\
  current_origin_realizes (current_event_valuation V visit l i n events)
    (current_event_origins outs' N visit l i n events)
    (FOLDL (\s kv. update_var (EL (FST kv) outs') (SND kv) s) st' events)
Proof
  Induct >> simp[current_event_valuation_def, current_event_origins_def] >>
  Cases_on `h` >> rpt gen_tac >> strip_tac >>
  simp[current_event_valuation_def, current_event_origins_def] >>
  first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> irule current_origin_absent_cons >> simp[] >>
      `n <= k /\ k <> n` by decide_tac >> metis_tac[]) >>
  conj_tac >> irule current_origin_realizes_fresh_write >> simp[] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem current_indexed_writes_origins:
  current_origin_realizes V M st /\ current_origin_realizes V N st' /\
  (!k. n <= k ==> current_origin_absent (visit,l,i,k) M /\
                    current_origin_absent (visit,l,i,k) N) /\
  current_indexed_writes outs events st after /\
  current_indexed_writes outs' events st' after' ==>
  current_origin_realizes (current_event_valuation V visit l i n events)
    (current_event_origins outs M visit l i n events) after /\
  current_origin_realizes (current_event_valuation V visit l i n events)
    (current_event_origins outs' N visit l i n events) after'
Proof
  strip_tac >> drule_all current_event_origins_realize >>
  disch_then (qspecl_then [`outs'`, `outs`, `events`] strip_assume_tac) >>
  conj_tac >> irule current_origin_realizes_vars >>
  goal_assum $ drule_at Any >>
  gvs[current_indexed_writes_def, current_event_fold_vars]
QED

Definition current_paired_origin_after_def:
  current_paired_origin_after V M N visit l i n outs outs' st st' after after' <=>
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\
    after.vs_prev_bb = after'.vs_prev_bb /\
    ?events.
      current_indexed_writes outs events st after /\
      current_indexed_writes outs' events st' after' /\
      current_origin_realizes (current_event_valuation V visit l i n events)
        (current_event_origins outs M visit l i n events) after /\
      current_origin_realizes (current_event_valuation V visit l i n events)
        (current_event_origins outs' N visit l i n events) after'
End

Theorem current_paired_after_origins:
  current_origin_realizes V M st /\ current_origin_realizes V N st' /\
  (!k. n <= k ==> current_origin_absent (visit,l,i,k) M /\
                    current_origin_absent (visit,l,i,k) N) /\
  current_paired_after outs outs' st st' after after' ==>
  current_paired_origin_after V M N visit l i n outs outs' st st' after after'
Proof
  simp[current_paired_after_def, current_paired_origin_after_def] >> rpt strip_tac >>
  qexists_tac `events` >> simp[] >> irule current_indexed_writes_origins >>
  simp[] >> conj_tac >> goal_assum (drule_at Any) >> simp[]
QED

Definition current_paired_origin_result_def:
  current_paired_origin_result V M N visit l i n outs outs' st st' result result' <=>
    case (result,result') of
      (OK after,OK after') =>
        current_paired_origin_after V M N visit l i n outs outs' st st' after after'
    | (Halt after,Halt after') =>
        current_paired_origin_after V M N visit l i n outs outs' st st' after after'
    | (Abort reason after,Abort reason' after') => reason = reason' /\
        current_paired_origin_after V M N visit l i n outs outs' st st' after after'
    | (IntRet ret after,IntRet ret' after') => ret = ret' /\
        current_paired_origin_after V M N visit l i n outs outs' st st' after after'
    | (Error msg,Error msg') => msg = msg'
    | _ => F
End

Theorem current_paired_result_origins:
  current_origin_realizes V M st /\ current_origin_realizes V N st' /\
  (!k. n <= k ==> current_origin_absent (visit,l,i,k) M /\
                    current_origin_absent (visit,l,i,k) N) /\
  current_paired_result_writes outs outs' st st' result result' ==>
  current_paired_origin_result V M N visit l i n outs outs' st st' result result'
Proof
  Cases_on `result` >> Cases_on `result'` >>
  simp[current_paired_result_writes_def, current_paired_origin_result_def] >>
  rpt strip_tac >> irule current_paired_after_origins >> simp[]
QED

Theorem current_step_inst_base_origins:
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\ inst'.inst_id = inst.inst_id /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst.inst_outputs = LENGTH inst'.inst_outputs /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' /\
  current_origin_realizes V M st /\ current_origin_realizes V N st' /\
  (!k. n <= k ==> current_origin_absent (visit,l,i,k) M /\
                    current_origin_absent (visit,l,i,k) N) ==>
  current_paired_origin_result V M N visit l i n inst.inst_outputs inst'.inst_outputs st st'
    (step_inst_base inst st) (step_inst_base inst' st')
Proof
  strip_tac >> gvs[] >> irule current_paired_result_origins >> simp[] >>
  irule current_step_inst_base_paired >> simp[] >> qexists_tac `rs` >>
  simp[]
QED
