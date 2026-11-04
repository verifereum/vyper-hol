(* Dynamic origins: (visit, source block, source instruction, output).
   Visit 0 is reserved for entry bindings; static allocation tokens are not
   dynamic origins. Indices/phases are supplied separately by PhaseShape. *)
Theory makeSsaCurrentJointRuntime
Ancestors
  makeSsaCurrentPhaseShape makeSsaCurrentTemporalWrites makeSsaCurrentOrdinary
  makeSsaCurrentSimDefs makeSsaCurrentDefs venomState stateFrame finite_map alist list

Definition current_origin_realizes_def:
  current_origin_realizes
    (V : (num # string # num # num) -> bytes32 option) M st <=>
    !n. lookup_var n st = case ALOOKUP M n of NONE => NONE | SOME origin => V origin
End

Definition current_joint_rel_def:
  current_joint_rel V source_origins target_origins rs D st st' <=>
    execution_frame st = execution_frame st' /\
    st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
    current_origin_realizes V source_origins st /\ current_origin_realizes V target_origins st' /\
    (!v. MEM v D ==> ALOOKUP source_origins v = ALOOKUP target_origins (latest_current_name rs v))
End

Theorem current_joint_name_agree:
  current_joint_rel V source_origins target_origins rs D st st' ==> current_name_agree rs D st st'
Proof
  simp[current_joint_rel_def, current_origin_realizes_def, current_name_agree_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem current_joint_frame:
  current_joint_rel V source_origins target_origins rs D st st' ==> execution_frame st = execution_frame st'
Proof
  simp[current_joint_rel_def]
QED

Theorem current_origin_realizes_write:
  current_origin_realizes V M st /\ V origin = SOME value ==>
  current_origin_realizes V ((dst,origin)::M) (update_var dst value st)
Proof
  simp[current_origin_realizes_def] >> rpt strip_tac >>
  Cases_on `n = dst` >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Theorem current_origin_snapshot_read:
  current_origin_realizes V incoming snapshot /\
  ALOOKUP incoming src = SOME origin /\ V origin = SOME value ==>
  lookup_var src snapshot = SOME value
Proof
  simp[current_origin_realizes_def] >> metis_tac[]
QED

Theorem current_origin_snapshot_copy:
  current_origin_realizes V incoming snapshot /\ current_origin_realizes V M st /\
  ALOOKUP incoming src = SOME origin /\ V origin = SOME value ==>
  lookup_var src snapshot = SOME value /\
  current_origin_copy incoming src dst M = SOME ((dst,origin)::M) /\
  current_origin_realizes V ((dst,origin)::M) (update_var dst value st)
Proof
  strip_tac >> drule_all current_origin_snapshot_read >> strip_tac >>
  simp[current_origin_copy_def] >> irule current_origin_realizes_write >> simp[]
QED

Theorem current_origin_sequential_copy:
  current_origin_realizes V M st /\
  ALOOKUP M src = SOME origin /\ V origin = SOME value ==>
  current_origin_copy M src dst M = SOME ((dst,origin)::M) /\
  current_origin_realizes V ((dst,origin)::M) (update_var dst value st)
Proof
  strip_tac >> simp[current_origin_copy_def] >>
  irule current_origin_realizes_write >> simp[]
QED

Definition current_ordinary_demand_def:
  (current_ordinary_demand [] exit = exit) /\
  (current_ordinary_demand (i::rest) exit =
    operand_vars i.inst_operands ++
    current_before_outputs i.inst_outputs (current_ordinary_demand rest exit))
End

Theorem current_ordinary_demand_operands:
  MEM v (operand_vars i.inst_operands) ==>
  MEM v (current_ordinary_demand (i::rest) exit)
Proof
  simp[current_ordinary_demand_def]
QED

Theorem current_ordinary_demand_before_outputs:
  MEM v (current_before_outputs i.inst_outputs (current_ordinary_demand rest exit)) ==>
  MEM v (current_ordinary_demand (i::rest) exit)
Proof
  simp[current_ordinary_demand_def]
QED

Theorem current_joint_restrict:
  current_joint_rel V source_origins target_origins rs D st st' /\ (!v. MEM v smaller ==> MEM v D) ==>
  current_joint_rel V source_origins target_origins rs smaller st st'
Proof
  simp[current_joint_rel_def] >> metis_tac[]
QED

Theorem current_joint_ordinary_inputs:
  current_joint_rel V source_origins target_origins rs (current_ordinary_demand (i::rest) exit) st st' ==>
  current_name_agree rs (operand_vars i.inst_operands) st st' /\
  current_name_agree rs
    (current_before_outputs i.inst_outputs (current_ordinary_demand rest exit)) st st'
Proof
  strip_tac >> drule current_joint_name_agree >>
  simp[current_ordinary_demand_def, current_name_agree_def]
QED

Definition current_origin_absent_def:
  current_origin_absent origin M <=> !n. ALOOKUP M n <> SOME origin
End

Theorem current_origin_realizes_extensional:
  current_origin_realizes V M st /\
  (!n origin. ALOOKUP M n = SOME origin ==> valuation origin = V origin) ==>
  current_origin_realizes valuation M st
Proof
  simp[current_origin_realizes_def] >> rpt strip_tac >>
  Cases_on `ALOOKUP M n` >> simp[] >> metis_tac[]
QED

Theorem current_origin_realizes_fresh_extension:
  current_origin_realizes V M st /\ current_origin_absent origin M ==>
  current_origin_realizes ((origin =+ SOME value) V) M st
Proof
  strip_tac >> irule current_origin_realizes_extensional >>
  qexists_tac `V` >> simp[] >>
  gvs[current_origin_absent_def] >> rpt strip_tac >>
  `origin' <> origin` by metis_tac[] >> simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem current_origin_realizes_fresh_write:
  current_origin_realizes V M st /\ current_origin_absent origin M ==>
  current_origin_realizes ((origin =+ SOME value) V)
    ((dst,origin)::M) (update_var dst value st)
Proof
  strip_tac >> irule current_origin_realizes_write >> simp[] >>
  irule current_origin_realizes_fresh_extension >> simp[]
QED

Theorem current_origin_realizes_paired_fresh_write:
  current_origin_realizes V M st /\ current_origin_realizes V N st' /\
  current_origin_absent origin M /\ current_origin_absent origin N ==>
  current_origin_realizes ((origin =+ SOME value) V)
    ((dst,origin)::M) (update_var dst value st) /\
  current_origin_realizes ((origin =+ SOME value) V)
    ((dst',origin)::N) (update_var dst' value st')
Proof
  strip_tac >> conj_tac >> irule current_origin_realizes_fresh_write >> simp[]
QED

Theorem current_origin_absent_cons:
  current_origin_absent fresh M /\ fresh <> origin ==>
  current_origin_absent fresh ((dst,origin)::M)
Proof
  simp[current_origin_absent_def] >> rpt strip_tac >>
  Cases_on `dst = n` >> gvs[]
QED
