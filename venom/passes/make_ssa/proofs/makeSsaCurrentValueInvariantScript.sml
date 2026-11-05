Theory makeSsaCurrentValueInvariant
Ancestors makeSsaCurrentOrdinaryJoint makeSsaCurrentCertificate
  makeSsaCurrentPairedWrites makeSsaCurrentFullWrites
  makeSsaCurrentDemand makeSsaCurrentRetainedRead makeSsaCurrentSingleSiteSegment
  makeSsaCurrentSimDefs venomState finite_map list alist

(* Count original output OCCURRENCES, including repeated outputs of one inst.
   Inserted definitions are deliberately absent from this permanent table. *)
Definition current_original_table_def:
  current_original_table fn = FLAT (MAP (\bb.
    FLAT (current_original_annotations bb.bb_label 0 bb.bb_instructions)) fn.fn_blocks)
End

Definition current_singleton_table_def:
  current_singleton_table fn H = FLAT (MAP (\tv.
    if LENGTH (FILTER (\tw. SND tw = SND tv) (current_original_table fn)) = 1
    then case current_token_name H (FST tv) of
           NONE => [] | SOME n => [(SND tv,n)]
    else []) (current_original_table fn))
End

Definition current_singleton_agree_def:
  current_singleton_agree table st st' <=>
    !v n. MEM (v,n) table ==> lookup_var v st = lookup_var n st'
End

(* Separation is stated pointwise, so the write theorem also covers updates
   of names absent from the permanent table. *)
Definition current_table_write_aligned_def:
  current_table_write_aligned table x y <=>
    !v n. MEM (v,n) table ==> (v = x <=> n = y)
End

Theorem current_singleton_agree_empty:
  st.vs_vars = FEMPTY /\ st'.vs_vars = FEMPTY ==>
  current_singleton_agree table st st'
Proof
  simp[current_singleton_agree_def, lookup_var_def]
QED

Theorem current_singleton_agree_write:
  current_singleton_agree table st st' /\
  current_table_write_aligned table x y ==>
  current_singleton_agree table (update_var x value st) (update_var y value st')
Proof
  simp[current_singleton_agree_def, current_table_write_aligned_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem current_singleton_agree_member_write:
  current_singleton_agree table st st' /\ MEM (x,y) table /\
  (!v n. MEM (v,n) table ==> (v = x <=> n = y)) ==>
  current_singleton_agree table (update_var x value st) (update_var y value st')
Proof
  metis_tac[current_singleton_agree_write, current_table_write_aligned_def]
QED

Theorem current_singleton_agree_writes:
  !writes st st'. current_singleton_agree table st st' /\
  EVERY (\xyv. current_table_write_aligned table (FST (FST xyv)) (SND (FST xyv))) writes ==>
  current_singleton_agree table
    (FOLDL (\s xyv. update_var (FST (FST xyv)) (SND xyv) s) st writes)
    (FOLDL (\s xyv. update_var (SND (FST xyv)) (SND xyv) s) st' writes)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> irule current_singleton_agree_write >> simp[]
QED

Theorem current_singleton_fold_no_write[local]:
  !writes m. ~MEM v (MAP FST writes) ==>
  FLOOKUP (FOLDL (\m dv. m |+ dv) m writes) v = FLOOKUP m v
Proof
  Induct >> simp[] >> Cases_on `h` >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  first_x_assum (qspec_then `m |+ (q,r)` mp_tac) >> simp[FLOOKUP_UPDATE]
QED

Theorem current_singleton_agree_nonwrites:
  current_singleton_agree table st st' /\
  (!v n. MEM (v,n) table ==> ~MEM v (MAP FST writes) /\ ~MEM n (MAP FST writes')) ==>
  current_singleton_agree table
    (st with vs_vars := FOLDL (\m dv. m |+ dv) st.vs_vars writes)
    (st' with vs_vars := FOLDL (\m dv. m |+ dv) st'.vs_vars writes')
Proof
  simp[current_singleton_agree_def, lookup_var_def] >> rpt strip_tac >>
  metis_tac[current_singleton_fold_no_write]
QED

Theorem current_singleton_indexed_fold[local]:
  !events m m'.
  (!v n. MEM (v,n) table ==> FLOOKUP m v = FLOOKUP m' n) /\
  EVERY (\kv. current_table_write_aligned table
    (EL (FST kv) outs) (EL (FST kv) outs')) events ==>
  !v n. MEM (v,n) table ==>
    FLOOKUP (FOLDL (\m kv. m |+ (EL (FST kv) outs,SND kv)) m events) v =
    FLOOKUP (FOLDL (\m kv. m |+ (EL (FST kv) outs',SND kv)) m' events) n
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> rpt strip_tac >>
  fs[current_table_write_aligned_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem current_singleton_agree_indexed:
  current_singleton_agree table st st' /\
  current_indexed_writes outs events st after /\
  current_indexed_writes outs' events st' after' /\
  EVERY (\kv. current_table_write_aligned table
    (EL (FST kv) outs) (EL (FST kv) outs')) events ==>
  current_singleton_agree table after after'
Proof
  simp[current_singleton_agree_def, lookup_var_def, current_indexed_writes_def] >>
  metis_tac[current_singleton_indexed_fold]
QED

(* An actual traced nondefining instruction: no extra singleton exclusion
   premise is required because both actual output footprints are empty.
   This is not the general defining-ordinary successor theorem. *)
Theorem current_singleton_trace_nondefining:
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_outputs = [] /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' /\
  current_singleton_agree table st st' /\
  step_inst_base inst st = OK after ==>
  ?after'. step_inst_base inst' st' = OK after' /\
    current_singleton_agree table after after' /\
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb
Proof
  strip_tac >>
  drule current_inst_trace_base_fields >> simp[] >> strip_tac >>
  `?after' events. step_inst_base inst' st' = OK after' /\
    current_indexed_writes inst.inst_outputs events st after /\
    current_indexed_writes inst'.inst_outputs events st' after' /\
    MAP FST events = GENLIST I (LENGTH inst.inst_outputs) /\
    execution_frame after = execution_frame after' /\
    after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb` by
    (irule current_step_inst_base_full_writes >>
     asm_rewrite_tac[] >> qexists_tac `rs` >> asm_rewrite_tac[]) >>
  pop_assum strip_assume_tac >>
  `events = []` by (Cases_on `events` >> gvs[]) >>
  `current_singleton_agree table after after'` by
    (irule current_singleton_agree_indexed >> metis_tac[EVERY_DEF]) >>
  qexists_tac `after'` >> gvs[stateFrameTheory.execution_frame_def]
QED

(* Persistent canonical agreement alone does not supply predecessor-selector
   agreement.  This is an interface counterexample, NOT a task counterexample:
   these stores need not be reachable through any paired execution. *)
Theorem current_singleton_selector_gap:
  current_singleton_agree [("v","canonical")]
    (st with vs_vars := FEMPTY |+ ("v",1w))
    (st' with vs_vars := FEMPTY |+ ("canonical",1w) |+ ("selected",2w)) /\
  lookup_var "v" (st with vs_vars := FEMPTY |+ ("v",1w)) <>
  lookup_var "selected"
    (st' with vs_vars := FEMPTY |+ ("canonical",1w) |+ ("selected",2w))
Proof
  simp[current_singleton_agree_def, lookup_var_def, FLOOKUP_UPDATE,
    wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

(* The precise additional value bridge required by retained reads.  This
   lemma records consumption of the bridge; it does not establish it from
   an actual path or from singleton-definition uniqueness. *)
Theorem current_singleton_selected_read:
  current_singleton_agree table st st' /\ MEM (v,n) table /\
  lookup_var n st' = lookup_var (latest_current_name rs v) st' ==>
  lookup_var v st = lookup_var (latest_current_name rs v) st'
Proof
  metis_tac[current_singleton_agree_def]
QED

(* The frozen PHI premise counts defining INSTRUCTIONS, not output slots.
   Consequently a permanent table restricted to unique output occurrences
   does not cover all legal original PHI operands. *)
Definition current_singleton_slots_probe_fn_def:
  current_singleton_slots_probe_fn = mk_raw_function "slots"
    [<| bb_label := "E"; bb_instructions :=
        [current_probe_inst 0 BUMP [Lit 3w; Lit 4w] ["x";"x"];
         current_probe_inst 1 JMP [Label "D"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [current_probe_inst 2 PHI [Label "E"; Var "x"; Label "D"; Var "y"] ["v"];
         current_probe_inst 3 ASSIGN [Lit 1w] ["y"];
         current_probe_inst 4 JMP [Label "D"] []] |>]
End

Theorem current_singleton_instruction_not_slot_probe:
  fn_phi_operands_single_def current_singleton_slots_probe_fn /\
  fn_inst_wf current_singleton_slots_probe_fn /\
  LENGTH (FILTER (\tv. SND tv = "x")
    (current_original_table current_singleton_slots_probe_fn)) = 2
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >>
  gvs[venomInstTheory.phi_pairs_def]
QED

Theorem current_singleton_slots_missing:
  !H n. ~MEM ("x",n) (current_singleton_table current_singleton_slots_probe_fn H)
Proof
  simp[current_singleton_table_def, current_original_table_def,
    current_singleton_slots_probe_fn_def, current_probe_inst_def,
    venomInstTheory.mk_raw_function_def, current_original_annotations_def,
    current_original_outputs_def] >> rpt gen_tac >>
  rpt (CASE_TAC >> simp[])
QED

(* Probe branch matrix (not a claim of global preservation):
   entry: empty singleton stores checked; certificate-derived phase/position
     initialization and the combined demanded relation are NOT yet defined.
   ordinary: synchronized indexed writes preserve singleton agreement under
     explicit table-key hit alignment; an actual traced successful zero-output
     step discharges those exclusions. General defining steps still need the
     static canonical-name selection theorem (including repeated BUMP outputs).
   original PHI: selected_read consumes canonical-to-selected value equality;
     selector_gap refutes deriving it from the singleton clause alone. A paired
     reachable-prefix/nonclobber invariant is needed to establish that bridge.
   inserted PHI: no forward target batch-success argument established here.
   cleanup: no selected-self temporal invariant established here; same-header
     reinsertion must use the retained batch result rather than entry values.
   control: no transfer of demands/selectors to a successor established here.
   INVOKE: no full-call successor theorem established here (base steps are not
     full exec_inst calls).
   terminal prefixes: no terminating-direction or intermediate-frame transport
     theorem established here.

   Definition problem exposed by instruction_not_slot_probe/slots_missing:
   the frozen single-def premise permits two outputs of ONE instruction to the
   same source spelling. The canonical table must select its LAST effective
   output slot, rather than omit such a spelling or relate it to both slots.
   This is a repair to proof infrastructure, not a change to the frozen task.
*)
