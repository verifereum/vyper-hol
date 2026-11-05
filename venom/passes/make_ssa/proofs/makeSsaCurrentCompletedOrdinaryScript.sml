Theory makeSsaCurrentCompletedOrdinary
Ancestors makeSsaCurrentJointOrdinaryStep makeSsaCurrentExecutionHistory
  makeSsaCurrentPairedRuntime makeSsaCurrentJointRuntime
  o1PassLift makeSsaCurrentValueInvariant venomState venomExecSemantics
  stateFrame venomWf finite_map alist list pair combin

(* Bounds include shadowed map entries. Archives record values, not execution. *)
Definition current_map_below_def:
  current_map_below a (M : (string # (num # string # num # num)) list) <=>
    !name origin. MEM (name,origin) M ==> FST origin < a
End

Definition current_archive_valid_def:
  current_archive_valid a (V : (num # string # num # num) -> bytes32 option) archive <=>
    !origin w. MEM (origin,w) archive ==> FST origin < a /\ V origin = SOME w
End

Theorem current_event_valuation_below:
  !writes (V : (num # string # num # num) -> bytes32 option) n origin.
    FST origin < (a:num) ==>
    current_event_valuation V a l i n writes origin = V origin
Proof
  Induct >- simp[current_event_valuation_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  simp[current_event_valuation_def] >>
  first_x_assum (qspecl_then [`((a,l,i,n) =+ SOME h1) V`, `SUC n`, `origin`] mp_tac) >>
  asm_rewrite_tac[] >> disch_then SUBST1_TAC >>
  `origin <> (a,l,i,n)` by (strip_tac >> gvs[] >> decide_tac) >>
  simp[APPLY_UPDATE_THM]
QED

Theorem current_event_origins_bounded:
  !writes M n. current_map_below b M /\ a < b ==>
    current_map_below b (current_event_origins outs M a l i n writes)
Proof
  Induct >- simp[current_event_origins_def] >>
  Cases_on `h` >> rpt strip_tac >>
  simp[current_event_origins_def] >> first_x_assum irule >>
  fs[current_map_below_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_event_origins_below:
  current_map_below a M ==>
    current_map_below (SUC a) (current_event_origins outs M a l i n writes)
Proof
  strip_tac >> irule current_event_origins_bounded >>
  fs[current_map_below_def] >> rpt strip_tac >> res_tac >> decide_tac
QED

Theorem current_event_archive_valid:
  current_archive_valid a V archive ==>
  current_archive_valid (SUC a) (current_event_valuation V a l i n writes) archive
Proof
  simp[current_archive_valid_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[current_event_valuation_below]
QED

Theorem current_completed_empty_entry:
  fn_entry_state fn e /\ fn_entry_state fn' e ==>
  current_actual_prefix fn C (CurrentEntry fuel) e []
    (SOME (CurrentEntry fuel)) (OK e) e /\
  current_actual_prefix fn' C' (CurrentEntry fuel') e []
    (SOME (CurrentEntry fuel')) (OK e) e /\
  current_origin_realizes (\origin. NONE) [] e /\
  current_map_below 1 [] /\ current_archive_valid 1 (\origin. NONE) [] /\
  current_singleton_agree table e e
Proof
  simp[fn_entry_state_def, current_origin_realizes_def, lookup_var_def,
    current_map_below_def, current_archive_valid_def, current_singleton_agree_def,
    current_actual_prefix_rules]
QED

Theorem current_completed_ordinary_continue:
  current_actual_prefix fn C loc seed phases (SOME (CurrentBody fuel bb)) (OK st) st /\
  lookup_block st.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb st.vs_inst_idx = SOME inst /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst st = OK post ==>
  current_actual_prefix fn C loc seed
    (phases ++ [CurrentOrdinary st.vs_current_bb st.vs_inst_idx inst; CurrentControl])
    (SOME (CurrentBody fuel bb))
    (OK (post with vs_inst_idx := SUC st.vs_inst_idx))
    (post with vs_inst_idx := SUC st.vs_inst_idx)
Proof
  strip_tac >> drule current_actual_prefix_append >>
  disch_then irule >> simp[] >>
  irule (cj 2 current_actual_prefix_rules) >>
  irule (cj 2 current_execution_edge_rules) >>
  simp[step_inst_non_invoke] >> metis_tac[]
QED

Theorem current_joint_rel_indices:
  current_joint_rel V M N rs D st st' ==>
  current_joint_rel V M N rs D (st with vs_inst_idx := k) (st' with vs_inst_idx := k')
Proof
  simp[current_joint_rel_def, current_origin_realizes_def, lookup_var_def,
    execution_frame_def]
QED

Theorem current_singleton_agree_indices:
  current_singleton_agree table st st' ==>
  current_singleton_agree table (st with vs_inst_idx := k) (st' with vs_inst_idx := k')
Proof
  simp[current_singleton_agree_def, lookup_var_def]
QED

