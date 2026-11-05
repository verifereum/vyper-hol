Theory makeSsaCurrentCompletedOrdinary
Ancestors makeSsaCurrentJointOrdinaryStep makeSsaCurrentExecutionHistory
  makeSsaCurrentOrdinary makeSsaCurrentOrdinaryJoint
  makeSsaCurrentSourceCuts makeSsaCurrentCleanupShape makeSsaCurrentFinalBlock
  makeSsaCurrentTreeTrace makeSsaCurrentRenameTrace makeSsaCurrentTreePaths dretShapeDefs
  makeSsaCurrentPairedRuntime makeSsaCurrentJointRuntime
  o1PassLift makeSsaCurrentValueInvariant venomState venomExecSemantics
  stateFrame venomWf venomInst cfgHelpers venomExecProps finite_map alist list pair combin

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

Theorem current_ordinary_fields_wf:
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  LENGTH inst'.inst_outputs = LENGTH inst.inst_outputs ==>
  inst_wf inst'
Proof
  strip_tac >>
  `parse_dret_shape inst' = parse_dret_shape inst` by
    metis_tac[current_parse_dret_shape] >>
  `inst'.inst_outputs = [] <=> inst.inst_outputs = []` by
    metis_tac[LENGTH_NIL] >>
  fs[inst_wf_def] >>
  Cases_on `inst.inst_opcode` >>
  fs[current_rename_operands_map, LENGTH_NIL] >>
  fs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `op` >> simp[get_label_def]
QED

Theorem current_no_id_wf:
  current_inst_no_id x = current_inst_no_id y ==> (inst_wf x <=> inst_wf y)
Proof
  strip_tac >>
  `!inst. inst_wf (current_inst_no_id inst) <=> inst_wf inst` by
    simp[current_inst_no_id_def, inst_wf_def, parse_dret_shape_def] >>
  metis_tac[]
QED

Theorem current_certificate_ordinary_execution_shape:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_inst_wf fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::later /\
  lookup_block l fn.fn_blocks = SOME old /\
  old.bb_instructions = phis ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  j < LENGTH tail /\ (EL j tail).inst_opcode <> PHI /\ i = LENGTH phis + j /\
  EVERY (\inst. inst.inst_opcode = PHI) ip /\
  current_edge_shape (old with bb_instructions := ip ++ old.bb_instructions) bb /\
  lookup_block l fn'.fn_blocks = SOME out ==>
  get_instruction old i = SOME (EL i old.bb_instructions) /\
  get_instruction out (LENGTH ip+i) = SOME (EL (LENGTH ip+i) out.bb_instructions) /\
  inst_wf (EL i old.bb_instructions) /\
  inst_wf (EL (LENGTH ip+i) out.bb_instructions) /\
  (EL i old.bb_instructions).inst_opcode <> PHI /\
  (EL (LENGTH ip+i) out.bb_instructions).inst_opcode =
    (EL i old.bb_instructions).inst_opcode
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_ordinary_position >> strip_tac >>
  `LENGTH ip' = LENGTH ip` by
    (imp_res_tac current_edge_shape_opcodes >>
     qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `out' = out` by metis_tac[optionTheory.SOME_11] >>
  `i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_opcode <> PHI` by
    simp[EL_APPEND_EQN] >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  drule_all current_inst_trace_base_fields >> strip_tac >>
  `inst_wf (EL (LENGTH ip+i) ren)` by
    (irule current_ordinary_fields_wf >> goal_assum $ drule_at Any >> metis_tac[]) >>
  `inst_wf (EL (LENGTH ip+i) out.bb_instructions)` by metis_tac[current_no_id_wf] >>
  `MEM (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events` by simp[] >>
  drule current_certificate_source_shape >>
  disch_then (qspecl_then [`old`,
    `(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)`, `eb`] mp_tac) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
    [current_event_label_def, current_event_input_block_def]) >>
  `LENGTH ren = LENGTH bb.bb_instructions` by
    (fs[current_event_trace_def] >> metis_tac[current_local_trace_lengths]) >>
  `LENGTH bb.bb_instructions = LENGTH ip + LENGTH old.bb_instructions` by
    (fs[current_edge_shape_def, LIST_REL_EL_EQN]) >>
  drule current_structural_certificate_final_event >>
  disch_then (qspecl_then
    [`(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)`, `eb`, `before`, `later`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
    [current_event_label_def, current_event_renamed_block_def]) >>
  `LENGTH out.bb_instructions = LENGTH ren` by
    (Cases_on `blocks_have_leading_phi fn.fn_blocks` >>
     gvs[current_cleanup_block_length, current_replay_edges_length]) >>
  `!inst. (current_inst_no_id inst).inst_opcode = inst.inst_opcode` by
    simp[current_inst_no_id_def] >>
  ` (EL (LENGTH ip+i) out.bb_instructions).inst_opcode =
      (EL i old.bb_instructions).inst_opcode` by metis_tac[] >>
  `LENGTH ip+i < LENGTH out.bb_instructions` by decide_tac >>
  simp[get_instruction_def]
QED

Theorem current_certificate_completed_ordinary:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_inst_wf fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::later /\
  lookup_block l fn.fn_blocks = SOME old /\
  old.bb_instructions = phis ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  j < LENGTH tail /\ (EL j tail).inst_opcode <> PHI /\ i = LENGTH phis + j ==>
  ?U ip out rs E rt Et.
    EVERY (\inst. inst.inst_opcode = PHI) ip /\
    current_edge_shape (old with bb_instructions := ip ++ old.bb_instructions) bb /\
    lookup_block l fn'.fn_blocks = SOME out /\
    current_source_cut A
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (LENGTH ip+i) rs E /\
    current_source_cut A
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (SUC (LENGTH ip+i)) rt Et /\
    (!st st' post V M N D a archive C C' loc loc' seed seed' phases phases' fuel fuel'.
      (!v. MEM v D ==> MEM v U) /\
      current_joint_rel V M N rs
        (venomInst$operand_vars (EL i old.bb_instructions).inst_operands ++
          current_before_outputs (EL i old.bb_instructions).inst_outputs D) st st' /\
      current_singleton_agree (current_instruction_singleton_table fn H) st st' /\
      current_map_below a M /\ current_map_below a N /\ current_archive_valid a V archive /\
      current_actual_prefix fn C loc seed phases (SOME (CurrentBody fuel old)) (OK st) st /\
      current_actual_prefix fn' C' loc' seed' phases' (SOME (CurrentBody fuel' out)) (OK st') st' /\
      st.vs_current_bb = l /\ st.vs_inst_idx = i /\ st'.vs_inst_idx = LENGTH ip+i /\
      (EL i old.bb_instructions).inst_opcode <> INVOKE /\
      ~is_terminator (EL i old.bb_instructions).inst_opcode /\
      step_inst_base (EL i old.bb_instructions) st = OK post ==>
      ?n writes post'.
        step_inst_base (EL (LENGTH ip+i) out.bb_instructions) st' = OK post' /\
        current_indexed_writes (EL i old.bb_instructions).inst_outputs writes st post /\
        current_indexed_writes (EL (LENGTH ip+i) out.bb_instructions).inst_outputs writes st' post' /\
        MAP FST writes = GENLIST I (LENGTH (EL i old.bb_instructions).inst_outputs) /\
        current_actual_prefix fn C loc seed
          (phases ++ [CurrentOrdinary l i (EL i old.bb_instructions); CurrentControl])
          (SOME (CurrentBody fuel old))
          (OK (post with vs_inst_idx := SUC i)) (post with vs_inst_idx := SUC i) /\
        current_actual_prefix fn' C' loc' seed'
          (phases' ++ [CurrentOrdinary l (LENGTH ip+i)
            (EL (LENGTH ip+i) out.bb_instructions); CurrentControl])
          (SOME (CurrentBody fuel' out))
          (OK (post' with vs_inst_idx := SUC (LENGTH ip+i)))
          (post' with vs_inst_idx := SUC (LENGTH ip+i)) /\
        current_joint_rel (current_event_valuation V a l i n writes)
          (current_event_origins (EL i old.bb_instructions).inst_outputs M a l i n writes)
          (current_event_origins (EL (LENGTH ip+i) out.bb_instructions).inst_outputs N a l i n writes)
          rt D (post with vs_inst_idx := SUC i)
          (post' with vs_inst_idx := SUC (LENGTH ip+i)) /\
        current_singleton_agree (current_instruction_singleton_table fn H)
          (post with vs_inst_idx := SUC i) (post' with vs_inst_idx := SUC (LENGTH ip+i)) /\
        current_map_below (SUC a)
          (current_event_origins (EL i old.bb_instructions).inst_outputs M a l i n writes) /\
        current_map_below (SUC a)
          (current_event_origins (EL (LENGTH ip+i) out.bb_instructions).inst_outputs N a l i n writes) /\
        current_archive_valid (SUC a) (current_event_valuation V a l i n writes) archive)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_ordinary_step_joint_singleton >> strip_tac >>
  drule_all current_certificate_ordinary_execution_shape >> strip_tac >>
  qexistsl_tac [`U`, `ip`, `out`, `rs`, `E`, `rt`, `Et`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `old.bb_instructions = _` kall_tac >>
  qpat_x_assum `i = _` kall_tac >>
  qpat_x_assum `events = _` kall_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `wf_function _` kall_tac >>
  qpat_x_assum `all_reachable _` kall_tac >>
  qpat_x_assum `entry_block _ = _` kall_tac >>
  qpat_x_assum `fn_inst_wf _` kall_tac >>
  qpat_x_assum `ir_supply_covers_fn _ _` kall_tac >>
  qpat_x_assum `ir_supply_inst_ok _` kall_tac >>
  qpat_x_assum `EVERY _ phis` kall_tac >>
  qpat_x_assum `tail = [] \/ _` kall_tac >>
  qpat_x_assum `j < _` kall_tac >>
  qpat_x_assum `(EL j tail).inst_opcode <> _` kall_tac >>
  qpat_x_assum `EVERY _ ip` kall_tac >>
  qpat_x_assum `current_edge_shape _ _` kall_tac >>
  ntac 2 (qpat_x_assum `current_source_cut _ _ _ _ _` kall_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!st st' post V M N D visit. _` (drule_all_then (qspec_then `a` strip_assume_tac)) >>
  qexistsl_tac [`n`, `writes`, `post'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `st'.vs_current_bb = l` by fs[current_joint_rel_def, execution_frame_def] >>
  conj_tac >- metis_tac[current_completed_ordinary_continue] >>
  conj_tac >- metis_tac[current_completed_ordinary_continue] >>
  conj_tac >- (irule current_joint_rel_indices >> first_assum ACCEPT_TAC) >>
  conj_tac >- (irule current_singleton_agree_indices >> first_assum ACCEPT_TAC) >>
  simp[current_event_origins_below, current_event_archive_valid]
QED
