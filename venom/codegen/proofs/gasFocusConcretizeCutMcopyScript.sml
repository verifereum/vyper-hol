Theory gasFocusConcretizeCutMcopy
Ancestors
  concretizePtrPairedPrefix concretizePtrWritePurity concretizePtrOpaqueRetpc
  concretizePtrChronologicalHistory concretizePtrRequestHistory
  concretizeStepStructure concretizePtrCopyContent concretizePtrParamSupport
  concretizePtrValueTransport contextCodegenRel codegenRel
  concretizePtrOrdinaryNext concretizePtrLedgerProbe concretizePtrSourceOwnership
  concretizePtrDeletedGapHistory concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrActivationChronology concretizePtrPrefixWriteAttach concretizePtrPairedFields
  concretizePtrPrefixLedger concretizePtrBytes concretizePtrComparisonTransport
  concretizePtrStagePlacements
  ptrDiscipline venomWf venomInst venomExecSemantics venomState memLocDefs
  passSimulationDefs words list arithmetic finite_map

Theorem ptr_focus_mcopy_inputs[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = MCOPY /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\
  inst_wf a.po_inst /\ MEM a.po_inst (fn_insts a.po_fn) /\
  fn_ptr_ok P a.po_fn /\ ptr_static_support P a.po_fn TG /\
  EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state ==>
  ?dop sop nop d r dt rt n.
    a.po_inst.inst_operands = [dop;sop;nop] /\
    a.po_inst.inst_outputs = [] /\ at.po_inst = a.po_inst /\
    eval_operand dop a.po_state = SOME d /\
    eval_operand sop a.po_state = SOME r /\
    eval_operand nop a.po_state = SOME n /\
    eval_operand dop at.po_state = SOME dt /\
    eval_operand sop at.po_state = SOME rt /\
    eval_operand nop at.po_state = SOME n /\
    op_taint a.po_taint dop = {} /\ op_taint a.po_taint sop = {} /\
    ptr_lookup_transport births positions (op_prov TG dop) {} (SOME d) (SOME dt) /\
    ptr_lookup_transport births positions (op_prov TG sop) {} (SOME r) (SOME rt) /\
    MEM (w2n r,w2n n) (source_memory_read_ranges a.po_inst a.po_state) /\
    MEM (w2n d,w2n n) (source_memory_write_ranges a.po_inst a.po_state)
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  `?dop sop nop. a.po_inst.inst_operands = [dop;sop;nop] /\
    a.po_inst.inst_outputs = []` by gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `op_taint a.po_taint dop = {} /\ op_taint a.po_taint sop = {} /\
   op_taint a.po_taint nop = {}` by
    (fs[taint_ok_def] >>
     qpat_x_assum `!op. _ /\ _ ==> _` mp_tac >> simp[] >> metis_tac[]) >>
  `!v. v IN FDOM TG ==> v IN fn_pv P a.po_fn` by
    (fs[ptr_static_support_def] >> metis_tac[FLOOKUP_DEF]) >>
  `mem_write_ops a.po_inst = SOME
     <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>` by
    simp[mem_write_ops_def] >>
  `op_prov TG nop = NONE` by
    (drule ptr_write_max_size_no_provenance >> simp[] >> disch_then drule >> simp[]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `!op. MEM op [dop;sop;nop] ==>
     ptr_lookup_transport births positions (op_prov TG op)
       (op_taint a.po_taint op)
       (eval_operand op a.po_state) (eval_operand op at.po_state)` by
    (rpt strip_tac >> irule ptr_mixed_vars_eval >>
     simp[] >> qexistsl [`a.po_fn`,`at.po_fn`] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `ptr_lookup_transport births positions (op_prov TG dop) {}
     (eval_operand dop a.po_state) (SOME dst) /\
   ptr_lookup_transport births positions (op_prov TG sop) {}
     (eval_operand sop a.po_state) (SOME src) /\
   ptr_lookup_transport births positions NONE {}
     (eval_operand nop a.po_state) (SOME sz)` by
    (qpat_x_assum `!op. MEM op [dop;sop;nop] ==> _` mp_tac >>
     simp[] >> metis_tac[]) >>
  Cases_on `eval_operand dop a.po_state` >> fs[ptr_lookup_transport_def] >>
  Cases_on `eval_operand sop a.po_state` >> fs[ptr_lookup_transport_def] >>
  Cases_on `eval_operand nop a.po_state` >>
  gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty] >>
  simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
       sized_source_write_range_def]
QED

Theorem ptr_focus_mcopy_edge[local]:
  a.po_inst.inst_opcode = MCOPY /\ a.po_inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop a.po_state = SOME d /\ eval_operand sop a.po_state = SOME r /\
  eval_operand nop a.po_state = SOME n /\ ptr_chrono_step C a z ==>
  z.po_stack = a.po_stack /\ z.po_fn = a.po_fn /\ z.po_params = a.po_params /\
  z.po_state = (mcopy (w2n d) (w2n r) (w2n n) a.po_state with
                 vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
  active_inst z.po_fn z.po_inst z.po_state
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_ledger_next_def, ptr_observe_def, ptr_observation_component_equality,
       is_terminator_def, step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  metis_tac[]
QED

Theorem ptr_focus_mcopy_successor[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = MCOPY /\ a.po_inst.inst_outputs = [] /\
  a.po_inst.inst_operands = [dop;sop;nop] /\ at.po_inst = a.po_inst /\
  eval_operand dop a.po_state = SOME d /\ eval_operand sop a.po_state = SOME r /\
  eval_operand nop a.po_state = SOME n /\ eval_operand dop at.po_state = SOME dt /\
  eval_operand sop at.po_state = SOME rt /\ eval_operand nop at.po_state = SOME n /\
  active_inst a.po_fn a.po_inst a.po_state /\ EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp a.po_fn) (Allocation ai.inst_id))) /\
  ptr_chrono_step C' at zt ==>
  ?z.
    ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    ptr_paired_sample positions z zt (tokens,registry,births,PT,TG,saved,entries) /\
    ptr_paired_code R lp positions z.po_fn zt.po_fn /\ ptr_paired_cursor lp z zt /\
    ptr_paired_params positions z zt (tokens,registry,births,PT,TG,saved,entries) /\
    z.po_stack = a.po_stack /\ zt.po_stack = at.po_stack /\
    ptr_chrono_step C a z /\
    z.po_state = (mcopy (w2n d) (w2n r) (w2n n) a.po_state with
                   vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
    zt.po_state = (mcopy (w2n dt) (w2n rt) (w2n n) at.po_state with
                    vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
    z.po_taint = step_taint a.po_inst a.po_state
                   (mcopy (w2n d) (w2n r) (w2n n) a.po_state) a.po_taint
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  qabbrev_tac `post = mcopy (w2n d) (w2n r) (w2n n) a.po_state` >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >>
     simp[Abbr `post`, mcopy_def, write_memory_with_expansion_def] >>
     qexists `a.po_inst` >> simp[is_terminator_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    (`ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG` by
       simp[ptr_tagged_step_def, step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
     `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     `step_inst 0 C a.po_inst a.po_state = OK post` by
       simp[Abbr `post`, step_inst_non_invoke, step_inst_base_opcode_eqs] >>
     drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
        a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]) >>
  drule_then assume_tac ptr_tagged_chrono_step_projection >>
  `zt.po_stack = at.po_stack /\ zt.po_fn = at.po_fn /\ zt.po_params = at.po_params /\
   zt.po_state = (mcopy (w2n dt) (w2n rt) (w2n n) at.po_state with
                    vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
   active_inst zt.po_fn zt.po_inst zt.po_state` by
    (irule ptr_focus_mcopy_edge >> simp[] >> metis_tac[]) >>
  `z.po_stack = a.po_stack /\ z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def, mcopy_def,
         write_memory_with_expansion_def] >>
  qexists `z` >> simp[] >> suspend "successor_fields"
QED

Resume ptr_focus_mcopy_successor[successor_fields]:
  conj_tac
  >- (drule ptr_ownership_overlay_fixed >> strip_tac >>
      drule (cj 3 ptr_structural_transcript_rules) >>
      disch_then drule >> disch_then drule >>
      simp[ptr_activation_tokens_def, ptr_activation_registry_def]) >>
  conj_tac >- suspend "sample" >>
  conj_tac >- fs[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  conj_tac >- suspend "cursor" >>
  gvs[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def,
      ptr_paired_params_def, mcopy_def, write_memory_with_expansion_def]
QED

Resume ptr_focus_mcopy_successor[sample]:
  fs[ptr_paired_sample_def] >>
  simp[ptr_paired_sample_def] >> reverse conj_tac
  >- (gvs[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def,
          mcopy_def, write_memory_with_expansion_def] >>
      irule ptr_history_content_masks >> qexists `a.po_taint` >>
      simp[step_taint_def, set_var_taint_def, adopt_reset_def,
           store_taint_def, imm_taint_def]) >>
  gvs[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def,
      ptr_mixed_vars_def, ptr_opaque_env_def, step_taint_def,
      mcopy_def, write_memory_with_expansion_def, set_var_taint_def,
      lookup_var_def, op_taint_def, DRESTRICT_UNIV] >> metis_tac[]
QED

Resume ptr_focus_mcopy_successor[cursor]:
  irule ptr_ordinary_next_cursor >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  qexistsl [`a`,`at`] >>
  fs[Abbr `post`, mcopy_def, write_memory_with_expansion_def, optionTheory.IS_SOME_EXISTS]
QED

Finalise ptr_focus_mcopy_successor

(* Access either stays in place (fixed or dynamic memory), or is moved by
   the live allocation's translation.  The address transport already gives
   the actual placement of the destination tag. *)
Theorem ptr_focus_mcopy_destination[local]:
  a.po_inst.inst_opcode = MCOPY /\ a.po_inst.inst_operands = [dop;sop;nop] /\
  MEM (w2n d,w2n n) (source_memory_write_ranges a.po_inst a.po_state) /\
  n <> 0w /\ ~in_revert_forward a.po_fn a.po_state /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ptr_ledger_erases (dyn_floor C a.po_state) births TG a.po_prov /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_value_transport births positions (op_prov TG dop) {} d dt /\
  (!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
                 pos + sz < dimword (:256)) ==>
  ptr_paired_write_owner (dyn_floor C a.po_state) lo positions
       (\x. w2n dt + (x - w2n d))
       {x | w2n d <= x /\ x < w2n d + w2n n}
       (tokens,registry,births,PT,TG,saved,entries:num |-> num)
Proof
  strip_tac >>
  `mem_write_ops a.po_inst = SOME
      <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>` by
    simp[mem_write_ops_def] >>
  Cases_on `op_prov a.po_prov dop = NONE /\ w2n d + w2n n <= lo`
  >- (`op_prov TG dop = NONE` by
        (Cases_on `dop` >> gvs[op_prov_def] >> rename1 `FLOOKUP TG v = NONE` >>
         Cases_on `FLOOKUP TG v` >> simp[] >>
         fs[ptr_ledger_erases_def] >>
         qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `v` mp_tac) >>
         simp[ptr_owner_erases_def] >> metis_tac[flookup_thm]) >>
      gvs[ptr_value_transport_scalar_empty] >>
      simp[ptr_paired_write_owner_def] >>
      rpt strip_tac >> disj1_tac >> decide_tac) >>
  `?v b sz. dop = Var v /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
      b <= w2n d /\ w2n d + w2n n <= b+sz` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     simp[access_ok_def] >> strip_tac >>
     qpat_x_assum `!off len. MEM _ (source_memory_write_ranges _ _) /\ _ ==> _`
       (qspecl_then [`w2n d`,`w2n n`] mp_tac) >>
     impl_tac >- (simp[] >> strip_tac >> fs[] >> decide_tac) >>
     simp[]) >>
  `ptr_owner_erases (dyn_floor C a.po_state) births (FLOOKUP TG v) (SOME (b,sz))` by
    (fs[ptr_ledger_erases_def] >>
     qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `v` mp_tac) >> simp[]) >>
  Cases_on `FLOOKUP TG v`
  >- (gvs[ptr_owner_erases_def, op_prov_def, ptr_value_transport_scalar_empty] >>
      simp[ptr_paired_write_owner_def] >>
      rpt strip_tac >> disj2_tac >> disj2_tac >> decide_tac) >>
  rename1 `FLOOKUP TG v = SOME owner` >> PairCases_on `owner` >>
  `MEM owner0 tokens` by (drule_all ptr_source_ownership_live_prov >> simp[]) >>
  `FLOOKUP births (owner0,owner1) = SOME (b,sz)` by fs[ptr_owner_erases_def] >>
  `?pos. FLOOKUP positions (Allocation owner1) = SOME (pos,sz) /\
         dt = d - n2w b + n2w pos` by fs[op_prov_def, ptr_value_transport_def] >>
  `w2n dt = pos + (w2n d - b)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists `sz` >>
     qpat_assum `!aid pos sz. FLOOKUP _ _ = _ ==> _` (drule_then assume_tac) >>
     simp[] >> decide_tac) >>
  qpat_x_assum `dt = d - n2w b + n2w pos` kall_tac >>
  simp[ptr_paired_write_owner_def] >>
  rpt strip_tac >> disj2_tac >> disj1_tac >>
  qexistsl [`owner0`,`owner1`,`b`,`sz`,`pos`,`x-b`] >> simp[] >> decide_tac
QED

Theorem ptr_focus_mcopy_footprint[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop s = SOME d /\ eval_operand sop s = SOME r /\
  eval_operand nop s = SOME n ==>
  range_bytes (step_writes inst s post) = {x | w2n d <= x /\ x < w2n d + w2n n}
Proof
  simp[step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, range_bytes_def]
QED

(* The read premise concerns only the concrete pre-state source interval.
   Its bytes need not be disjoint from the destination; the paired posts
   below are both produced from their own pre-state. *)
Theorem ptr_focus_mcopy_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = MCOPY /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\
  inst_wf a.po_inst /\ MEM a.po_inst (fn_insts a.po_fn) /\
  fn_ptr_ok P a.po_fn /\ ptr_static_support P a.po_fn TG /\
  EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  active_inst a.po_fn a.po_inst a.po_state /\ EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp a.po_fn) (Allocation ai.inst_id))) /\
  ~in_revert_forward a.po_fn a.po_state /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ptr_ledger_erases (dyn_floor C a.po_state) births TG a.po_prov /\
  (!aid pos sz. FLOOKUP positions (Allocation aid) = SOME (pos,sz) ==>
                pos + sz < dimword (:256)) /\
  (!dop sop nop r rt n j.
    a.po_inst.inst_operands = [dop;sop;nop] /\
    eval_operand sop a.po_state = SOME r /\ eval_operand sop at.po_state = SOME rt /\
    eval_operand nop a.po_state = SOME n /\
    MEM (w2n r,w2n n) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG sop) {} (SOME r) (SOME rt) /\
    j < w2n n /\ w2n r + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n r+j) a.po_state.vs_memory = read_byte (w2n rt+j) at.po_state.vs_memory) ==>
  ?z extra. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls (ws ++ extra)
Proof
  strip_tac >> drule_all ptr_focus_mcopy_inputs >> strip_tac >>
  drule_all ptr_focus_mcopy_successor >> strip_tac >>
  `range_bytes (step_writes a.po_inst a.po_state z.po_state) =
     {x | w2n d <= x /\ x < w2n d + w2n n}` by
    simp[ptr_focus_mcopy_footprint] >>
  Cases_on `n = 0w`
  >- (qexistsl [`z`,`[]`] >> irule ptr_paired_prefix_write_attach >> simp[] >>
      qexistsl [`TG`,`a`,`at`] >> gvs[pred_setTheory.EXTENSION]) >>
  `!i. i < w2n n /\ w2n r + i NOTIN a.po_taint.t_mem ==>
     read_byte (w2n r+i) a.po_state.vs_memory =
     read_byte (w2n rt+i) at.po_state.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     qexistsl [`dop`,`n`,`nop`,`sop`] >> simp[]) >>
  `!i. i < w2n n /\ w2n d+i NOTIN z.po_taint.t_mem ==>
     read_byte (w2n d+i) z.po_state.vs_memory =
     read_byte (w2n dt+i) zt.po_state.vs_memory` by
    (drule_all ptr_mcopy_masked_content >>
     simp[step_inst_base_opcode_eqs, step_taint_def]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `ptr_value_transport births positions (op_prov TG dop) {} d dt` by
    fs[ptr_lookup_transport_def] >>
  qabbrev_tac `addr_map = \x. w2n dt + (x - w2n d)` >>
  `ptr_paired_write_owner (dyn_floor C a.po_state) lo positions addr_map
       {x | w2n d <= x /\ x < w2n d + w2n n}
       (tokens,registry,births,PT,TG,saved,entries:num |-> num)` by
    (simp[Abbr `addr_map`] >> irule ptr_focus_mcopy_destination >>
     simp[] >> rpt conj_tac
     >- gvs[] >>
     qexistsl [`h`,`vs`] >> simp[]) >>
  qexistsl [`z`,`[(LENGTH h - 1,LENGTH done,addr_map)]`] >>
  irule ptr_paired_prefix_write_attach >> simp[] >>
  reverse conj_tac >- (qexistsl [`TG`,`a`,`at`] >> simp[]) >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule_then (strip_assume_tac o MATCH_MP ptr_chrono_history_end)
    ptr_structural_trace_source >>
  drule_then (strip_assume_tac o MATCH_MP ptr_chrono_history_end)
    ptr_structural_trace_target >>
  `SUC (LENGTH h - 1) = LENGTH h /\ SUC (LENGTH done) = LENGTH ht /\
   LENGTH ht - 1 = LENGTH done` by decide_tac >>
  `EL (LENGTH h - 1) h = a` by
    (qspec_then `h` mp_tac LAST_EL >> simp[PRE_SUB1]) >>
  `EL (LENGTH done) ht = at` by
    (qspec_then `ht` mp_tac LAST_EL >> simp[PRE_SUB1]) >>
  `0 < w2n n` by (CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS]) >>
  `{x | w2n d <= x /\ x < w2n d + w2n n} <> {}` by
    (simp[pred_setTheory.EXTENSION] >> qexists `w2n d` >> simp[]) >>
  `range_bytes (step_writes a.po_inst at.po_state zt.po_state) =
     {x | w2n dt <= x /\ x < w2n dt + w2n n}` by
    simp[ptr_focus_mcopy_footprint] >>
  simp[ptr_paired_write_def, EL_APPEND_EQN, ptr_ledger_write_pair_def,
       ptr_bytes_agree_def, is_terminator_def, IgnAsm `z.po_state = _`,
       IgnAsm `zt.po_state = _`, IgnAsm `z.po_taint = _`] >>
  conj_tac
  >- (rpt strip_tac >>
      `i = w2n d + (i - w2n d) /\ i - w2n d < w2n n` by decide_tac >>
      simp[Abbr `addr_map`] >> decide_tac) >>
  rpt strip_tac >>
  `w2n d + (i - w2n d) = i /\ i - w2n d < w2n n` by decide_tac >>
  qpat_x_assum `!i. i < w2n n /\ _ ==> read_byte _ z.po_state.vs_memory = _`
    (qspec_then `i - w2n d` mp_tac) >>
  simp[Abbr `addr_map`, IgnAsm `z.po_state = _`,
       IgnAsm `zt.po_state = _`, IgnAsm `z.po_taint = _`]
QED
