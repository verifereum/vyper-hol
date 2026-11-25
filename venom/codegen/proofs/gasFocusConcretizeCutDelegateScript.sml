Theory gasFocusConcretizeCutDelegate
Ancestors concretizePtrCreateFamily[qualified]
  concretizePtrDallocaWriterGeometry lowerDloadSafetyDelegate
  concretizePtrRequestHistory concretizeLayoutDelegate
  concretizePtrOpaqueRetpc concretizePtrValueTransport
  concretizePtrTaintContent concretizePtrSharedFields venomCallOracleDefs extCallOracle
  ptrDiscipline pointerConfinedDefs memLocDefs finite_map list
  venomInst venomExecSemantics venomState
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrOrdinaryNext
  concretizePtrLedgerProbe concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrTaggedSupport concretizePtrPrefixWriteAttach
  concretizePtrEventEmbedding concretizePtrBytes concretizePtrPrefixLedger
  concretizePtrReturnTransport codegenRel venomMemProps venomInstProofs
  regularCallEmitSim opcodeClass arithmetic concretizePtrSourceOwnership
  concretizeStepStructure concretizePtrActivationChronology
  concretizePtrComparisonTransport concretizePtrPlacementBounds
  contextCodegenRel concretizeMemLocDefs concretizeLayoutCleanRead
  gasFocusConcretizeTaggedSupport concretizePtrParamSupport
  venomWfProps unitShapeDefs o1PassContract venomWf cfgWf pred_set
  ptrDisciplineEmptyTaint unitLabelMapIdentity venomExecProps frameViewFacts

Theorem ptr_focus_delegate_target[local]:
  ptr_chrono_step C at zt /\ at.po_inst.inst_opcode = DELEGATECALL ==>
  ?g a ao az ro rz gas addr y n q rn post.
    at.po_inst.inst_operands = [g;a;ao;az;ro;rz] /\
    eval_operand g at.po_state = SOME gas /\
    eval_operand a at.po_state = SOME addr /\
    eval_operand ao at.po_state = SOME y /\
    eval_operand az at.po_state = SOME n /\
    eval_operand ro at.po_state = SOME q /\
    eval_operand rz at.po_state = SOME rn /\
    exec_delegatecall at.po_inst at.po_state gas addr y n q rn = OK post /\
    zt.po_state = post with vs_inst_idx := SUC at.po_state.vs_inst_idx /\
    zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
    active_inst zt.po_fn zt.po_inst zt.po_state
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >> strip_tac >>
  gvs[is_terminator_def, step_inst_non_invoke] >>
  imp_res_tac step_inst_base_intret_opcodes >> gvs[] >>
  drule_all ld_delegate_dispatch >> metis_tac[]
QED

Theorem ptr_focus_delegate_dispatch_ok[local]:
  inst.inst_opcode = DELEGATECALL /\ inst.inst_operands = [ga;ad;ao;az;ro;rz] /\
  eval_operand ga s = SOME gas /\ eval_operand ad s = SOME addr /\
  eval_operand ao s = SOME x /\ eval_operand az s = SOME n /\
  eval_operand ro s = SOME r /\ eval_operand rz s = SOME rn /\
  exec_delegatecall inst s gas addr x n r rn = OK post ==>
  step_inst fuel C inst s = OK post
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  PURE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >>
  PURE_REWRITE_TAC[opcode_case_def] >> simp[]
QED

(* Both executions are already fixed when extending the structural trace. *)
Theorem ptr_focus_delegate_structural[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  active_inst a.po_fn a.po_inst a.po_state /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn) /\
  (!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p) /\
  a.po_inst.inst_opcode = DELEGATECALL /\ at.po_inst = a.po_inst /\
  ptr_chrono_step C' at zt /\
  zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
  active_inst zt.po_fn zt.po_inst zt.po_state /\
  zt.po_state = target with vs_inst_idx := SUC at.po_state.vs_inst_idx /\
  step_inst 0 C a.po_inst a.po_state = OK post /\
  step_inst 0 C' at.po_inst at.po_state = OK target /\
  ptr_history_content a.po_taint post target /\
  (~a.po_state.vs_call_ctx.cc_static /\ (HD a.po_state.vs_outcomes).co_success ==>
   post.vs_accounts = target.vs_accounts /\ post.vs_transient = target.vs_transient) /\
  ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
    (step_taint a.po_inst a.po_state post a.po_taint) a.po_fn at.po_fn post target ==>
  ?z TG'.
    z.po_state = post with vs_inst_idx := SUC a.po_state.vs_inst_idx /\
    ptr_chrono_step C a z /\
    ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) /\
    ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
    ptr_paired_params positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
    ptr_paired_code R lp positions z.po_fn zt.po_fn /\
    ptr_paired_cursor lp z zt /\
    z.po_stack = a.po_stack
Proof
  strip_tac >>
  `is_ext_call_op a.po_inst.inst_opcode /\ is_ext_call_op at.po_inst.inst_opcode /\
   ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[is_ext_call_op_def, is_terminator_def] >>
  qpat_assum `step_inst 0 C _ _ = OK post`
    (mp_then Any mp_tac venomInstProofsTheory.step_ext_call_preserves) >>
  simp[] >> strip_tac >>
  qpat_assum `step_inst 0 C' _ _ = OK target`
    (mp_then Any mp_tac venomInstProofsTheory.step_ext_call_preserves) >>
  simp[] >> strip_tac >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >> simp[] >> qexists `a.po_inst` >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qabbrev_tac `TG' = step_prov PT TG a.po_inst post` >>
  `z.po_state = (post with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
   z.po_fn = a.po_fn /\ z.po_stack = a.po_stack /\ z.po_inst = i` by
    simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG' saved` by
    suspend "tagged" >>
  `ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries)` by
    suspend "sample" >>
  `ptr_paired_cursor lp z zt` by suspend "cursor" >>
  qexistsl [`z`,`TG'`] >> simp[] >>
  conj_tac >- metis_tac[ptr_tagged_chrono_step_projection] >>
  conj_tac >- suspend "transcript" >>
  fs[ptr_paired_params_def]
QED

Resume ptr_focus_delegate_structural[tagged]:
  simp[Abbr `z`, Abbr `TG'`, ptr_ledger_next_def] >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  drule_all (cj 1 ptr_tagged_chrono_step_rules) >>
  simp[ptr_tagged_step_def, step_prov_def, out_prov_def] >> metis_tac[]
QED

Resume ptr_focus_delegate_structural[sample]:
  simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  conj_tac
  >- (irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `post.vs_call_ctx = target.vs_call_ctx` by
    metis_tac[ptr_history_content_call_ctx] >>
  Cases_on `adopt_guard a.po_state.vs_call_ctx.cc_static a.po_state post (HD a.po_state.vs_outcomes).co_success` >>
  fs[ptr_history_content_def, ptr_taint_content_def, step_taint_def,
     store_taint_def, adopt_reset_def, imm_taint_def, contract_storage_def,
     contract_transient_def, storage_agree_except_def, word_agree_except_def] >>
  first_assum ACCEPT_TAC
QED

Resume ptr_focus_delegate_structural[cursor]:
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_ordinary_next_cursor >> disch_then irule >> simp[]
QED

Resume ptr_focus_delegate_structural[transcript]:
  drule ptr_ownership_overlay_fixed >> strip_tac >>
  drule (cj 3 ptr_structural_transcript_rules) >> disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED

Finalise ptr_focus_delegate_structural

(* Resolve the reserved return range before using the smaller actual write. *)
Theorem ptr_focus_delegate_return_geometry[local]:
  inst.inst_opcode = DELEGATECALL /\ inst.inst_operands = [ga;ad;ao;az;ro;rz] /\
  eval_operand ga s = SOME gas /\ eval_operand ad s = SOME addr /\
  eval_operand ao s = SOME x /\ eval_operand az s = SOME n /\
  eval_operand ro s = SOME r /\ eval_operand rz s = SOME rn /\
  ~in_revert_forward fn s /\ access_ok lo G fn inst s /\
  ptr_ledger_erases dyn births TG G /\
  ptr_lookup_transport births positions (op_prov TG ro) {} (SOME r) (SOME q) /\
  (!v token aid. FLOOKUP TG v = SOME (token,aid) ==> MEM token tokens) /\
  (!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==>
               p + sz < dimword(:256)) /\
  0 < w2n rn ==>
  (q = r /\ (w2n r + w2n rn <= lo \/ dyn <= w2n r)) \/
  ?token aid db sz pb. MEM token tokens /\
    FLOOKUP births (token,aid) = SOME (db,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pb,sz) /\
    db <= w2n r /\ w2n r + w2n rn <= db + sz /\ w2n q = pb + (w2n r - db)
Proof
  strip_tac >>
  `op_prov TG ro <> NONE ==> op_prov G ro <> NONE` by
    (Cases_on `ro` >> simp[op_prov_def] >> strip_tac >>
     rename1 `FLOOKUP TG v <> NONE` >>
     Cases_on `FLOOKUP TG v` >> gvs[] >>
     rename1 `FLOOKUP TG v = SOME owner` >> PairCases_on `owner` >>
     `ptr_owner_erases dyn births (FLOOKUP TG v) (FLOOKUP G v)` by
       fs[ptr_ledger_erases_def] >>
     gvs[ptr_owner_erases_def, ptr_lookup_transport_some, op_prov_def,
         ptr_value_transport_def]) >>
  `(lo < w2n r + w2n rn \/ op_prov TG ro <> NONE) ==>
    ?v db sz. ro = Var v /\ FLOOKUP G v = SOME (db,sz) /\
       db <= w2n r /\ w2n r + w2n rn <= db + sz` by
    (disch_tac >> qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     simp[access_ok_def, source_memory_write_ranges_def, mem_write_ops_def] >>
     disch_then (mp_tac o cj 1) >>
     Cases_on `rn = 0w` >> gvs[] >> metis_tac[]) >>
  Cases_on `op_prov TG ro` >> fs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty]
  >- (Cases_on `w2n r + w2n rn <= lo`
      >- metis_tac[] >>
      disj1_tac >> gvs[] >>
      rename1 `dyn <= w2n r` >>
      gvs[op_prov_def, ptr_ledger_erases_def] >>
      qpat_x_assum `!v. ptr_owner_erases _ _ _ _`
        (qspec_then `v` (assume_tac o REWRITE_RULE[ptr_owner_erases_def])) >>
      fs[] >> (gvs[LESS_EQ_TRANS])) >>
  rename1 `op_prov TG _ = SOME tag` >> PairCases_on `tag` >>
  gvs[ptr_value_transport_def] >>
  gvs[op_prov_def] >>
  `ptr_owner_erases dyn births (FLOOKUP TG v) (FLOOKUP G v)` by fs[ptr_ledger_erases_def] >>
  gvs[ptr_owner_erases_def] >>
  rename1 `FLOOKUP births (token,aid) = SOME (db,sz)` >>
  rename1 `FLOOKUP positions (Allocation aid) = SOME (pb,sz)` >>
  `MEM token tokens /\ pb + sz < dimword(:256)` by metis_tac[] >>
  `w2n r <= db + sz` by decide_tac >>
  `w2n (r - n2w db + n2w pb) = pb + (w2n r - db)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists `sz` >> simp[]) >>
  disj2_tac >> qexistsl [`token`,`aid`,`db`,`sz`,`pb`] >> simp[]
QED

(* Pair the bytes actually copied, which can be fewer than the reserved size. *)
Theorem ptr_focus_delegate_actual_write[local]:
  ptr_chrono_step C a z /\ ptr_chrono_step C' at zt /\
  at.po_inst = a.po_inst /\ a.po_inst.inst_opcode = DELEGATECALL /\
  (!i. i IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
       x <= i /\ i < x+k) /\
  (!i. i IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
       y <= i /\ i < y+k) /\
  (!j. j < k ==> read_byte (x+j) z.po_state.vs_memory =
                  read_byte (y+j) zt.po_state.vs_memory) /\
  k <= n /\
  ((x = y /\ (x+n <= lo \/ dyn <= x)) \/
   (?token aid b sz p. MEM token tokens /\
      FLOOKUP births (token,aid) = SOME (b,sz) /\
      FLOOKUP positions (Allocation aid) = SOME (p,sz) /\
      b <= x /\ x+n <= b+sz /\ y = p + (x-b))) ==>
  ptr_ledger_write_pair C C' (\i. y + (i-x)) a z at zt /\
  ptr_paired_write_owner dyn lo positions (\i. y + (i-x))
    (range_bytes (step_writes a.po_inst a.po_state z.po_state))
    (tokens,registry,births,PT,TG',saved,entries)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (simp[ptr_ledger_write_pair_def, ptr_bytes_agree_def, is_terminator_def] >>
      rpt strip_tac >>
      rename1 `x <= i` >>
      `x+(i-x) = i /\ i-x < k` by decide_tac >>
      gvs[] >> first_x_assum (qspec_then `i-x` mp_tac) >> simp[]) >>
  simp[ptr_paired_write_owner_def] >> rpt strip_tac >> gvs[] >>
  rename1 `x <= i` >>
  disj2_tac >> disj1_tac >> qexistsl [`token`,`aid`,`b`,`sz`,`p`,`i - b`] >>
  simp[] >> decide_tac
QED

Theorem ptr_focus_delegate_attach[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
    (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) /\
  ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
  ptr_paired_code R lp positions z.po_fn zt.po_fn /\
  ptr_paired_cursor lp z zt /\
  ptr_paired_params positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
  z.po_stack = a.po_stack /\ zt.po_stack = at.po_stack /\
  (!i. i IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
       x <= i /\ i < x+k) /\
  (0 < k ==> ptr_ledger_write_pair C C' shift a z at zt /\
     ptr_paired_write_owner (dyn_floor C a.po_state) lo positions shift
       (range_bytes (step_writes a.po_inst a.po_state z.po_state))
       (tokens,registry,births,PT,TG',saved,entries)) ==>
  ?ws'. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws'
Proof
  strip_tac >> Cases_on `k = 0`
  >- (`range_bytes (step_writes a.po_inst a.po_state z.po_state) = {}` by
        simp[EXTENSION] >>
      qexists `ws ++ []` >> MATCH_MP_TAC ptr_paired_prefix_write_attach >> simp[]) >>
  `0 < k` by decide_tac >> first_x_assum drule >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  `LENGTH H = LENGTH h /\ 0 < LENGTH h /\ LENGTH ht = SUC (LENGTH done)` by
    fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def] >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH done) ht = at` by
    (`h <> [] /\ LAST h = a /\ ht <> [] /\ LAST ht = at` by
       metis_tac[ptr_chrono_history_end] >>
     conj_tac
     >- (qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL]) >>
  `range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {}` by
    (simp[EXTENSION] >> qexists `x` >> simp[]) >>
  `ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)])
    (LENGTH h - 1,LENGTH done,shift)` by
    (`SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
     simp[ptr_paired_write_def, EL_APPEND_EQN]) >>
  qexists `ws ++ [(LENGTH h - 1,LENGTH done,shift)]` >>
  MATCH_MP_TAC ptr_paired_prefix_write_attach >> simp[]
QED

Theorem ptr_focus_delegate_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state /\
  o1_ctx_shape C /\ EVERY ssa_form C.ctx_functions /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
        ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p) /\
  a.po_inst.inst_opcode = DELEGATECALL /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  (!aid p sz. FLOOKUP positions (Allocation aid) = SOME (p,sz) ==>
              p + sz < dimword(:256)) /\
  ptr_chrono_step C' at zt /\
  (!ops x y n.
     mem_read_ops a.po_inst = SOME ops /\ inst_read_op a.po_inst = SOME ops.iao_ofst /\
     MEM ops.iao_ofst a.po_inst.inst_operands /\
     eval_operand ops.iao_ofst a.po_state = SOME x /\
     eval_operand ops.iao_ofst at.po_state = SOME y /\
     MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
     ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
     !j. j < n /\ w2n x + j NOTIN a.po_taint.t_mem ==>
       read_byte (w2n x+j) a.po_state.vs_memory = read_byte (w2n y+j) at.po_state.vs_memory) ==>
  ?z TG' ws'. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     once_rewrite_tac[frame_reachable_cases] >> rpt strip_tac >> simp[]) >>
  `dyn_floor C a.po_state = dyn_floor C vs` by
    (drule frame_reachable_initial_fmp >> simp[dyn_floor_def]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `inst_wf a.po_inst /\ fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
   ssa_form a.po_fn /\ EVERY bb_well_formed a.po_fn.fn_blocks /\
   ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands /\
   ptr_use_ok P (fn_pv P a.po_fn) a.po_inst /\
   (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn)` by
    (conj_tac
     >- (simp[EVERY_MEM] >> rpt strip_tac >> Cases_on `e` >>
         simp[ptr_nonopaque_operand_def] >>
         rename1 `~retpc_var a.po_fn v` >> strip_tac >>
         qpat_assum `opaque_use_ok _` (mp_tac o REWRITE_RULE [opaque_use_ok_def]) >>
         disch_then (qspecl_then [`a.po_inst`,`v`] mp_tac) >>
         gvs[retpc_use_ok_def, MEM]) >>
     fs[fn_ptr_ok_def, ptr_static_support_def] >> metis_tac[]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn a.po_state at.po_state /\
   ptr_history_content a.po_taint a.po_state at.po_state` by
    fs[ptr_paired_sample_def] >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by metis_tac[ptr_history_content_labels] >>
  suspend "execute"
QED

Resume ptr_focus_delegate_step[execute]:
  `at.po_inst.inst_opcode = DELEGATECALL` by simp[] >>
  drule_all ptr_focus_delegate_target >> strip_tac >>
  `?out. a.po_inst.inst_outputs = [out] /\ ~retpc_var a.po_fn out` by
    (drule delegate_success_envelope >> strip_tac >>
     qexists `out` >> conj_tac >- metis_tac[] >>
     irule noncopy_output_not_retpc >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `a.po_inst` >> gvs[MEM]) >>
  `a.po_inst.inst_operands = [g;a';ao;az;ro;rz]` by gvs[] >>
  drule_all concretizePtrCreateFamilyTheory.ptr_create_family_delegate_operand_transport >> strip_tac >>
  `read_memory (w2n x) (w2n n) a.po_state = read_memory (w2n y) (w2n n) at.po_state` by
    suspend "input" >>
  `exec_delegatecall a.po_inst at.po_state gas addr y n q rn = OK post` by metis_tac[] >>
  drule_all concretizePtrCreateFamilyTheory.ptr_create_family_delegate_mixed_execution >>
  disch_then (qspecl_then [`r`,`PT`] strip_assume_tac) >>
  `step_inst 0 C a.po_inst a.po_state = OK u` by
    (irule ptr_focus_delegate_dispatch_ok >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `step_inst 0 C' at.po_inst at.po_state = OK post` by
    (irule ptr_focus_delegate_dispatch_ok >> rpt (goal_assum (drule_at Any)) >> fs[]) >>
  drule_all ptr_focus_delegate_structural >> strip_tac >>
  suspend "write"
QED

Resume ptr_focus_delegate_step[input]:
  irule concretize_read_memory_bytes >>
  `MEM (w2n x,w2n n) (source_memory_read_ranges a.po_inst a.po_state)` by
    simp[source_memory_read_ranges_def, mem_read_ops_def,
         memory_range_of_operands_def, eval_operands_def] >>
  `!j. j < w2n n ==> w2n x+j NOTIN a.po_taint.t_mem` by
    (rpt strip_tac >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def, about_to_revert_def] >>
     disj2_tac >> qexistsl [`w2n x`,`w2n n`,`w2n x+j`] >> simp[]) >>
  qpat_x_assum `!ops x y n. _` mp_tac >>
  simp[mem_read_ops_def, inst_read_op_def] >>
  disch_then (qspec_then `w2n n` mp_tac) >>
  gvs[ADD_COMM] >> metis_tac[ADD_COMM]
QED

Resume ptr_focus_delegate_step[write]:
  qabbrev_tac `k = MIN (w2n rn) (LENGTH u.vs_returndata)` >>
  `(!b. b IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
         w2n r <= b /\ b < w2n r + k) /\
   (!b. b IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
         w2n q <= b /\ b < w2n q + k)` by
    (gvs[Abbr `k`, step_writes_def, source_memory_write_ranges_def,
         range_bytes_def]) >>
  `!j. j < k ==> read_byte (w2n r+j) z.po_state.vs_memory =
                 read_byte (w2n q+j) zt.po_state.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `exec_delegatecall _ a.po_state _ _ _ _ _ _ = OK u`
       (mp_then (Pos hd) (qspec_then `j` mp_tac) concretizePtrCreateFamilyTheory.ptr_create_family_delegate_written_byte) >>
     qpat_assum `exec_delegatecall _ at.po_state _ _ _ _ _ _ = OK post`
       (mp_then (Pos hd) (qspec_then `j` mp_tac) concretizePtrCreateFamilyTheory.ptr_create_family_delegate_written_byte) >>
     gvs[Abbr `k`, ADD_COMM]) >>
  qexistsl [`z`,`TG'`] >>
  irule ptr_focus_delegate_attach >>
  rpt (goal_assum (drule_at Any)) >>
  qexists `\i. w2n q + (i - w2n r)` >> BETA_TAC >> disch_tac >>
  suspend "owner"
QED

Resume ptr_focus_delegate_step[owner]:
  `k <= w2n rn /\ 0 < w2n rn` by (gvs[Abbr `k`, MIN_DEF] >> decide_tac) >>
  `!v token aid. FLOOKUP TG v = SOME (token,aid) ==> MEM token tokens` by
    metis_tac[ptr_source_ownership_live_prov] >>
  drule_all ptr_focus_delegate_return_geometry >> disch_tac >>
  irule ptr_focus_delegate_actual_write >> simp[ADD_COMM] >>
  qexistsl [`k`,`w2n rn`] >> gvs[ADD_COMM] >>
  disj2_tac >> qexistsl [`token`,`aid`,`db`,`sz`,`pb`] >> simp[] >> decide_tac
QED

Finalise ptr_focus_delegate_step
