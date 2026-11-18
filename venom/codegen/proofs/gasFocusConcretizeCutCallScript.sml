Theory gasFocusConcretizeCutCall
Ancestors
  concretizePtrCallFamily concretizePtrOrdinaryNext
  gasFocusConcretizeTaggedSupport concretizePtrPrefixWriteAttach
  concretizePtrPairedFields concretizePtrTaintContent concretizePtrSharedFields
  concretizeMemLocDefs concretizePtrBytes concretizePtrActivationChronology
  frameViewFacts list venomState ptrDiscipline copyFwdEquiv allocaRemapDefs
  codegenRel opcodeClass concretizePtrChronologicalHistory venomInst
  venomExecProofs concretizePtrStructuralTrace venomInstProofs1 venomExecSemantics
  contextCodegenRel venomWf concretizePtrValueTransport finite_map
  concretizePtrRequestHistory memLocDefs concretizePtrPairedPrefix
  concretizePtrOpaqueRetpc concretizePtrLedgerProbe concretizePtrPrefixLedger
  pred_set concretizePtrStructuralTranscript concretizePtrDeletedGapHistory
  concretizePtrSourceOwnership concretizePtrParamSupport concretizeStepStructure
  unitLabelMapIdentity option

Theorem ptr_focus_call_read_slice[local]:
  MEM a.po_inst.inst_opcode [CALL; STATICCALL] /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
  (!j. j < n /\ w2n x + j NOTIN a.po_taint.t_mem ==>
     read_byte (w2n x + j) a.po_state.vs_memory =
     read_byte (w2n y + j) t.vs_memory) ==>
  read_memory (w2n x) n a.po_state = read_memory (w2n y) n t
Proof
  strip_tac >>
  `!j. j < n ==> w2n x + j NOTIN a.po_taint.t_mem` by
    (rpt strip_tac >>
     `w2n x <= w2n x + j /\ w2n x + j < w2n x + n` by decide_tac >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     fs[MEM] >> simp[taint_ok_def, about_to_revert_def] >>
     disj2_tac >> qexistsl [`w2n x`, `n`, `w2n x + j`] >> simp[]) >>
  `!j. j < n ==> read_byte (w2n x + j) a.po_state.vs_memory =
                   read_byte (w2n y + j) t.vs_memory` by metis_tac[] >>
  irule LIST_EQ >> simp[read_memory_def, LENGTH_TAKE_EQ] >>
  rpt strip_tac >>
  simp[take_drop_replicate_el, GSYM read_byte_def, mem_byte_at_def]
QED

Theorem ptr_focus_call_target_edge[local]:
  at.po_inst = inst /\ MEM inst.inst_opcode [CALL; STATICCALL] /\
  ptr_chrono_step C' at zt ==>
  ?post.
    step_inst_base inst at.po_state = OK post /\
    zt.po_stack = at.po_stack /\ zt.po_fn = at.po_fn /\
    zt.po_state = post with vs_inst_idx := SUC at.po_state.vs_inst_idx /\
    active_inst zt.po_fn zt.po_inst zt.po_state
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  qpat_x_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM", step_inst_non_invoke] >>
  drule step_inst_base_intret_opcodes >> fs[]
QED

(* The memory premise is only for the input range of this instruction. *)
Theorem ptr_focus_call_execute[local]:
  MEM a.po_inst.inst_opcode [CALL; STATICCALL] /\
  at.po_inst = a.po_inst /\ ptr_chrono_step C' at zt /\
  inst_wf a.po_inst /\ MEM a.po_inst (fn_insts a.po_fn) /\
  fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn) /\
  ptr_history_content a.po_taint a.po_state at.po_state /\
  ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state /\
  (!ops x y n j.
    mem_read_ops a.po_inst = SOME ops /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y) /\ j < n /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
    read_byte (w2n y+j) at.po_state.vs_memory) ==>
  ?out w u v ops x y (n:256 word) k.
    a.po_inst.inst_outputs = [out] /\
    step_inst 0 C a.po_inst a.po_state = OK (update_var out w u) /\
    zt.po_state = update_var out w v with vs_inst_idx := SUC at.po_state.vs_inst_idx /\
    zt.po_stack = at.po_stack /\ zt.po_fn = at.po_fn /\
    active_inst zt.po_fn zt.po_inst zt.po_state /\
    u.vs_allocas = a.po_state.vs_allocas /\
    u.vs_current_bb = a.po_state.vs_current_bb /\ u.vs_prev_bb = a.po_state.vs_prev_bb /\
    v.vs_current_bb = at.po_state.vs_current_bb /\ v.vs_prev_bb = at.po_state.vs_prev_bb /\
    u.vs_params = a.po_state.vs_params /\ v.vs_params = at.po_state.vs_params /\
    u.vs_return_pc_token = a.po_state.vs_return_pc_token /\
    v.vs_return_pc_token = at.po_state.vs_return_pc_token /\
    (!r. r <> out ==> lookup_var r u = lookup_var r a.po_state /\
                      lookup_var r v = lookup_var r at.po_state) /\
    ptr_history_content (step_taint a.po_inst a.po_state (update_var out w u) a.po_taint)
      (update_var out w u) (update_var out w v) /\
    u.vs_returndata = v.vs_returndata /\
    mem_write_ops a.po_inst = SOME ops /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) /\
    MEM (w2n x,w2n n) (source_memory_write_ranges a.po_inst a.po_state) /\
    k = MIN (w2n n) (LENGTH u.vs_returndata) /\
    (!q. q IN range_bytes (step_writes a.po_inst a.po_state (update_var out w u)) <=>
       w2n x <= q /\ q < w2n x+k) /\
    (!q. q IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
       w2n y <= q /\ q < w2n y+k) /\
    (!j. j < k ==> read_byte (w2n x+j) u.vs_memory = read_byte (w2n y+j) v.vs_memory)
Proof
  strip_tac >>
  drule_all ptr_focus_call_target_edge >> strip_tac >>
  `a.po_state.vs_labels = at.po_state.vs_labels /\
   a.po_state.vs_call_ctx = at.po_state.vs_call_ctx` by
    metis_tac[ptr_history_content_labels, ptr_history_content_call_ctx] >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf _` mp_tac >> fs[MEM] >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> INVOKE` by fs[MEM] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  Cases_on `a.po_inst.inst_opcode = CALL` >> fs[MEM] >>
  pure_rewrite_tac[step_inst_base_def] >>
  qpat_assum `a.po_inst.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `?pre vop.
    ((a.po_inst.inst_opcode = CALL /\ pre = [gas_op;addr_op;vop]) \/
     (a.po_inst.inst_opcode = STATICCALL /\ pre = [gas_op;addr_op])) /\
    a.po_inst.inst_operands = pre ++ [ao_op;as_op;ro_op;rs_op]` by
    (Cases_on `a.po_inst.inst_opcode = CALL`
     >- (gvs[] >> qexistsl [`[gas_op;addr_op;val_op]`,`val_op`] >> simp[]) >>
     gvs[] >> qexistsl [`[gas_op;addr_op]`,`Lit 0w`] >> simp[]) >>
  `(!op. MEM op a.po_inst.inst_operands ==>
      op_taint a.po_taint op = {} /\
      ptr_lookup_transport births positions (op_prov TG op) {}
        (eval_operand op a.po_state) (eval_operand op at.po_state)) /\
    eval_operands (pre ++ [as_op;rs_op]) a.po_state =
    eval_operands (pre ++ [as_op;rs_op]) at.po_state` by
    (irule ptr_call_operand_transport >> simp[] >> metis_tac[]) >>
  `?sa sr. eval_operand ao_op a.po_state = SOME sa /\
      eval_operand ro_op a.po_state = SOME sr /\
      ptr_lookup_transport births positions (op_prov TG ao_op) {} (SOME sa) (SOME ao) /\
      ptr_lookup_transport births positions (op_prov TG ro_op) {} (SOME sr) (SOME ro)` by
    (`ptr_lookup_transport births positions (op_prov TG ao_op) {}
        (eval_operand ao_op a.po_state) (SOME ao) /\
      ptr_lookup_transport births positions (op_prov TG ro_op) {}
        (eval_operand ro_op a.po_state) (SOME ro)` by
       (`MEM ao_op a.po_inst.inst_operands /\ MEM ro_op a.po_inst.inst_operands` by
          simp[] >> metis_tac[]) >>
     fs[ptr_lookup_transport_some_right] >> metis_tac[ptr_lookup_transport_some]) >>
  qpat_x_assum `eval_operands _ a.po_state = _` mp_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >> strip_tac >>
  `read_memory (w2n sa) (w2n as_) a.po_state =
    read_memory (w2n ao) (w2n as_) at.po_state` by
    (irule ptr_focus_call_read_slice >> simp[MEM] >>
     qpat_x_assum `!ops x y n j. _` mp_tac >>
     simp[mem_read_ops_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, eval_operands_def] >> metis_tac[]) >>
  drule_at (Pos last) ptr_call_history_execution >>
  disch_then drule >> simp[] >>
  disch_then (drule_at (Pos last)) >> simp[] >>
  disch_then (qspecl_then [`sr`,`gas`] strip_assume_tac) >>
  `u.vs_allocas = a.po_state.vs_allocas /\
   u.vs_current_bb = a.po_state.vs_current_bb /\
   u.vs_prev_bb = a.po_state.vs_prev_bb /\
   u.vs_params = a.po_state.vs_params /\
   (!x. x <> out ==> lookup_var x u = lookup_var x a.po_state) /\
   u.vs_return_pc_token = a.po_state.vs_return_pc_token` by
    (qpat_x_assum `exec_ext_call _ a.po_state _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exec_ext_call_def, update_var_def, venom_state_component_equality] >>
     strip_tac >> gvs[lookup_var_def] >> metis_tac[FLOOKUP_UPDATE]) >>
  `v.vs_current_bb = at.po_state.vs_current_bb /\
   v.vs_prev_bb = at.po_state.vs_prev_bb /\
   v.vs_params = at.po_state.vs_params /\
   (!x. x <> out ==> lookup_var x v = lookup_var x at.po_state) /\
   v.vs_return_pc_token = at.po_state.vs_return_pc_token` by
    (qpat_x_assum `exec_ext_call _ at.po_state _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exec_ext_call_def, update_var_def, venom_state_component_equality] >>
     strip_tac >> gvs[lookup_var_def] >> metis_tac[FLOOKUP_UPDATE]) >>
  qexistsl [`w`,`u`,`v`,
    `<|iao_ofst := ro_op; iao_size := NONE; iao_max_size := SOME rs_op|>`,
    `sr`,`ro`,`rs`] >>
  gvs[Excl "MEM"] >>
  simp[step_inst_non_invoke, step_inst_base_def, mem_write_ops_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       memory_range_of_operands_def, eval_operands_def, step_writes_def,
       range_bytes_def, update_var_def]
QED

Theorem ptr_focus_call_sample[local]:
  MEM a.po_inst.inst_opcode [CALL; STATICCALL] /\
  a.po_inst.inst_outputs = [out] /\ ssa_form a.po_fn /\
  MEM a.po_inst (fn_insts a.po_fn) /\
  ptr_paired_sample positions a at (tokens,registry,births,PT,TG,saved,entries) /\
  ptr_paired_params positions a at (tokens,registry,births,PT,TG,saved,entries) /\
  z = ptr_ledger_next a i (update_var out w u) /\
  zt.po_state = update_var out w v with vs_inst_idx := SUC at.po_state.vs_inst_idx /\
  zt.po_fn = at.po_fn /\
  u.vs_params = a.po_state.vs_params /\ v.vs_params = at.po_state.vs_params /\
  u.vs_return_pc_token = a.po_state.vs_return_pc_token /\
  v.vs_return_pc_token = at.po_state.vs_return_pc_token /\
  (!r. r <> out ==> lookup_var r u = lookup_var r a.po_state /\
                    lookup_var r v = lookup_var r at.po_state) /\
  ptr_history_content (step_taint a.po_inst a.po_state (update_var out w u) a.po_taint)
    (update_var out w u) (update_var out w v) ==>
  ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries) /\
  ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)
Proof
  strip_tac >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >> simp[] >>
     qexists `a.po_inst` >> fs[MEM]) >>
  reverse conj_tac
  >- (qpat_x_assum `ptr_paired_params _ _ _ _` mp_tac >>
      simp[ptr_paired_params_def, ptr_ledger_next_def, ptr_observe_def,
           update_var_def]) >>
  qpat_x_assum `ptr_paired_sample _ _ _ _` mp_tac >>
  simp[ptr_paired_sample_def, ptr_ledger_next_def, ptr_observe_def] >>
  simp[ptr_mixed_vars_pointwise] >> strip_tac >>
  fs[MEM] >> gen_tac >>
  (Cases_on `x = out`
   >- simp[FLOOKUP_DRESTRICT, word_agree_except_def, step_prov_def,
           out_prov_def, set_prov_def, step_taint_def, out_taint_def,
           set_var_taint_def, op_taint_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
           ptr_lookup_transport_def, ptr_value_transport_def] >>
   qpat_x_assum `!x. if retpc_var _ x then _ else _` (qspec_then `x` mp_tac) >>
   gvs[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       out_taint_def, set_var_taint_def, op_taint_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT])
QED

(* Shortening the advertised output slice to the bytes actually returned
   preserves ownership, with the very same translation of offsets. *)
Theorem ptr_focus_call_write_owner[local]:
  k <= n /\
  (!q. q IN xs <=> x <= q /\ q < x+k) /\
  ((x = y /\ (x+n <= lo \/ dyn <= x)) \/
   (?token aid b sz pa. MEM token tokens /\
      FLOOKUP births (token,aid) = SOME (b,sz) /\
      FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
      b <= x /\ x+n <= b+sz /\ y = pa + (x-b))) ==>
  ptr_paired_write_owner dyn lo positions (\q. y + (q-x)) xs
    (tokens,registry,births,PT,TG',saved,entries)
Proof
  strip_tac >> simp[ptr_paired_write_owner_def] >> rpt strip_tac >>
  gvs[] >> disj2_tac >> disj1_tac >>
  qexistsl [`token`,`aid`,`b`,`sz`,`pa`,`q-b`] >> simp[] >> decide_tac
QED

Theorem ptr_focus_call_write_pair[local]:
  ptr_chrono_step C a z /\ ptr_chrono_step C' at zt /\
  at.po_inst = a.po_inst /\ MEM a.po_inst.inst_opcode [CALL; STATICCALL] /\
  (!q. q IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
       x <= q /\ q < x+k) /\
  (!q. q IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
       y <= q /\ q < y+k) /\
  (!j. j < k ==> read_byte (x+j) z.po_state.vs_memory =
                  read_byte (y+j) zt.po_state.vs_memory) ==>
  ptr_ledger_write_pair C C' (\q. y + (q-x)) a z at zt
Proof
  strip_tac >> simp[ptr_ledger_write_pair_def, ptr_bytes_agree_def] >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    fs[MEM, is_terminator_def] >>
  simp[] >> rpt strip_tac >>
  rename1 `read_byte q _ = _` >>
  `x + (q-x) = q /\ y + (q-x) = q+y-x /\ q-x < k` by decide_tac >>
  qpat_x_assum `!j. j < k ==> read_byte _ _ = _`
    (qspec_then `q-x` mp_tac) >>
  pure_asm_rewrite_tac[] >> simp[]
QED

Theorem ptr_focus_call_attach[local]:
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
  ptr_chrono_step C a z /\ ptr_chrono_step C' at zt /\
  at.po_inst = a.po_inst /\ MEM a.po_inst.inst_opcode [CALL; STATICCALL] /\
  (!q. q IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
       x <= q /\ q < x+k) /\
  (!q. q IN range_bytes (step_writes at.po_inst at.po_state zt.po_state) <=>
       y <= q /\ q < y+k) /\
  (!j. j < k ==> read_byte (x+j) z.po_state.vs_memory =
                  read_byte (y+j) zt.po_state.vs_memory) /\
  (0 < k ==> ptr_paired_write_owner (dyn_floor C a.po_state) lo positions
     (\q. y + (q-x)) (range_bytes (step_writes a.po_inst a.po_state z.po_state))
     (tokens,registry,births,PT,TG',saved,entries)) ==>
  ?ws'. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws'
Proof
  strip_tac >>
  Cases_on `k = 0`
  >- (`range_bytes (step_writes a.po_inst a.po_state z.po_state) = {}` by
        simp[EXTENSION] >>
      qexists `ws ++ []` >>
      MATCH_MP_TAC ptr_paired_prefix_write_attach >>
      simp[]) >>
  drule_all ptr_focus_call_write_pair >> strip_tac >>
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
     >- (qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, arithmeticTheory.PRE_SUB1]) >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL]) >>
  `range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {}` by
    (simp[EXTENSION] >> qexists `x` >> simp[]) >>
  `ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
    (done ++ [LENGTH h - 1])
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)])
    (LENGTH h - 1,LENGTH done,\q. y + (q-x))` by
    (`SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
     simp[ptr_paired_write_def, EL_APPEND_EQN]) >>
  qexists `ws ++ [(LENGTH h - 1,LENGTH done,\q. y + (q-x))]` >>
  MATCH_MP_TAC ptr_paired_prefix_write_attach >>
  simp[]
QED

(* Only the current read slice and the geometry of the current destination
   are supplied by the bounded history. The return length and both posts are
   obtained from the selected target edge, not from that history premise. *)
Theorem ptr_focus_call_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  EVERY (\f. fn_inst_wf f /\ opaque_use_ok f /\ ssa_form f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALL; STATICCALL] /\
  (!ops x y n j.
    mem_read_ops a.po_inst = SOME ops /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y) /\ j < n /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
    read_byte (w2n y+j) at.po_state.vs_memory) /\
  (!ops x y n.
    mem_write_ops a.po_inst = SOME ops /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,n) (source_memory_write_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y) /\ 0 < n ==>
    (x = y /\ (w2n x+n <= lo \/ dyn_floor C a.po_state <= w2n x)) \/
    (?token aid b sz pa. MEM token tokens /\
       FLOOKUP births (token,aid) = SOME (b,sz) /\
       FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
       b <= w2n x /\ w2n x+n <= b+sz /\ w2n y = pa + (w2n x-b))) ==>
  ?z ws'. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT (step_prov PT TG a.po_inst z.po_state) saved entries
    (H ++ [(tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)])
    calls ws'
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `inst_wf a.po_inst /\ fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
   ssa_form a.po_fn /\ EVERY bb_well_formed a.po_fn.fn_blocks /\
   ALL_DISTINCT (fn_labels a.po_fn) /\
   (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
     ?p. FLOOKUP (lp a.po_fn) (Allocation i.inst_id) = SOME p)` by
    (fs[EVERY_MEM, IS_SOME_EXISTS] >> metis_tac[]) >>
  `at.po_inst = a.po_inst /\ ~is_terminator a.po_inst.inst_opcode /\
   a.po_inst.inst_opcode <> NOP /\ a.po_inst.inst_opcode <> INVOKE` by
    fs[MEM, concretize_inst_with_positions_def, is_terminator_def] >>
  qpat_assum `ptr_paired_sample _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_paired_sample_def] >> strip_tac >>
  qpat_x_assum `ptr_static_support _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_static_support_def] >> strip_tac >>
  drule_all ptr_focus_call_execute >> disch_then (qspec_then `C` strip_assume_tac) >>
  qabbrev_tac `post = update_var out w u` >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >> simp[Abbr `post`, update_var_def] >>
     qexists `a.po_inst` >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `z.po_fn = a.po_fn /\ z.po_stack = a.po_stack /\
   z.po_state = post with vs_inst_idx := SUC a.po_state.vs_inst_idx /\
   z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def, update_var_def] >>
  qabbrev_tac `TG' = step_prov PT TG a.po_inst z.po_state` >>
  suspend "finish"
QED

Resume ptr_focus_call_step[finish]:
  `ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG'` by
    (fs[MEM] >> simp[Abbr `TG'`, ptr_tagged_step_def, step_prov_def, out_prov_def]) >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG' saved` by
    (drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
     `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
       a.po_fn a.po_inst a.po_state = a` by
       simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
     simp[Abbr `z`, ptr_ledger_next_def] >>
     qpat_assum `ptr_tagged_step _ _ _ _ _ = TG'` (SUBST1_TAC o SYM) >>
     qpat_assum `!stk PG G tn token PT TG saved. ptr_tagged_chrono_step _ _ _ _ _ _ _ _ _ _`
       (qspecl_then [`a.po_stack`,`a.po_params`,`a.po_prov`,`a.po_taint`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `ptr_chrono_step C a z` by metis_tac[ptr_tagged_chrono_step_projection] >>
  `ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
    (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)])` by
    (drule ptr_ownership_overlay_fixed >> strip_tac >>
     drule (cj 3 ptr_structural_transcript_rules) >>
     disch_then drule >> disch_then drule >>
     simp[ptr_activation_tokens_def, ptr_activation_registry_def]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    ((qpat_assum `ptr_paired_code _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_paired_code_def] >> strip_tac >>
     fs[fn_labels_def, GSYM (REWRITE_RULE [fn_labels_def] concretize_positions_labels)] >> (metis_tac[fn_labels_def, GSYM (REWRITE_RULE [fn_labels_def] concretize_positions_labels)]))) >>
  `ptr_paired_cursor lp z zt` by
    (irule ptr_ordinary_next_cursor >>
     rpt conj_tac
     >- simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def]
     >- simp[] >>
     qexistsl [`a`,`at`] >>
     simp[Abbr `post`, update_var_def]) >>
  `ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
   ptr_paired_params positions z zt (tokens,registry,births,PT,TG',saved,entries)` by
    (simp[Abbr `TG'`, IgnAsm `z.po_state = _`] >>
     MATCH_MP_TAC ptr_focus_call_sample >>
     simp[Abbr `z`, Abbr `post`] >> metis_tac[]) >>
  `(!q. q IN range_bytes (step_writes a.po_inst a.po_state z.po_state) <=>
       w2n x <= q /\ q < w2n x+k) /\
   (!j. j < k ==> read_byte (w2n x+j) z.po_state.vs_memory =
                  read_byte (w2n y+j) zt.po_state.vs_memory)` by
    (conj_tac
     >- (`step_writes a.po_inst a.po_state z.po_state =
           step_writes a.po_inst a.po_state post` by simp[step_writes_def] >>
         qpat_assum `!q. q IN range_bytes (step_writes _ _ post) <=> _`
           (fn th => simp[th])) >>
     `z.po_state.vs_memory = u.vs_memory /\ zt.po_state.vs_memory = v.vs_memory` by
       simp[Abbr `post`, update_var_def] >>
     qpat_assum `z.po_state.vs_memory = _` (SUBST1_TAC) >>
     qpat_assum `zt.po_state.vs_memory = _` (SUBST1_TAC) >>
     first_assum ACCEPT_TAC) >>
  `(0 < k ==> ptr_paired_write_owner (dyn_floor C a.po_state) lo positions
     (\q. w2n y + (q-w2n x)) (range_bytes (step_writes a.po_inst a.po_state z.po_state))
     (tokens,registry,births,PT,TG',saved,entries))` by
    (strip_tac >>
     `k <= w2n n` by simp[arithmeticTheory.MIN_LE] >>
     `0 < w2n n` by decide_tac >>
     qpat_x_assum `!ops x y n. mem_write_ops _ = _ /\ _ ==> _`
       (qspecl_then [`ops`,`x`,`y`,`w2n n`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >>
     irule ptr_focus_call_write_owner >> qexistsl [`k`,`w2n n`] >>
     rpt conj_tac >> first_assum (fn th => FIRST [ACCEPT_TAC th, metis_tac[th]])) >>
  `ptr_paired_code R lp positions z.po_fn zt.po_fn` by simp[] >>
  qexists `z` >> drule_all ptr_focus_call_attach >> simp[Abbr `TG'`]
QED

Finalise ptr_focus_call_step
