Theory concretizePtrCallPointExecution
Ancestors
  concretizePtrCallFamily concretizePtrChronologicalHistory
  concretizePtrRequestHistory concretizePtrValueTransport concretizePtrOpaqueRetpc
  concretizePtrBytes copyFwdEquiv list venomState allocaRemapDefs ptrDiscipline
  opcodeClass venomInst venomInstProofs1 venomExecSemantics venomExecProofs
  venomWf memLocDefs codegenRel contextCodegenRel finite_map pred_set

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
Theorem ptr_focus_call_execute:
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
  disch_then (qspec_then `sr` strip_assume_tac) >>
  `u.vs_allocas = a.po_state.vs_allocas /\
   u.vs_current_bb = a.po_state.vs_current_bb /\
   u.vs_prev_bb = a.po_state.vs_prev_bb /\
   u.vs_params = a.po_state.vs_params /\
   (!x. x <> out ==> lookup_var x u = lookup_var x a.po_state) /\
   u.vs_return_pc_token = a.po_state.vs_return_pc_token` by
    (Cases_on `a.po_state.vs_outcomes = []` >>
     qpat_x_assum `exec_ext_call _ a.po_state _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exec_ext_call_def, update_var_def, venom_state_component_equality] >>
     strip_tac >> gvs[lookup_var_def] >> qx_gen_tac `x` >> disch_tac >>
     qpat_assum `_ |+ _ = _ |+ _` (mp_tac o Q.AP_TERM `\m. FLOOKUP m x`) >>
     simp[FLOOKUP_UPDATE]) >>
  `v.vs_current_bb = at.po_state.vs_current_bb /\
   v.vs_prev_bb = at.po_state.vs_prev_bb /\
   v.vs_params = at.po_state.vs_params /\
   (!x. x <> out ==> lookup_var x v = lookup_var x at.po_state) /\
   v.vs_return_pc_token = at.po_state.vs_return_pc_token` by
    (Cases_on `at.po_state.vs_outcomes = []` >>
     qpat_x_assum `exec_ext_call _ at.po_state _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exec_ext_call_def, update_var_def, venom_state_component_equality] >>
     strip_tac >> gvs[lookup_var_def] >> qx_gen_tac `x` >> disch_tac >>
     qpat_assum `_ |+ _ = _ |+ _` (mp_tac o Q.AP_TERM `\m. FLOOKUP m x`) >>
     simp[FLOOKUP_UPDATE]) >>
  qexistsl [`w`,`u`,`v`,
    `<|iao_ofst := ro_op; iao_size := NONE; iao_max_size := SOME rs_op|>`,
    `sr`,`ro`,`rs`] >>
  gvs[Excl "MEM"] >>
  (conj_tac >-
    (simp[step_inst_non_invoke] >>
     pure_rewrite_tac[step_inst_base_def] >>
     qpat_assum `a.po_inst.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[opcode_case_def] >>
     simp[])) >>
  simp[mem_write_ops_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, memory_range_of_operands_def,
       eval_operands_def, step_writes_def, range_bytes_def, update_var_def]
QED
