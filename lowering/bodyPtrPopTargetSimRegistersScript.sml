Theory bodyPtrPopTargetSimRegisters
Ancestors
  bodyPtrPopTargetSimArrayGuard
  bodyPtrPopTargetSimArrayEndpoint fragGasFresh appendStorageStageTransportPtr
  bodyPtrBopScalarRun bodyPtrBopScalarSeq bodyPtrBopScalarOutcome bodyPtrBopScalarDynamic
  varsExt freshWrites fragExec venomState
  exprSimArrayIndex exprLoweringProps compileEnv list pred_set venomInst ptrDiscipline

(* Normalize only the ordinary run.  The pointer certificate is applied to
   the original state and original ghost, not to the normalized registers. *)
Theorem target_bounds_transport_opcodes_ptr:
  array_bounds_check idx len sgn sa = ((),sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule target_bounds_check_certificate_ptr >>
  disch_then (qspecl_then [`{}`, `{idx;len;Lit 0w}`] mp_tac) >>
  simp[] >> strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all bop_scalar_seq_outputs >> strip_tac >>
  gvs[MEM, is_terminator_def, is_ext_call_op_def]
QED

Theorem target_bounds_run_old_inputs_ptr:
  array_bounds_check idx len sgn sa = ((),sb) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  idx_in_range sgn i n ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t
Proof
  strip_tac >>
  `eval_operand idx (drop_fresh sa s) = SOME i /\
   eval_operand len (drop_fresh sa s) = SOME n` by
    gvs[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all array_bounds_check_ok >> strip_tac >>
  drule target_bounds_transport_opcodes_ptr >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def] >> metis_tac[]
QED

Theorem target_bounds_path_old_inputs_ptr:
  array_bounds_check idx len sgn sa = ((),sb) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  idx_in_range sgn i n /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un. run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
       FLOOKUP H z = FLOOKUP G z /\ FLOOKUP un.t_var z = FLOOKUP tn.t_var z)
Proof
  strip_tac >> drule_all target_bounds_run_old_inputs_ptr >> strip_tac >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z} {idx;len;Lit 0w}
        (emitted_insts sa sb) B` by
    (irule target_bounds_check_certificate_ptr >> simp[] >> metis_tac[]) >>
  `!op. op IN {idx;len;Lit 0w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[]
QED

Theorem target_array_suffix_run_old_inputs_ptr:
  array_bounds_check idx len sgn sa = ((),sm) /\
  array_elem_ptr bop idx dyn ws esz sm = (dst,sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  eval_operand len s = SOME n /\ idx_in_range sgn i n ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    copy_old_operand sb dst /\
    eval_operand dst t = SOME ((if dyn then b+n2w ws else b)+i*n2w esz) /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `eval_operand bop (drop_fresh sa s) = SOME b /\
   eval_operand idx (drop_fresh sa s) = SOME i /\
   eval_operand len (drop_fresh sa s) = SOME n` by
    gvs[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all target_array_suffix_runtime >> strip_tac >>
  drule_all target_array_suffix_writes_fresh >> strip_tac >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     gvs[EVERY_CONJ]) >>
  gvs[vars_ext_result_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  goal_assum (drule_at Any) >> simp[lookup_var_def] >>
  metis_tac[vars_ext_eval_operand]
QED

Theorem target_fixed_array_run_old_inputs_ptr:
  compile_array_subscript bop idx F cnt ws esz sgn loader sa = (dst,sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME i /\
  idx_in_range sgn i (n2w cnt) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand dst t = SOME (b+i*n2w esz) /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sa = (unit,sm)` >> Cases_on `unit` >>
  `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
  `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all target_array_suffix_run_old_inputs_ptr >> simp[] >>
  metis_tac[lookup_var_def]
QED

Theorem target_bounds_run_abort_old_inputs_ptr:
  array_bounds_check idx len sgn sa = ((),sb) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  ~idx_in_range sgn i n ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  `eval_operand idx (drop_fresh sa s) = SOME i /\
   eval_operand len (drop_fresh sa s) = SOME n` by
    gvs[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all array_bounds_check_oob >> strip_tac >>
  drule target_bounds_transport_opcodes_ptr >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def] >> metis_tac[]
QED

Theorem target_bounds_abort_old_inputs_ptr:
  array_bounds_check idx len sgn sa = ((),sb) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  eval_operand idx s = SOME i /\ eval_operand len s = SOME n /\
  ~idx_in_range sgn i n /\
  op_prov G idx = NONE /\ op_taint tn idx = {} /\
  op_prov G len = NONE /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un fuel pc. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_path_ptr D 0 ctx fn PG G tn s fuel H un
      (Abort Revert_abort (t with vs_inst_idx := pc)) /\
    un.t_mem = tn.t_mem /\ un.t_stor = tn.t_stor /\
    un.t_trans = tn.t_trans /\ un.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==>
       FLOOKUP H z = FLOOKUP G z /\ FLOOKUP un.t_var z = FLOOKUP tn.t_var z)
Proof
  strip_tac >> drule_all target_bounds_run_abort_old_inputs_ptr >> strip_tac >>
  `?B. bop_scalar_seq {z | not_fresh_at sa z} {idx;len;Lit 0w}
        (emitted_insts sa sb) B` by
    (irule target_bounds_check_certificate_ptr >> simp[] >> metis_tac[]) >>
  `!op. op IN {idx;len;Lit 0w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_abort_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
