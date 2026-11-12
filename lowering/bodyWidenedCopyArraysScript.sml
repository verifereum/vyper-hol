Theory bodyWidenedCopyArrays
Ancestors
  bodyWidenedCopyFields bodyWidenedCopyPrimitive bodyWidenedCopyPath placeMemoryArrayForward
  placeMemoryArrayControl placeMemoryForwardPath placeMemoryCopyEffect
  placeMemoryTypedBase placeMemoryCopyFrames fragExecMem fragExec freshWrites
  context compileEnv loweringStateRelDefs exprLoweringProps emitHelper emitHelperProps
  venomState venomInst venomExecSemantics venomExecProofs venomInstProofs
  fragGasSeqMem fragGasMode ASCIInumbers list rich_list

Theorem typed_memory_array_addresses_checked_sequence:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, mk_inst_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       memSafeRunTheory.inst_dload_in_section_def]
QED

Theorem typed_memory_array_addresses_forward_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_array_addresses_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule typed_memory_array_addresses_checked_sequence >> goal_assum (drule_at Any)) >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path_mem >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  metis_tac[lookup_var_def]
QED

val M = ``\cenv tenv ctx func dt.
  !st dtv stv v dp sp a b u dw sw.
    type_widens_to tenv st dt /\
    evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
    type_memory_bytes cenv dt = type_memory_size dtv /\
    type_memory_bytes cenv st = type_memory_size stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    value_has_type stv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
        gas_marked_path T ctx func u 0 (OK t)``;

val M_margin = ``\k:num. \cenv tenv ctx func dt.
  !st dtv stv v dp sp a b u dw sw.
    type_widens_to tenv st dt /\
    evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
    type_memory_bytes cenv dt = type_memory_size dtv /\
    type_memory_bytes cenv st = type_memory_size stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    value_has_type stv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv + k < dimword (:256) /\
    w2n sw + type_memory_size stv <= u.vs_alloca_next /\
    w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
        gas_marked_path T ctx func u 0 (OK t)``;

Theorem typed_memory_array_element_margin_forward_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
      doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  ^M_margin k cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw + i * type_memory_size stv) s.vs_memory /\
  (w2n sw + i * type_memory_size stv + type_memory_size stv <=
     w2n dw + i * type_memory_size dtv \/
   w2n dw + i * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + i * type_memory_size stv) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv + k < dimword (:256) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  fn_has_code sa b4 func /\ fn_has_code b4 b5 func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw + i * type_memory_size dtv) t.vs_memory /\
      typed_copy_effect ctx func sa b5 s t
        (w2n dw + i * type_memory_size dtv) (type_memory_size dtv) /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >> fs[] >>
  drule_all typed_memory_array_addresses_forward_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule typed_memory_array_addresses_fresh >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `(_ with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `w2n (sw + n2w (i * type_memory_size stv)) = w2n sw + i * type_memory_size stv /\
   w2n (dw + n2w (i * type_memory_size dtv)) = w2n dw + i * type_memory_size dtv` by
    (`w2n sw + i * type_memory_size stv < dimword (:256) /\
      w2n dw + i * type_memory_size dtv < dimword (:256) /\
      i * type_memory_size stv < dimword (:256) /\
      i * type_memory_size dtv < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `?t. val_in_memory dtv v (w2n (dw + n2w (i * type_memory_size dtv))) t.vs_memory /\
       typed_copy_effect ctx func b4 b5 u t
         (w2n (dw + n2w (i * type_memory_size dtv))) (type_memory_size dtv) /\
       gas_marked_path T ctx func u 0 (OK t)` by
    (first_x_assum (irule o SPEC_ALL) >> simp[] >>
     qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> gvs[] >> decide_tac) >>
  (`typed_copy_effect ctx func sa b4 s u
      (w2n dw + i * type_memory_size dtv) (type_memory_size dtv)` by
     (simp[typed_copy_effect_def] >> conj_tac
      >- (simp[gas_marked_path_def] >> metis_tac[gas_marked_path_exec]) >>
      qpat_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
   qexists_tac `t` >> gvs[] >> conj_tac
   >- (irule typed_copy_effect_then >> qexistsl_tac [`b4`, `b4`, `u`] >>
       gvs[] >> metis_tac[not_fresh_at_mono]) >>
   qpat_assum `gas_marked_path T ctx func s 0 (OK u)` mp_tac >>
   qpat_assum `gas_marked_path T ctx func u 0 (OK t)` mp_tac >>
   rpt (pop_assum kall_tac) >>
   metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES])
QED

Theorem typed_memory_array_element_forward_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
      doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  ^M cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw + i * type_memory_size stv) s.vs_memory /\
  (w2n sw + i * type_memory_size stv + type_memory_size stv <=
     w2n dw + i * type_memory_size dtv \/
   w2n dw + i * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + i * type_memory_size stv) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv + 64 < dimword (:256) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  fn_has_code sa b4 func /\ fn_has_code b4 b5 func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw + i * type_memory_size dtv) t.vs_memory /\
      typed_copy_effect ctx func sa b5 s t
        (w2n dw + i * type_memory_size dtv) (type_memory_size dtv) /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  mp_tac (Q.INST [`k` |-> `64`] typed_memory_array_element_margin_forward_mem) >>
  BETA_TAC >> rewrite_tac[arithmeticTheory.ADD_CLAUSES]
QED

Theorem typed_memory_array_element_frontier_forward_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv st))];
      doff <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dt))];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  compile_store_memory_typed cenv dp dt sp st b4 = ((),b5) /\
  ^M_margin 0 cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw + i * type_memory_size stv) s.vs_memory /\
  (w2n sw + i * type_memory_size stv + type_memory_size stv <=
     w2n dw + i * type_memory_size dtv \/
   w2n dw + i * type_memory_size dtv + type_memory_size dtv <=
     w2n sw + i * type_memory_size stv) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
  w2n sw + i * type_memory_size stv + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + i * type_memory_size dtv + type_memory_size dtv <= s.vs_alloca_next /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\
  fn_has_code sa b4 func /\ fn_has_code b4 b5 func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw + i * type_memory_size dtv) t.vs_memory /\
      typed_copy_effect ctx func sa b5 s t
        (w2n dw + i * type_memory_size dtv) (type_memory_size dtv) /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  mp_tac (Q.INST [`k` |-> `0`] typed_memory_array_element_margin_forward_mem) >>
  BETA_TAC >> rewrite_tac[arithmeticTheory.ADD_CLAUSES]
QED

Theorem typed_memory_array_iteration_forward_mem:
  val_wf stv v /\
  (!j. j < N ==> val_wf dtv (elem j)) /\
  (src + type_memory_size stv <= dst \/
   dst + N * type_memory_size dtv <= src) /\
  val_in_memory stv v src u.vs_memory /\
  typed_copy_effect ctx func sa head s u dst (N * type_memory_size dtv) /\
  gas_marked_path T ctx func s 0 (OK u) /\
  lookup_var counter u = SOME (n2w 0) /\
  (!i a. i < N /\
     val_in_memory stv v src a.vs_memory /\
     (!j. j < i ==> val_in_memory dtv (elem j)
       (dst + j * type_memory_size dtv) a.vs_memory) /\
     typed_copy_effect ctx func sa head s a dst (N * type_memory_size dtv) /\
     lookup_var counter a = SOME (n2w i) ==>
     ?b. val_in_memory dtv (elem i)
           (dst + i * type_memory_size dtv) b.vs_memory /\
         typed_copy_effect ctx func sa head a b
           (dst + i * type_memory_size dtv) (type_memory_size dtv) /\
         gas_marked_path T ctx func a 0 (OK b) /\
         lookup_var counter b = SOME (n2w (SUC i))) ==>
  ?t. val_in_memory stv v src t.vs_memory /\
      (!j. j < N ==> val_in_memory dtv (elem j)
        (dst + j * type_memory_size dtv) t.vs_memory) /\
      typed_copy_effect ctx func sa head s t dst (N * type_memory_size dtv) /\
      gas_marked_path T ctx func s 0 (OK t) /\
      lookup_var counter t = SOME (n2w N)
Proof
  strip_tac >> (
  `!i. i <= N ==> ?a.
     val_in_memory stv v src a.vs_memory /\
     (!j. j < i ==> val_in_memory dtv (elem j)
       (dst + j * type_memory_size dtv) a.vs_memory) /\
     typed_copy_effect ctx func sa head s a dst (N * type_memory_size dtv) /\
     gas_marked_path T ctx func s 0 (OK a) /\
     lookup_var counter a = SOME (n2w i)` suffices_by metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
  Induct >> strip_tac
  >- (qexists_tac `u` >> simp[]) >>
  `i <= N /\ i < N` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!i a. _` drule_all >> strip_tac >>
  `val_in_memory stv v src b.vs_memory /\
   (!j. j < SUC i ==> val_in_memory dtv (elem j)
     (dst + j * type_memory_size dtv) b.vs_memory)` by
    (irule typed_memory_array_prefix_step >>
     conj_tac >- (qexists_tac `N` >> simp[]) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `i * type_memory_size dtv + type_memory_size dtv <= N * type_memory_size dtv` by
    (`SUC i * type_memory_size dtv <= N * type_memory_size dtv` by simp[] >>
     qpat_x_assum `SUC i * _ <= _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `typed_copy_effect ctx func sa head a b dst (N * type_memory_size dtv)` by
    (irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> decide_tac) >>
  qexists_tac `b` >> simp[] >> conj_tac
  >- (irule typed_copy_effect_then >>
      qpat_assum `typed_copy_effect ctx func sa head a b dst _` (irule_at Any) >>
      qpat_assum `typed_copy_effect ctx func sa head s a dst _` (irule_at Any) >> simp[]) >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES])
QED

Theorem typed_memory_prefix_jump_forward_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = prefix ++ [term] /\
  s.vs_inst_idx + LENGTH prefix = k /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
  EVERY (\i. i.inst_opcode <> GAS) prefix /\
  run_inst_seq prefix s = OK u /\ run_inst_seq_mem_ok prefix s /\
  is_terminator term.inst_opcode /\ term.inst_opcode <> INVOKE /\
  term.inst_opcode <> GAS /\
  inst_mem_below_frontier term (u with vs_inst_idx := k) /\
  inst_dload_in_section term (u with vs_inst_idx := k) /\
  step_inst_base term (u with vs_inst_idx := k) =
    OK (jump_to lbl (u with vs_inst_idx := k)) ==>
  gas_marked_path T ctx func s 0
    (OK (jump_to lbl (u with vs_inst_idx := k)))
Proof
  strip_tac >>
  `isPREFIX prefix (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `FILTER (\i. i.inst_opcode = GAS) prefix = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[EVERY_MEM]) >>
  `gas_marked_path T ctx func s 0
     (OK (u with vs_inst_idx := k))` by
    (drule_all fragGasSeqMemTheory.run_inst_seq_gas_path_mem >> simp[gas_marked_path_def]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (conj_tac >> irule run_inst_seq_preserves_field >>
     qexists_tac `prefix` >> simp[] >> rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (qpat_x_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `i` mp_tac) >> simp[]) >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all venomInstProofsTheory.step_preserves_halted >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  `gas_marked_path T ctx func (u with vs_inst_idx := k) 0
     (OK (jump_to lbl (u with vs_inst_idx := k)))` by
    (irule gas_marked_path_zero_jump_mem >> simp[] >>
     qexists_tac `term` >>
     `DROP k bb.bb_instructions = [term]` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP (LENGTH prefix)`) >>
        pure_rewrite_tac[DROP_DROP_T] >>
        `LENGTH prefix + s.vs_inst_idx = k` by decide_tac >>
        simp[DROP_APPEND]) >>
     `k < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP k _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_DROP]) >>
     simp[get_instruction_def] >>
     qpat_x_assum `DROP k _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP] >> gvs[]) >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem typed_memory_array_init_forward_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ASSIGN [Lit 0w] [counter]; mk_inst id2 JMP [Label hdr] []] ==>
  gas_marked_path T ctx func s 0
    (OK (jump_to hdr ((update_var counter 0w s) with
                     vs_inst_idx := s.vs_inst_idx + 1)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_forward_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def, run_inst_seq_mem_ok_def,
       step_inst_base_opcode_eqs, eval_operand_def] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       memSafeRunTheory.inst_dload_in_section_def]
QED

Theorem typed_memory_array_backedge_forward_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  lookup_var counter s = SOME (n2w i) /\ SUC i < dimword (:256) ==>
  gas_marked_path T ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) s)) with
        vs_inst_idx := s.vs_inst_idx + 2)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_forward_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def, run_inst_seq_mem_ok_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, wordsTheory.word_add_n2w, arithmeticTheory.ADD1] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       memSafeRunTheory.inst_dload_in_section_def]
QED

Theorem typed_memory_array_condition_forward_mem:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  eval_operand (Var counter) s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) ==>
  gas_marked_path T ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))
Proof
  strip_tac >>
  irule typed_memory_prefix_jump_forward_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def, run_inst_seq_mem_ok_def,
       step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_update_var] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       memSafeRunTheory.inst_dload_in_section_def] >>
  `i < dimword (:256)` by decide_tac >>
  gvs[eval_operand_def] >>
  Cases_on `i < N` >> simp[bool_to_word_def, wordsTheory.w2n_n2w,
    arithmeticTheory.LESS_MOD, lookup_var_update_var]
QED

Theorem typed_memory_array_backedge_effect_mem:
  typed_copy_effect ctx func bst b5 s v d n /\
  gas_marked_path T ctx func s 0 (OK v) /\
  lookup_var counter s = SOME (n2w i) /\ not_fresh_at bst counter /\
  (!x. not_fresh_at old x ==>
       not_fresh_at bst x /\ x <> inc /\ x <> counter) /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME bb /\
  DROP (LENGTH b5.cs_current_insts) bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  SUC i < dimword (:256) /\
  head.cs_current_bb = hdr /\ head.cs_current_insts = [] ==>
  ?t. typed_copy_effect ctx func old head s t d n /\
      lookup_var counter t = SOME (n2w (SUC i)) /\ t.vs_memory = v.vs_memory /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >>
  `lookup_var counter v = SOME (n2w i)` by
    metis_tac[typed_copy_effect_lookup] >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  `gas_marked_path T ctx func v 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)))` by
    (irule typed_memory_array_backedge_forward_mem >> simp[] >>
     qexistsl_tac [`id1`, `id2`, `id3`] >> simp[]) >>
  `gas_marked_path T ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)))` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  `gas_marked_path F ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)))` by
    (simp[gas_marked_path_def] >> metis_tac[gas_marked_path_exec]) >>
  qexists_tac `jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
        vs_inst_idx := v.vs_inst_idx + 2)` >>
  simp[jump_to_def, lookup_var_update_var] >>
  qpat_x_assum `typed_copy_effect _ _ _ _ _ _ _ _` mp_tac >>
  strip_tac >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem typed_memory_array_condition_effect_mem:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  lookup_var counter s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) /\
  counter <> lt /\ counter <> done /\
  (!x. not_fresh_at old x ==> x <> lt /\ x <> done) /\
  next.cs_current_bb = (if i < N then blabel else exit) /\
  next.cs_current_insts = [] ==>
  ?t. typed_copy_effect ctx func old next s t d n /\
      lookup_var counter t = SOME (n2w i) /\ t.vs_memory = s.vs_memory /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >>
  `gas_marked_path T ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))` by
    (irule typed_memory_array_condition_forward_mem >> simp[eval_operand_def] >>
     qexistsl_tac [`counter`, `id1`, `id2`, `id3`, `length`] >> simp[]) >>
  `gas_marked_path F ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))` by
    (simp[gas_marked_path_def] >> metis_tac[gas_marked_path_exec]) >>
  qexists_tac `jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)` >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem typed_memory_array_round_effect_mem:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME hbb /\
  hbb.bb_instructions =
    [mk_inst h1 LT [Var counter; length] [lt];
     mk_inst h2 ISZERO [Var lt] [done];
     mk_inst h3 JNZ [Var done; Label exit; Label blabel] []] /\
  lookup_var counter s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i < N /\ N < dimword (:256) /\
  counter <> lt /\ counter <> done /\ not_fresh_at bst counter /\
  (!x. not_fresh_at old x ==> x <> lt /\ x <> done /\
       not_fresh_at bst x /\ x <> inc /\ x <> counter) /\
  bst.cs_current_bb = blabel /\ bst.cs_current_insts = [] /\
  head.cs_current_bb = s.vs_current_bb /\ head.cs_current_insts = [] /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME ebb /\
  DROP (LENGTH b5.cs_current_insts) ebb.bb_instructions =
    [mk_inst e1 ADD [Var counter; Lit 1w] [inc];
     mk_inst e2 ASSIGN [Var inc] [counter];
     mk_inst e3 JMP [Label head.cs_current_bb] []] /\
  (!a. typed_copy_effect ctx func old bst s a d n /\
       lookup_var counter a = SOME (n2w i) /\ a.vs_memory = s.vs_memory ==>
       ?v. val_in_memory dtv value d v.vs_memory /\
           typed_copy_effect ctx func bst b5 a v d n /\
           gas_marked_path T ctx func a 0 (OK v)) ==>
  ?t. val_in_memory dtv value d t.vs_memory /\
      typed_copy_effect ctx func old head s t d n /\
      lookup_var counter t = SOME (n2w (SUC i)) /\
      gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >>
  `?a. typed_copy_effect ctx func old bst s a d n /\
       lookup_var counter a = SOME (n2w i) /\ a.vs_memory = s.vs_memory /\
       gas_marked_path T ctx func s 0 (OK a)` by
    (irule typed_memory_array_condition_effect_mem >>
     qpat_assum `hbb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  qpat_x_assum `!a. _ ==> ?v. _` drule_all >> strip_tac >>
  `?t. typed_copy_effect ctx func old head a t d n /\
       lookup_var counter t = SOME (n2w (SUC i)) /\ t.vs_memory = v.vs_memory /\
       gas_marked_path T ctx func a 0 (OK t)` by
    (irule typed_memory_array_backedge_effect_mem >>
     qpat_assum `typed_copy_effect ctx func bst b5 a v d n` (irule_at Any) >>
     qpat_assum `DROP _ ebb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule typed_copy_effect_then >>
      qpat_assum `typed_copy_effect ctx func old head a t d n` (irule_at Any) >>
      qpat_assum `typed_copy_effect ctx func old bst s a d n` (irule_at Any) >> simp[]) >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED
