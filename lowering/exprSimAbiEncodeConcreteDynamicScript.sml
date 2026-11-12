Theory exprSimAbiEncodeConcreteDynamic
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodeConcreteWrappers abiEncoderWindowChild abiEncoderChildCode
  abiEncoderWindowSequence abiEncoderWindowPhase abiEncoderWindowLookup
  abiEncoderAddressReach emitHelperProps compileEnv emitHelper
  venomState venomInst list words valueEncodingProps freshWrites arithmetic
  exprLoweringProps rich_list abiEncoderWindowLeaves
  exprSimAbiEncodeConcreteCompose abiEncoderRegisteredEffect
  exprSimAbiEncodeNoBlockStructure abiEncoderWindowContract abiEncoderProps
  abiEncoderAppend abiDecoderReentry pred_set abiEncoderChildContext fragExec

Theorem abi_encode_emit_counter[local]:
  emit_op opc operands st = (out,en) ==>
  en.cs_next_var = st.cs_next_var+1
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_encode_prefix_pure:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w slot) /\
  (!x. dst = Var x \/ dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ mem_word_at slot s.vs_memory = n2w off ==>
  ?r. window_pure_seq st en s r /\
    eval_operand (FST ops) r = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) r = SOME (n2w off) /\
    eval_operand (SND (SND ops)) r = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x \/
      SND (SND ops) = Var x ==> not_fresh_at en x)
Proof
  simp_tac bool_ss [abi_encode_child_prefix_def, comp_bind_def,
    comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [dst;Lit (n2w ho)] st = (head,a)` >>
  rename1 `emit_op MLOAD [dp] a = (offset,b)` >>
  rename1 `emit_op ADD [dst;offset] b = (child,en)` >>
  `st.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
    b.cs_next_var <= en.cs_next_var` by
    metis_tac[abi_encode_emit_counter, LESS_EQ_ADD] >>
  `eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq st a s r1` >>
  `eval_operand dp r1 = SOME (n2w slot) /\ eval_operand dst r1 = SOME (n2w d)` by
    (conj_tac >> irule window_seq_eval >>
     qexistsl_tac [`s`, `st`, `a`] >> fs[window_pure_seq_def]) >>
  `mload slot r1 = n2w off` by
    fs[window_pure_seq_def, mem_word_at_eq_mload, mload_def, read_memory_def] >>
  drule_all window_emit_load_pure >> strip_tac >>
  rename1 `window_pure_seq a b r1 r2` >>
  `eval_operand dst r2 = SOME (n2w d)` by
    (irule window_seq_eval >> qexistsl_tac [`r1`, `a`, `b`] >>
     fs[window_pure_seq_def] >> metis_tac[not_fresh_at_mono]) >>
  drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq b en r2 r3` >>
  `window_pure_seq a en r1 r3` by metis_tac[window_pure_seq_chain] >>
  `eval_operand head r3 = SOME (n2w (d+ho))` by
    (irule window_seq_eval >> qexistsl_tac [`r1`, `a`, `en`] >>
     fs[window_pure_seq_def, word_add_n2w]) >>
  `eval_operand offset r3 = SOME (n2w off)` by
    (irule window_seq_eval >> qexistsl_tac [`r2`, `b`, `en`] >>
     fs[window_pure_seq_def]) >>
  qexists_tac `r3` >> simp[word_add_n2w] >>
  conj_tac >- metis_tac[window_pure_seq_chain] >>
  metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]
QED

Theorem abi_encode_prefix_outputs[local]:
  abi_encode_child_prefix dst ho dp st = (ops,en) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ EVERY (not_fresh_at en) i.inst_outputs)
    (emitted_insts st en)
Proof
  simp_tac bool_ss [abi_encode_child_prefix_def, comp_bind_def,
    comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  simp[not_fresh_at_def]
QED

Theorem abi_encode_child_prefix_concrete:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  fn_has_code st en func /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w slot) /\
  (!x. dst = Var x \/ dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ mem_word_at slot s.vs_memory = n2w off /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_phase ctx func st en {} [] s
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    eval_operand (FST ops) (r with vs_inst_idx := LENGTH en.cs_current_insts) = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) (r with vs_inst_idx := LENGTH en.cs_current_insts) = SOME (n2w off) /\
    eval_operand (SND (SND ops)) (r with vs_inst_idx := LENGTH en.cs_current_insts) = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x \/
         SND (SND ops) = Var x ==> not_fresh_at en x) /\
    (r with vs_inst_idx := LENGTH en.cs_current_insts).vs_labels = s.vs_labels /\
    (!x. ~not_fresh_at en x ==>
      lookup_var x (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >> drule_all abi_encode_prefix_pure >> strip_tac >>
  `window_phase ctx func st en {} [] s
    (r with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_pure_seq_phase >> simp[]) >>
  `r.vs_labels = s.vs_labels` by
    metis_tac[window_seq_labels, window_pure_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ EVERY (not_fresh_at en) i.inst_outputs)
    (emitted_insts st en)` by metis_tac[abi_encode_prefix_outputs] >>
  `!x. ~not_fresh_at en x ==>
    lookup_var x (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s` by
    (fs[window_pure_seq_def] >> drule window_seq_high_vars >> simp[]) >>
  qexists_tac `r` >> fs[window_pure_seq_def, window_seq_def, EVERY_MEM,
    eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem abi_encode_store_eval[local]:
  eval_operand op ((mstore p w s) with vs_inst_idx := idx) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def,
    mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_add_concrete[local]:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?r. window_pure_seq st en s r /\
    window_phase ctx func st en {} [] s
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    eval_operand out (r with vs_inst_idx := LENGTH en.cs_current_insts) = SOME (a+b) /\
    (!x. ~not_fresh_at en x ==>
      lookup_var x (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >> drule_all window_emit_add_pure >> strip_tac >>
  rename1 `window_pure_seq st en s r` >>
  `window_phase ctx func st en {} [] s
    (r with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_pure_seq_phase >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ EVERY (not_fresh_at en) i.inst_outputs)
    (emitted_insts st en)` by
    (irule abi_window_emit_register_bounds >>
     qexistsl_tac [`[lhs;rhs]`, `ADD`, `out`] >> simp[]) >>
  qexists_tac `r` >> simp[eval_operand_def, lookup_var_def] >>
  fs[window_pure_seq_def] >> drule window_seq_high_vars >> simp[lookup_var_def]
QED

Theorem abi_encode_three_runs[local]:
  inst_extends st a /\ inst_extends a b /\ inst_extends b en /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st a) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts b en) /\
  run_inst_seq (emitted_insts st a) s = OK r1 /\
  run_inst_seq (emitted_insts a b)
    (r1 with vs_inst_idx := LENGTH a.cs_current_insts) = OK r2 /\
  run_inst_seq (emitted_insts b en)
    (r2 with vs_inst_idx := LENGTH b.cs_current_insts) = OK r3 ==>
  ?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    (r3 with vs_inst_idx := LENGTH en.cs_current_insts) =
    (r with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >>
  `inst_extends st b /\ inst_extends st en` by metis_tac[inst_extends_trans] >>
  `emitted_insts st b = emitted_insts st a ++ emitted_insts a b /\
   emitted_insts st en = emitted_insts st b ++ emitted_insts b en` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  `?u. run_inst_seq (emitted_insts st b) s = OK u /\
    (u with vs_inst_idx := LENGTH b.cs_current_insts) =
    (r2 with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (asm_rewrite_tac[] >> irule abi_encode_run_append_normalized >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`LENGTH a.cs_current_insts`, `r1`] >> simp[]) >>
  `?r. run_inst_seq (emitted_insts st en) s = OK r /\
    (r with vs_inst_idx := LENGTH en.cs_current_insts) =
    (r3 with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (asm_rewrite_tac[] >> irule abi_encode_run_append_normalized >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`LENGTH b.cs_current_insts`, `u`] >> metis_tac[]) >>
  qexists_tac `r` >> simp[EVERY_APPEND]
QED

Theorem abi_encode_store_concrete[local]:
  emit_void MSTORE [ptr_op;value] st = ((),en) /\
  eval_operand ptr_op s = SOME (n2w p) /\ eval_operand value s = SOME w /\
  p < dimword (:256) ==>
  run_inst_seq (emitted_insts st en) s = OK (mstore p w s) /\
  inst_extends st en /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)
Proof
  strip_tac >> drule_all window_emit_store_run >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_encode_child_suffix_concrete:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a b t1 t2 t3 r.
    window_phase ctx func st a {} [(h,32)] s t1 /\
    window_phase ctx func a b {} [] t1 t2 /\
    window_phase ctx func b en {site} [] t2 t3 /\
    a.cs_next_var = st.cs_next_var /\ b.cs_next_var = a.cs_next_var+1 /\
    t1.vs_memory = (mstore h (n2w off) s).vs_memory /\
    t3 = ((mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts) /\
    out = len /\ eval_operand out t3 = SOME (n2w n) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t3 = lookup_var x s) /\
    inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    t3 = (r with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >> drule_all window_child_suffix_context >> strip_tac >>
  qabbrev_tac `t1 = (mstore h (n2w off) s) with vs_inst_idx := LENGTH a.cs_current_insts` >>
  `window_phase ctx func st a {} [(h,32)] s t1` by
    (simp_tac bool_ss [Abbr `t1`] >> irule window_output_store_phase >>
     asm_rewrite_tac[] >> qexistsl_tac [`head`, `offset`] >> asm_rewrite_tac[]) >>
  `eval_operand offset t1 = SOME (n2w off) /\
   eval_operand len t1 = SOME (n2w n) /\ eval_operand dp t1 = SOME (n2w slot)` by
    simp[Abbr `t1`, abi_encode_store_eval] >>
  `alloca_inv t1 /\ alloca_room ctx func t1 /\ ~t1.vs_halted /\
   t1.vs_current_bb = a.cs_current_bb /\ t1.vs_inst_idx = LENGTH a.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  drule_all abi_encode_add_concrete >> strip_tac >>
  rename1 `window_pure_seq a b t1 r2` >>
  qabbrev_tac `t2 = r2 with vs_inst_idx := LENGTH b.cs_current_insts` >>
  `window_phase ctx func a b {} [] t1 t2 /\
   eval_operand next t2 = SOME (n2w (off+n)) /\
   (!x. ~not_fresh_at b x ==> lookup_var x t2 = lookup_var x t1)` by
    fs[Abbr `t2`, word_add_n2w] >>
  `t2.vs_labels = t1.vs_labels` by
    (fs[Abbr `t2`] >> metis_tac[window_seq_labels, window_pure_seq_def]) >>
  `eval_operand dp t2 = SOME (n2w slot) /\ eval_operand len t2 = SOME (n2w n)` by
    (conj_tac >> irule window_phase_eval >> asm_rewrite_tac[] >>
     qexistsl_tac [`ctx`, `b`, `func`, `{}`, `[]`, `t1`, `a`] >>
     asm_rewrite_tac[] >> fs[not_fresh_at_def] >> metis_tac[]) >>
  `alloca_inv t2 /\ alloca_room ctx func t2 /\ ~t2.vs_halted /\
   t2.vs_current_bb = b.cs_current_bb /\ t2.vs_inst_idx = LENGTH b.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `FLOOKUP t2.vs_allocas site = SOME (slot,32)` by
    (irule abi_encoder_registered_effect_allocated >>
     qexistsl_tac [`{}`, `[]`, `t1`] >>
     (conj_tac >- simp[Abbr `t1`, mstore_def, write_memory_with_expansion_def]) >>
     metis_tac[window_phase_effect]) >>
  qabbrev_tac `t3 = (mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `window_phase ctx func b en {site} [] t2 t3` by
    (simp_tac bool_ss [Abbr `t3`] >> irule window_cursor_store_phase >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st a) s = OK (mstore h (n2w off) s) /\
   inst_extends st a /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st a)` by
    (irule abi_encode_store_concrete >> conj_tac >- simp[] >> qexistsl_tac [`head`, `offset`] >> simp[]) >>
  `run_inst_seq (emitted_insts b en) t2 = OK (mstore slot (n2w (off+n)) t2) /\
   inst_extends b en /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts b en)` by
    (irule abi_encode_store_concrete >> conj_tac >- simp[] >> qexistsl_tac [`dp`, `next`] >> simp[]) >>
  `?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    t3 = (r with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (simp_tac bool_ss [Abbr `t3`] >>
     irule abi_encode_three_runs >>
     qexistsl_tac [`a`, `b`, `mstore h (n2w off) s`, `r2`] >>
     fs[Abbr `t1`, Abbr `t2`, window_pure_seq_def, window_seq_def, EVERY_MEM] >>
     metis_tac[]) >>
  qexistsl_tac [`a`, `b`, `t1`, `t2`, `t3`, `r`] >>
  simp[abi_encode_store_eval, Abbr `t3`, Abbr `t1`] >>
  rpt strip_tac >>
  qpat_x_assum `!x. ~not_fresh_at b x ==> _` (qspec_then `x` mp_tac) >>
  simp[not_fresh_at_def, lookup_var_def, mstore_def, write_memory_with_expansion_def] >>
  fs[not_fresh_at_def] >>
  qpat_x_assum `(mstore _ _ _ with vs_inst_idx := _) = _` mp_tac >>
  simp[venom_state_component_equality, mstore_def, write_memory_with_expansion_def] >>
  metis_tac[]
QED

Theorem abi_encode_child_pre_end[local]:
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  mid.cs_next_id <= en.cs_next_id /\ fn_has_code st mid func ==>
  abi_encoder_window_pre ctx func st mid dst src ei at av sb cap d s
Proof
  pure_rewrite_tac [abi_encoder_window_pre_def] >> strip_tac >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `inst.inst_id IN frag_ids st en` by
    (qpat_x_assum `_ IN frag_ids st mid` mp_tac >>
     simp_tac (srw_ss()) [frag_ids_def] >> decide_tac) >> metis_tac[]
QED

Theorem abi_encode_dynamic_child_call_concrete[local]:
  abi_encode_concrete_contract ei /\
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) src
    ei at av sb cap (d+off) s /\ st.cs_blocks = en.cs_blocks /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w slot) /\
  (!x. dst = Var x \/ dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ mem_word_at slot s.vs_memory = n2w off ==>
  ?ops ready len child_end pr cr.
    abi_encode_child_prefix dst ho dp st = (ops,ready) /\
    compile_abi_encode_to_buf (SND (SND ops)) src ei ready = (len,child_end) /\
    abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len child_end = (out,en) /\
    fn_has_code child_end en func /\
    st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= child_end.cs_next_var /\
    st.cs_next_id <= ready.cs_next_id /\ child_end.cs_next_id <= en.cs_next_id /\
    child_end.cs_next_var <= en.cs_next_var /\
    (!x. len = Var x ==> not_fresh_at child_end x) /\
    inst_extends st ready /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready) /\
    run_inst_seq (emitted_insts st ready) s = OK pr /\
    abi_encode_concrete_result ctx func ready child_end len at av (d+off)
      (pr with vs_inst_idx := LENGTH ready.cs_current_insts) cr /\
    window_phase ctx func st ready {} [] s
      (pr with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    eval_operand (FST ops) (cr with vs_inst_idx := LENGTH child_end.cs_current_insts) = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) (cr with vs_inst_idx := LENGTH child_end.cs_current_insts) = SOME (n2w off) /\
    window_phase ctx func st child_end
      (window_alloca_sites func (frag_ids ready child_end))
      [(d+off,LENGTH (enc at av))] s
      (cr with vs_inst_idx := LENGTH child_end.cs_current_insts) /\
    (!x. ~not_fresh_at child_end x ==>
      lookup_var x (cr with vs_inst_idx := LENGTH child_end.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
  drule_all abi_encode_child_prefix_concrete >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK pr` >>
  qabbrev_tac `prep = pr with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  `cs_extends child_end en` by
    (drule abi_encode_child_suffix_shape >> strip_tac >>
     irule abi_encoder_straight_extends >> asm_rewrite_tac[]) >>
  `child_end.cs_next_var <= en.cs_next_var` by
    (drule_all window_child_suffix_context >> strip_tac >> decide_tac) >>
  `cs_extends ready child_end` by metis_tac[cs_extends_abi_encode] >>
  `cs_extends st ready` by
    (drule abi_encode_child_prefix_shape >> strip_tac >>
     irule abi_encoder_straight_extends >> asm_rewrite_tac[]) >>
  `fn_has_code ready en func` by metis_tac[cs_extends_trans, fn_has_code_split] >>
  `abi_encoder_window_pre ctx func ready en (SND (SND ops)) src
    ei at av sb cap (d+off) prep` by
    (irule window_static_child_pre >> asm_rewrite_tac[] >> simp[] >>
     qexistsl_tac [`Lit (n2w (d+off))`, `s`, `st`] >> simp[]) >>
  `abi_encoder_window_pre ctx func ready child_end (SND (SND ops)) src
    ei at av sb cap (d+off) prep` by
    (irule abi_encode_child_pre_end >> asm_rewrite_tac[] >> qexists_tac `en` >> simp[]) >>
  `ready.cs_blocks = child_end.cs_blocks` by
    (drule_all abi_encode_dynamic_child_no_block >> strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `abi_encode_concrete_contract ei` mp_tac >>
  rewrite_tac[abi_encode_concrete_contract_def] >>
  disch_then drule_all >> strip_tac >>
  rename1 `abi_encode_concrete_result _ _ _ _ _ _ _ _ prep cr` >>
  qabbrev_tac `actual = cr with vs_inst_idx := LENGTH child_end.cs_current_insts` >>
  `window_strong_result ctx func ready child_end child_len at av (d+off) prep actual /\
   (!x. ~not_fresh_at child_end x ==> lookup_var x actual = lookup_var x prep)` by
    fs[abi_encode_concrete_result_def, Abbr `actual`] >>
  `!x. ~not_fresh_at child_end x ==> lookup_var x actual = lookup_var x s` by
    metis_tac[abi_window_high_vars_trans] >>
  `window_phase ctx func ready child_end
    (window_alloca_sites func (frag_ids ready child_end))
    [(d+off,LENGTH (enc at av))] prep actual` by
    metis_tac[window_phase_strong_result] >>
  `(?x. FST ops = Var x) /\ (?x. FST (SND ops) = Var x)` by
    (drule window_child_prefix_variables >> strip_tac >> asm_rewrite_tac[] >> simp[]) >>
  `eval_operand (FST ops) actual = SOME (n2w (d+ho)) /\
   eval_operand (FST (SND ops)) actual = SOME (n2w off)` by
    metis_tac[window_phase_eval_var] >>
  qexistsl_tac [`ops`, `ready`, `child_len`, `child_end`, `pr`, `cr`] >>
  fs[Abbr `prep`, Abbr `actual`] >>
  conj_tac >- (Cases_on `child_len` >>
    fs[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `ready`,
    `window_alloca_sites func (frag_ids ready child_end)`,
    `[(d+off,LENGTH (enc at av))]`,
    `pr with vs_inst_idx := LENGTH ready.cs_current_insts`] >> simp[]
QED

Theorem abi_encode_pure_word[local]:
  window_phase ctx func st en {} [] s t ==>
  mem_word_at p t.vs_memory = mem_word_at p s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at p 32 t.vs_memory = mem_bytes_at p 32 s.vs_memory` by
    (irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{}`, `[]`] >>
     simp[] >> metis_tac[window_phase_effect]) >>
  drule abiEncoderInputFrameTheory.abi_encoder_window_word >>
  disch_then (qspec_then `0` mp_tac) >> simp[]
QED

Theorem abi_encode_child_suffix_run_concrete[local]:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  (h+32 <= slot \/ slot+32 <= h) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_phase ctx func st en {site} [(h,32)] s
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    mem_word_at h r.vs_memory = n2w off /\
    mem_word_at slot r.vs_memory = n2w (off+n) /\
    FLOOKUP r.vs_allocas site = SOME (slot,32) /\
    eval_operand out (r with vs_inst_idx := LENGTH en.cs_current_insts) = SOME (n2w n) /\
    (!x. ~not_fresh_at en x ==> lookup_var x
      (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >> drule_all abi_encode_child_suffix_concrete >> strip_tac >>
  `window_phase ctx func a en {site} [] t1 t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `b`, `{site}`, `[]`, `t2`] >> simp[]) >>
  `window_phase ctx func st en {site} [(h,32)] s t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[(h,32)]`, `a`, `{site}`, `[]`, `t1`] >> simp[]) >>
  `mem_word_at h t2.vs_memory = n2w off` by
    (`mem_word_at h t2.vs_memory = mem_word_at h t1.vs_memory` by
       metis_tac[abi_encode_pure_word] >>
     asm_rewrite_tac[] >> simp[mstore_mem_word_at_same]) >>
  `mem_word_at h t3.vs_memory = n2w off /\
   mem_word_at slot t3.vs_memory = n2w (off+n)` by
    (qpat_x_assum `t3 = (r with vs_inst_idx := _)` kall_tac >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
     metis_tac[mstore_mem_word_at_disjoint, mstore_mem_word_at_same]) >>
  `FLOOKUP t3.vs_allocas site = SOME (slot,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `t3.vs_memory = r.vs_memory /\ t3.vs_allocas = r.vs_allocas` by
    (qpat_x_assum `t3 = (r with vs_inst_idx := _)` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `r` >> metis_tac[]
QED

Theorem abi_encode_dynamic_child_concrete:
  abi_encode_concrete_contract ei /\
  compile_abi_encode_child dst src ei T ho (Var cursor) st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) src
    ei at av sb cap (d+off) s /\ st.cs_blocks = en.cs_blocks /\
  eval_operand dst s = SOME (n2w d) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\ not_fresh_at st cursor /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\
  slot < dimword (:256) /\ d+ho < dimword (:256) /\
  mem_word_at slot s.vs_memory = n2w off /\
  (d+ho+32 <= slot \/ slot+32 <= d+ho) /\
  venomMemDefs$regions_disjoint (d+off,LENGTH (enc at av)) (d+ho,32) /\
  venomMemDefs$regions_disjoint (d+off,LENGTH (enc at av)) (slot,32) ==>
  ?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_phase ctx func st en
      (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+ho,32);(d+off,LENGTH (enc at av))] s
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    mem_bytes_at (d+off) (LENGTH (enc at av)) r.vs_memory = enc at av /\
    mem_word_at (d+ho) r.vs_memory = n2w off /\
    mem_word_at slot r.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP r.vs_allocas site = SOME (slot,32) /\
    eval_operand out (r with vs_inst_idx := LENGTH en.cs_current_insts) =
      SOME (n2w (LENGTH (enc at av))) /\
    (!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
      FLOOKUP r.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    (!x. ~not_fresh_at en x ==> lookup_var x
      (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. dst = Var x \/ Var cursor = Var x ==> not_fresh_at st x` by
    (simp[] >> metis_tac[]) >>
  drule_all abi_encode_dynamic_child_call_concrete >> strip_tac >>
  qabbrev_tac `actual = cr with vs_inst_idx := LENGTH child_end.cs_current_insts` >>
  `window_strong_result ctx func ready child_end len at av (d+off)
    (pr with vs_inst_idx := LENGTH ready.cs_current_insts) actual` by
    fs[abi_encode_concrete_result_def, Abbr `actual`] >>
  `eval_operand (Var cursor) actual = SOME (n2w slot)` by
    metis_tac[window_phase_eval_var] >>
  `not_fresh_at child_end cursor` by metis_tac[not_fresh_at_mono, LESS_EQ_TRANS] >>
  `abi_encoder_registered_effect
    (window_alloca_sites func (frag_ids ready child_end))
    [(d+off,LENGTH (enc at av))] s actual` by metis_tac[window_phase_effect] >>
  `FLOOKUP actual.vs_allocas site = SOME (slot,32)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `alloca_inv actual /\ alloca_room ctx func actual /\ ~actual.vs_halted /\
    actual.vs_current_bb = child_end.cs_current_bb /\
    actual.vs_inst_idx = LENGTH child_end.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand len actual = SOME (n2w (LENGTH (enc at av)))` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  `!x. Var cursor = Var x \/ len = Var x ==> not_fresh_at child_end x` by
    (simp[] >> metis_tac[]) >>
  `?sr. inst_extends child_end en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts child_end en) /\
    run_inst_seq (emitted_insts child_end en) actual = OK sr /\
    window_phase ctx func child_end en {site} [(d+ho,32)] actual
      (sr with vs_inst_idx := LENGTH en.cs_current_insts) /\
    mem_word_at (d+ho) sr.vs_memory = n2w off /\
    mem_word_at slot sr.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP sr.vs_allocas site = SOME (slot,32) /\
    eval_operand out (sr with vs_inst_idx := LENGTH en.cs_current_insts) =
      SOME (n2w (LENGTH (enc at av))) /\
    (!x. ~not_fresh_at en x ==> lookup_var x
      (sr with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x actual)` by
    (irule abi_encode_child_suffix_run_concrete >> asm_rewrite_tac[] >>
     qexistsl_tac [`Var cursor`, `FST ops`, `len`, `FST (SND ops)`] >> simp[] >> metis_tac[]) >>
  qabbrev_tac `t = sr with vs_inst_idx := LENGTH en.cs_current_insts` >>
  suspend "aggregate"
QED

Resume abi_encode_dynamic_child_concrete[aggregate]:
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s` by
    metis_tac[abi_window_high_vars_trans] >>
  `window_alloca_sites func (frag_ids ready child_end) SUBSET
    window_alloca_sites func (frag_ids st en)` by
    (irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, frag_ids_def] >> decide_tac) >>
  `window_phase ctx func st en
    (window_alloca_sites func (frag_ids st en) UNION {site})
    [(d+ho,32);(d+off,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`window_alloca_sites func (frag_ids ready child_end)`,
       `[(d+off,LENGTH (enc at av))]`, `child_end`, `{site}`, `[(d+ho,32)]`, `actual`] >>
     simp[] >> metis_tac[LESS_EQ_TRANS, SUBSET_UNION, SUBSET_TRANS]) >>
  `mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory =
    mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory` by
    (irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{site}`, `[(d+ho,32)]`] >> simp[Abbr `t`] >>
     metis_tac[window_phase_effect, optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
    FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (simp_tac bool_ss [IN_UNION, IN_SING] >> rpt gen_tac >>
     Cases_on `i = site` >- (gvs[Abbr `t`] >> metis_tac[]) >> strip_tac >>
     `i IN window_alloca_sites func (frag_ids st en)` by metis_tac[] >>
     `FLOOKUP actual.vs_allocas i = SOME (b,sz)` by
       (qpat_assum `window_phase _ _ child_end en _ _ actual t`
          (mp_tac o MATCH_MP window_phase_effect) >>
        simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >>
        metis_tac[]) >>
     Cases_on `i IN window_alloca_sites func (frag_ids ready child_end)`
     >- metis_tac[window_strong_result_sizes] >>
     `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
       (qpat_assum `abi_encoder_registered_effect _ _ s actual` mp_tac >>
        simp_tac bool_ss [abi_encoder_registered_effect_def] >> metis_tac[]) >>
     metis_tac[window_pre_sites]) >>
  `inst_extends ready child_end /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ready child_end) /\
    run_inst_seq (emitted_insts ready child_end)
      (pr with vs_inst_idx := LENGTH ready.cs_current_insts) = OK cr` by
    (qpat_x_assum `abi_encode_concrete_result _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encode_concrete_result_def] >> metis_tac[]) >>
  `?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    t = (r with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (simp_tac bool_ss [Abbr `t`] >> irule abi_encode_three_runs >>
     qexistsl_tac [`ready`, `child_end`, `pr`, `cr`] >> simp[Abbr `actual`]) >>
  `sr.vs_memory = t.vs_memory /\ sr.vs_allocas = t.vs_allocas` by
    simp[Abbr `t`] >>
  `t.vs_memory = r.vs_memory /\ t.vs_allocas = r.vs_allocas` by
    (qpat_x_assum `t = (r with vs_inst_idx := _)` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `r` >> metis_tac[]
QED

Finalise abi_encode_dynamic_child_concrete
