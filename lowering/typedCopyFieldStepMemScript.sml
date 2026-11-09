Theory typedCopyFieldStepMem
Ancestors
  typedCopyFieldsPathMem typedNormalizeFields typedNormalizeFrame abiDecoderFrame
  typedBytesArrayMem externalReturnNormalizeMem context compileEnv emitHelper
  venomInst exprLoweringProps memContinuation venomState fragGasPathMem

Theorem normalize_field_offsets_path_mem:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sd fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sa.cs_next_var <= sd.cs_next_var /\
  (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
  ?u. gas_path_mem ctx fn s 0 (OK u) /\
      eval_operand dp u = SOME (d + n2w doff) /\
      eval_operand sp u = SOME (p + n2w soff) /\
      ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
      u.vs_inst_idx = LENGTH sd.cs_current_insts /\
      (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >> imp_res_tac normalize_byte_offset_straight >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all normalize_byte_offset_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `compile_with_byte_offset dst doff sa = _` kall_tac >>
  `eval_operand src t = SOME p` by
    (Cases_on `src` >> gvs[eval_operand_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `!x. src = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all normalize_byte_offset_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx fn t 0 (OK u)` >>
  `eval_operand dp u = SOME (d + n2w doff)` by
    (Cases_on `dp` >> gvs[eval_operand_def, venom_state_component_equality] >>
     metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  conj_tac >- decide_tac >>
  conj_tac >- (rpt strip_tac >> gvs[not_fresh_at_def] >>
    metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexists_tac `u` >> simp[] >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  gvs[venom_state_component_equality]
QED

Theorem normalize_field_child_path_mem:
  compile_with_byte_offset dst doff sa = (dp,sc) /\
  compile_with_byte_offset src soff sc = (sp,sd) /\
  compile_store_memory_typed ce dp dt sp st sd = ((),se) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) /\
  (emitted_blocks sa se <> [] ==>
    ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa se fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  Src s.vs_memory /\
  (!u. eval_operand dp u = SOME (d + n2w doff) /\
    eval_operand sp u = SOME (p + n2w soff) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    u.vs_alloca_next = s.vs_alloca_next /\ Src u.vs_memory ==>
    ?v. gas_path_mem ctx fn u 0 (OK v) /\ D v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame fp u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) ==>
  ?v. gas_path_mem ctx fn s 0 (OK v) /\ D v.vs_memory /\
    ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
    v.vs_inst_idx = LENGTH se.cs_current_insts /\
    abi_decode_footprint_frame fp s v /\
    (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s) /\
    sa.cs_next_var <= se.cs_next_var /\
    (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >>
  `cs_extends sd se` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  imp_res_tac normalize_byte_offset_straight >>
  `cs_extends sa sd` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sd fn /\ fn_has_code sd se fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all normalize_field_offsets_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    gvs[venom_state_component_equality] >>
  `emitted_blocks sd se = emitted_blocks sa se` by
    gvs[fragExecTheory.emitted_blocks_def] >>
  `Src u.vs_memory` by metis_tac[] >>
  qpat_x_assum `!u. _ ==> ?v. _` (qspec_then `u` mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexists_tac `v` >> simp[] >>
  conj_tac >- (drule_all gas_path_mem_then >> simp[]) >>
  conj_tac >- gvs[abi_decode_footprint_frame_def, venom_state_component_equality] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sd x` by
      (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  gvs[venom_state_component_equality]
QED
