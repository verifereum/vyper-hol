(* The three unmarked instructions at the memory Append guard.  The
   witnesses for the execution cuts do not depend on the gas horizon. *)
Theory bodyAppendMemoryGuardMods
Ancestors
  appendStorageStageTransportPtr bodyPtrBopScalarStep decoderNavigationPtr
  decoderGuardClampCorePtr entryChecksRejectJoint typedCopyOriginPtrBase
  fragGasOriginPtrLoop exprLoweringProps emitHelperProps instMemFrontier
  ptrSafetyTransport ptrDiscipline venomState venomExecSemantics venomInst
  typedMemoryCopy loweringStateRelDefs memSafeRun compileEnv freshWrites fragExec
  finite_map words

Theorem append_load_ready[local]:
  emit_op MLOAD [Var p] a = (lop,b) /\ fn_has_code a b func /\
  lookup_var p s = SOME bp /\ ptr_covers G tn p s 32 /\
  (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
  w2n bp+32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?x t Gf tf.
    lop = Var x /\ not_fresh_at b x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    lookup_var x t = SOME (mload (w2n bp) s) /\
    op_taint tf lop = {} /\ op_prov Gf lop = NONE /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!y. not_fresh_at a y ==> lookup_var y t = lookup_var y s /\
      FLOOKUP Gf y = FLOOKUP G y /\ op_taint tf (Var y) = op_taint tn (Var y))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  qabbrev_tac `u = update_var x (mload (w2n bp) s) s` >>
  `run_inst_seq (emitted_insts a b) s = OK u` by
    simp[Abbr `u`, run_inst_seq_def, eval_operand_def,
      step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def] >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core_exact_frame >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choosel_then [`Gf`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`x`,`u with vs_inst_idx := LENGTH b.cs_current_insts`,`Gf`,`tf`] >>
  `a.cs_current_bb = b.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `not_fresh_at b x` by metis_tac[typed_copy_emit_op_fresh] >>
  `!y. not_fresh_at a y ==> y <> x` by
    (simp[Abbr `x`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[typed_copy_state_frame_def, Abbr `u`, allocas_from_def,
    allocas_below_fmp_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem append_test_ready[local]:
  emit_op LT [lop; Lit (n2w cap)] a = (valid,b) /\ fn_has_code a b func /\
  eval_operand lop s = SOME len /\ cap < dimword (:256) /\
  op_taint tn lop = {} /\ op_prov G lop = NONE /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?x t Gf tf.
    valid = Var x /\ not_fresh_at b x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand valid t = SOME (bool_to_word (w2n len < cap)) /\
    op_taint tf valid = {} /\ op_prov Gf valid = NONE /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!y. not_fresh_at a y ==> lookup_var y t = lookup_var y s /\
      FLOOKUP Gf y = FLOOKUP G y /\ op_taint tf (Var y) = op_taint tn (Var y))
Proof
  strip_tac >>
  qabbrev_tac `w = bool_to_word (w2n len < cap)` >>
  `!out. step_inst_base (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s =
    OK (update_var out w s)` by
    simp[Abbr `w`, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      eval_operand_def] >>
  `!D out. ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s` by
    (rpt gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `0` >> simp[] >>
     irule bop_scalar_ptr_inst_ok >> simp[op_prov_def, op_taint_def]) >>
  `!out. inst_mem_below_frontier (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s /\
    inst_dload_in_section (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s` by
    (simp[inst_dload_in_section_def, mk_inst_def] >>
     simp[GSYM mk_inst_def, below_frontier_no_ranges, mk_inst_def]) >>
  qabbrev_tac `x = STRING #"%" (toString a.cs_next_var)` >>
  `valid = Var x /\ not_fresh_at b x` by
    (drule emitted_insts_emit_op >> simp[Abbr `x`] >> metis_tac[typed_copy_emit_op_fresh]) >>
  qabbrev_tac `u = update_var x w s` >>
  qabbrev_tac `ins = mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [x]` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gf = step_prov PG G ins u` >>
  qabbrev_tac `tf = step_taint ins s u tn` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
    eval_operand valid t = SOME w /\ typed_copy_state_frame a 0 0 s t /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts` by
    (gen_tac >>
     `!out. ptr_inst_ok D lo 0 ctx func G tn
       (mk_inst a.cs_next_id LT [lop; Lit (n2w cap)] [out]) s` by simp[] >>
     `LT <> INVOKE /\ LT <> GAS /\ LT <> DALLOCA /\ ~is_terminator LT` by
       simp[is_terminator_def] >>
     drule_all (Q.INST [`off` |-> `0`, `len` |-> `0`] typed_copy_origin_ptr_emit_op_path) >>
     disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
     gvs[Abbr `t`, Abbr `Gf`, Abbr `tf`, Abbr `ins`, Abbr `u`]) >>
  `!y. not_fresh_at a y ==> y <> x` by
    (simp[Abbr `x`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qexistsl_tac [`x`,`t`,`Gf`,`tf`] >> simp[] >>
  mp_tac (Q.INST [`opc` |-> `LT`, `ops` |-> `[lop; Lit (n2w cap)]`,
      `tn` |-> `tn`, `G` |-> `G`, `PG` |-> `PG`, `u` |-> `u`, `s` |-> `s`,
      `tmp` |-> `x`, `id` |-> `a.cs_next_id`] bop_scalar_ghost_frame) >>
  simp[Abbr `Gf`, Abbr `tf`, Abbr `ins`, Abbr `t`, Abbr `u`, op_prov_def,
    op_taint_def, allocas_from_def, allocas_below_fmp_def, update_var_def,
    lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem append_frame_inst_idx[local]:
  typed_copy_state_frame a off len s t ==>
  typed_copy_state_frame a off len s (t with vs_inst_idx := i)
Proof
  rw[typed_copy_state_frame_def, lookup_var_def] >>
  fs[venom_state_component_equality]
QED

Theorem append_memory_guard_path_mods:
  emit_op MLOAD [Var p] a = (lop,b) /\
  emit_op LT [lop; Lit (n2w cap)] b = (valid,c) /\
  emit_void ASSERT [valid] c = ((),d) /\ fn_has_code a d func /\
  lookup_var p s = SOME bp /\ ptr_covers G tn p s 32 /\
  (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
  w2n bp+32 <= s.vs_alloca_next /\ mload (w2n bp) s = n2w len /\
  len <= cap /\ cap < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  if len < cap then
    ?x t Gf tf.
      lop = Var x /\ not_fresh_at d x /\ lookup_var x t = SOME (n2w len) /\
      op_taint tf lop = {} /\ op_prov Gf lop = NONE /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      typed_copy_state_frame a 0 0 s t /\ t.vs_memory = s.vs_memory /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
      t.vs_inst_idx = LENGTH d.cs_current_insts /\
      (!x. not_fresh_at a x ==> not_fresh_at d x /\ lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
  else
    ?r Gf tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort r,Gf,tf))
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by fs[ci_mono_def] >>
  `fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c d func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!x. (not_fresh_at a x ==> not_fresh_at b x) /\
       (not_fresh_at b x ==> not_fresh_at c x) /\
       (not_fresh_at c x ==> not_fresh_at d x)` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  drule_all append_load_ready >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `lop = Var x` >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t1,G1,tn1)` >>
  `eval_operand lop t1 = SOME (n2w len)` by simp[eval_operand_def] >>
  drule_all append_test_ready >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t1,G1,tn1) [] (OK t2,G2,tn2)` >>
  `len < dimword (:256)` by decide_tac >>
  `eval_operand valid t2 = SOME (bool_to_word (len < cap))` by simp[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t2,G2,tn2)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  `d.cs_current_bb = c.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  Cases_on `len < cap` >> simp[]
  >- suspend "success" >> suspend "capacity"
QED

Resume append_memory_guard_path_mods[success]:
  qpat_x_assum `lop = Var x` SUBST_ALL_TAC >>
  `run_inst_seq (emitted_insts c d) t2 = OK t2` by
    (irule emit_append_assert_actual >> qexists_tac `valid` >> simp[]) >>
  qabbrev_tac `u = t2 with vs_inst_idx := LENGTH d.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t2,G2,tn2) [] (OK u,G2,tn2)` by
    (drule_all emit_assert_endpoint_ptr_origin_core >>
     disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
     simp[Abbr `u`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  `typed_copy_state_frame a 0 0 s t2` by
    metis_tac[typed_copy_state_frame_mono, typed_copy_state_frame_trans] >>
  `typed_copy_state_frame a 0 0 s u` by
    (simp[Abbr `u`] >> irule append_frame_inst_idx >> simp[]) >>
  qexistsl_tac [`u`,`G2`,`tn2`] >>
  simp[Abbr `u`, lookup_var_def, op_prov_def, allocas_from_def, allocas_below_fmp_def] >>
  fs[lookup_var_def, op_prov_def, allocas_from_def, allocas_below_fmp_def] >>
  metis_tac[]
QED

Resume append_memory_guard_path_mods[capacity]:
  drule emitted_insts_emit_void >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb t2.vs_inst_idx = SOME (mk_inst c.cs_next_id ASSERT [valid] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block t2.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `eval_operand valid t2 = SOME 0w` by fs[bool_to_word_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t2,G2,tn2) []
    (Abort Revert_abort (revert_state (set_returndata [] t2)),G2,tn2)` by
    (drule_all assert_revert_origin_ptr >> disch_then (qspec_then `PG` mp_tac) >> simp[]) >>
  qexistsl_tac [`revert_state (set_returndata [] t2)`,`G2`,`tn2`] >>
  metis_tac[gas_origin_ptr_path_trans]
QED

Finalise append_memory_guard_path_mods
