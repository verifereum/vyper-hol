(* Separated scratch allocation resources, independent of expression posts. *)
Theory reasonSlotResourcesPtr
Ancestors allocationPtr reasonEncoderTailPtr reasonPrefixPtr exprSimAlloc normalizationAllocPtr
  robustCopyTransportPtr compileEnv venomState venomExecSemantics venomInst
  finite_map ptrDiscipline exprLoweringProps emitHelperProps exprSimProps loweringHalt bodyPtrDefs ghostPcTransportPtr

Theorem reason_alloca_exterior_effects:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (b,n) ==>
  t.vs_memory = s.vs_memory /\
  (!i. ~(b <= i /\ i < b+n) ==>
    (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
     <=> i IN tn.t_mem))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] mp_tac) >> simp[update_var_def]
QED

Theorem reason_slot_alloc_run:
  compile_alloc_buffer 32 sa = (buf,c1) /\ buf.buf_operand = Var slot /\
  fn_has_code sa c1 func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  ?t a.
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ lookup_var slot t = SOME a /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,32) /\
    w2n a + 32 < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n a) 32 b len)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts sa c1 =
    [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> drule emitted_insts_emit_op >>
     gvs[]) >>
  gvs[run_inst_seq_def, eval_operand_def, AllCaseEqs()] >>
  rpt strip_tac >>
  qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
  qexists_tac `aid` >> simp[]
QED

Theorem reason_alloca_robust_preserved:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (b,n) /\
  regions_disjoint b n a capacity /\ val_wf tv v /\
  val_footprint tv v <= capacity /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v a m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
    t.vs_memory m ==> val_in_memory tv v a m
Proof
  strip_tac >> drule_all reason_alloca_exterior_effects >> strip_tac >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem`,
    `{i | b <= i /\ i < b+n}`] >>
  simp[] >> gvs[regions_disjoint_def] >> rpt strip_tac >> decide_tac
QED

Theorem reason_slot_initialize_resources_ptr:
  compile_alloc_buffer 32 sa = (buf,c1) /\ buf.buf_operand = Var slot /\
  emit_void MSTORE [Var slot;Lit 32w] c1 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  ?t a G1 tn1 tnf sf.
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) s = OK t /\
    G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) t /\
    tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) s t tn /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,32) /\
    w2n a + 32 < dimword (:256) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var slot sf = SOME a /\ ptr_covers G1 tnf slot sf 32 /\
    mload (w2n a) sf = 32w /\
    tnf.t_mem = tn1.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    sf.vs_memory = (mstore (w2n a) 32w t).vs_memory /\
    (!p. lookup_var p sf = lookup_var p t /\
      op_taint tnf (Var p) = op_taint tn1 (Var p)) /\
    (!p k. p <> slot /\ ptr_covers G tn p s k ==> ptr_covers G1 tnf p sf k) /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n a) 32 b len)
Proof
  strip_tac >> drule_all reason_slot_alloc_run >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) (fn_insts func)` by gvs[] >>
  qabbrev_tac `G1 = step_prov PG G
    (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) t` >>
  qabbrev_tac `tn1 = step_taint
    (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) s t tn` >>
  `ptr_covers G1 tn1 slot t 32` by
    (simp[Abbr `G1`, Abbr `tn1`] >> irule alloca_step_ptr_covers >>
     simp[wordsTheory.dimword_def] >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`] >> simp[]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_all reason_encoder_alloc_path_ptr >> simp[Abbr `G1`, Abbr `tn1`]) >>
  qabbrev_tac `s1 = t with vs_inst_idx := SUC s.vs_inst_idx` >>
  `s1.vs_current_bb = c1.cs_current_bb /\
   s1.vs_inst_idx = LENGTH c1.cs_current_insts /\ ~s1.vs_halted /\
   lookup_var slot s1 = SOME a /\ ptr_covers G1 tn1 slot s1 32` by
    suspend "cursor" >>
  `eval_operand (Lit 32w) s1 = SOME 32w /\ op_taint tn1 (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all reason_encoder_mstore_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `tnf`
    (qx_choose_then `sf` strip_assume_tac))) >>
  qexistsl_tac [`t`, `a`, `G1`, `tn1`, `tnf`, `sf`] >>
  simp[GSYM (Abbr `G1`), GSYM (Abbr `tn1`)] >>
  rpt conj_tac
  >- suspend "path"
  >- suspend "memory"
  >- suspend "vars"
  >- suspend "covers" >>
  rpt strip_tac >>
  qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _` irule >>
  qexists_tac `aid` >> simp[]
QED

Resume reason_slot_initialize_resources_ptr[cursor]:
  `t.vs_current_bb = s.vs_current_bb /\
   t.vs_inst_idx = s.vs_inst_idx /\ ~t.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = OK t` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >> gvs[AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def]) >>
  `c1.cs_current_bb = sa.cs_current_bb /\
   LENGTH c1.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
         fresh_var_def, emitHelperTheory.emit_inst_def,
         fresh_id_def, emit_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  gvs[Abbr `s1`, lookup_var_def, ptr_covers_def]
QED

Resume reason_slot_initialize_resources_ptr[path]:
  gvs[Abbr `s1`] >>
  metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Resume reason_slot_initialize_resources_ptr[memory]:
  PURE_ONCE_REWRITE_TAC[mstore_def] >> simp[Abbr `s1`]
QED

Resume reason_slot_initialize_resources_ptr[vars]:
  gvs[Abbr `s1`, lookup_var_def]
QED

Resume reason_slot_initialize_resources_ptr[covers]:
  rpt strip_tac >>
  qpat_x_assum `!p k. ptr_covers _ _ p s1 k ==> _` irule >>
  simp[Abbr `s1`] >>
  irule alloca_step_old_ptr_covers >> simp[wordsTheory.dimword_def] >>
  qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`] >> simp[]
QED

Finalise reason_slot_initialize_resources_ptr

Theorem reason_slot_tuple_resources_ptr:
  compile_alloc_buffer 32 sa = (buf,c1) /\ buf.buf_operand = Var slot /\
  emit_void MSTORE [Var slot;Lit 32w] c1 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,capacity) /\
  32 <= capacity /\ not_fresh_at sa tuple /\ tuple <> slot /\
  lookup_var tuple s = SOME (n2w b) /\ ptr_covers G tn tuple s capacity /\
  mload b s = n2w len /\
  (!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf a.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var slot sf = SOME a /\ ptr_covers Gf tnf slot sf 32 /\
    mload (w2n a) sf = 32w /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tnf.t_mem) /\
    lookup_var tuple sf = SOME (n2w b) /\ ptr_covers Gf tnf tuple sf capacity /\
    mload b sf = n2w len /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN tnf.t_mem) /\
    (!p k. p <> slot /\ ptr_covers G tn p s k ==> ptr_covers Gf tnf p sf k) /\
    (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s)
Proof
  strip_tac >> drule_all reason_slot_initialize_resources_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> drule compile_alloc_buffer_parts >> gvs[]) >>
  `regions_disjoint (w2n a) 32 b capacity` by metis_tac[] >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  `t.vs_memory = s.vs_memory /\
   (!i. ~(w2n a <= i /\ i < w2n a+32) ==>
     (i IN tn1.t_mem <=> i IN tn.t_mem))` by
    (qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
     irule reason_alloca_exterior_effects >> simp[wordsTheory.dimword_def] >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`] >> simp[]) >>
  `lookup_var tuple t = lookup_var tuple s` by suspend "lookup" >>
  qexistsl_tac [`G1`, `tnf`, `sf`, `a`] >> simp[] >>
  conj_tac >- suspend "length" >>
  conj_tac
  >- (rpt strip_tac >> gvs[regions_disjoint_def] >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  suspend "oldlookup"
QED

Resume reason_slot_tuple_resources_ptr[lookup]:
  drule_all reason_slot_alloc_run >> strip_tac >>
  gvs[]
QED

Resume reason_slot_tuple_resources_ptr[length]:
  `mload b sf = mload b (mstore (w2n a) 32w t)` by simp[mload_def] >>
  `mload b (mstore (w2n a) 32w t) = mload b t` by
    (irule venomMemProofsTheory.mload_mstore_disjoint_proof >>
     gvs[regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  gvs[mload_def]
QED

Resume reason_slot_tuple_resources_ptr[oldlookup]:
  drule_all reason_slot_alloc_run >> strip_tac >> gvs[]
QED

Finalise reason_slot_tuple_resources_ptr
