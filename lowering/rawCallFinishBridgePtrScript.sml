(* CALL postconditions at the result-suffix boundary.  No cleanliness is
   asserted for unused output capacity or copied tuple padding. *)
Theory rawCallFinishBridgePtr
Ancestors
  rawCallOracleProofPtr rawCallResultProofPtr rawCallResultLayoutPtr
  rawCallSourceActionPtr decoderGhostFramePtr rawCallMemoryFramePtr
  valueEncodingProps venomState finite_map pred_set

Theorem oracle_call_old_buffer:
  inst.inst_outputs = [out] /\ src <> out /\
  t.vs_vars = s.vs_vars |+ (out,result) /\
  t.vs_allocas = s.vs_allocas /\
  ptr_covers G tn src s capacity ==>
  lookup_var src (t with vs_inst_idx := pc) = lookup_var src s /\
  ptr_covers (step_prov PG G inst t) (step_taint inst s t tn)
    src (t with vs_inst_idx := pc) capacity /\
  FLOOKUP (t with vs_inst_idx := pc).vs_allocas aid = FLOOKUP s.vs_allocas aid
Proof
  strip_tac >>
  `lookup_var src t = lookup_var src s` by
    simp[lookup_var_def, FLOOKUP_UPDATE] >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >>
  irule ptr_covers_step_frame >> simp[]
QED

Theorem oracle_call_return_bytes:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  source_memory_write_ranges inst s = [(dst,cap)] /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_memory = (write_memory_with_expansion dst (TAKE cap t.vs_returndata) s).vs_memory ==>
  mem_bytes_at dst (LENGTH (TAKE cap t.vs_returndata))
    (t with vs_inst_idx := pc).vs_memory = TAKE cap t.vs_returndata /\
  (!i. dst <= i /\ i < dst + LENGTH (TAKE cap t.vs_returndata) ==>
    i NOTIN (step_taint inst s t tn).t_mem)
Proof
  rpt gen_tac >> disch_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  conj_tac >- simp[write_memory_mem_bytes_at_same] >>
  drule_all oracle_call_write_taint >> simp[]
QED

Theorem oracle_call_result_lookup:
  t.vs_vars = s.vs_vars |+ (out,result) ==>
  eval_operand (Var out) (t with vs_inst_idx := pc) = SOME result
Proof
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem oracle_call_suffix_ready:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  inst.inst_outputs = [out] /\ src <> out /\
  source_memory_write_ranges inst s = [(w2n a + 32,cap)] /\
  t.vs_vars = s.vs_vars |+ (out,result) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_memory = (write_memory_with_expansion (w2n a + 32)
    (TAKE cap t.vs_returndata) s).vs_memory /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
  FLOOKUP s.vs_allocas aid = SOME (off,len) /\
  H = step_prov PG G inst t /\ un = step_taint inst s t tn ==>
  lookup_var src (t with vs_inst_idx := pc) = SOME a /\
  ptr_covers H un src (t with vs_inst_idx := pc) capacity /\
  FLOOKUP (t with vs_inst_idx := pc).vs_allocas aid = SOME (off,len) /\
  mem_bytes_at (w2n a + 32) (LENGTH (TAKE cap t.vs_returndata))
    (t with vs_inst_idx := pc).vs_memory = TAKE cap t.vs_returndata /\
  (!i. w2n a + 32 <= i /\ i < w2n a + 32 + LENGTH (TAKE cap t.vs_returndata) ==>
    i NOTIN un.t_mem) /\
  eval_operand (Var out) (t with vs_inst_idx := pc) = SOME result
Proof
  rpt gen_tac >> disch_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all oracle_call_old_buffer >>
  disch_then (qspecl_then [`pc`, `aid`, `PG`] strip_assume_tac) >>
  drule_all oracle_call_return_bytes >>
  disch_then (qspecl_then [`tn`, `pc`] strip_assume_tac) >>
  fs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    write_memory_mem_bytes_at_same]
QED

Theorem ghost_kept_scopes_cong:
  ee.scopes = es.scopes ==>
  (ghost_kept cenv ee protected G tn s H un <=>
   ghost_kept cenv es protected G tn s H un)
Proof
  simp[bodyPtrDefsTheory.ghost_kept_def]
QED

Theorem wb_frame_scopes_cong:
  ee.scopes = es.scopes ==>
  (wb_frame cenv ee protected s t <=> wb_frame cenv es protected s t)
Proof
  simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def]
QED

Theorem oracle_suffix_frames_compose:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv protected /\
  ee.scopes = es.scopes /\ ci_mono protected sa /\
  ghost_kept cenv es protected G tn s H un /\
  wb_frame cenv es protected s t /\
  ghost_kept cenv ee sa H un t J vn /\ wb_frame cenv ee sa t u ==>
  ghost_kept cenv es protected G tn s J vn /\ wb_frame cenv es protected s u
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  `protected.cs_next_var <= sa.cs_next_var /\
   protected.cs_next_id <= sa.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  conj_tac
  >- (irule wordOperandsPtrTheory.ghost_kept_trans >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule exprSimWordArgsTheory.wb_frame_trans >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem oracle_taken_suffix_frames:
  take_call_outcome target data value_opt es = (INL (rq,outcome),es1) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv protected /\
  ci_mono protected sa /\ ghost_kept cenv es protected G tn s H un /\
  wb_frame cenv es protected s t /\
  ghost_kept cenv (SND (adopt_call_outcome rq outcome es1)) sa H un t J vn /\
  wb_frame cenv (SND (adopt_call_outcome rq outcome es1)) sa t u ==>
  ghost_kept cenv es protected G tn s J vn /\ wb_frame cenv es protected s u
Proof
  strip_tac >> drule_all oracle_take_adoption_locals >> strip_tac >>
  irule oracle_suffix_frames_compose >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
