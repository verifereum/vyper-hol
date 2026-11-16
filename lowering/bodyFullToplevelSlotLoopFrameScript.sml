(* Runtime framing accompanies the very same joint TopLevelName loop run. *)
Theory bodyFullToplevelSlotLoopFrame
Ancestors
  bodyFullToplevelSlotLoop exprPtrUnwrapRuntimeFrame exprPtrUnwrapLoopInvariant
  slotCopyExecution venomState arithmetic fragGasOriginPtr

Theorem toplevel_slot_copy_joint_finish_framed:
  compile_expr cenv ty (TopLevelName ann nsid) ca = (place,cb) /\
  (load=SLOAD \/ load=TLOAD) /\ i <= n /\
  slot_copy_inv cs load original p d n regions i s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d /\
  op_taint tn src = {} /\ ~s.vs_halted /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  lookup_block (slot_copy_cond cs) fn.fn_blocks = SOME cond /\
  cond.bb_instructions = slot_copy_cond_insts cs n /\
  lookup_block (slot_copy_body cs) fn.fn_blocks = SOME bodybb /\
  bodybb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  w2n d+32*n <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  slot_copy_runtime_frame cs d i r s ==>
  ?t Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK t,Gf,tnf)) /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
    slot_copy_inv cs load original p d n regions n t /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_alloca_next = s.vs_alloca_next /\
    slot_copy_runtime_frame cs d n r t
Proof
  map_every qid_spec_tac [`tn`, `G`, `s`] >>
  measureInduct_on `n-i` >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  Cases_on `i=n`
  >- (gvs[] >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME cond` by simp[] >>
      drule_all toplevel_slot_copy_joint_exit >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      `slot_copy_runtime_frame cs d i r t` by
        metis_tac[slot_copy_runtime_frame_condition] >>
      qexistsl [`t`, `G1`, `tn1`] >>
      simp[slot_copy_cond_result_def, jump_to_def, update_var_def]) >>
  `i<n` by decide_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME cond` by simp[] >>
  drule_all toplevel_slot_copy_joint_step >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `slot_copy_inv cs load original p d n regions (i+1) mid` >>
  `~mid.vs_halted /\ mid.vs_current_bb = slot_copy_cond cs /\ mid.vs_inst_idx = 0` by
    simp[Abbr `mid`, slot_copy_body_result_def, slot_copy_cond_result_def,
         update_var_def, jump_to_def, mstore_def] >>
  `op_taint tnf src = {}` by metis_tac[copy_ghost_external_taint] >>
  `slot_copy_runtime_frame cs d (i+1) r mid` by
    (simp[Abbr `mid`] >> irule slot_copy_runtime_frame_body >>
     reverse conj_tac >- metis_tac[slot_copy_runtime_frame_condition] >>
     qexists `n` >> fs[slot_copy_inv_def]) >>
  first_x_assum (qspec_then `i+1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`mid`, `Gf`, `tnf`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  qexistsl [`t`, `Gf'`, `tnf'`] >> simp[] >>
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`, `explicit`] mp_tac) >> disch_tac >>
  drule gas_origin_ptr_path_append >>
  disch_then (qspecl_then [`mid`, `Gf`, `tnf`, `[]`] mp_tac) >>
  simp[] >> disch_then irule >> simp[]
QED
