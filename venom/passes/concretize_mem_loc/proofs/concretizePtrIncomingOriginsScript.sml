Theory concretizePtrIncomingOrigins
Ancestors contextCodegenRel ptrDiscipline frameOriginUpdates frameOriginReachable concretizePtrParamSupport concretizePtrRootCover
  pointerClosure pointerConfinedDefs venomInst finite_map pred_set list words
  execEquivParamBase removeUnusedSsaProofs concretizeAnalysisRoots concretizePtrFrameOrigins

Definition origin_tag_supported_def:
  origin_tag_supported tag X om <=>
    !v site. FLOOKUP om v = SOME (tag,site) ==> v IN X
End

Theorem origin_tag_empty[simp]:
  origin_tag_supported tag X FEMPTY
Proof simp[origin_tag_supported_def]
QED

Theorem origin_tag_restrict:
  origin_tag_supported tag X om ==>
  origin_tag_supported tag X (DRESTRICT om keys)
Proof simp[origin_tag_supported_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem origin_tag_set[local]:
  origin_tag_supported tag X om /\
  (!site. p = SOME (tag,site) ==> !out. MEM out outs ==> out IN X) ==>
  origin_tag_supported tag X (origin_set om outs p)
Proof
  Cases_on `outs` >> Cases_on `p` >>
  simp[origin_set_def, origin_tag_supported_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `t` >> gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem origin_tag_first[local]:
  !ops. origin_first om ops = SOME (tag,site) ==>
    ?v. MEM (Var v) ops /\ FLOOKUP om v = SOME (tag,site)
Proof
  Induct >> simp[origin_first_def] >>
  Cases_on `h` >> simp[origin_op_def] >>
  Cases_on `FLOOKUP om s` >> simp[] >> metis_tac[]
QED

Theorem origin_tag_step:
  origin_tag_supported tag X om /\ MEM inst (fn_insts fn) /\
  (!i v out. MEM i (fn_insts fn) /\
    is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
    v IN X /\ MEM out i.inst_outputs ==> out IN X) /\
  (!site. (inst.inst_opcode = ALLOCA \/ inst.inst_opcode = DALLOCA \/
    inst.inst_opcode = PARAM) /\ origin_out PG om inst s' = SOME (tag,site) ==>
    !out. MEM out inst.inst_outputs ==> out IN X) ==>
  origin_tag_supported tag X (origin_step PG om inst s')
Proof
  strip_tac >> simp[origin_step_def] >> irule origin_tag_set >> simp[] >>
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA \/ inst.inst_opcode = DALLOCA \/
            inst.inst_opcode = PARAM`
  >- metis_tac[] >>
  `origin_first om inst.inst_operands = SOME (tag,site) /\
   is_pointer_preserving_op inst.inst_opcode` by
    (gvs[origin_out_def, AllCaseEqs()] >> simp[is_pointer_preserving_op_def]) >>
  drule origin_tag_first >> strip_tac >>
  gvs[origin_tag_supported_def] >> metis_tac[]
QED

Theorem origin_tag_phi[local]:
  origin_tag_supported tag X om /\ origin_phi prev om inst = SOME (tag,site) ==>
  ?v. MEM (Var v) inst.inst_operands /\ v IN X
Proof
  simp[origin_phi_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `op` >> gvs[origin_op_def, origin_tag_supported_def] >>
  metis_tac[resolve_phi_MEM]
QED

Theorem origin_tag_phis:
  origin_tag_supported tag X om /\
  (!i v out. MEM i (fn_insts fn) /\
    is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
    v IN X /\ MEM out i.inst_outputs ==> out IN X) /\
  EVERY (\i. MEM i (fn_insts fn)) insts ==>
  origin_tag_supported tag X (origin_phis prev om insts)
Proof
  Induct_on `insts` >> simp[origin_phis_def] >> strip_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >> irule origin_tag_set >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> drule_all origin_tag_phi >> strip_tac >>
  metis_tac[is_pointer_preserving_op_def]
QED

Theorem origin_tag_entry:
  origin_tag_supported tag X om /\
  (!i v out. MEM i (fn_insts fn) /\
    is_pointer_preserving_op i.inst_opcode /\ MEM (Var v) i.inst_operands /\
    v IN X /\ MEM out i.inst_outputs ==> out IN X) ==>
  origin_tag_supported tag X (origin_entry fn s om)
Proof
  strip_tac >> simp[origin_entry_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule origin_tag_phis >> simp[] >> qexists `fn` >> simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM x fn.fn_blocks` by
    (gvs[lookup_block_def] >> metis_tac[FIND_MEM]) >>
  simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem origin_parameter_step:
  origin_tag_supported (OriginParameter k)
    (pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)) om /\
  ptr_params_ok P fn PG /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
  MEM inst (fn_insts fn) ==>
  origin_tag_supported (OriginParameter k)
    (pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn))
    (origin_step PG om inst s')
Proof
  strip_tac >> irule origin_tag_step >> simp[] >>
  reverse conj_tac
  >- (qexists `fn` >> simp[] >>
      metis_tac[pointer_derived_vars_closed, FINITE_DIFF, ptr_roots_finite]) >>
  rpt strip_tac >>
  `inst.inst_opcode = PARAM /\ ?idx. inst.inst_operands = [Lit idx] /\
    w2n idx < LENGTH PG /\ EL (w2n idx) PG = SOME site` by
    (gvs[origin_out_def, AllCaseEqs()] >> metis_tac[]) >>
  irule (pointer_derived_vars_roots |> REWRITE_RULE [SUBSET_DEF]) >>
  simp[FINITE_DIFF, ptr_roots_finite] >>
  `out IN ptr_frame_site_roots fn FEMPTY PG site` by
    (simp[ptr_frame_site_roots_def] >> metis_tac[]) >>
  drule_all ptr_param_root_cover >> simp[]
QED

Theorem origin_dynamic_step:
  origin_tag_supported OriginDynamic {} om /\ inst.inst_opcode <> DALLOCA /\
  MEM inst (fn_insts fn) ==>
  origin_tag_supported OriginDynamic {} (origin_step PG om inst s')
Proof
  strip_tac >> irule origin_tag_step >> simp[] >>
  reverse conj_tac >- (qexists `fn` >> simp[]) >>
  rpt strip_tac >> gvs[origin_out_def, AllCaseEqs()]
QED

Definition origin_incoming_ok_def:
  origin_incoming_ok P fn om <=>
    (!k. origin_tag_supported (OriginParameter k)
      (pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)) om) /\
    origin_tag_supported OriginDynamic {} om
End

Theorem origin_incoming_empty[simp]:
  origin_incoming_ok P fn FEMPTY
Proof simp[origin_incoming_ok_def]
QED

Theorem origin_incoming_restrict:
  origin_incoming_ok P fn om ==>
  origin_incoming_ok P fn (DRESTRICT om keys)
Proof simp[origin_incoming_ok_def] >> metis_tac[origin_tag_restrict]
QED

Theorem origin_incoming_step:
  origin_incoming_ok P fn om /\ ptr_params_ok P fn PG /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> DALLOCA ==>
  origin_incoming_ok P fn (origin_step PG om inst s')
Proof
  simp[origin_incoming_ok_def] >> metis_tac[origin_parameter_step, origin_dynamic_step]
QED

Theorem origin_incoming_entry:
  origin_incoming_ok P fn om ==> origin_incoming_ok P fn (origin_entry fn s om)
Proof
  simp[origin_incoming_ok_def] >> rpt strip_tac >> irule origin_tag_entry >> simp[]
  >- metis_tac[pointer_derived_vars_closed, FINITE_DIFF, ptr_roots_finite] >>
  qexists `fn` >> simp[]
QED

Theorem origin_incoming_invariant:
  !vs0 ctx stk PG G tn fn inst s oms om.
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
  !P. EVERY (fn_ptr_ok P) ctx.ctx_functions /\
    EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
    EVERY ssa_form ctx.ctx_functions /\ ~ctx_has_dalloca ctx ==>
  origin_incoming_ok P fn om /\
  LIST_REL (\f m. origin_incoming_ok P f.cf_fn m) stk oms
Proof
  ho_match_mp_tac origin_frame_reachable_strongind >> rpt conj_tac
  >- simp[]
  >- suspend "next"
  >- suspend "block"
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      first_x_assum (qspec_then `P` mp_tac) >> simp[])
  >> suspend "ret"
QED

Resume origin_incoming_invariant[next]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  irule origin_incoming_step >> simp[] >>
  `frame_reachable vs0 ctx stk PG G tn fn inst s` by metis_tac[origin_frame_erasure] >>
  `MEM fn ctx.ctx_functions /\ ptr_params_ok P fn PG` by
    metis_tac[ptr_frame_current_static] >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[MEM_EL]) >>
  fs[EVERY_MEM, ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]
QED

Resume origin_incoming_invariant[block]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[origin_incoming_entry]
QED

Resume origin_incoming_invariant[ret]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[origin_incoming_restrict]
QED

Finalise origin_incoming_invariant

Theorem origin_frame_current_incoming:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
  FLOOKUP om v = SOME (OriginParameter k,site) ==>
  v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)
Proof
  strip_tac >> drule origin_incoming_invariant >>
  disch_then (qspec_then `P` mp_tac) >>
  simp[origin_incoming_ok_def, origin_tag_supported_def] >> metis_tac[]
QED

Theorem origin_frame_saved_incoming:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
  n < LENGTH stk /\ FLOOKUP (EL n oms) v = SOME (OriginParameter k,site) ==>
  v IN pointer_derived_vars (EL n stk).cf_fn
    (ptr_roots P (EL n stk).cf_fn DIFF alloca_roots (EL n stk).cf_fn)
Proof
  strip_tac >> drule origin_incoming_invariant >>
  disch_then (qspec_then `P` mp_tac) >>
  simp[LIST_REL_EL_EQN, origin_incoming_ok_def, origin_tag_supported_def] >> metis_tac[]
QED

Theorem origin_frame_current_not_dynamic:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ ~ctx_has_dalloca ctx ==>
  FLOOKUP om v <> SOME (OriginDynamic,site)
Proof
  strip_tac >> drule origin_incoming_invariant >>
  disch_then (qspec_then `P` mp_tac) >>
  simp[origin_incoming_ok_def, origin_tag_supported_def] >> metis_tac[]
QED

Theorem origin_frame_saved_not_dynamic:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\ n < LENGTH stk ==>
  FLOOKUP (EL n oms) v <> SOME (OriginDynamic,site)
Proof
  strip_tac >> drule origin_incoming_invariant >>
  disch_then (qspec_then `P` mp_tac) >>
  simp[LIST_REL_EL_EQN, origin_incoming_ok_def, origin_tag_supported_def] >> metis_tac[]
QED
