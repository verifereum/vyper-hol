Theory dftGasInvSSAProbe
Ancestors
  dftGasOracleDefs dftGasInvOracleFrame dftGasInvCrossingProbe dftRunRel dftAvailability
  dftScheduleOrder dftWf dftIdempotent dftTopoSort venomWf
  venomWfProps venomExecSemantics venomInst venomState
  list finite_map pred_set option dftSsaPreserve

Theorem inv_remaining_head_vars:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  dft_remaining_inv fn bb (x::rest) s ==>
  !v. MEM (Var v) x.inst_operands ==> v IN FDOM s.vs_vars
Proof
  strip_tac >>
  `MEM x bb.bb_instructions /\ ~is_pseudo x.inst_opcode /\
   (!d. MEM d rest ==>
     id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id d.inst_id)` by
    (irule dft_remaining_inv_head_order >> qexistsl_tac [`fn`, `[]`, `s`] >> simp[]) >>
  rpt strip_tac >> irule dft_bubble_head_ready >>
  qexistsl_tac [`bb`, `fn`, `rest`, `[]`, `x`] >>
  fs[dft_remaining_inv_def] >> metis_tac[]
QED

Theorem inv_remaining_head_operands:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  dft_remaining_inv fn bb (x::rest) s /\
  ~is_terminator x.inst_opcode /\ x.inst_opcode <> INVOKE /\
  x.inst_opcode <> CODECOPY ==>
  !op. MEM op x.inst_operands ==> IS_SOME (eval_operand op s)
Proof
  strip_tac >>
  `!v. MEM (Var v) x.inst_operands ==> v IN FDOM s.vs_vars` by
    metis_tac[inv_remaining_head_vars] >>
  Cases >> simp[eval_operand_def] >> strip_tac
  >- (simp[lookup_var_def, FLOOKUP_DEF] >> metis_tac[])
  >> fs[dft_remaining_inv_def] >> metis_tac[FLOOKUP_DEF, IS_SOME_EXISTS]
QED

Theorem inv_fold_outputs_frame[local]:
  !s. (FOLDL (\s (x,v). update_var x v s) s xs).vs_current_bb = s.vs_current_bb /\
      (FOLDL (\s (x,v). update_var x v s) s xs).vs_labels = s.vs_labels
Proof
  Induct_on `xs` >> simp[] >> rpt gen_tac >>
  rename1 `((\(x,v). update_var x v s) pair).vs_current_bb = _` >>
  PairCases_on `pair` >> simp[]
QED

Theorem inv_bind_outputs_frame:
  bind_outputs outs vals s = SOME t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_labels = s.vs_labels
Proof
  simp[bind_outputs_def] >> strip_tac >>
  gvs[AllCaseEqs(), inv_fold_outputs_frame]
QED

Theorem inv_ev_step_availability:
  ev_step orc p d fuel ctx x s = OK t /\ inst_wf x /\
  x.inst_opcode <> PHI /\ ~is_terminator x.inst_opcode ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_labels = s.vs_labels /\
  FDOM t.vs_vars = FDOM s.vs_vars UNION set x.inst_outputs
Proof
  strip_tac >> Cases_on `x.inst_opcode = GAS`
  >- (gvs[Once ev_step_def, ev_gas_def, AllCaseEqs()] >>
      simp[update_var_def, FDOM_FUPDATE] >> pred_setLib.SET_TAC[]) >>
  Cases_on `x.inst_opcode = INVOKE`
  >- (gvs[Once ev_step_def, AllCaseEqs()] >>
      rename1 `bind_outputs _ ret.iret_values _ = SOME _` >>
      drule inv_bind_outputs_frame >> drule venomExecProofsTheory.bind_outputs_fdom >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  `step_inst fuel ctx x s = OK t` by
    gvs[Once ev_step_def, Once step_inst_def] >>
  drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
  drule venomExecProofsTheory.step_inst_preserves_labels_always >> strip_tac >>
  drule_all venomExecProofsTheory.step_inst_fdom >> simp[]
QED

Theorem inv_remaining_ev_step:
  wf_function fn /\ EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ x::post) s /\
  ~is_terminator x.inst_opcode /\ ev_step orc p d fuel ctx x s = OK t ==>
  dft_remaining_inv fn bb (pre ++ post)
    (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `MEM x bb.bb_instructions /\ ~is_pseudo x.inst_opcode` by
    metis_tac[dft_remaining_inv_head_order] >>
  `inst_wf x /\ x.inst_opcode <> PHI` by
    (fs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  drule_all inv_ev_step_availability >> strip_tac >>
  `strict_dom_vars_defined fn t` by
    (fs[dft_remaining_inv_def, strict_dom_vars_defined_def, IN_UNION] >>
     metis_tac[]) >>
  fs[dft_remaining_inv_def] >> simp[dft_remaining_inv_def] >> rpt conj_tac
  >- (gvs[ALL_DISTINCT_APPEND] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[dftSsaPreserveTheory.id_before_append,
          dftSsaPreserveTheory.id_before_cons] >> metis_tac[])
  >- (fs[strict_dom_vars_defined_def] >> metis_tac[])
  >- (rpt strip_tac >> rename1 `MEM producer bb.bb_instructions` >>
      Cases_on `producer = x` >> gvs[] >> metis_tac[])
  >> metis_tac[]
QED

Theorem inv_entry_pseudo_initialized:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY inst_wf bb.bb_instructions /\
  bb.bb_instructions = pseudos ++ normal /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) normal /\
  fn_entry_label fn = SOME s.vs_current_bb /\ bb.bb_label = s.vs_current_bb /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     i.inst_opcode <> CODECOPY /\ MEM (Label l) i.inst_operands ==>
     l IN FDOM s.vs_labels) /\
  eval_phis s bb.bb_instructions = OK u /\
  FOLDR (dft_exec_cons fuel ctx) OK (DROP (phi_prefix_length pseudos) pseudos)
    (u with vs_inst_idx := phi_prefix_length pseudos) = OK t ==>
  dft_remaining_inv fn bb normal t
Proof
  strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = pseudos /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = normal` by
    (simp[FILTER_APPEND_DISTRIB] >>
     `FILTER (\i. is_pseudo i.inst_opcode) pseudos = pseudos /\
      FILTER (\i. is_pseudo i.inst_opcode) normal = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) pseudos = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) normal = normal` by
       (simp[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >>
        fs[EVERY_MEM] >> metis_tac[]) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) normal` by
    (fs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `eval_phis s pseudos = OK u` by
    metis_tac[dftIndexedExecTheory.dft_eval_phis_append] >>
  `strict_dom_vars_defined fn s` by metis_tac[strict_dom_vars_defined_entry] >>
  qpat_assum `FILTER (\i. ~is_pseudo i.inst_opcode) _ = normal`
    (fn th => once_rewrite_tac[GSYM th]) >>
  irule dft_remaining_inv_initialized >> simp[] >>
  qexistsl_tac [`ctx`, `fuel`, `s`, `u`] >> simp[] >>
  qpat_x_assum `!i l. _` mp_tac >> simp[MEM_APPEND]
QED

(* One use-site test: initialize at function entry, delete an actual OK
   oracle step, and manufacture success for the earliest residual crossing. *)
Theorem inv_entry_residual_extension:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY inst_wf bb.bb_instructions /\
  bb.bb_instructions = pseudos ++ normal /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) normal /\
  fn_entry_label fn = SOME s.vs_current_bb /\ bb.bb_label = s.vs_current_bb /\
  ~s.vs_call_ctx.cc_static /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     i.inst_opcode <> CODECOPY /\ MEM (Label l) i.inst_operands ==>
     l IN FDOM s.vs_labels) /\
  eval_phis s bb.bb_instructions = OK u /\
  FOLDR (dft_exec_cons fuel ctx) OK (DROP (phi_prefix_length pseudos) pseudos)
    (u with vs_inst_idx := phi_prefix_length pseudos) = OK t /\
  normal = pre ++ executed::post /\ pre ++ post = x::rest /\
  ~is_terminator executed.inst_opcode /\
  ev_step orc p d fuel ctx executed t = OK v /\
  inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> CODECOPY /\
  inv_memory_observation y.inst_opcode /\ ~dft_must_order x y ==>
  ?w. ev_step orc p d fuel ctx x
    (v with vs_inst_idx := SUC t.vs_inst_idx) = OK w
Proof
  strip_tac >>
  `dft_remaining_inv fn bb normal t` by
    (irule inv_entry_pseudo_initialized >> simp[] >>
     qexistsl_tac [`ctx`, `fuel`, `s`, `u`] >> simp[] >>
     gvs[] >> conj_tac
     >- metis_tac[] >>
     qpat_x_assum `eval_phis _ _ = OK _` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  `dft_remaining_inv fn bb (x::rest)
     (v with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_x_assum `normal = _` SUBST_ALL_TAC >>
     drule_all inv_remaining_ev_step >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (DROP (phi_prefix_length pseudos) pseudos)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) pseudos` by
       (fs[EVERY_MEM] >> rpt strip_tac >>
        `is_pseudo i.inst_opcode` by metis_tac[] >>
        Cases_on `i.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
     metis_tac[TAKE_DROP, EVERY_APPEND]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (drule_all dft_prefix_call_ctx >> simp[] >>
     drule dft_eval_phis_call_ctx >> simp[]) >>
  drule inv_ev_step_call_ctx >> strip_tac >>
  irule inv_crossed_predecessor_total >> simp[] >>
  `MEM x bb.bb_instructions /\ ~is_pseudo x.inst_opcode` by
    fs[dft_remaining_inv_def] >>
  `inst_wf x` by (gvs[EVERY_MEM] >> metis_tac[]) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `IS_SOME (eval_operand op (v with vs_inst_idx := SUC t.vs_inst_idx))` by
        metis_tac[inv_remaining_head_operands] >>
      fs[IS_SOME_EXISTS]) >>
  qexists_tac `y` >> simp[]
QED
