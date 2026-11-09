Theory algebraicOptMainRunProofs
Ancestors
  algebraicOptMainBlockProofs algebraicOptMainEntryProofs
  algebraicOptMainLayoutProofs algebraicOptTraceProofs
  algebraicOptReachabilityProofs venomExecProofs venomExecProps
  venomExecSemantics venomWf venomInst venomState stateEquiv
Libs
  listTheory rich_listTheory

Theorem ao_main_run_block:
  ao_source_prefix ctx fn s0 n (SUC k) T s /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> lookup_var x s0 = NONE) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ao_transform_insts_supply (dfg_build_function fn) (range_analyze fn)
    bb.bb_label (ao_compute_fn_iszero_targets fn) supply 0 bb.bb_instructions = (outs,last) /\
  ir_supply_inst_ok supply /\ V SUBSET set supply.irs_used_vars /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  ao_main_observations fn V s r /\
  s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|> = r ==>
  (?e. run_block k ctx bb s = Error e) \/
  lift_result
    (\t u. ao_main_observations fn V t u /\
      t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> = u /\
      t.vs_inst_idx = 0 /\ u.vs_inst_idx = 0 /\
      ao_source_prefix ctx fn s0 n k T t)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (run_block k ctx bb s)
    (run_block k ctx (bb with bb_instructions := outs) r)
Proof
  strip_tac >> drule ao_source_prefix_has_trace >> strip_tac >>
  Q.SUBGOAL_THEN `2 <= LENGTH trace \/ s.vs_prev_bb = NONE` assume_tac
  >- (Cases_on `trace` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE` by (simp[] >> metis_tac[]) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- suspend "phis_ok"
  >> disj1_tac >> simp[run_block_def]
QED
Resume ao_main_run_block[phis_ok]:
  rename1 `eval_phis s bb.bb_instructions = OK p` >>
  drule_all ao_main_entry_supply >> strip_tac >>
  `ao_source_prefix ctx fn s0 n k F
     (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[ao_source_prefix_trace_iff] >> goal_assum (drule_at Any) >> simp[]) >>
  `p = s with vs_vars := p.vs_vars` by
    metis_tac[eval_phis_only_updates_vs_vars] >>
  `bb_well_formed bb` by metis_tac[wf_function_def, lookup_block_MEM] >>
  Cases_on `ao_transform_insts_supply (dfg_build_function fn) (range_analyze fn)
    bb.bb_label (ao_compute_fn_iszero_targets fn) supply 0
    (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` >>
  rename1 `ao_transform_insts_supply _ _ _ _ _ _ (TAKE _ _) = (pre,mid)` >>
  `LENGTH pre = phi_prefix_length bb.bb_instructions` by
    metis_tac[ao_transform_insts_supply_take_phi_length] >>
  `phi_prefix_length outs = phi_prefix_length bb.bb_instructions` by
    metis_tac[ao_transform_insts_supply_phi_prefix_length] >>
  `p.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `p = s with vs_vars := _`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[run_block_def] >>
  irule ao_main_block_suffix >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl [`last`, `mid`, `pre`, `supply`,
    `TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions`,
    `DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions`] >>
  simp[ao_main_block_nonphi_suffix, LENGTH_TAKE, phi_prefix_length_le]
QED
Finalise ao_main_run_block
