Theory algebraicOptMainEntryProofs
Ancestors
  algebraicOptMainPhiProofs algebraicOptMainLayoutProofs algebraicOptTraceProofs
  algebraicOptMainResidualProofs analysisSimProofsBase venomExecSemantics venomState venomWf
Libs
  listTheory

Theorem ao_eval_phis_initial_prefix:
  s.vs_prev_bb = NONE /\ eval_phis s insts = OK p ==>
  phi_prefix_length insts = 0
Proof
  Cases_on `insts` >> simp[phi_prefix_length_def, eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def, eval_phis_def] >>
  strip_tac >> gvs[eval_one_phi_def, AllCaseEqs()]
QED

Theorem ao_main_entry_supply:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  trace <> [] /\ ao_source_trace ctx fn trace /\ LAST trace = (SUC k,T,s) /\
  (2 <= LENGTH trace \/ s.vs_prev_bb = NONE) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  ao_main_observations fn V s r /\
  s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|> = r /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  ao_transform_insts_supply dfg ra lbl (ao_compute_fn_iszero_targets fn)
    supply 0 bb.bb_instructions = (outs,supply') /\
  eval_phis s bb.bb_instructions = OK p ==>
  ?q trace'. eval_phis r outs = OK q /\
    ao_main_observations fn V
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      (q with vs_inst_idx := phi_prefix_length outs) /\
    (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) with
      vs_vars := q.vs_vars = (q with vs_inst_idx := phi_prefix_length outs) /\
    trace' <> [] /\ ao_source_trace ctx fn trace' /\ HD trace' = HD trace /\
    LAST trace' = (k,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_labels = r.vs_labels /\ s.vs_prev_bb = r.vs_prev_bb` by
    (qpat_x_assum `s with <|vs_vars := _; vs_inst_idx := _|> = r`
      (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `phi_prefix_length outs = phi_prefix_length bb.bb_instructions` by
    metis_tac[ao_transform_insts_supply_phi_prefix_length] >>
  `?q. eval_phis r outs = OK q /\ ao_main_observations fn V p q /\
    p = s with vs_vars := p.vs_vars /\ q = r with vs_vars := q.vs_vars` by
    (Cases_on `2 <= LENGTH trace`
     >- (irule ao_main_eval_phis_supply >> metis_tac[]) >>
     `s.vs_prev_bb = NONE` by metis_tac[] >>
     `phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[ao_eval_phis_initial_prefix] >>
     `p = s` by metis_tac[ao_eval_phis_no_predecessor] >>
     qexists `r` >> simp[phi_prefix_length_zero_eval_phis_ok]) >>
  qexistsl [`q`, `trace ++ [(k,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)]`] >>
  simp[LAST_APPEND_CONS] >> conj_tac
  >- (irule ao_main_observations_vars >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `p = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      qpat_x_assum `q = r with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      qpat_x_assum `s with <|vs_vars := _; vs_inst_idx := _|> = r`
        (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  conj_tac
  >- (irule ao_source_trace_snoc >> simp[] >> irule (cj 1 ao_source_step_rules) >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `trace` >> gvs[]
QED
