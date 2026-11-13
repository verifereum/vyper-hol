(* Concrete assembly of the independently checked emission interfaces. *)
Theory acBlockSimulationProofs
Ancestors
  acMergeCursorProofs acMergeCursorDefs acMergeRuntimeDefs acMergeRuntimeProofs
  acLiveEmissionProofs acDeferredEmissionProofs acMergeSimulationProofs
  acBlockTransformProofs acSupplyProofs acChainProofs acAbortRelProofs
  acRuntimePhiProofs acRuntimeSuccessorProofs acRuntimeInvariantDefs
  runInstsExecBlockProps assertCombinerDefs venomExecSemantics venomExecProofs
  venomWf venomWfProps venomState venomInst dfgAnalysisProps
  stateEquiv stateEquivProps stateFrame irSupply irSupplyFreshProps list rich_list pred_set
  acSourceBlockInvariantProofs venomExecProps mmWfProofs

Theorem ac_query_fresh_operand:
  ir_supply_covers_fn su fn /\
  ac_get_iszero_operand (dfg_build_function fn) {} c = SOME (Var v) ==>
  v NOTIN ac_fresh_vars su fn
Proof
  rpt strip_tac >> drule ac_get_iszero_operand_src >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  metis_tac[ac_fresh_vars_original_operand]
QED

(* Source suffixes begin after the parallel PHI batch. The state in the
   certificate is normalized, but the two actual list states are not. *)
Theorem ac_merge_suffix_simulation:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn su fn /\ MEM bb fn.fn_blocks /\
  offset <= LENGTH bb.bb_instructions /\
  EVERY (\i. i.inst_opcode <> PHI) (DROP offset bb.bb_instructions) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (DROP offset bb.bb_instructions)) /\
  ir_supply_extends
    (SND (ac_merge_insts
      (ac_scan_block (dfg_build_function fn) (DROP offset bb.bb_instructions) NONE)
      [] su0 (DROP offset bb.bb_instructions))) su_end /\
  (set su_end.irs_used_vars DIFF set su0.irs_used_vars) SUBSET ac_fresh_vars su fn /\
  (!i v. MEM i (DROP offset bb.bb_instructions) /\
    (MEM (Var v) i.inst_operands \/ MEM v i.inst_outputs) ==>
    v NOTIN ac_fresh_vars su fn) /\
  ac_merge_runtime_cert fn bb offset 0 s /\
  state_equiv (ac_fresh_vars su fn) s t ==>
  (?e. run_insts fuel ctx (DROP offset bb.bb_instructions) s = Error e) \/
  lift_result (state_equiv (ac_fresh_vars su fn)) (execution_equiv UNIV)
    ac_abort_equiv
    (run_insts fuel ctx (DROP offset bb.bb_instructions) s)
    (run_insts fuel ctx
      (FST (ac_merge_insts
        (ac_scan_block (dfg_build_function fn) (DROP offset bb.bb_instructions) NONE)
        [] su0 (DROP offset bb.bb_instructions))) t)
Proof
  rpt strip_tac >>
  qabbrev_tac `xs = DROP offset bb.bb_instructions` >>
  qabbrev_tac `cs = ac_scan_block (dfg_build_function fn) xs NONE` >>
  qabbrev_tac `shape = ac_merge_static xs cs su0 su_end` >>
  qabbrev_tac `pending = (ac_merge_pending xs cs : num -> (num # operand) list -> ir_supply -> (num # operand) option)` >>
  qabbrev_tac `cert = ac_merge_runtime_cert fn bb offset` >>
  `ac_merge_cursor_laws xs (dfg_build_function fn) cs (ac_fresh_vars su fn)
     su0 shape pending` by
    (metis_tac[Abbr `shape`, Abbr `pending`, Abbr `cs`, ac_merge_cursor_laws_scan]) >>
  `ac_merge_runtime_laws xs (dfg_build_function fn) fuel ctx cert` by
    (simp[Abbr `xs`, Abbr `cert`] >> irule ac_merge_runtime_cert_laws >> simp[]) >>
  `!c q v. ac_get_iszero_operand (dfg_build_function fn) {} c = SOME q /\
       q = Var v ==> v NOTIN ac_fresh_vars su fn` by
    (rpt strip_tac >> gvs[] >> metis_tac[ac_query_fresh_operand]) >>
  `ac_live_emission_contract xs cs fuel ctx
     (state_equiv (ac_fresh_vars su fn)) (execution_equiv UNIV) ac_abort_equiv
     (ac_merge_live (ac_fresh_vars su fn) cert shape pending)
     (ac_merge_revert_deferred (ac_fresh_vars su fn) cert shape pending)` by
    (irule acLiveEmissionProofsTheory.ac_live_emission_contract >> metis_tac[]) >>
  `ac_deferred_emission_contract xs cs fuel ctx ac_abort_equiv
     (ac_merge_revert_deferred (ac_fresh_vars su fn) cert shape pending)` by
    (irule acDeferredEmissionProofsTheory.ac_deferred_emission_contract >> metis_tac[]) >>
  `ac_emission_end_contract xs (state_equiv (ac_fresh_vars su fn))
     (ac_merge_live (ac_fresh_vars su fn) cert shape pending)
     (ac_merge_revert_deferred (ac_fresh_vars su fn) cert shape pending)` by
    (simp[ac_emission_end_contract_def] >> conj_tac
     >- simp[ac_merge_live_def] >> metis_tac[ac_deferred_end]) >>
  drule ac_merge_insts_simulation_suffix >> simp[] >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum irule >>
  simp[ac_merge_live_def] >>
  fs[ac_merge_cursor_laws_def, Abbr `cert`]
QED

(* Concrete transformation, with the actual block-local supplies. *)
Theorem ac_run_block_simulation:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn su fn /\
  ac_cursor_inv fn bb 0 s /\ ac_merge_safe_labels fn s /\
  ac_transform_block (dfg_build_function fn) su0 bb = (bt,st) /\
  (set st.irs_used_vars DIFF set su0.irs_used_vars) SUBSET ac_fresh_vars su fn /\
  state_equiv (ac_fresh_vars su fn) s t ==>
  (?e. run_block fuel ctx bb s = Error e) \/
  lift_result (state_equiv (ac_fresh_vars su fn)) (execution_equiv UNIV)
    ac_abort_equiv (run_block fuel ctx bb s) (run_block fuel ctx bt t)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by gvs[ac_cursor_inv_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mmWfProofsTheory.fn_inst_ids_distinct_block, wf_function_def] >>
  `bb_well_formed bt` by metis_tac[ac_transform_block_shape] >>
  drule_all ac_transform_block_phi_boundary >> strip_tac >>
  irule run_block_run_insts_lift_result >> simp[] >>
  conj_tac >- simp[ac_abort_equiv_frame, execution_frame_def] >>
  conj_tac >- simp[execution_equiv_def, execution_frame_def] >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[state_equiv_def, execution_equiv_def, execution_frame_def, lookup_var_def]) >>
  rpt strip_tac >>
  `?v. eval_phis t bb.bb_instructions = OK v /\
       state_equiv (ac_fresh_vars su fn) u v` by
    (irule eval_phis_state_equiv >> simp[] >> reverse conj_tac
     >- (qexists `s` >> simp[]) >> simp[EVERY_MEM] >> metis_tac[ac_fresh_vars_original_operand,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff, fn_insts_def]) >>
  qexists `v` >> simp[] >>
  `ac_merge_runtime_cert fn bb (phi_prefix_length bb.bb_instructions) 0 u` by
    (drule_all ac_cursor_inv_phis >> strip_tac >>
     simp[ac_merge_runtime_cert_def, ac_merge_runtime_def] >> conj_tac
     >- (fs[ac_cursor_inv_def] >>
         `u with <|vs_current_bb := bb.bb_label;
                   vs_inst_idx := phi_prefix_length bb.bb_instructions|> =
          u with vs_inst_idx := phi_prefix_length bb.bb_instructions` by
           simp[venom_state_component_equality] >>
         qpat_x_assum `u with <|vs_current_bb := _; vs_inst_idx := _|> = _`
           (fn th => pure_rewrite_tac[th]) >> metis_tac[]) >>
     qpat_assum `eval_phis s _ = OK u`
       (mp_tac o MATCH_MP eval_phis_preserves_labels) >>
     fs[ac_merge_safe_labels_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`offset` |-> `phi_prefix_length bb.bb_instructions`,
    `su_end` |-> `st`, `s` |-> `u`, `t` |-> `v`] ac_merge_suffix_simulation) >>
  simp[] >> disch_then irule >>
  simp[phi_prefix_length_le, ir_supply_extends_refl] >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[ALL_DISTINCT_DROP, MAP_DROP] >>
      metis_tac[algebraicOptMainBlockProofsTheory.ao_main_block_nonphi_suffix]) >>
  rpt gen_tac >> disch_tac >> irule ac_fresh_vars_original_var >> simp[] >>
  simp[fn_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  qexists `block_ir_vars bb` >> conj_tac
  >- (qexists `bb` >> simp[]) >>
  simp[block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  qexists `inst_ir_vars i` >> conj_tac
  >- (qexists `i` >> metis_tac[MEM_DROP_IMP]) >>
  gvs[inst_ir_vars_def, inst_uses_def,
      passSharedDefsTheory.MEM_operand_vars_eq_Var]
QED

(* Actual function supplies and lookup, with no remaining emission laws. *)
Theorem ac_transform_function_run_block:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn su fn /\
  ac_cursor_inv fn bb 0 s /\ ac_merge_safe_labels fn s /\
  lookup_block l fn.fn_blocks = SOME bb /\
  state_equiv (ac_fresh_vars su fn) s t ==>
  ?bt. lookup_block l (FST (ac_transform_function su fn)).fn_blocks = SOME bt /\
    ((?e. run_block fuel ctx bb s = Error e) \/
     lift_result (state_equiv (ac_fresh_vars su fn)) (execution_equiv UNIV)
       ac_abort_equiv (run_block fuel ctx bb s) (run_block fuel ctx bt t))
Proof
  strip_tac >> drule ac_transform_function_lookup >>
  disch_then (qspec_then `su` strip_assume_tac) >>
  qexists `bb'` >> simp[] >> irule ac_run_block_simulation >> simp[] >>
  metis_tac[]
QED

(* Successful source exits re-establish the entry certificate of the chosen
   successor; all PHI-suffix side conditions follow from well-formedness. *)
Theorem ac_run_block_successor:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ac_cursor_inv fn bb 0 s /\ ac_merge_safe_labels fn s /\
  run_block fuel ctx bb s = OK t /\
  MEM sb fn.fn_blocks /\ sb.bb_label = t.vs_current_bb ==>
  ac_cursor_inv fn sb 0 t /\ ac_merge_safe_labels fn t
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by gvs[ac_cursor_inv_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  irule ac_source_run_block_successor >> simp[] >>
  qexistsl [`bb`, `ctx`, `fuel`, `s`] >> simp[] >> conj_tac
  >- metis_tac[phi_prefix_length_lt_wf] >>
  metis_tac[algebraicOptMainBlockProofsTheory.ao_main_block_nonphi_suffix]
QED
