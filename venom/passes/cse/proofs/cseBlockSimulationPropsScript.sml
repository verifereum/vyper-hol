Theory cseBlockSimulationProps
Ancestors cseAssignProps cseZeroReplayProps cseDefs

(* Executable lookup filters candidates, so replay uses list membership. *)
Theorem cse_lookup_replay_source:
 (!canon dfg av inst src expr.
   cse_lookup canon dfg av inst = SOME (src, expr) ==>
   expr = mk_expr dfg inst /\
   src.inst_id <> inst.inst_id /\
   operand_ids_match canon dfg inst src /\
   ?xs. FLOOKUP av (mk_expr dfg inst) = SOME xs /\ MEM src xs) /\
 (!canon dfg av ids inst src expr.
   cse_lookup_same_bb canon dfg av ids inst = SOME (src, expr) ==>
   expr = mk_expr dfg inst /\
   src.inst_id <> inst.inst_id /\
   operand_ids_match canon dfg inst src /\
   ?xs. FLOOKUP av (mk_expr dfg inst) = SOME xs /\ MEM src xs)
Proof
 conj_tac >> rpt gen_tac >>
 simp[cse_lookup_def, cse_lookup_same_bb_def, AllCaseEqs()] >>
 rpt strip_tac >> gvs[listTheory.FILTER_EQ_CONS] >>
 metis_tac[listTheory.MEM_APPEND, listTheory.MEM]
QED

Theorem cse_inst_replay_cases:
 !ids canon dfg av_opt inst.
   cse_inst ids canon (dfg, av_opt) inst = inst \/
   (~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI /\
    ?src xs. FLOOKUP (avail_unwrap av_opt) (mk_expr dfg inst) = SOME xs /\
      MEM src xs /\ src.inst_id <> inst.inst_id /\
      operand_ids_match canon dfg inst src /\
      ((?x y. inst.inst_outputs = [x] /\ src.inst_outputs = [y] /\
         cse_inst ids canon (dfg, av_opt) inst = mk_assign_inst inst (Var y)) \/
       (inst.inst_outputs = [] /\
         cse_inst ids canon (dfg, av_opt) inst = mk_nop_inst inst)))
Proof
 rpt gen_tac >>
 Cases_on `inst.inst_opcode = PHI`
 >- simp[cse_inst_def, cse_skip_opcode_def] >>
 Cases_on `is_terminator inst.inst_opcode`
 >- simp[cse_inst_def] >>
 simp[cse_inst_def] >> rpt (IF_CASES_TAC >> simp[]) >>
 Cases_on `inst.inst_outputs` >> simp[]
 >- (rpt (CASE_TAC >> gvs[]) >> metis_tac[cse_lookup_replay_source]) >>
 Cases_on `t` >> simp[] >>
 Cases_on `cse_lookup canon dfg (avail_unwrap av_opt) inst` >> simp[] >>
 rename1 `_ = SOME pair` >> PairCases_on `pair` >> simp[] >>
 IF_CASES_TAC
 >- (Cases_on `pair0.inst_outputs` >> simp[] >>
     Cases_on `t` >> simp[] >> metis_tac[cse_lookup_replay_source]) >>
 IF_CASES_TAC
 >- (Cases_on `pair0.inst_outputs` >> simp[] >>
     Cases_on `t` >> simp[] >> metis_tac[cse_lookup_replay_source]) >>
 Cases_on `cse_lookup_same_bb canon dfg (avail_unwrap av_opt) ids inst` >> simp[] >>
 rename1 `_ = SOME pair2` >> PairCases_on `pair2` >>
 simp[] >> Cases_on `pair20.inst_outputs` >> simp[] >>
 Cases_on `t` >> simp[] >> metis_tac[cse_lookup_replay_source]
QED

(* For eligible opcodes well-formedness fixes the output arity. *)
Theorem cse_same_opcode_zero_outputs:
 inst_wf inst /\ inst_wf src /\ src.inst_opcode = inst.inst_opcode /\
 inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> BUMP /\
 inst.inst_outputs = [] ==> src.inst_outputs = []
Proof
 strip_tac >> Cases_on `inst.inst_opcode` >>
 gvs[venomWfTheory.inst_wf_def]
QED

Theorem cse_prefix_inst_replacement:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst ==>
 (?e. step_inst n ctx inst s = Error e) \/
 lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
   (step_inst n ctx inst s)
   (step_inst n ctx
     (cse_inst ids (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
       (dfg_build_function fn,
        df_at NONE (avail_analyze fn) bb.bb_label s.vs_inst_idx) inst) s)
Proof
 strip_tac >>
 `MEM inst (fn_insts fn)` by
   (drule_all cseHistoryPropsTheory.cse_prefix_exec_control >> strip_tac >>
    simp[venomInstTheory.fn_insts_def] >>
    irule venomInstTheory.fmp_fn_insts_blocks_intro >>
    gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
    metis_tac[venomExecPropsTheory.lookup_block_MEM, listTheory.EL_MEM]) >>
 `inst_wf inst` by
   (gvs[venomWfTheory.fn_inst_wf_def, venomInstTheory.fn_insts_def,
        venomWfPropsTheory.fn_insts_blocks_flat,
        listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
 qabbrev_tac `changed = cse_inst ids
   (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
   (dfg_build_function fn,
    df_at NONE (avail_analyze fn) bb.bb_label s.vs_inst_idx) inst` >>
 Cases_on `changed = inst`
 >- (simp[] >> disj2_tac >> irule passSimulationPropsTheory.lift_result_refl >>
     simp[stateEquivPropsTheory.state_equiv_refl,
          stateEquivPropsTheory.execution_equiv_refl]) >>
 `?src xs. FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx)
     (mk_expr (dfg_build_function fn) inst) = SOME xs /\ MEM src xs /\
   operand_ids_match
     (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
     (dfg_build_function fn) inst src /\
   ((?x y. inst.inst_outputs = [x] /\ src.inst_outputs = [y] /\
      changed = mk_assign_inst inst (Var y)) \/
    (inst.inst_outputs = [] /\ changed = mk_nop_inst inst))` by
   (metis_tac[cse_inst_replay_cases, availExprDefsTheory.ae_lookup_inst_def]) >>
 `MEM src (fn_insts fn) /\
  avail_source_birth (dfg_build_function fn)
    (mk_expr (dfg_build_function fn) inst) src src` by
   (irule cseSourcePropsTheory.cse_avail_source_provenance >>
    metis_tac[availExprDefsTheory.ae_lookup_inst_def]) >>
 `inst_wf src` by
   (gvs[venomWfTheory.fn_inst_wf_def, venomInstTheory.fn_insts_def,
        venomWfPropsTheory.fn_insts_blocks_flat,
        listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[])
 >- (gvs[] >> irule cse_available_assign_replacement >> metis_tac[]) >>
 `src.inst_opcode = inst.inst_opcode` by
   (gvs[availExprProofsTheory.avail_source_birth_def] >>
    metis_tac[cseReplayPropsTheory.mk_expr_root_inversion]) >>
 `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> BUMP` by
   (gvs[availExprProofsTheory.avail_source_birth_def,
        availExprDefsTheory.avail_nonidempotent_def,
        venomEffectsTheory.is_nonidempotent_def] >>
    strip_tac >> gvs[venomEffectsTheory.is_nonidempotent_def]) >>
 `src.inst_outputs = []` by metis_tac[cse_same_opcode_zero_outputs] >>
 gvs[] >> irule cse_available_nop_replacement >> metis_tac[]
QED


(* Local instruction law in precisely the prefix simulator's block interface. *)
Theorem cse_prefix_block_replacement:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 state_equiv {} s t /\ get_instruction bb s.vs_inst_idx = SOME inst /\
 get_instruction
   (cse_block_transform
     (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
     (dfg_build_function fn) (avail_analyze fn) bb)
   s.vs_inst_idx = SOME j ==>
 (?e. step_inst n ctx inst s = Error e) \/
 lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
   (step_inst n ctx inst s) (step_inst n ctx j t)
Proof
 strip_tac >>
 `t = s` by metis_tac[stateEquivPropsTheory.state_equiv_empty_eq] >>
 gvs[cse_block_transform_def, venomInstTheory.get_instruction_def,
     indexedListsTheory.LENGTH_MAPi, indexedListsTheory.EL_MAPi] >>
 irule cse_prefix_inst_replacement >>
 metis_tac[venomInstTheory.get_instruction_def]
QED

Theorem cse_inst_control_shape:
 (inst.inst_opcode = PHI ==> cse_inst ids canon (dfg,av_opt) inst = inst) /\
 ((cse_inst ids canon (dfg,av_opt) inst).inst_opcode = PHI <=>
   inst.inst_opcode = PHI) /\
 (is_terminator (cse_inst ids canon (dfg,av_opt) inst).inst_opcode <=>
   is_terminator inst.inst_opcode)
Proof
 Cases_on `inst.inst_opcode = PHI`
 >- simp[cse_inst_def, cse_skip_opcode_def] >>
 Cases_on `is_terminator inst.inst_opcode`
 >- simp[cse_inst_def] >>
 mp_tac (SPEC_ALL cse_inst_replay_cases) >>
 strip_tac >> gvs[passSharedDefsTheory.mk_assign_inst_def,
   passSharedDefsTheory.mk_nop_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem cse_block_label[simp]:
 (cse_block_transform canon dfg result bb).bb_label = bb.bb_label
Proof
 simp[cse_block_transform_def]
QED

Theorem cse_block_lookup:
 lookup_block l (function_map_transform (cse_block_transform canon dfg result) fn).fn_blocks =
 OPTION_MAP (cse_block_transform canon dfg result) (lookup_block l fn.fn_blocks)
Proof
 simp[passTransformTheory.function_map_transform_def,
      passSimulationPropsTheory.lookup_block_map]
QED

Theorem cse_block_instruction:
 get_instruction bb i = SOME inst ==>
 ?j. get_instruction (cse_block_transform canon dfg result bb) i = SOME j /\
     is_terminator j.inst_opcode = is_terminator inst.inst_opcode
Proof
 simp[venomInstTheory.get_instruction_def, cse_block_transform_def,
      indexedListsTheory.EL_MAPi, cse_inst_control_shape] >>
 rpt strip_tac >> gvs[]
QED

(* Indexed maps preserving PHIs preserve both prefix length and evaluation,
   with no requirement that PHIs elsewhere in the list form a prefix. *)
Theorem mapi_phi_observations:
 !l f.
 (!idx inst. (inst.inst_opcode = PHI ==> f idx inst = inst) /\
   ((f idx inst).inst_opcode = PHI <=> inst.inst_opcode = PHI)) ==>
 phi_prefix_length (MAPi f l) = phi_prefix_length l /\
 !s. eval_phis s (MAPi f l) = eval_phis s l
Proof
 Induct >> simp[indexedListsTheory.MAPi_def,
   venomExecSemanticsTheory.phi_prefix_length_def,
   venomExecSemanticsTheory.eval_phis_def] >>
 rpt strip_tac >>
 first_x_assum (qspec_then `\idx inst. f (SUC idx) inst` mp_tac) >>
 simp[] >> strip_tac >>
 Cases_on `h.inst_opcode = PHI` >>
 gvs[venomExecSemanticsTheory.phi_prefix_length_def,
     venomExecSemanticsTheory.eval_phis_def]
QED

Theorem cse_block_phi:
 phi_prefix_length (cse_block_transform canon dfg result bb).bb_instructions =
   phi_prefix_length bb.bb_instructions /\
 !s. eval_phis s (cse_block_transform canon dfg result bb).bb_instructions =
   eval_phis s bb.bb_instructions
Proof
 simp[cse_block_transform_def] >>
 irule mapi_phi_observations >> simp[cse_inst_control_shape]
QED
