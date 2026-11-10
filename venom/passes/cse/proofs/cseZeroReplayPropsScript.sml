Theory cseZeroReplayProps
Ancestors cseStageBindingProps venomMemProps venomState
Libs cseReplayLib

(* Repeating a byte write after its resulting memory has survived is an
   identity on the entire current state, not merely on its memory field. *)
Theorem cse_memory_write_replay:
 s.vs_memory = (write_memory_with_expansion dst bytes u).vs_memory ==>
 write_memory_with_expansion dst bytes s = s
Proof
 strip_tac >> irule write_memory_with_expansion_identity >>
 simp[write_memory_with_expansion_read_self,
      LENGTH_write_memory_with_expansion]
QED

Theorem cse_mstore_replay:
 s.vs_memory = (mstore dst value u).vs_memory ==>
 mstore dst value s = s
Proof
 simp[mstore_eq_write_mem] >> metis_tac[cse_memory_write_replay]
QED

Theorem cse_mstore8_replay:
 s.vs_memory = (mstore8 dst value u).vs_memory ==>
 mstore8 dst value s = s
Proof
 simp[mstore8_eq_write_mem] >> metis_tac[cse_memory_write_replay]
QED

Theorem cse_istore_replay:
 s.vs_memory = (istore dst value u).vs_memory /\
 s.vs_immutables = (istore dst value u).vs_immutables ==>
 istore dst value s = s
Proof
 simp[venomExecSemanticsTheory.istore_def] >> strip_tac >>
 `mstore dst value s = s` by metis_tac[cse_mstore_replay] >>
 simp[finite_mapTheory.FUPDATE_EQ] >>
 qpat_x_assum `s.vs_immutables = _` (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Theorem cse_sstore_replay:
 contract_storage s = contract_storage (sstore key value u) ==>
 sstore key value s = s
Proof
 rewrite_tac[contract_storage_def, sstore_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
 strip_tac >>
 `update_storage key value
    (lookup_account s.vs_call_ctx.cc_address s.vs_accounts).storage =
    (lookup_account s.vs_call_ctx.cc_address s.vs_accounts).storage` by
   (gvs[vfmStateTheory.lookup_account_def, vfmStateTheory.update_storage_def,
        combinTheory.UPDATE_EQ]) >>
 qpat_x_assum `update_storage _ _ _ = _`
   (mp_tac o REWRITE_RULE [vfmStateTheory.lookup_account_def]) >>
 qpat_x_assum `(s.vs_accounts _).storage = _` kall_tac >>
 strip_tac >> simp[] >>
 simp[combinTheory.APPLY_UPDATE_ID]
QED

Theorem cse_tstore_replay:
 contract_transient s = contract_transient (tstore key value u) ==>
 tstore key value s = s
Proof
 simp[contract_transient_def, tstore_def, combinTheory.APPLY_UPDATE_THM,
      vfmStateTheory.update_storage_def] >> strip_tac >>
 qpat_x_assum `s.vs_transient _ = _`
   (fn th => rewrite_tac[GSYM th]) >> simp[combinTheory.APPLY_UPDATE_ID]
QED

Theorem cse_exec_write2_replay:
 exec_write2 f src u = OK v /\ exec_write2 f inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 R v s /\
 (!a b u s. R (f a b u) s ==> f a b s = s) ==>
 t = s
Proof
 simp[venomExecSemanticsTheory.exec_write2_def, AllCaseEqs()] >>
 rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem cse_selected_MSTORE_replay:
 src.inst_opcode = MSTORE /\ inst.inst_opcode = MSTORE /\
 step_inst_base src u = OK v /\ step_inst_base inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 s.vs_memory = v.vs_memory ==> t = s
Proof
 strip_tac >> cseReplayLib.selected_base_tac >>
 qpat_assum `exec_write2 _ src u = OK v`
   (mp_then Any mp_tac (Q.INST [`R` |-> `\v s. s.vs_memory = v.vs_memory`]
      cse_exec_write2_replay)) >>
 disch_then irule >> simp[] >>
 metis_tac[cse_mstore_replay]
QED

Theorem cse_selected_MSTORE8_replay:
 src.inst_opcode = MSTORE8 /\ inst.inst_opcode = MSTORE8 /\
 step_inst_base src u = OK v /\ step_inst_base inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 s.vs_memory = v.vs_memory ==> t = s
Proof
 strip_tac >> cseReplayLib.selected_base_tac >>
 qpat_assum `exec_write2 _ src u = OK v`
   (mp_then Any mp_tac (Q.INST [`R` |-> `\v s. s.vs_memory = v.vs_memory`]
      cse_exec_write2_replay)) >>
 disch_then irule >> simp[] >>
 metis_tac[cse_mstore8_replay]
QED

Theorem cse_selected_ISTORE_replay:
 src.inst_opcode = ISTORE /\ inst.inst_opcode = ISTORE /\
 step_inst_base src u = OK v /\ step_inst_base inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 s.vs_memory = v.vs_memory /\ s.vs_immutables = v.vs_immutables ==> t = s
Proof
 strip_tac >> cseReplayLib.selected_base_tac >>
 gvs[AllCaseEqs()] >>
 irule cse_istore_replay >> goal_assum (drule_at Any) >> simp[]
QED

Theorem cse_selected_SSTORE_replay:
 src.inst_opcode = SSTORE /\ inst.inst_opcode = SSTORE /\
 step_inst_base src u = OK v /\ step_inst_base inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 contract_storage s = contract_storage v ==> t = s
Proof
 strip_tac >> cseReplayLib.selected_base_tac >>
 gvs[AllCaseEqs()] >>
 qpat_assum `exec_write2 _ src u = OK v`
   (mp_then Any mp_tac (Q.INST [`R` |->
      `\v s. contract_storage s = contract_storage v`] cse_exec_write2_replay)) >>
 disch_then irule >> simp[] >> metis_tac[cse_sstore_replay]
QED

Theorem cse_selected_TSTORE_replay:
 src.inst_opcode = TSTORE /\ inst.inst_opcode = TSTORE /\
 step_inst_base src u = OK v /\ step_inst_base inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 contract_transient s = contract_transient v ==> t = s
Proof
 strip_tac >> cseReplayLib.selected_base_tac >>
 gvs[AllCaseEqs()] >>
 qpat_assum `exec_write2 _ src u = OK v`
   (mp_then Any mp_tac (Q.INST [`R` |->
      `\v s. contract_transient s = contract_transient v`] cse_exec_write2_replay)) >>
 disch_then irule >> simp[] >> metis_tac[cse_tstore_replay]
QED

Theorem cse_selected_copy_replay:
 (src.inst_opcode = CALLDATACOPY \/ src.inst_opcode = RETURNDATACOPY \/
  src.inst_opcode = DLOADBYTES \/ src.inst_opcode = CODECOPY \/
  src.inst_opcode = EXTCODECOPY) /\
 inst.inst_opcode = src.inst_opcode /\
 step_inst_base src u = OK v /\ step_inst_base inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 s.vs_memory = v.vs_memory /\
 u.vs_call_ctx = s.vs_call_ctx /\
 u.vs_data_section = s.vs_data_section /\ u.vs_code = s.vs_code /\
 (Eff_RETURNDATA IN read_effects inst.inst_opcode ==>
    u.vs_returndata = s.vs_returndata) /\
 (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
    !addr. (lookup_account addr u.vs_accounts).code =
           (lookup_account addr s.vs_accounts).code) ==> t = s
Proof
 strip_tac >> gvs[venomEffectsTheory.read_effects_def] >>
 cseReplayLib.selected_base_tac >>
 gvs[AllCaseEqs()] >>
 irule cse_memory_write_replay >> goal_assum (drule_at Any)
QED

Theorem cse_selected_assert_identity:
 (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
 step_inst_base inst s = OK t ==> t = s
Proof
 strip_tac >> cseReplayLib.selected_base_tac >> gvs[AllCaseEqs()]
QED

Theorem cse_zero_two_state_replay:
 inst_wf src /\ inst_wf inst /\ src.inst_opcode = inst.inst_opcode /\
 ~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
 ~is_terminator inst.inst_opcode /\ ~avail_nonidempotent inst.inst_opcode /\
 ~has_conflicting_effects inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode /\
 src.inst_outputs = [] /\ inst.inst_outputs = [] /\
 step_inst m ctx src u = OK v /\ step_inst n ctx inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 u.vs_call_ctx = s.vs_call_ctx /\ u.vs_data_section = s.vs_data_section /\
 u.vs_code = s.vs_code /\
 (Eff_MEMORY IN write_effects inst.inst_opcode ==> s.vs_memory = v.vs_memory) /\
 (Eff_STORAGE IN write_effects inst.inst_opcode ==>
    contract_storage s = contract_storage v) /\
 (Eff_TRANSIENT IN write_effects inst.inst_opcode ==>
    contract_transient s = contract_transient v) /\
 (Eff_IMMUTABLES IN write_effects inst.inst_opcode ==>
    s.vs_immutables = v.vs_immutables) /\
 (Eff_RETURNDATA IN read_effects inst.inst_opcode ==> u.vs_returndata = s.vs_returndata) /\
 (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
    !addr. (lookup_account addr u.vs_accounts).code =
           (lookup_account addr s.vs_accounts).code) ==> t = s
Proof
 strip_tac >>
 `inst.inst_opcode <> INVOKE` by
   (strip_tac >> gvs[availExprDefsTheory.avail_nonidempotent_def,
                    venomEffectsTheory.is_nonidempotent_def]) >>
 `src.inst_opcode <> INVOKE` by metis_tac[] >>
 gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
 Cases_on `inst.inst_opcode` >>
 gvs[venomInstTheory.is_pseudo_def, venomInstTheory.is_terminator_def,
     availExprDefsTheory.avail_nonidempotent_def,
     venomEffectsTheory.is_nonidempotent_def,
     venomEffectsTheory.has_conflicting_effects_def, venomInstTheory.is_alloca_op_def] >>
 qpat_x_assum `inst_wf inst` mp_tac >>
 pure_rewrite_tac[venomWfTheory.inst_wf_def] >> simp[] >> rpt strip_tac >>
 gvs[venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
     venomEffectsTheory.empty_effects_def]
 >- (irule cse_selected_MSTORE_replay >> metis_tac[])
 >- (irule cse_selected_MSTORE8_replay >> metis_tac[])
 >- (irule cse_selected_SSTORE_replay >> metis_tac[])
 >- (irule cse_selected_TSTORE_replay >> metis_tac[])
 >- (irule cse_selected_ISTORE_replay >> metis_tac[])
 >- (cseReplayLib.selected_base_tac >> gvs[])
 >- (irule cse_selected_copy_replay >> qexistsl [`inst`, `src`, `u`, `v`] >>
       simp[venomEffectsTheory.read_effects_def,
       venomEffectsTheory.empty_effects_def] >> metis_tac[])
 >- (irule cse_selected_copy_replay >> qexistsl [`inst`, `src`, `u`, `v`] >>
       simp[venomEffectsTheory.read_effects_def,
       venomEffectsTheory.empty_effects_def] >> metis_tac[])
 >- (irule cse_selected_copy_replay >> qexistsl [`inst`, `src`, `u`, `v`] >>
       simp[venomEffectsTheory.read_effects_def,
       venomEffectsTheory.empty_effects_def] >> metis_tac[])
 >- (irule cse_selected_copy_replay >> qexistsl [`inst`, `src`, `u`, `v`] >>
       simp[venomEffectsTheory.read_effects_def,
       venomEffectsTheory.empty_effects_def] >> metis_tac[])
 >- (irule cse_selected_assert_identity >> metis_tac[])
 >- (irule cse_selected_assert_identity >> metis_tac[]) >>
 irule cse_selected_copy_replay >> qexistsl [`inst`, `src`, `u`, `v`] >>
       simp[venomEffectsTheory.read_effects_def,
       venomEffectsTheory.empty_effects_def] >> metis_tac[]
QED

Theorem cse_zero_history_replay:
 wf_function fn /\ fn_inst_wf fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 cse_prefix ctx fn fuel0 s0 (pre ++ [CseStep m sb src u v] ++ post)
   (CseExec n ib s) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 get_instruction ib s.vs_inst_idx = SOME inst /\
 inst_wf src /\ inst_wf inst /\ src.inst_opcode = inst.inst_opcode /\
 ~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
 ~is_terminator inst.inst_opcode /\ ~avail_nonidempotent inst.inst_opcode /\
 ~has_conflicting_effects inst.inst_opcode /\
 src.inst_outputs = [] /\ inst.inst_outputs = [] /\
 step_inst m ctx src u = OK v /\ step_inst n ctx inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 EVERY (cse_event_survives (mk_expr (dfg_build_function fn) inst)) post ==>
 t = s
Proof
 strip_tac >>
 `~is_alloca_op src.inst_opcode` by
   (irule cseObservationPropsTheory.cse_prefix_step_allocation_free >>
    goal_assum (drule_at Any) >> simp[] >>
    qexistsl [`sb`, `m`, `u`, `v`] >> simp[]) >>
 `cse_prefix ctx fn fuel0 s0 (pre ++ [CseStep m sb src u v])
    (CseExec m sb (v with vs_inst_idx := SUC u.vs_inst_idx))` by
   (irule cseHistoryPropsTheory.cse_prefix_ordinary_extend >> simp[]) >>
 qpat_assum `step_inst m ctx src u = OK v`
   (mp_then Any mp_tac cseObservationPropsTheory.cse_step_read_observations) >>
 simp[] >> strip_tac >>
 `root_effects (mk_expr (dfg_build_function fn) inst) =
    read_effects inst.inst_opcode UNION write_effects inst.inst_opcode` by
   (simp[availExprDefsTheory.mk_expr_def, Once availExprDefsTheory.mk_operand_expr_def,
         availExprDefsTheory.canon_expr_def, availExprDefsTheory.root_effects_def] >>
    IF_CASES_TAC >> simp[availExprDefsTheory.root_effects_def]) >>
 qpat_assum `cse_prefix _ _ _ _ (pre ++ [CseStep m sb src u v]) _`
   (mp_then Any mp_tac cseObservationPropsTheory.cse_prefix_interval_observations) >>
 simp[cseHistoryPropsTheory.cse_phase_state_def, listTheory.APPEND_ASSOC] >>
 disch_then (qspecl_then [`post`, `CseExec n ib s`,
   `mk_expr (dfg_build_function fn) inst`] mp_tac) >>
 simp[cseHistoryPropsTheory.cse_phase_state_def,
      contract_storage_def] >> strip_tac >>
 irule cse_zero_two_state_replay >>
 qexistsl [`ctx`, `inst`, `m`, `n`, `src`, `u`, `v`] >>
 gvs[cseObservationPropsTheory.cse_fixed_observation_def,
     cseObservationPropsTheory.cse_effect_observation_def] >>
 rpt conj_tac >> rpt strip_tac >> gvs[] >>
 metis_tac[contract_storage_def, contract_transient_def]
QED

Theorem cse_zero_not_commutative:
 inst_wf inst /\ inst.inst_outputs = [] ==> ~is_commutative inst.inst_opcode
Proof
 Cases_on `inst.inst_opcode` >>
 simp[venomEffectsTheory.is_commutative_def] >>
 simp[venomWfTheory.inst_wf_def]
QED

(* Historical success rules out exceptional control results at a repeated
   zero-output instruction; ordinary errors remain allowed to the caller. *)
Theorem cse_zero_result_normal:
 inst_wf inst /\ src.inst_opcode = inst.inst_opcode /\
 ~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
 ~is_terminator inst.inst_opcode /\ ~avail_nonidempotent inst.inst_opcode /\
 ~has_conflicting_effects inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode /\
 inst.inst_outputs = [] /\
 step_inst m ctx src u = OK v /\ step_inst n ctx inst s = r /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands /\
 u.vs_call_ctx = s.vs_call_ctx /\
 (inst.inst_opcode = RETURNDATACOPY ==> u.vs_returndata = s.vs_returndata) ==>
 (?e. r = Error e) \/ (?t. r = OK t)
Proof
 strip_tac >>
 `inst.inst_opcode <> INVOKE` by
   (strip_tac >> gvs[availExprDefsTheory.avail_nonidempotent_def,
                    venomEffectsTheory.is_nonidempotent_def]) >>
 `src.inst_opcode <> INVOKE` by metis_tac[] >>
 gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
 Cases_on `inst.inst_opcode` >>
 gvs[venomInstTheory.is_pseudo_def, venomInstTheory.is_terminator_def,
     availExprDefsTheory.avail_nonidempotent_def,
     venomEffectsTheory.is_nonidempotent_def,
     venomEffectsTheory.has_conflicting_effects_def, venomInstTheory.is_alloca_op_def] >>
 qpat_x_assum `inst_wf inst` mp_tac >>
 pure_rewrite_tac[venomWfTheory.inst_wf_def] >> simp[] >> rpt strip_tac >>
 Cases_on `step_inst_base inst s` >> gvs[] >> cseReplayLib.selected_base_tac >>
 gvs[venomExecSemanticsTheory.exec_write2_def, AllCaseEqs()] >>
 gvs[venomStateTheory.eval_operands_def]
QED

Theorem cse_available_zero_replay:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 inst_wf inst /\ inst_wf src /\ inst.inst_outputs = [] /\ src.inst_outputs = [] /\
 FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx)
   (mk_expr (dfg_build_function fn) inst) = SOME xs /\ MEM src xs /\
 operand_ids_match
   (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
   (dfg_build_function fn) inst src ==>
 (?e. step_inst n ctx inst s = Error e) \/ step_inst n ctx inst s = OK s
Proof
 strip_tac >>
 drule_all cseHistoryPropsTheory.cse_prefix_exec_avail_interval >> strip_tac >>
 `MEM (CseStep m sb src u v) events` by gvs[listTheory.MEM_APPEND] >>
 drule_all cseHistoryPropsTheory.cse_prefix_event_provenance >> simp[] >> strip_tac >>
 `MEM src (fn_insts fn)` by
   (irule (cj 1 cseSourcePropsTheory.cse_avail_source_provenance) >>
    metis_tac[availExprDefsTheory.ae_lookup_inst_def]) >>
 `~is_pseudo src.inst_opcode /\ src.inst_opcode <> ASSIGN /\
  ~is_terminator src.inst_opcode /\ ~avail_nonidempotent src.inst_opcode /\
  ~has_conflicting_effects src.inst_opcode /\
  mk_expr (dfg_build_function fn) inst = mk_expr (dfg_build_function fn) src` by
   gvs[availExprProofsTheory.avail_source_birth_def] >>
 `inst.inst_opcode = src.inst_opcode` by
   metis_tac[cseReplayPropsTheory.mk_expr_root_inversion] >>
 `src.inst_opcode <> PHI /\ inst.inst_opcode <> PHI /\ LENGTH src.inst_outputs <= 1` by
   (simp[] >> strip_tac >> gvs[venomInstTheory.is_pseudo_def]) >>
 `~is_commutative inst.inst_opcode` by metis_tac[cse_zero_not_commutative] >>
 `MAP (\op. eval_operand op u) src.inst_operands =
    MAP (\op. eval_operand op s) inst.inst_operands` by
   (drule_all cse_final_source_interval_operand_alignment >> simp[]) >>
 `root_effects (mk_expr (dfg_build_function fn) inst) =
    read_effects inst.inst_opcode UNION write_effects inst.inst_opcode` by
   (simp[availExprDefsTheory.mk_expr_def, Once availExprDefsTheory.mk_operand_expr_def,
         availExprDefsTheory.canon_expr_def, availExprDefsTheory.root_effects_def] >>
    IF_CASES_TAC >> simp[availExprDefsTheory.root_effects_def]) >>
 `~is_alloca_op src.inst_opcode` by
   (irule cseObservationPropsTheory.cse_prefix_step_allocation_free >>
    goal_assum (drule_at Any) >> simp[] >>
    metis_tac[]) >>
 `cse_prefix ctx fn fuel0 s0 (pre ++ [CseStep m sb src u v])
    (CseExec m sb (v with vs_inst_idx := SUC u.vs_inst_idx))` by
   (irule cseHistoryPropsTheory.cse_prefix_ordinary_extend >> simp[]) >>
 qpat_assum `step_inst m ctx src u = OK v`
   (mp_then Any mp_tac cseObservationPropsTheory.cse_step_read_observations) >>
 simp[] >> strip_tac >>
 qpat_assum `cse_prefix _ _ _ _ (pre ++ [CseStep m sb src u v]) _`
   (mp_then Any mp_tac cseObservationPropsTheory.cse_prefix_interval_observations) >>
 simp[cseHistoryPropsTheory.cse_phase_state_def, listTheory.APPEND_ASSOC] >>
 disch_then (qspecl_then [`post`, `CseExec n bb s`,
   `mk_expr (dfg_build_function fn) inst`] mp_tac) >>
 simp[cseHistoryPropsTheory.cse_phase_state_def] >> strip_tac >>
 `u.vs_call_ctx = s.vs_call_ctx` by
   gvs[cseObservationPropsTheory.cse_fixed_observation_def] >>
 `(inst.inst_opcode = RETURNDATACOPY ==> u.vs_returndata = s.vs_returndata)` by
   (strip_tac >>
    gvs[venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
        venomEffectsTheory.empty_effects_def,
        cseObservationPropsTheory.cse_effect_observation_def]) >>
 `(?e. step_inst n ctx inst s = Error e) \/
  (?t. step_inst n ctx inst s = OK t)` by
   (metis_tac[cse_zero_result_normal]) >>
 gvs[] >>
 `t = s` by (irule cse_zero_history_replay >> simp[] >> metis_tac[]) >> simp[]
QED


Theorem cse_available_nop_replacement:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 inst_wf inst /\ inst_wf src /\ inst.inst_outputs = [] /\ src.inst_outputs = [] /\
 FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx)
   (mk_expr (dfg_build_function fn) inst) = SOME xs /\ MEM src xs /\
 operand_ids_match
   (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
   (dfg_build_function fn) inst src ==>
 (?e. step_inst n ctx inst s = Error e) \/
 lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
   (step_inst n ctx inst s) (step_inst n ctx (mk_nop_inst inst) s)
Proof
 strip_tac >> drule_all cse_available_zero_replay >> strip_tac >> simp[] >>
 `step_inst n ctx (mk_nop_inst inst) s = OK s` by
   (irule venomInstPropsTheory.step_nop_identity >>
    simp[passSharedDefsTheory.mk_nop_inst_def]) >>
 simp[stateEquivTheory.lift_result_def, stateEquivPropsTheory.state_equiv_refl]
QED
