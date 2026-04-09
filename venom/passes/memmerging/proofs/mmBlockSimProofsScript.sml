(*
 * Memmerging — Block / Function / Pass Simulation (Proofs)
 *
 * Builds on mmCorrectness (per-instruction simulation, invariants)
 * to prove block-level, function-level, and pass-level correctness.
 * Re-exported by mmBlockSimScript.sml.
 *)

Theory mmBlockSimProofs
Ancestors
  mmCorrectnessProofs mmTransform mmCopyEquiv passSimulationDefs passSimulationProofs
  crossBlockSimProofs crossBlockSimDefs passSimulationProps stateEquivProps
  stateEquiv stateEquivProofs venomExecSemantics execEquivParamProofs
  analysisSimProofsBase analysisSimDefs venomInstProofs venomWf
  dfgAnalysisProps dfgDefs
  venomInst venomState venomEffects pred_set finite_map
  list rich_list arithmetic words alist
  mmCopy mmScan passSharedField passSharedDefs execEquivProps

(* apply_groups_inst on non-terminators produces non-terminators/non-INVOKE *)
Theorem apply_groups_inst_non_term[local]:
  !mode nop_set rep_map inst.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (apply_groups_inst mode nop_set rep_map inst)
Proof
  rpt gen_tac >> strip_tac >>
  rw[apply_groups_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[EVERY_DEF] >>
  rpt CASE_TAC >> TRY (Cases_on `mode`) >>
  simp[EVERY_DEF, mk_nop_from_def, mk_bulk_copy_inst_def,
       mk_load_inst_def, mk_mstore_from_load_def,
       is_terminator_def, mode_copy_opcode_def, mode_load_opcode_def]
QED

(* Block sim for mode sub-pass.
   Uses flat_map_same_start_block_bridge (same pattern as memzero block proof). *)
Theorem mm_block_simulates_mode_proof[local]:
  !mode dfg bb fresh.
    mm_block_fresh_mode dfg mode bb SUBSET fresh /\
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb.bb_instructions /\
         is_terminator (EL k bb.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb.bb_instructions)) /\
    EVERY inst_wf bb.bb_instructions /\
    (!x. MEM (Var x) (LAST bb.bb_instructions).inst_operands ==>
       x NOTIN fresh) /\
    mode_block_wf dfg mode bb ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (transform_block_mode dfg mode bb) s)
Proof
  rpt gen_tac >> simp[mode_block_wf_def, LET_THM] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp[transform_block_mode_def, LET_THM] >>
  qabbrev_tac `nop_set = nop_ids_of_groups dfg mode bb.bb_instructions
    (scan_block dfg mode bb).ss_flushed` >>
  qabbrev_tac `rep_map = rep_map_of_groups bb.bb_instructions
    (scan_block dfg mode bb).ss_flushed` >>
  qabbrev_tac `non_terms = FILTER (\i. ~is_terminator i.inst_opcode)
    bb.bb_instructions` >>
  qabbrev_tac `term = LAST bb.bb_instructions` >>
  `bb.bb_instructions = non_terms ++ [term] /\
   is_terminator term.inst_opcode /\
   EVERY (\i. ~is_terminator i.inst_opcode) non_terms` by (
    imp_res_tac bb_wf_decompose_weak >>
    gvs[LET_THM, Abbr `non_terms`, Abbr `term`]) >>
  `EVERY (mode_inst_ok nop_set rep_map fresh) non_terms` by (
    first_x_assum (qspec_then `fresh` mp_tac) >> impl_tac >- fs[] >>
    simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
     non_terms` by (
    irule EVERY_MONOTONIC >>
    qexists_tac `mode_inst_ok nop_set rep_map fresh` >>
    rw[mode_inst_ok_def]) >>
  `apply_groups_inst mode nop_set rep_map term = [term]` by (
    simp[Abbr `term`, Abbr `nop_set`, Abbr `rep_map`,
         apply_groups_inst_def]) >>
  `!x. MEM (Var x) term.inst_operands ==> x NOTIN fresh` by
    fs[Abbr `term`] >>
  suspend "bridge"
QED

Resume mm_block_simulates_mode_proof[bridge]:
  SUBGOAL_THEN ``(term:instruction).inst_opcode <> INVOKE`` ASSUME_TAC
    THENL [CCONTR_TAC >> fs[is_terminator_def], ALL_TAC] >>
  SUBGOAL_THEN ``EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
     (FLAT (MAP (apply_groups_inst mode nop_set rep_map) non_terms))``
    ASSUME_TAC THENL [
    simp[EVERY_FLAT, EVERY_MAP] >>
    irule EVERY_MONOTONIC >>
    qexists_tac `\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` >>
    rw[apply_groups_inst_non_term], ALL_TAC] >>
  qspecl_then [`apply_groups_inst mode nop_set rep_map`,
    `non_terms`, `term`, `bb`, `fresh`, `\s. T`]
    mp_tac flat_map_same_start_block_bridge >>
  BETA_TAC >>
  (impl_tac >- (
    fs[] >> rpt strip_tac >>
    match_mp_tac mode_run_insts_lift_result >>
    (conj_tac >- fs[]) >> fs[])) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  BETA_TAC >> rw[]
QED

Finalise mm_block_simulates_mode_proof;

(* ===== Dload block simulation proof ===== *)

(* Dload invariant: after DLOAD executes, the source operand is still defined
   and the output var holds the computed dload value. *)
Definition dload_inv_def:
  dload_inv dfg dp s <=>
    ?off. eval_operand dp.dp_src s = SOME off /\
          lookup_var (dp_out_var dfg dp) s =
          SOME (word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w)))
End

(* Helper: the dload transform is a MAP, so transformed block has same length *)
Theorem transform_block_dload_length[local,simp]:
  !dfg bb. LENGTH (transform_block_dload dfg bb).bb_instructions =
           LENGTH bb.bb_instructions
Proof
  simp[transform_block_dload_def]
QED

(* Helper: EL of dload-transformed block *)
Theorem transform_block_dload_el[local]:
  !dfg bb i. i < LENGTH bb.bb_instructions ==>
    EL i (transform_block_dload dfg bb).bb_instructions =
    let inst = EL i bb.bb_instructions in
    let pairs = find_dload_pairs dfg bb.bb_instructions in
    let dload_nops = MAP (\dp. dp.dp_dload_id) pairs in
    let mstore_map = MAP (\dp. (dp.dp_mstore_id, dp)) pairs in
    if MEM inst.inst_id dload_nops then mk_nop_from inst
    else case ALOOKUP mstore_map inst.inst_id of
           SOME dp => mk_dloadbytes_inst inst dp.dp_src dp.dp_dst
         | NONE => inst
Proof
  simp[transform_block_dload_def, EL_MAP]
QED

(* Block sim for dload peephole sub-pass.
   WF preconditions:
   - inst_wf: all instructions are well-formed
   - dload_pair_wf: SSA property for dload output vars
   Both are trivially satisfied by the Venom pipeline (SSA-like IR). *)
(* Bridge: mstore with dload value on s1 = write_memory_with_expansion on s2
   when states are equiv. Combines dload_mstore_eq_dloadbytes with
   write_memory_with_expansion_preserves. *)
Theorem mstore_dload_write_mem_equiv[local]:
  !src dst fresh s1 s2.
    state_equiv fresh s1 s2 ==>
    state_equiv fresh
      (mstore dst (word_of_bytes T 0w
        (TAKE 32 (DROP src s1.vs_data_section ++ REPLICATE 32 0w))) s1)
      (write_memory_with_expansion dst
        (TAKE 32 (DROP src s1.vs_data_section ++ REPLICATE 32 0w)) s2)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[SIMP_RULE (srw_ss()) [LET_THM] dload_mstore_eq_dloadbytes] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

(* MSTORE with dload value = DLOADBYTES: produces state_equiv results.
   Preconditions:
   - dp.dp_dst operand doesn't reference fresh vars (address is shared)
   - dp.dp_src operand doesn't reference fresh vars (DLOAD source is shared) *)
Theorem dload_mstore_dloadbytes_equiv[local]:
  !dfg dp fresh fuel ctx s1 s2 inst.
    state_equiv fresh s1 s2 /\
    dp_out_var dfg dp IN fresh /\
    dload_inv dfg dp s1 /\
    inst.inst_opcode = MSTORE /\
    inst.inst_operands = [dp.dp_dst; Var (dp_out_var dfg dp)] /\
    (!x. dp.dp_dst = Var x ==> x NOTIN fresh) /\
    (!x. dp.dp_src = Var x ==> x NOTIN fresh) ==>
    (?e. step_inst fuel ctx inst s1 = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (mk_dloadbytes_inst inst dp.dp_src dp.dp_dst) s2)
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def,
    exec_write2_def, is_terminator_def] >>
  Cases_on `eval_operand dp.dp_dst s1` >> gvs[] >>
  gvs[dload_inv_def, eval_operand_def, lookup_var_def] >>
  simp[mk_dloadbytes_inst_def, step_inst_non_invoke, step_inst_base_def,
       is_terminator_def] >>
  `eval_operand dp.dp_dst s2 = SOME x`
    by (mp_tac (SPECL [``fresh:string set``, ``(dp:dload_pair).dp_dst``,
                        ``s1:venom_state``, ``s2:venom_state``]
                  eval_operand_equiv) >> simp[]) >>
  `eval_operand dp.dp_src s2 = SOME off`
    by (mp_tac (SPECL [``fresh:string set``, ``(dp:dload_pair).dp_src``,
                        ``s1:venom_state``, ``s2:venom_state``]
                  eval_operand_equiv) >> simp[]) >>
  simp[eval_operand_def] >>
  `s2.vs_data_section = s1.vs_data_section`
    by fs[state_equiv_def, execution_equiv_def] >>
  gvs[lift_result_def, w2n_def, dimword_def] >>
  irule mstore_dload_write_mem_equiv >> simp[]
QED

(* NOP'd DLOAD: original DLOAD writes fresh var, NOP is identity.
   The source operand must not reference the output variable (SSA property:
   the DLOAD reads from a pre-existing variable, not its own output). *)
Theorem dload_nop_sim[local]:
  !dfg dp fresh fuel ctx s1 s2 inst.
    state_equiv fresh s1 s2 /\
    dp_out_var dfg dp IN fresh /\
    inst.inst_opcode = DLOAD /\
    inst.inst_operands = [dp.dp_src] /\
    inst.inst_outputs = [dp_out_var dfg dp] /\
    (!x. dp.dp_src = Var x ==> x <> dp_out_var dfg dp) ==>
    (?e. step_inst fuel ctx inst s1 = Error e) \/
    (lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (mk_nop_from inst) s2) /\
     !s1'. step_inst fuel ctx inst s1 = OK s1' ==>
       dload_inv dfg dp s1')
Proof
  rpt strip_tac >> gvs[] >>
  `inst.inst_opcode <> INVOKE` by simp[is_terminator_def] >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def] >>
  Cases_on `eval_operand dp.dp_src s1` >> gvs[] >>
  simp[step_inst_nop, lift_result_def] >> conj_tac
  >- (fs[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE] >> rw[] >> metis_tac[IN_DEF])
  >- (simp[dload_inv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      Cases_on `dp.dp_src` >>
      gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE])
QED

(* dload_inv preservation through a non-output step *)
Theorem dload_inv_preserved[local]:
  !dfg dp fuel ctx inst s s'.
    dload_inv dfg dp s /\
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~MEM (dp_out_var dfg dp) inst.inst_outputs /\
    (!x. dp.dp_src = Var x ==> ~MEM x inst.inst_outputs) ==>
    dload_inv dfg dp s'
Proof
  rw[dload_inv_def] >>
  `lookup_var (dp_out_var dfg dp) s' = lookup_var (dp_out_var dfg dp) s`
    by (irule step_preserves_non_output_vars >> metis_tac[]) >>
  `s'.vs_data_section = s.vs_data_section`
    by (irule step_preserves_data_section >> metis_tac[]) >>
  `s'.vs_labels = s.vs_labels`
    by (irule step_preserves_labels >> metis_tac[]) >>
  qexists_tac `off` >> simp[] >>
  Cases_on `dp.dp_src` >> gvs[eval_operand_def] >>
  `lookup_var s'' s' = lookup_var s'' s`
    by (irule step_preserves_non_output_vars >> metis_tac[]) >> gvs[]
QED

(* dload_inv is independent of vs_inst_idx *)
Theorem dload_inv_inst_idx[local,simp]:
  !dfg dp s n. dload_inv dfg dp (s with vs_inst_idx := n) <=> dload_inv dfg dp s
Proof
  rw[dload_inv_def] >> eq_tac >> strip_tac >> qexists_tac `off` >> gvs[] >>
  Cases_on `dp.dp_src` >> gvs[eval_operand_def, lookup_var_def]
QED

(* dload_inv is preserved by any instruction strictly between the DLOAD
   and MSTORE of pair dp. Combines dload_inv_preserved with dload_pair_wf
   SSA clauses. Reusable across all three cases of mm_block_dload_ind.
   Caller provides di < idx < mi bounds (always available from IH). *)
Theorem unchanged_preserves_dload_inv[local]:
  !dfg dp insts di mi idx fuel ctx s s'.
    dload_pair_wf dfg dp insts /\
    dload_inv dfg dp s /\
    step_inst fuel ctx (EL idx insts) s = OK s' /\
    ~is_terminator (EL idx insts).inst_opcode /\
    idx < LENGTH insts /\
    di < LENGTH insts /\ mi < LENGTH insts /\
    (EL di insts).inst_id = dp.dp_dload_id /\
    (EL mi insts).inst_id = dp.dp_mstore_id /\
    di < idx /\ idx < mi ==>
    dload_inv dfg dp s'
Proof
  rpt strip_tac >>
  fs[dload_pair_wf_def] >>
  (* Reconcile indices: di' = di and mi' = mi by ALL_DISTINCT *)
  `di' = di` by (
    irule all_distinct_inst_id_idx >>
    qexists_tac `insts` >> gvs[]) >>
  `mi' = mi` by (
    irule all_distinct_inst_id_idx >>
    qexists_tac `insts` >> gvs[]) >>
  gvs[] >>
  qspecl_then [`dfg`, `dp`, `fuel`, `ctx`, `EL idx insts`, `s`, `s'`]
    mp_tac dload_inv_preserved >> simp[] >>
  (impl_tac >- (
    rpt conj_tac
    >- ((* ~MEM dp_out_var in inst.inst_outputs *)
        first_x_assum irule >> decide_tac)
    >> (* dp.dp_src = Var x ==> ~MEM x inst.inst_outputs *)
    rpt strip_tac >>
    first_x_assum (qspecl_then [`x`, `idx`] mp_tac) >> simp[])) >>
  simp[]
QED

(* Key property: mm_block_fresh_dload elements are exactly dp_out_vars.
   With DFG consistency in dload_pair_wf, the fresh set variables are
   exactly the output variables of DLOAD instructions in pairs. *)
Theorem mm_block_fresh_dload_is_dp_out[local]:
  !dfg bb x.
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    x IN mm_block_fresh_dload dfg bb ==>
    ?dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) /\
         x = dp_out_var dfg dp
Proof
  rw[mm_block_fresh_dload_def, LET_THM] >>
  qexists_tac `dp` >> simp[] >>
  fs[EVERY_MEM] >>
  first_x_assum drule >> rw[dload_pair_wf_def] >>
  (* x is in dload_inst.inst_outputs = [dp_out_var dfg dp] *)
  gvs[MEM]
QED

(* dp_src and dp_dst variables are not in the fresh set.
   Key for proving dload_mstore_dloadbytes_equiv preconditions. *)
Theorem dp_src_dst_not_fresh[local]:
  !dfg bb dp.
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
    (!x. dp.dp_src = Var x ==> x NOTIN mm_block_fresh_dload dfg bb) /\
    (!x. dp.dp_dst = Var x ==> x NOTIN mm_block_fresh_dload dfg bb)
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `?dp'. MEM dp' (find_dload_pairs dfg bb.bb_instructions) /\
         x = dp_out_var dfg dp'` by metis_tac[mm_block_fresh_dload_is_dp_out] >>
  gvs[] >>
  `dload_pair_wf dfg dp bb.bb_instructions` by fs[EVERY_MEM] >>
  `dload_pair_wf dfg dp' bb.bb_instructions` by fs[EVERY_MEM] >>
  (* Expand dp' wf to get single-use clause *)
  qpat_x_assum `dload_pair_wf dfg dp' _`
    (strip_assume_tac o REWRITE_RULE[dload_pair_wf_def]) >>
  (* Expand dp wf to get src/dst clauses *)
  qpat_x_assum `dload_pair_wf dfg dp _`
    (strip_assume_tac o REWRITE_RULE[dload_pair_wf_def]) >>
  (* dp' single-use: Var(dp_out_var dfg dp') only at mi *)
  (* dp.dp_src or dp.dp_dst = Var(dp_out_var dfg dp') *)
  (* dp_src in operands of EL di' (DLOAD for dp),
     dp_dst in operands of EL mi' (MSTORE for dp) *)
  (* For dp_src case: di' must = mi. But opcode DLOAD vs MSTORE *)
  (* For dp_dst case: mi' must = mi. Same inst => dp_out_var dp = dp_out_var dp'
     => dp.dp_dst = Var(dp_out_var dp) => contradicts dp's clause *)
  TRY (
    `di' = mi` by (
      CCONTR_TAC >>
      qpat_x_assum `!j. j < _ /\ j <> mi ==> ~MEM (Var _) _`
        (qspec_then `di'` mp_tac) >> simp[MEM]) >>
    gvs[]) >>
  TRY (
    `mi' = mi` by (
      CCONTR_TAC >>
      qpat_x_assum `!j. j < _ /\ j <> mi ==> ~MEM (Var _) _`
        (qspec_then `mi'` mp_tac) >> simp[MEM]) >>
    gvs[MEM] >> metis_tac[])
QED

(* For an unchanged instruction (not DLOAD or MSTORE of any pair),
   operand variables are not dp_out_var of any pair. *)
Theorem unchanged_operands_not_fresh[local]:
  !dfg insts idx x dp0.
    EVERY (\dp'. dload_pair_wf dfg dp' insts)
      (find_dload_pairs dfg insts) /\
    MEM dp0 (find_dload_pairs dfg insts) /\
    idx < LENGTH insts /\
    ~MEM (EL idx insts).inst_id
      (MAP (\dp'. dp'.dp_dload_id) (find_dload_pairs dfg insts)) /\
    ALOOKUP (MAP (\dp'. (dp'.dp_mstore_id, dp'))
                  (find_dload_pairs dfg insts))
      (EL idx insts).inst_id = NONE /\
    MEM (Var x) (EL idx insts).inst_operands ==>
    x <> dp_out_var dfg dp0
Proof
  rw[] >>
  `dload_pair_wf dfg dp0 insts` by fs[EVERY_MEM] >>
  pop_assum mp_tac >> simp[dload_pair_wf_def] >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  (* Now have x = dp_out_var dfg dp0 in assumptions *)
  (* idx <> mi: if idx=mi then ALOOKUP finds dp0, contradicting NONE *)
  `idx <> mi` by (
    strip_tac >>
    fs[ALOOKUP_NONE, MEM_MAP] >>
    qexists_tac `dp0` >> simp[]
  ) >>
  (* single-use: Var(dp_out) not in operands at idx, since idx <> mi *)
  first_x_assum (qspec_then `idx` mp_tac) >>
  simp[]
QED

(* Operand agreement for unchanged instructions:
   variables in operands of an unchanged instruction (not DLOAD-NOP, not MSTORE)
   are not in the fresh set, so lookup_var agrees under state_equiv. *)
Theorem unchanged_inst_operand_agreement[local]:
  !dfg bb idx s1 s2.
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
    idx < LENGTH bb.bb_instructions /\
    ~MEM (EL idx bb.bb_instructions).inst_id
      (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions)) /\
    ALOOKUP (MAP (\dp. (dp.dp_mstore_id, dp))
                  (find_dload_pairs dfg bb.bb_instructions))
      (EL idx bb.bb_instructions).inst_id = NONE ==>
    !x. MEM (Var x) (EL idx bb.bb_instructions).inst_operands ==>
        lookup_var x s1 = lookup_var x s2
Proof
  rpt strip_tac >>
  `x NOTIN mm_block_fresh_dload dfg bb` by (
    CCONTR_TAC >> fs[] >>
    drule_all mm_block_fresh_dload_is_dp_out >> strip_tac >>
    gvs[] >>
    metis_tac[unchanged_operands_not_fresh]
  ) >>
  fs[state_equiv_def, execution_equiv_def]
QED

(* Chaining lemma: if one instruction step gives lift_result, and the IH
   handles the continuation (for non-terminator OK), then the whole exec_block
   step is correct. Reusable across all 3 cases of the dload induction.
   Requires ~is_terminator for both instructions. For terminators,
   use exec_block_step_chain_term instead. *)
Theorem exec_block_step_chain[local]:
  !R R' inst1 inst2 bb1 bb2 fuel ctx s1 s2.
    s1.vs_inst_idx < LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    EL s1.vs_inst_idx bb1.bb_instructions = inst1 /\
    EL s1.vs_inst_idx bb2.bb_instructions = inst2 /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    lift_result R R' R' (step_inst fuel ctx inst1 s1) (step_inst fuel ctx inst2 s2) /\
    (!s1' s2'. step_inst fuel ctx inst1 s1 = OK s1' /\ R s1' s2' ==>
      (?e. exec_block fuel ctx bb1 (s1' with vs_inst_idx := SUC s1.vs_inst_idx) = Error e) \/
      lift_result R R' R'
        (exec_block fuel ctx bb1 (s1' with vs_inst_idx := SUC s1.vs_inst_idx))
        (exec_block fuel ctx bb2 (s2' with vs_inst_idx := SUC s1.vs_inst_idx)))
    ==>
    (?e. exec_block fuel ctx bb1 s1 = Error e) \/
    lift_result R R' R' (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx inst1 s1` >>
  Cases_on `step_inst fuel ctx inst2 s2` >>
  gvs[lift_result_def] >>
  simp[lift_result_def] >>
  first_x_assum (qspecl_then [`v`, `v'`] mp_tac) >> simp[]
QED

(* Variant: step-level sim may produce Error or lift_result.
   Error on step => Error on exec_block. OK => delegate to exec_block_step_chain. *)
Theorem exec_block_step_chain_err[local]:
  !R R' inst1 inst2 bb1 bb2 fuel ctx s1 s2.
    s1.vs_inst_idx < LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    EL s1.vs_inst_idx bb1.bb_instructions = inst1 /\
    EL s1.vs_inst_idx bb2.bb_instructions = inst2 /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ((?e. step_inst fuel ctx inst1 s1 = Error e) \/
     lift_result R R' R' (step_inst fuel ctx inst1 s1) (step_inst fuel ctx inst2 s2)) /\
    (!s1' s2'. step_inst fuel ctx inst1 s1 = OK s1' /\ R s1' s2' ==>
      (?e. exec_block fuel ctx bb1 (s1' with vs_inst_idx := SUC s1.vs_inst_idx) = Error e) \/
      lift_result R R' R'
        (exec_block fuel ctx bb1 (s1' with vs_inst_idx := SUC s1.vs_inst_idx))
        (exec_block fuel ctx bb2 (s2' with vs_inst_idx := SUC s1.vs_inst_idx)))
    ==>
    (?e. exec_block fuel ctx bb1 s1 = Error e) \/
    lift_result R R' R' (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac
  >- ((* Error on step => Error on exec_block *)
      DISJ1_TAC >> qexists_tac `e` >>
      ONCE_REWRITE_TAC[exec_block_def] >>
      simp[get_instruction_def])
  >> (* lift_result on step => delegate to exec_block_step_chain *)
  irule exec_block_step_chain >> simp[] >>
  MAP_EVERY qexists_tac [`inst1`, `inst2`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* Terminator version: same instruction, no IH needed. *)
Theorem exec_block_step_chain_term[local]:
  !R R' inst bb1 bb2 fuel ctx s1 s2.
    s1.vs_inst_idx < LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    EL s1.vs_inst_idx bb1.bb_instructions = inst /\
    EL s1.vs_inst_idx bb2.bb_instructions = inst /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    is_terminator inst.inst_opcode /\
    lift_result R R' R' (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2) /\
    (!a b. R a b ==> (a.vs_halted <=> b.vs_halted)) /\
    (!a b. R a b ==> R' a b) ==>
    (?e. exec_block fuel ctx bb1 s1 = Error e) \/
    lift_result R R' R' (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[lift_result_def] >>
  Cases_on `v.vs_halted` >> Cases_on `v'.vs_halted` >>
  gvs[lift_result_def] >> res_tac >> gvs[]
QED

(* Step simulation for an unchanged instruction (not a NOP'd DLOAD, not an MSTORE
   paired with a DLOAD). The instruction is the same in both original and transformed
   blocks, so step_inst_preserves_R_proof applies directly. *)
Theorem unchanged_inst_step_sim[local]:
  !dfg bb idx fuel ctx s1 s2.
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
    idx < LENGTH bb.bb_instructions /\
    ~MEM (EL idx bb.bb_instructions).inst_id
      (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions)) /\
    ALOOKUP (MAP (\dp. (dp.dp_mstore_id, dp))
                  (find_dload_pairs dfg bb.bb_instructions))
      (EL idx bb.bb_instructions).inst_id = NONE ==>
    lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
      (step_inst fuel ctx (EL idx bb.bb_instructions) s1)
      (step_inst fuel ctx (EL idx bb.bb_instructions) s2)
Proof
  rpt strip_tac >>
  irule step_inst_preserves_R_proof >>
  simp[] >> rpt strip_tac
  >- (irule unchanged_inst_operand_agreement >> metis_tac[])
  >> MATCH_ACCEPT_TAC state_equiv_execution_equiv_valid_state_rel_proof
QED

(* If two dload pairs share the same DLOAD id and both are well-formed,
   dload_inv for one implies dload_inv for the other — they reference
   the same DLOAD instruction so have same source operand and output var. *)
Theorem dload_inv_same_dload_id[local]:
  !dfg dp dp0 insts s.
    dp.dp_dload_id = dp0.dp_dload_id /\
    dload_pair_wf dfg dp insts /\
    dload_pair_wf dfg dp0 insts /\
    dload_inv dfg dp0 s ==>
    dload_inv dfg dp s
Proof
  rpt strip_tac >>
  fs[dload_pair_wf_def] >>
  `di = di'` by (
    irule all_distinct_inst_id_idx >>
    qexists_tac `insts` >> gvs[]) >>
  gvs[dload_inv_def]
QED

(* After stepping at index idx, dload_inv is preserved for all pairs.
   Bundles the di' < idx (old invariant + preservation) and di' = idx
   (case-specific) branches. Caller provides the di' = idx case. *)
Theorem dload_inv_after_step[local]:
  !dfg bb idx fuel ctx s1 s1'.
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s1 = OK s1' /\
    (* Old dload_inv: for all pairs with di' < idx and idx <= mi' *)
    (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
      !di' mi'. di' < LENGTH bb.bb_instructions /\ mi' < LENGTH bb.bb_instructions /\
        di' < mi' /\
        (EL di' bb.bb_instructions).inst_id = dp.dp_dload_id /\
        (EL mi' bb.bb_instructions).inst_id = dp.dp_mstore_id /\
        di' < idx /\ idx <= mi' ==>
        dload_inv dfg dp s1) /\
    (* di' = idx case: provided by caller *)
    (!dp di'. MEM dp (find_dload_pairs dfg bb.bb_instructions) /\
      dload_pair_wf dfg dp bb.bb_instructions /\
      di' < LENGTH bb.bb_instructions /\
      (EL di' bb.bb_instructions).inst_id = dp.dp_dload_id /\
      di' = idx ==>
      dload_inv dfg dp s1') ==>
    (* Conclusion: dload_inv for all pairs with di' < SUC idx *)
    !dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
      !di' mi'. di' < LENGTH bb.bb_instructions /\ mi' < LENGTH bb.bb_instructions /\
        di' < mi' /\
        (EL di' bb.bb_instructions).inst_id = dp.dp_dload_id /\
        (EL mi' bb.bb_instructions).inst_id = dp.dp_mstore_id /\
        di' < SUC idx /\ SUC idx <= mi' ==>
        dload_inv dfg dp s1'
Proof
  rpt strip_tac >>
  `dload_pair_wf dfg dp bb.bb_instructions` by fs[EVERY_MEM] >>
  `(di':num) < idx \/ di' = idx` by decide_tac
  >- ((* di' < idx: old invariant + preservation *)
      `dload_inv dfg dp s1` by (
        qpat_x_assum `!dp. MEM dp _ ==> !di' mi'. _`
          (qspec_then `dp` mp_tac) >> simp[] >>
        disch_then match_mp_tac >>
        MAP_EVERY qexists_tac [`di':num`, `mi':num`] >> decide_tac) >>
      qspecl_then [`dfg`, `dp`, `bb.bb_instructions`,
                   `di':num`, `mi':num`, `idx:num`,
                   `fuel`, `ctx:venom_context`, `s1`, `s1'`]
        mp_tac unchanged_preserves_dload_inv >>
      simp[] >> (impl_tac >- decide_tac) >> simp[])
  >> (* di' = idx: delegate to caller-provided proof *)
  first_x_assum irule >> gvs[]
QED

(* Combine step-level Error∨lift_result with IH application for
   non-terminator cases in the dload induction. Takes everything
   needed and produces the full block-level Error∨lift_result.
   Internalizes exec_block_step_chain_err + IH instantiation. *)
Theorem dload_ind_step_case[local]:
  !dfg bb n fuel ctx idx s1 s2 inst1 inst2.
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    s1.vs_inst_idx = idx /\ s2.vs_inst_idx = idx /\
    idx < LENGTH bb.bb_instructions /\
    SUC n = LENGTH bb.bb_instructions - idx /\
    state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
    EL idx bb.bb_instructions = inst1 /\
    EL idx (transform_block_dload dfg bb).bb_instructions = inst2 /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ((?e. step_inst fuel ctx inst1 s1 = Error e) \/
     lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
       (step_inst fuel ctx inst1 s1) (step_inst fuel ctx inst2 s2)) /\
    (* dload_inv preservation at SUC idx — caller proves this *)
    (!s1'. step_inst fuel ctx inst1 s1 = OK s1' ==>
      !dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
        !di' mi'. di' < LENGTH bb.bb_instructions /\
          mi' < LENGTH bb.bb_instructions /\ di' < mi' /\
          (EL di' bb.bb_instructions).inst_id = dp.dp_dload_id /\
          (EL mi' bb.bb_instructions).inst_id = dp.dp_mstore_id /\
          di' < SUC idx /\ SUC idx <= mi' ==>
          dload_inv dfg dp s1') /\
    (* IH *)
    (!fuel ctx s1 s2.
      n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
      state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
      s1.vs_inst_idx <= LENGTH bb.bb_instructions /\
      (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
        !di mi. di < LENGTH bb.bb_instructions /\
          mi < LENGTH bb.bb_instructions /\ di < mi /\
          (EL di bb.bb_instructions).inst_id = dp.dp_dload_id /\
          (EL mi bb.bb_instructions).inst_id = dp.dp_mstore_id /\
          di < s1.vs_inst_idx /\ s1.vs_inst_idx <= mi ==>
          dload_inv dfg dp s1) ==>
      (?e. exec_block fuel ctx bb s1 = Error e) \/
      lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx (transform_block_dload dfg bb) s2)) ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (transform_block_dload dfg bb) s2)
Proof
  rpt strip_tac >>
  irule exec_block_step_chain_err >> simp[] >>
  rpt strip_tac >>
  (* Apply IH — use underscores to avoid bound/free variable clash *)
  first_x_assum
    (qspecl_then [`fuel`, `ctx`,
                  `s1' with vs_inst_idx := SUC idx`,
                  `s2' with vs_inst_idx := SUC idx`] mp_tac) >>
  simp[] >>
  (impl_tac >- (
    gvs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
    metis_tac[])) >>
  simp[]  
QED

(* Callback for Case 3: dload_inv preservation after MSTORE step *)
Theorem dload_inv_callback_mstore[local]:
  !dfg bb fuel ctx s1 s1' dp0 di mi mstore_inst.
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    (EL mi bb.bb_instructions) = mstore_inst /\
    mstore_inst.inst_opcode = MSTORE /\
    mstore_inst.inst_id = dp0.dp_mstore_id /\
    dload_pair_wf dfg dp0 bb.bb_instructions /\
    di < mi /\ mi < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL mi bb.bb_instructions) s1 = OK s1' /\
    (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
      !di' mi'. di' < LENGTH bb.bb_instructions /\
        mi' < LENGTH bb.bb_instructions /\ di' < mi' /\
        (EL di' bb.bb_instructions).inst_id = dp.dp_dload_id /\
        (EL mi' bb.bb_instructions).inst_id = dp.dp_mstore_id /\
        di' < mi /\ mi <= mi' ==>
        dload_inv dfg dp s1) ==>
    !dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
      !di' mi'. di' < LENGTH bb.bb_instructions /\
        mi' < LENGTH bb.bb_instructions /\ di' < mi' /\
        (EL di' bb.bb_instructions).inst_id = dp.dp_dload_id /\
        (EL mi' bb.bb_instructions).inst_id = dp.dp_mstore_id /\
        di' < SUC mi /\ SUC mi <= mi' ==>
        dload_inv dfg dp s1'
Proof
  rpt strip_tac >>
  `(di':num) < mi \/ di' = mi` by decide_tac
  >- ((* di' < mi: old invariant preserved *)
      `dload_inv dfg dp s1` by (
        first_x_assum (qspec_then `dp` mp_tac) >> simp[] >>
        disch_then match_mp_tac >>
        MAP_EVERY qexists_tac [`di':num`, `mi':num`] >>
        decide_tac) >>
      qspecl_then [`dfg`, `dp`, `bb.bb_instructions`,
                   `di':num`, `mi':num`, `mi:num`,
                   `fuel`, `ctx:venom_context`, `s1`, `s1'`]
        mp_tac unchanged_preserves_dload_inv >>
      simp[is_terminator_def] >> fs[EVERY_MEM] >> decide_tac)
  >> (* di' = mi: contradiction — inst at mi is MSTORE, not DLOAD *)
  `F` suffices_by simp[] >>
  `dload_pair_wf dfg dp bb.bb_instructions` by fs[EVERY_MEM] >>
  qpat_x_assum `dload_pair_wf dfg dp _`
    (strip_assume_tac o REWRITE_RULE[dload_pair_wf_def]) >>
  `mi = di''` by (
    irule all_distinct_inst_id_idx >>
    qexists_tac `bb.bb_instructions` >> gvs[]) >>
  gvs[]
QED

(* Callback for Case 1: dload_inv preservation after DLOAD step.
   Unlike Case 3 (MSTORE), di' = di is NOT a contradiction — the instruction
   IS a DLOAD. We use dload_inv_same_dload_id to transfer invariant. *)
Theorem dload_inv_callback_dload[local]:
  !dfg bb fuel ctx s1 s1' dp0 di.
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    (EL di bb.bb_instructions).inst_opcode = DLOAD /\
    (EL di bb.bb_instructions).inst_id = dp0.dp_dload_id /\
    dload_pair_wf dfg dp0 bb.bb_instructions /\
    di < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL di bb.bb_instructions) s1 = OK s1' /\
    (!s1'. step_inst fuel ctx (EL di bb.bb_instructions) s1 = OK s1' ==>
       dload_inv dfg dp0 s1') /\
    (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
      !di' mi'. di' < LENGTH bb.bb_instructions /\
        mi' < LENGTH bb.bb_instructions /\ di' < mi' /\
        (EL di' bb.bb_instructions).inst_id = dp.dp_dload_id /\
        (EL mi' bb.bb_instructions).inst_id = dp.dp_mstore_id /\
        di' < di /\ di <= mi' ==>
        dload_inv dfg dp s1) ==>
    !dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
      !di' mi'. di' < LENGTH bb.bb_instructions /\
        mi' < LENGTH bb.bb_instructions /\ di' < mi' /\
        (EL di' bb.bb_instructions).inst_id = dp.dp_dload_id /\
        (EL mi' bb.bb_instructions).inst_id = dp.dp_mstore_id /\
        di' < SUC di /\ SUC di <= mi' ==>
        dload_inv dfg dp s1'
Proof
  rpt strip_tac >>
  `(di':num) < di \/ di' = di` by decide_tac
  >- ((* di' < di: old invariant preserved *)
      `dload_inv dfg dp s1` by (
        first_x_assum (qspec_then `dp` mp_tac) >> simp[] >>
        disch_then match_mp_tac >>
        MAP_EVERY qexists_tac [`di':num`, `mi':num`] >>
        decide_tac) >>
      qspecl_then [`dfg`, `dp`, `bb.bb_instructions`,
                   `di':num`, `mi':num`, `di:num`,
                   `fuel`, `ctx:venom_context`, `s1`, `s1'`]
        mp_tac unchanged_preserves_dload_inv >>
      simp[is_terminator_def] >> fs[EVERY_MEM] >> decide_tac)
  >> (* di' = di: same DLOAD id — transfer invariant from dp0 *)
  `di' = di` by decide_tac >>
  `dp.dp_dload_id = dp0.dp_dload_id` by fs[] >>
  `dload_inv dfg dp0 s1'` by gvs[] >>
  `dload_pair_wf dfg dp bb.bb_instructions` by fs[EVERY_MEM] >>
  irule dload_inv_same_dload_id >>
  qexists_tac `dp0` >>
  qexists_tac `bb.bb_instructions` >> gvs[]
QED

(* Case 1 of dload induction: NOP'd DLOAD.
   Parallel to dload_ind_case3 — uses dload_nop_sim for step sim
   and dload_inv_callback_dload for invariant preservation. *)
Theorem dload_ind_case1[local]:
  !dfg bb n fuel ctx s1 s2 dp0.
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    MEM dp0 (find_dload_pairs dfg bb.bb_instructions) /\
    state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
    s1.vs_inst_idx < LENGTH bb.bb_instructions /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    SUC n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    MEM (EL s1.vs_inst_idx bb.bb_instructions).inst_id
      (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions)) /\
    (EL s1.vs_inst_idx bb.bb_instructions).inst_id = dp0.dp_dload_id /\
    dload_pair_wf dfg dp0 bb.bb_instructions /\
    (* IH *)
    (!fuel ctx s1 s2.
      n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
      state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
      s1.vs_inst_idx <= LENGTH bb.bb_instructions /\
      (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
        !di mi. di < LENGTH bb.bb_instructions /\
          mi < LENGTH bb.bb_instructions /\ di < mi /\
          (EL di bb.bb_instructions).inst_id = dp.dp_dload_id /\
          (EL mi bb.bb_instructions).inst_id = dp.dp_mstore_id /\
          di < s1.vs_inst_idx /\ s1.vs_inst_idx <= mi ==>
          dload_inv dfg dp s1) ==>
      (?e. exec_block fuel ctx bb s1 = Error e) \/
      lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx (transform_block_dload dfg bb) s2)) /\
    (* dload_inv invariant *)
    (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
      !di mi. di < LENGTH bb.bb_instructions /\
        mi < LENGTH bb.bb_instructions /\ di < mi /\
        (EL di bb.bb_instructions).inst_id = dp.dp_dload_id /\
        (EL mi bb.bb_instructions).inst_id = dp.dp_mstore_id /\
        di < s1.vs_inst_idx /\ s1.vs_inst_idx <= mi ==>
        dload_inv dfg dp s1) ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (transform_block_dload dfg bb) s2)
Proof
  rpt strip_tac >>
  qpat_x_assum `dload_pair_wf dfg dp0 _`
    (strip_assume_tac o REWRITE_RULE[dload_pair_wf_def]) >>
  rename1 `EL dload_idx bb.bb_instructions = dload_inst` >>
  rename1 `EL mstore_idx bb.bb_instructions = mstore_inst` >>
  `s1.vs_inst_idx = dload_idx` by (
    irule all_distinct_inst_id_idx >>
    qexists_tac `bb.bb_instructions` >> gvs[]) >>
  fs[] >>
  `dp_out_var dfg dp0 IN mm_block_fresh_dload dfg bb` by (
    simp[mm_block_fresh_dload_def, LET_THM, MEM_MAP] >>
    qexists_tac `dp0` >> qexists_tac `dload_inst` >> gvs[MEM]) >>
  (* Get step sim + dload_inv from dload_nop_sim *)
  qspecl_then [`dfg`, `dp0`, `mm_block_fresh_dload dfg bb`,
               `fuel`, `ctx:venom_context`, `s1`, `s2`, `dload_inst`]
    mp_tac dload_nop_sim >>
  (impl_tac >- (gvs[] >> metis_tac[])) >>
  disch_tac >>
  (* dload_nop_sim gives: Error \/ (lift_result /\ dload_inv).
     Extract both parts. *)
  `!s1'. step_inst fuel ctx dload_inst s1 = OK s1' ==>
    dload_inv dfg dp0 s1'` by (
      rpt strip_tac >>
      first_x_assum strip_assume_tac >> gvs[] >> fs[]) >>
  `(?e. step_inst fuel ctx dload_inst s1 = Error e) \/
   lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
     (step_inst fuel ctx dload_inst s1)
     (step_inst fuel ctx (mk_nop_from dload_inst) s2)`
    by (first_x_assum strip_assume_tac >> gvs[] >> DISJ2_TAC >> fs[]) >>
  `~is_terminator dload_inst.inst_opcode`
    by (gvs[] >> simp[is_terminator_def]) >>
  (`EL dload_idx (transform_block_dload dfg bb).bb_instructions =
    mk_nop_from dload_inst` by (
      simp[transform_block_dload_el, LET_THM] >>
      simp[MEM_MAP] >> qexists_tac `dp0` >> gvs[])) >>
  (`~is_terminator (mk_nop_from dload_inst).inst_opcode`
    by simp[mk_nop_from_def, is_terminator_def]) >>
  (* Apply dload_ind_step_case *)
  qspecl_then [`dfg`, `bb`, `n`, `fuel:num`, `ctx:venom_context`,
               `dload_idx:num`, `s1`, `s2`,
               `dload_inst`,
               `EL (dload_idx:num) (transform_block_dload dfg bb).bb_instructions`]
    mp_tac dload_ind_step_case >>
  disch_then match_mp_tac >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[is_terminator_def, mk_nop_from_def]) >>
  TRY (fs[mk_nop_from_def]) >>
  (* Callback: dload_inv preserved after DLOAD step *)
  strip_tac >> strip_tac >>
  match_mp_tac dload_inv_callback_dload >>
  MAP_EVERY qexists_tac
    [`fuel`, `ctx:venom_context`, `s1`, `dp0`] >>
  rpt conj_tac >> gvs[EVERY_MEM]
QED

(* Case 3 of dload induction: MSTORE -> DLOADBYTES.
   Statement avoids di/mi/dload_inst/mstore_inst as universals to prevent
   batch parser variable name clashes with IH's bound ∀di mi. (L215).
   Instead takes dload_pair_wf as hypothesis and expands internally. *)
Theorem dload_ind_case3[local]:
  !dfg bb n fuel ctx s1 s2 dp0.
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    MEM dp0 (find_dload_pairs dfg bb.bb_instructions) /\
    state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
    s1.vs_inst_idx < LENGTH bb.bb_instructions /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    SUC n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    ~MEM (EL s1.vs_inst_idx bb.bb_instructions).inst_id
      (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions)) /\
    ALOOKUP (MAP (\dp. (dp.dp_mstore_id, dp))
                  (find_dload_pairs dfg bb.bb_instructions))
      (EL s1.vs_inst_idx bb.bb_instructions).inst_id = SOME dp0 /\
    dload_pair_wf dfg dp0 bb.bb_instructions /\
    (* IH *)
    (!fuel ctx s1 s2.
      n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
      state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
      s1.vs_inst_idx <= LENGTH bb.bb_instructions /\
      (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
        !di mi. di < LENGTH bb.bb_instructions /\
          mi < LENGTH bb.bb_instructions /\ di < mi /\
          (EL di bb.bb_instructions).inst_id = dp.dp_dload_id /\
          (EL mi bb.bb_instructions).inst_id = dp.dp_mstore_id /\
          di < s1.vs_inst_idx /\ s1.vs_inst_idx <= mi ==>
          dload_inv dfg dp s1) ==>
      (?e. exec_block fuel ctx bb s1 = Error e) \/
      lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx (transform_block_dload dfg bb) s2)) /\
    (* dload_inv invariant *)
    (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
      !di mi. di < LENGTH bb.bb_instructions /\
        mi < LENGTH bb.bb_instructions /\ di < mi /\
        (EL di bb.bb_instructions).inst_id = dp.dp_dload_id /\
        (EL mi bb.bb_instructions).inst_id = dp.dp_mstore_id /\
        di < s1.vs_inst_idx /\ s1.vs_inst_idx <= mi ==>
        dload_inv dfg dp s1) ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (transform_block_dload dfg bb) s2)
Proof
  rpt strip_tac >>
  qpat_x_assum `dload_pair_wf dfg dp0 _`
    (strip_assume_tac o REWRITE_RULE[dload_pair_wf_def]) >>
  rename1 `EL dload_idx bb.bb_instructions = dload_inst` >>
  rename1 `EL mstore_idx bb.bb_instructions = mstore_inst` >>
  (* Derive s1.vs_inst_idx = mstore_idx from ALOOKUP + ALL_DISTINCT *)
  `s1.vs_inst_idx = mstore_idx` by (
    irule all_distinct_inst_id_idx >>
    qexists_tac `bb.bb_instructions` >>
    imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> gvs[]) >>
  fs[] >>
  `dp_out_var dfg dp0 IN mm_block_fresh_dload dfg bb` by (
    simp[mm_block_fresh_dload_def, LET_THM, MEM_MAP] >>
    metis_tac[MEM]) >>
  `dload_inv dfg dp0 s1` by (
    first_x_assum (qspec_then `dp0` mp_tac) >>
    simp[] >> disch_then match_mp_tac >>
    MAP_EVERY qexists_tac [`dload_idx`, `mstore_idx`] >>
    gvs[] >> decide_tac) >>
  `(!x. dp0.dp_src = Var x ==> x NOTIN mm_block_fresh_dload dfg bb) /\
   (!x. dp0.dp_dst = Var x ==> x NOTIN mm_block_fresh_dload dfg bb)` by (
    irule dp_src_dst_not_fresh >> metis_tac[]) >>
  (* Get step sim from dload_mstore_dloadbytes_equiv *)
  qspecl_then [`dfg`, `dp0`, `mm_block_fresh_dload dfg bb`,
               `fuel`, `ctx:venom_context`, `s1`, `s2`,
               `EL mstore_idx bb.bb_instructions`]
    mp_tac dload_mstore_dloadbytes_equiv >>
  (impl_tac >- (gvs[] >> metis_tac[])) >>
  disch_tac >>
  `~is_terminator (EL mstore_idx bb.bb_instructions).inst_opcode`
    by (gvs[] >> simp[is_terminator_def]) >>
  (`EL mstore_idx (transform_block_dload dfg bb).bb_instructions =
    mk_dloadbytes_inst (EL mstore_idx bb.bb_instructions) dp0.dp_src dp0.dp_dst` by (
      simp[transform_block_dload_el, LET_THM] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >> gvs[])) >>
  `~is_terminator (mk_dloadbytes_inst (EL mstore_idx bb.bb_instructions)
      dp0.dp_src dp0.dp_dst).inst_opcode`
    by simp[mk_dloadbytes_inst_def, is_terminator_def] >>
  (* Apply dload_ind_step_case *)
  qspecl_then [`dfg`, `bb`, `n`, `fuel:num`, `ctx:venom_context`,
               `mstore_idx:num`, `s1`, `s2`,
               `EL (mstore_idx:num) bb.bb_instructions`,
               `EL (mstore_idx:num) (transform_block_dload dfg bb).bb_instructions`]
    mp_tac dload_ind_step_case >>
  simp[is_terminator_def, mk_dloadbytes_inst_def] >>
  disch_then match_mp_tac >>
  conj_tac >- gvs[mk_dloadbytes_inst_def] >>
  conj_tac
  >- (strip_tac >> strip_tac >>
      match_mp_tac dload_inv_callback_mstore >>
      MAP_EVERY qexists_tac
        [`fuel`, `ctx:venom_context`, `s1`, `dp0`,
         `dload_idx`, `mstore_inst`] >>
      rpt conj_tac >> gvs[EVERY_MEM])
  >> first_assum ACCEPT_TAC
QED

(* Induction core for dload block simulation.
   Uses the tight fresh set (mm_block_fresh_dload) internally,
   then the main theorem weakens to arbitrary fresh superset. *)
Theorem mm_block_dload_ind[local]:
  !dfg bb.
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) ==>
    !n fuel ctx s1 s2.
      n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
      state_equiv (mm_block_fresh_dload dfg bb) s1 s2 /\
      s1.vs_inst_idx <= LENGTH bb.bb_instructions /\
      (* Invariant: dload_inv holds for active pairs *)
      (!dp. MEM dp (find_dload_pairs dfg bb.bb_instructions) ==>
        !di mi. di < LENGTH bb.bb_instructions /\
          mi < LENGTH bb.bb_instructions /\ di < mi /\
          (EL di bb.bb_instructions).inst_id = dp.dp_dload_id /\
          (EL mi bb.bb_instructions).inst_id = dp.dp_mstore_id /\
          di < s1.vs_inst_idx /\ s1.vs_inst_idx <= mi ==>
          dload_inv dfg dp s1) ==>
      (?e. exec_block fuel ctx bb s1 = Error e) \/
      lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx (transform_block_dload dfg bb) s2)
Proof
  rpt gen_tac >> strip_tac >>
  Induct >> rpt strip_tac
  >- ((* Base case: inst_idx >= LENGTH *)
      (`s2.vs_inst_idx = s1.vs_inst_idx` by fs[state_equiv_def]) >>
      ONCE_REWRITE_TAC[exec_block_def] >>
      simp[get_instruction_def, lift_result_def])
  >> (* Step case *)
  (`s2.vs_inst_idx = s1.vs_inst_idx` by fs[state_equiv_def]) >>
  (`s1.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac) >>
  (* Establish: transformed EL = ... based on case *)
  Cases_on `MEM (EL s1.vs_inst_idx bb.bb_instructions).inst_id
                (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions))`
  >- ((* Case 1: NOP'd DLOAD — delegate to standalone helper *)
    fs[MEM_MAP] >> rename1 `MEM dp0 _` >>
    qspecl_then [`dfg`, `bb`, `n:num`, `fuel`, `ctx:venom_context`,
                 `s1`, `s2`, `dp0`]
      mp_tac dload_ind_case1 >>
    (impl_tac >- (
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      TRY (gvs[EVERY_MEM]) >>
      simp[MEM_MAP] >> metis_tac[])) >>
    disch_tac >> first_x_assum ACCEPT_TAC)
  >> (* Not a DLOAD NOP *)
  Cases_on `ALOOKUP (MAP (\dp. (dp.dp_mstore_id, dp))
                          (find_dload_pairs dfg bb.bb_instructions))
              (EL s1.vs_inst_idx bb.bb_instructions).inst_id`
  >- ((* Case 2: unchanged instruction (ALOOKUP = NONE) *)
      (`lift_result (state_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
               (execution_equiv (mm_block_fresh_dload dfg bb))
         (step_inst fuel ctx (EL s1.vs_inst_idx bb.bb_instructions) s1)
         (step_inst fuel ctx (EL s1.vs_inst_idx bb.bb_instructions) s2)` by (
        irule unchanged_inst_step_sim >> simp[])) >>
      (`EL s1.vs_inst_idx (transform_block_dload dfg bb).bb_instructions =
        EL s1.vs_inst_idx bb.bb_instructions` by (
          simp[transform_block_dload_el, LET_THM])) >>
      Cases_on `is_terminator (EL s1.vs_inst_idx bb.bb_instructions).inst_opcode`
      >- ((* Terminator case *)
          irule exec_block_step_chain_term >> simp[] >>
          rpt strip_tac >> fs[state_equiv_def, execution_equiv_def])
      >> (* Non-terminator case *)
      irule exec_block_step_chain >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >>
      rpt conj_tac >> (TRY decide_tac)
      >- ((* dload_inv preservation for unchanged instruction *)
          rpt strip_tac >>
          `(di:num) < s1.vs_inst_idx \/ di = s1.vs_inst_idx` by decide_tac
          >- ((* di < idx: old invariant + preservation *)
              `dload_inv dfg dp s1` by (
                first_x_assum (qspec_then `dp` mp_tac) >> simp[] >>
                disch_then match_mp_tac >>
                MAP_EVERY qexists_tac [`di:num`, `mi:num`] >>
                decide_tac) >>
              qspecl_then [`dfg`, `dp`, `bb.bb_instructions`,
                           `di:num`, `mi:num`, `s1.vs_inst_idx`,
                           `fuel`, `ctx:venom_context`, `s1`, `s1'`]
                mp_tac unchanged_preserves_dload_inv >>
              simp[] >> fs[EVERY_MEM] >> decide_tac)
          >> (* di = idx: contradiction — inst at idx is the DLOAD of dp *)
          `F` suffices_by simp[] >>
          qpat_x_assum `~MEM _ _` mp_tac >> simp[MEM_MAP] >>
          qexists_tac `dp` >> simp[] >>
          `dload_pair_wf dfg dp bb.bb_instructions` by fs[EVERY_MEM] >>
          pop_assum mp_tac >> simp[dload_pair_wf_def] >> strip_tac >>
          `s1.vs_inst_idx = di'` by (
            irule all_distinct_inst_id_idx >>
            qexists_tac `bb.bb_instructions` >> gvs[]) >>
          gvs[])
      >> gvs[state_equiv_def, execution_equiv_def, lookup_var_def]
     )
  >> (* Case 3: MSTORE -> DLOADBYTES — delegate to standalone helper *)
  rename1 `ALOOKUP _ _ = SOME dp0` >>
  qspecl_then [`dfg`, `bb`, `n:num`, `fuel`, `ctx:venom_context`,
               `s1`, `s2`, `dp0`]
    mp_tac dload_ind_case3 >>
  (impl_tac >- (gvs[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP, EVERY_MEM] >>
                 gvs[] >> metis_tac[])) >>
  disch_tac >> first_x_assum ACCEPT_TAC
QED

Theorem mm_block_simulates_dload:
  !dfg bb fresh.
    mm_block_fresh_dload dfg bb SUBSET fresh /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (transform_block_dload dfg bb) s)
Proof
  rpt strip_tac >>
  qspecl_then [`dfg`, `bb`] mp_tac mm_block_dload_ind >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
  simp[] >>
  strip_tac >> gvs[] >> (
    DISJ1_TAC >> metis_tac[]
    ORELSE
    (DISJ2_TAC >> irule lift_result_state_equiv_mono >>
     qexists_tac `mm_block_fresh_dload dfg bb` >> simp[])
  )
QED

Theorem ALL_DISTINCT_MAP_EL_IMP[local]:
  !f l i j. ALL_DISTINCT (MAP f l) /\ i < LENGTH l /\ j < LENGTH l /\
    f (EL i l) = f (EL j l) ==> i = j
Proof
  rpt strip_tac >>
  `EL i (MAP f l) = EL j (MAP f l)` by simp[EL_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED

(* Dload transform preserves the LAST instruction when bb_well_formed and
   dload_pair_wf hold: the LAST (terminator) is not DLOAD or MSTORE. *)
Theorem transform_block_dload_last[local]:
  !dfg bb.
    bb_well_formed bb /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) ==>
    LAST (transform_block_dload dfg bb).bb_instructions =
    LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by
    (fs[bb_well_formed_def] >> Cases_on `bb.bb_instructions` >> fs[]) >>
  simp[transform_block_dload_def, LAST_MAP] >>
  (* Reduce to: the MAP function applied to LAST returns LAST unchanged *)
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    (fs[bb_well_formed_def] >> metis_tac[]) >>
  (* Case 1: not in dload_nops *)
  Cases_on `MEM (LAST bb.bb_instructions).inst_id
    (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions))`
  >- (fs[MEM_MAP] >>
      rename1 `MEM dp0 _` >>
      `dload_pair_wf dfg dp0 bb.bb_instructions` by fs[EVERY_MEM] >>
      fs[dload_pair_wf_def] >>
      `(LAST bb.bb_instructions).inst_id =
       (EL di bb.bb_instructions).inst_id` by metis_tac[] >>
      `LAST bb.bb_instructions = EL (PRE (LENGTH bb.bb_instructions))
         bb.bb_instructions` by simp[LAST_EL] >>
      `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
        (Cases_on `bb.bb_instructions` >> fs[]) >>
      `PRE (LENGTH bb.bb_instructions) = di` by
        (qspecl_then [`\i. i.inst_id`, `bb.bb_instructions`,
           `PRE (LENGTH bb.bb_instructions)`, `di`]
           mp_tac ALL_DISTINCT_MAP_EL_IMP >> simp[] >> metis_tac[]) >>
      gvs[is_terminator_def]) >>
  simp[] >>
  (* Case 2: not in mstore_map *)
  CASE_TAC >> simp[] >>
  imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP] >>
  rename1 `MEM dp0 _` >>
  `dload_pair_wf dfg dp0 bb.bb_instructions` by fs[EVERY_MEM] >>
  fs[dload_pair_wf_def] >>
  `(LAST bb.bb_instructions).inst_id =
   (EL mi bb.bb_instructions).inst_id` by metis_tac[] >>
  `LAST bb.bb_instructions = EL (PRE (LENGTH bb.bb_instructions))
     bb.bb_instructions` by simp[LAST_EL] >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `PRE (LENGTH bb.bb_instructions) = mi` by
    (qspecl_then [`\i. i.inst_id`, `bb.bb_instructions`,
       `PRE (LENGTH bb.bb_instructions)`, `mi`]
       mp_tac ALL_DISTINCT_MAP_EL_IMP >> simp[] >> metis_tac[]) >>
  gvs[is_terminator_def]
QED

Theorem lift_result_se_trans[local]:
  !fresh r1 r2 r3.
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r1 r2 /\
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r2 r3 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r1 r3
Proof
  rpt strip_tac >>
  irule (lift_result_trans |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  metis_tac[state_equiv_trans, execution_equiv_trans]
QED

(* Structural conditions preserved through sub-transforms. *)

(* Dload is a MAP, so term structure is straightforward. *)
Theorem transform_block_dload_term_structure[local]:
  !dfg bb.
    bb_well_formed bb /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) ==>
    (transform_block_dload dfg bb).bb_instructions <> [] /\
    is_terminator
      (LAST (transform_block_dload dfg bb).bb_instructions).inst_opcode /\
    (!k. k < LENGTH (transform_block_dload dfg bb).bb_instructions /\
         is_terminator
           (EL k (transform_block_dload dfg bb).bb_instructions).inst_opcode
         ==>
         k = PRE (LENGTH (transform_block_dload dfg bb).bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> []` by
    (Cases_on `bb.bb_instructions` >> fs[bb_well_formed_def]) >>
  `LAST (transform_block_dload dfg bb).bb_instructions =
   LAST bb.bb_instructions` by
    (irule transform_block_dload_last >> simp[]) >>
  rpt conj_tac
  >- simp[transform_block_dload_def]
  >- fs[bb_well_formed_def]
  >- (simp[transform_block_dload_def] >>
      rpt strip_tac >>
      gvs[EL_MAP] >>
      Cases_on `MEM (EL k bb.bb_instructions).inst_id
        (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions))` >> gvs[] >>
      Cases_on `ALOOKUP
        (MAP (\dp. (dp.dp_mstore_id, dp))
           (find_dload_pairs dfg bb.bb_instructions))
        (EL k bb.bb_instructions).inst_id` >> gvs[] >| [
        (* NONE: identity — use bb_well_formed *)
        qpat_x_assum `bb_well_formed _` mp_tac >>
        rw[bb_well_formed_def] >> strip_tac >> res_tac,
        (* SOME: mk_dloadbytes_inst — not a terminator *)
        fs[mk_dloadbytes_inst_def, is_terminator_def]
      ])
QED

(* FLAT MAP transforms: memzero and mode. *)
Theorem transform_block_memzero_term_structure[local]:
  !dfg bb.
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb.bb_instructions /\
         is_terminator (EL k bb.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb.bb_instructions)) /\
    (let scan_result = scan_block_memzero dfg bb in
     let groups = scan_result.mz_flushed in
     let nop_set = nop_ids_of_groups dfg Mem2Mem bb.bb_instructions groups in
     let rep_map = rep_map_of_groups bb.bb_instructions groups in
     ~MEM (LAST bb.bb_instructions).inst_id nop_set /\
     ALOOKUP rep_map (LAST bb.bb_instructions).inst_id = NONE) ==>
    (transform_block_memzero dfg bb).bb_instructions <> [] /\
    is_terminator
      (LAST (transform_block_memzero dfg bb).bb_instructions).inst_opcode /\
    (!k. k < LENGTH (transform_block_memzero dfg bb).bb_instructions /\
         is_terminator
           (EL k (transform_block_memzero dfg bb).bb_instructions).inst_opcode
         ==>
         k = PRE (LENGTH (transform_block_memzero dfg bb).bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> gvs[LET_THM] >>
  simp[transform_block_memzero_def, LET_THM] >>
  match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM] flat_map_term_structure) >>
  simp[] >> rpt conj_tac
  >- (rw[apply_memzero_inst_def] >> rpt (IF_CASES_TAC >> simp[]) >>
      rpt (CASE_TAC >> simp[]))
  >- (simp[apply_memzero_inst_def])
  >- (rw[apply_memzero_inst_def, EVERY_DEF] >>
      rpt (IF_CASES_TAC >> simp[is_terminator_def, mk_nop_from_def]) >>
      rpt (CASE_TAC >>
           simp[is_terminator_def, mk_zero_store_inst_def,
                mk_calldatasize_inst_def, mk_memzero_calldatacopy_def]))
QED

Theorem transform_block_mode_term_structure[local]:
  !dfg mode bb.
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb.bb_instructions /\
         is_terminator (EL k bb.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb.bb_instructions)) /\
    (let scan_result = scan_block dfg mode bb in
     let groups = scan_result.ss_flushed in
     let nop_set = nop_ids_of_groups dfg mode bb.bb_instructions groups in
     let rep_map = rep_map_of_groups bb.bb_instructions groups in
     ~MEM (LAST bb.bb_instructions).inst_id nop_set /\
     ALOOKUP rep_map (LAST bb.bb_instructions).inst_id = NONE) ==>
    (transform_block_mode dfg mode bb).bb_instructions <> [] /\
    is_terminator
      (LAST (transform_block_mode dfg mode bb).bb_instructions).inst_opcode /\
    (!k. k < LENGTH (transform_block_mode dfg mode bb).bb_instructions /\
         is_terminator
           (EL k (transform_block_mode dfg mode bb).bb_instructions).inst_opcode
         ==>
         k = PRE (LENGTH (transform_block_mode dfg mode bb).bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> gvs[LET_THM] >>
  simp[transform_block_mode_def, LET_THM] >>
  match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM] flat_map_term_structure) >>
  simp[] >> rpt conj_tac >| [
    (* 1: non-empty *)
    rw[apply_groups_inst_def, LET_THM] >>
    rpt IF_CASES_TAC >> simp[] >>
    rpt CASE_TAC >> simp[],
    (* 2: terminator identity *)
    simp[apply_groups_inst_def],
    (* 3: non-term preservation *)
    rpt strip_tac >>
    rw[apply_groups_inst_def, LET_THM] >>
    rpt IF_CASES_TAC >> simp[EVERY_DEF] >>
    rpt CASE_TAC >> simp[EVERY_DEF] >>
    Cases_on `mode` >>
    simp[is_terminator_def, mk_nop_from_def, mk_bulk_copy_inst_def,
         mk_load_inst_def, mk_mstore_from_load_def,
         mode_copy_opcode_def, mode_load_opcode_def]
  ]
QED

(* Bundle: one mode step produces simulation AND preserves structural conditions.
   This avoids re-establishing 7 separate preconditions for each chained mode step. *)
Theorem mm_mode_step_bundle[local]:
  !mode dfg bb fresh.
    mm_block_fresh_mode dfg mode bb SUBSET fresh /\
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb.bb_instructions /\
         is_terminator (EL k bb.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb.bb_instructions)) /\
    EVERY inst_wf bb.bb_instructions /\
    (!x. MEM (Var x) (LAST bb.bb_instructions).inst_operands ==>
       x NOTIN fresh) /\
    mode_block_wf dfg mode bb ==>
    (!fuel ctx s.
       s.vs_inst_idx = 0 ==>
       lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
         (exec_block fuel ctx bb s)
         (exec_block fuel ctx (transform_block_mode dfg mode bb) s)) /\
    (transform_block_mode dfg mode bb).bb_instructions <> [] /\
    is_terminator
      (LAST (transform_block_mode dfg mode bb).bb_instructions).inst_opcode /\
    (!k. k < LENGTH (transform_block_mode dfg mode bb).bb_instructions /\
         is_terminator
           (EL k (transform_block_mode dfg mode bb).bb_instructions).inst_opcode
         ==>
         k = PRE (LENGTH (transform_block_mode dfg mode bb).bb_instructions)) /\
    EVERY inst_wf (transform_block_mode dfg mode bb).bb_instructions /\
    LAST (transform_block_mode dfg mode bb).bb_instructions =
      LAST bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  (* Simulation *)
  (conj_tac >- (
    rpt strip_tac >>
    irule mm_block_simulates_mode_proof >> fs[])) >>
  (* Term structure *)
  `(transform_block_mode dfg mode bb).bb_instructions <> [] /\
   is_terminator
     (LAST (transform_block_mode dfg mode bb).bb_instructions).inst_opcode /\
   (!k. k < LENGTH (transform_block_mode dfg mode bb).bb_instructions /\
        is_terminator
          (EL k (transform_block_mode dfg mode bb).bb_instructions).inst_opcode
        ==>
        k = PRE (LENGTH (transform_block_mode dfg mode bb).bb_instructions))`
  by (
    irule transform_block_mode_term_structure >> fs[mode_block_wf_def, LET_THM]) >>
  simp[] >>
  (* inst_wf *)
  (conj_tac >- (irule transform_block_mode_inst_wf >> fs[])) >>
  (* LAST identity *)
  simp[transform_block_mode_def, LET_THM] >>
  irule flat_map_last_identity >>
  rpt conj_tac >| [
    (* non-empty *)
    simp[apply_groups_inst_nonempty],
    (* bb <> [] *)
    fs[],
    (* LAST identity *)
    irule apply_groups_unchanged >>
    qpat_x_assum `mode_block_wf _ _ _` mp_tac >>
    rw[mode_block_wf_def, LET_THM]
  ]
QED

(* Structural conditions for bb2 = memzero(dload(bb)).
   Establishes that bb2 preserves block structure and LAST identity. *)
Theorem bb2_structural[local]:
  !dfg bb.
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    memzero_block_wf dfg (transform_block_dload dfg bb) ==>
    let bb2 = transform_block_memzero dfg (transform_block_dload dfg bb) in
    bb2.bb_instructions <> [] /\
    is_terminator (LAST bb2.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb2.bb_instructions /\
         is_terminator (EL k bb2.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb2.bb_instructions)) /\
    EVERY inst_wf bb2.bb_instructions /\
    LAST bb2.bb_instructions = LAST bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  imp_res_tac transform_block_dload_term_structure >>
  imp_res_tac transform_block_dload_last >>
  `memzero_block_wf dfg (transform_block_dload dfg bb)` by fs[] >>
  qabbrev_tac `bb1 = transform_block_dload dfg bb` >>
  mp_tac (Q.SPECL [`dfg`, `bb1`] transform_block_memzero_term_structure) >>
  (impl_tac >- (
    qunabbrev_tac `bb1` >> fs[memzero_block_wf_def, LET_THM])) >>
  strip_tac >> simp[] >>
  (conj_tac >- (
    irule transform_block_memzero_inst_wf >>
    qunabbrev_tac `bb1` >>
    irule transform_block_dload_inst_wf >> fs[])) >>
  simp[transform_block_memzero_def, LET_THM] >>
  qpat_x_assum `LAST bb1.bb_instructions = LAST bb.bb_instructions`
    (fn th => REWRITE_TAC [GSYM th]) >>
  match_mp_tac flat_map_last_identity >>
  simp[apply_memzero_inst_nonempty] >>
  match_mp_tac apply_memzero_unchanged >>
  qunabbrev_tac `bb1` >>
  qpat_x_assum `memzero_block_wf _ _` mp_tac >>
  rw[memzero_block_wf_def, LET_THM]
QED

(* Full block simulation: compose sub-passes.
   Error ∨ lift_result chains: if any sub-pass original errors, the composition
   original also errors (same block prefix). *)
Theorem mm_block_simulates:
  !dfg bb fresh.
    mm_block_fresh dfg bb SUBSET fresh /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    memzero_block_wf dfg (transform_block_dload dfg bb) /\
    (* Mode sub-pass well-formedness for each intermediate block *)
    mode_block_wf dfg CalldataMerge
      (transform_block_memzero dfg (transform_block_dload dfg bb)) /\
    mode_block_wf dfg DloadMerge
      (transform_block_mode dfg CalldataMerge
        (transform_block_memzero dfg (transform_block_dload dfg bb))) /\
    mode_block_wf dfg Mem2Mem
      (transform_block_mode dfg DloadMerge
        (transform_block_mode dfg CalldataMerge
          (transform_block_memzero dfg (transform_block_dload dfg bb)))) /\
    (!x. MEM (Var x) (LAST bb.bb_instructions).inst_operands ==>
       x NOTIN fresh) ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (transform_block dfg bb) s)
Proof
  rw[transform_block_def, mm_block_fresh_def, LET_THM] >>
  rpt strip_tac >>
  (* Forward chain: bb -> bb1 -> bb2 -> bb3 -> bb4 -> result. *)
  (* Step 1: dload (may Error) *)
  `(?e. exec_block fuel ctx bb s = Error e) \/
   lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
     (exec_block fuel ctx bb s)
     (exec_block fuel ctx (transform_block_dload dfg bb) s)` by (
    irule mm_block_simulates_dload >> simp[]) >>
  reverse (Cases_on `?e. exec_block fuel ctx bb s = Error e`)
  >- (DISJ1_TAC >> metis_tac[]) >>
  gvs[] >>
  (* Step 2: memzero *)
  `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
     (exec_block fuel ctx (transform_block_dload dfg bb) s)
     (exec_block fuel ctx
       (transform_block_memzero dfg (transform_block_dload dfg bb)) s)` by (
    irule mm_block_simulates_memzero >>
    rpt conj_tac >> fs[] >>
    TRY (irule transform_block_dload_inst_wf >> simp[] >> NO_TAC) >>
    `LAST (transform_block_dload dfg bb).bb_instructions =
     LAST bb.bb_instructions` by
      (irule transform_block_dload_last >> simp[]) >>
    simp[]) >>
  (* Steps 3-5: mode sub-passes. Use suspend for each. *)
  suspend "modes"
QED

Resume mm_block_simulates[modes]:
  qabbrev_tac `bb2 = transform_block_memzero dfg
    (transform_block_dload dfg bb)` >>
  (* bb2 structural conditions via bb2_structural *)
  SUBGOAL_THEN ``(bb2:basic_block).bb_instructions <> [] /\
    is_terminator (LAST bb2.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb2.bb_instructions /\
         is_terminator (EL k bb2.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb2.bb_instructions)) /\
    EVERY inst_wf bb2.bb_instructions /\
    LAST bb2.bb_instructions = LAST bb.bb_instructions``
  STRIP_ASSUME_TAC THENL [
    qunabbrev_tac `bb2` >>
    mp_tac (SIMP_RULE (srw_ss()) [LET_THM] bb2_structural) >>
    disch_then irule >> fs[],
    ALL_TAC
  ] >>
  (* Establish LAST operand condition for bb2 *)
  SUBGOAL_THEN ``!x. MEM (Var x) (LAST (bb2:basic_block).bb_instructions).inst_operands ==>
    x NOTIN fresh`` ASSUME_TAC THENL [fs[], ALL_TAC] >>
  (* Step 3: CalldataMerge *)
  mp_tac mm_mode_step_bundle >>
  disch_then (qspecl_then [`CalldataMerge`, `dfg`, `bb2`, `fresh`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Propagate LAST identity for next step *)
  SUBGOAL_THEN ``LAST (transform_block_mode dfg CalldataMerge bb2).bb_instructions =
    LAST bb.bb_instructions`` ASSUME_TAC THENL [fs[], ALL_TAC] >>
  SUBGOAL_THEN ``!x. MEM (Var x)
    (LAST (transform_block_mode dfg CalldataMerge bb2).bb_instructions).inst_operands ==>
    x NOTIN fresh`` ASSUME_TAC THENL [fs[], ALL_TAC] >>
  (* Step 4: DloadMerge *)
  mp_tac mm_mode_step_bundle >>
  disch_then (qspecl_then [`DloadMerge`, `dfg`,
    `transform_block_mode dfg CalldataMerge bb2`, `fresh`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Propagate LAST identity for Mem2Mem step *)
  SUBGOAL_THEN ``LAST (transform_block_mode dfg DloadMerge
    (transform_block_mode dfg CalldataMerge bb2)).bb_instructions =
    LAST bb.bb_instructions`` ASSUME_TAC THENL [fs[], ALL_TAC] >>
  SUBGOAL_THEN ``!x. MEM (Var x)
    (LAST (transform_block_mode dfg DloadMerge
      (transform_block_mode dfg CalldataMerge bb2)).bb_instructions).inst_operands ==>
    x NOTIN fresh`` ASSUME_TAC THENL [fs[], ALL_TAC] >>
  (* Step 5: Mem2Mem *)
  mp_tac mm_block_simulates_mode_proof >>
  disch_then (qspecl_then [`Mem2Mem`, `dfg`,
    `transform_block_mode dfg DloadMerge
      (transform_block_mode dfg CalldataMerge bb2)`, `fresh`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Chain transitively *)
  qabbrev_tac `bb3 = transform_block_mode dfg CalldataMerge bb2` >>
  qabbrev_tac `bb4 = transform_block_mode dfg DloadMerge bb3` >>
  irule lift_result_se_trans >>
  qexists_tac `exec_block fuel ctx bb4 s` >>
  (reverse conj_tac >- (first_x_assum irule >> qunabbrev_tac `bb4` >> qunabbrev_tac `bb3` >> fs[])) >>
  irule lift_result_se_trans >>
  qexists_tac `exec_block fuel ctx bb3 s` >>
  (reverse conj_tac >- (first_x_assum irule >> qunabbrev_tac `bb3` >> fs[])) >>
  irule lift_result_se_trans >>
  qexists_tac `exec_block fuel ctx bb2 s` >>
  (reverse conj_tac >- (first_x_assum irule >> fs[])) >>
  irule lift_result_se_trans >>
  qexists_tac
    `exec_block fuel ctx (transform_block_dload dfg bb) s` >>
  fs[]
QED

Finalise mm_block_simulates;

(* ===== Function-level correctness ===== *)

(* step_inst OK preserves vs_call_ctx for ALL opcodes (including terminators).
   Non-terminators: step_preserves_call_ctx.
   Terminators returning OK (JMP/JNZ/DJMP): use jump_to which only modifies
   vs_prev_bb, vs_current_bb, vs_inst_idx. Other terminators produce Halt, not OK. *)
Theorem step_inst_ok_preserves_call_ctx[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rpt strip_tac >>
  reverse (Cases_on `is_terminator inst.inst_opcode`)
  >- (drule_all step_preserves_call_ctx >> simp[])
  >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  simp[step_inst_base_def, AllCaseEqs(), jump_to_def] >>
  rpt strip_tac >> gvs[]
QED

(* exec_block preserves vs_call_ctx: every step_inst OK preserves it. *)
Theorem exec_block_preserves_call_ctx[local]:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst fuel ctx x s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK s_mid` >>
  imp_res_tac step_inst_ok_preserves_call_ctx >>
  Cases_on `is_terminator inst.inst_opcode` >> fs[] >>
  strip_tac
  >- (* Terminator: exec_block returns OK s_mid directly *)
     (fs[AllCaseEqs()] >> gvs[])
  >>
  (* Non-terminator: apply IH *)
  first_x_assum (qspec_then
    `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (fs[get_instruction_def, AllCaseEqs()] >> simp[])) >>
  disch_then (qspecl_then [`bb`,
    `s_mid with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s'`] mp_tac) >>
  simp[]
QED

(* Derive LAST operand condition from block membership + per-inst condition *)
Theorem last_operand_not_fresh[local]:
  !fn bb fresh.
    bb_well_formed bb /\
    MEM bb fn.fn_blocks /\
    (!bb' inst x. MEM bb' fn.fn_blocks /\
                  MEM inst bb'.bb_instructions /\
                  MEM (Var x) inst.inst_operands ==> x NOTIN fresh)
    ==>
    !x. MEM (Var x) (LAST bb.bb_instructions).inst_operands ==> x NOTIN fresh
Proof
  rpt strip_tac >>
  first_x_assum
    (qspecl_then [`bb`, `LAST bb.bb_instructions`, `x`] mp_tac) >>
  simp[] >> irule MEM_LAST_NOT_NIL >> fs[bb_well_formed_def]
QED

(* Step A of two-state block sim: R-related states give lift_result on same block *)
Theorem mm_two_state_step_A[local]:
  !fresh fn fuel ctx bb s1 s2.
    (!bb' inst x. MEM bb' fn.fn_blocks /\
                  MEM inst bb'.bb_instructions /\
                  MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    MEM bb fn.fn_blocks /\
    state_equiv fresh s1 s2
    ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx bb s2)
Proof
  rpt strip_tac
  \\ qspecl_then [`state_equiv fresh`, `execution_equiv fresh`, `fn`]
       mp_tac (cj 1 exec_block_preserves_R_proof)
  \\ impl_tac
  >- (rpt conj_tac
      >- simp[state_equiv_execution_equiv_valid_state_rel_proof]
      >- metis_tac[state_equiv_trans]
      >- metis_tac[execution_equiv_trans]
      >- (rpt strip_tac >> res_tac >>
          fs[state_equiv_def, execution_equiv_def]))
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `s2`] mp_tac)
  \\ simp[]
QED

(* Step B of two-state block sim: chain A + mm_block_simulates *)
Theorem mm_two_state_block_sim[local]:
  !dfg bb fresh fn fuel ctx s1 s2.
    mm_block_fresh dfg bb SUBSET fresh /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    memzero_block_wf dfg (transform_block_dload dfg bb) /\
    mode_block_wf dfg CalldataMerge
      (transform_block_memzero dfg (transform_block_dload dfg bb)) /\
    mode_block_wf dfg DloadMerge
      (transform_block_mode dfg CalldataMerge
        (transform_block_memzero dfg (transform_block_dload dfg bb))) /\
    mode_block_wf dfg Mem2Mem
      (transform_block_mode dfg DloadMerge
        (transform_block_mode dfg CalldataMerge
          (transform_block_memzero dfg (transform_block_dload dfg bb)))) /\
    (!bb' inst x. MEM bb' fn.fn_blocks /\
                  MEM inst bb'.bb_instructions /\
                  MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    MEM bb fn.fn_blocks /\
    state_equiv fresh s1 s2 /\
    LENGTH s1.vs_call_ctx.cc_calldata < dimword (:256) /\
    s1.vs_inst_idx = 0
    ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (transform_block dfg bb) s2)
Proof
  rpt strip_tac >>
  qspecl_then [`fresh`, `fn`, `fuel`, `ctx`, `bb`, `s1`, `s2`]
       mp_tac mm_two_state_step_A >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  strip_tac >>
  qspecl_then [`fn`, `bb`, `fresh`] mp_tac last_operand_not_fresh >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  strip_tac >>
  qspecl_then [`dfg`, `bb`, `fresh`] mp_tac mm_block_simulates >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s2`] mp_tac) >>
  (impl_tac >- (
      `s2.vs_inst_idx = s1.vs_inst_idx` by fs[state_equiv_def] >>
      `s2.vs_call_ctx = s1.vs_call_ctx` by fs[state_equiv_def, execution_equiv_def] >>
      fs[])) >>
  strip_tac >>
  gvs[]
  >- ((* s2 errors => s1 also errors (from lift_result agreement) *)
      DISJ1_TAC >> fs[] >>
      Cases_on `exec_block fuel ctx bb s1` >>
      fs[lift_result_def])
  >- ((* s2 doesn't error => chain lift_result via transitivity *)
      DISJ2_TAC >>
      irule lift_result_se_trans >>
      qexists_tac `exec_block fuel ctx bb s2` >>
      simp[])
QED

(* Function-level correctness.
   Preconditions:
   - mm_block_fresh ⊆ fresh for each block (from scan correctness)
   - fresh vars don't appear as operands in block instructions
     (ensured by load_safe_to_nop: NOP'd load outputs have all uses within group,
      and the group instructions are NOP'd/replaced in the transform) *)
Theorem mm_per_block_sim[local]:
  !fn fresh bb fuel ctx s1 s2.
    fn_inst_wf fn /\
    wf_function fn /\
    mm_block_fresh (dfg_build_function fn) bb SUBSET fresh /\
    EVERY (\dp. dload_pair_wf (dfg_build_function fn) dp bb.bb_instructions)
      (find_dload_pairs (dfg_build_function fn) bb.bb_instructions) /\
    memzero_block_wf (dfg_build_function fn)
      (transform_block_dload (dfg_build_function fn) bb) /\
    mode_block_wf (dfg_build_function fn) CalldataMerge
      (transform_block_memzero (dfg_build_function fn)
        (transform_block_dload (dfg_build_function fn) bb)) /\
    mode_block_wf (dfg_build_function fn) DloadMerge
      (transform_block_mode (dfg_build_function fn) CalldataMerge
        (transform_block_memzero (dfg_build_function fn)
          (transform_block_dload (dfg_build_function fn) bb))) /\
    mode_block_wf (dfg_build_function fn) Mem2Mem
      (transform_block_mode (dfg_build_function fn) DloadMerge
        (transform_block_mode (dfg_build_function fn) CalldataMerge
          (transform_block_memzero (dfg_build_function fn)
            (transform_block_dload (dfg_build_function fn) bb)))) /\
    (!bb' inst x. MEM bb' fn.fn_blocks /\
                  MEM inst bb'.bb_instructions /\
                  MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    MEM bb fn.fn_blocks /\
    state_equiv fresh s1 s2 /\
    LENGTH s1.vs_call_ctx.cc_calldata < dimword (:256) /\
    s1.vs_inst_idx = 0
    ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (transform_block (dfg_build_function fn) bb) s2)
Proof
  rpt strip_tac >>
  irule mm_two_state_block_sim >>
  fs[wf_function_def] >>
  rpt conj_tac >>
  TRY (qexists_tac `fn` >> fs[] >> NO_TAC) >>
  TRY (first_assum ACCEPT_TAC) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  fs[fn_inst_wf_def] >> res_tac >>
  qexists_tac `fn` >> fs[] >> metis_tac[]
QED

Theorem mm_p_preserved[local]:
  !bb fn fresh fuel ctx s1 s2 s1' s2'.
    MEM bb fn.fn_blocks /\
    exec_block fuel ctx bb s1 = OK s1'
    ==>
    LENGTH s1'.vs_call_ctx.cc_calldata = LENGTH s1.vs_call_ctx.cc_calldata
Proof
  rpt strip_tac >>
  drule exec_block_preserves_call_ctx >> simp[]
QED

Theorem state_equiv_implies_exec_equiv[local]:
  !fresh s1 s2. state_equiv fresh s1 s2 ==> execution_equiv fresh s1 s2
Proof
  simp[state_equiv_def]
QED

Theorem state_equiv_implies_control[local]:
  !fresh s1 s2. state_equiv fresh s1 s2 ==>
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (s1.vs_halted <=> s2.vs_halted)
Proof
  simp[state_equiv_def, execution_equiv_def]
QED

Theorem mm_function_correct:
  !fn fresh.
    let dfg = dfg_build_function fn in
    fn_inst_wf fn /\
    wf_function fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      mm_block_fresh dfg bb SUBSET fresh) /\
    (!bb. MEM bb fn.fn_blocks ==>
      EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
        (find_dload_pairs dfg bb.bb_instructions)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      memzero_block_wf dfg (transform_block_dload dfg bb)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      mode_block_wf dfg CalldataMerge
        (transform_block_memzero dfg (transform_block_dload dfg bb))) /\
    (!bb. MEM bb fn.fn_blocks ==>
      mode_block_wf dfg DloadMerge
        (transform_block_mode dfg CalldataMerge
          (transform_block_memzero dfg (transform_block_dload dfg bb)))) /\
    (!bb. MEM bb fn.fn_blocks ==>
      mode_block_wf dfg Mem2Mem
        (transform_block_mode dfg DloadMerge
          (transform_block_mode dfg CalldataMerge
            (transform_block_memzero dfg
              (transform_block_dload dfg bb))))) /\
    (!bb inst x. MEM bb fn.fn_blocks /\
                 MEM inst bb.bb_instructions /\
                 MEM (Var x) inst.inst_operands ==> x NOTIN fresh)
    ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
      (?e. run_function fuel ctx fn s = Error e) \/
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (run_function fuel ctx fn s)
        (run_function fuel ctx (transform_function fn) s)
Proof
  rw[LET_THM, transform_function_eq]
  \\ rpt strip_tac
  \\ qspecl_then
       [`\s. LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)`,
        `state_equiv fresh`, `execution_equiv fresh`,
        `transform_block (dfg_build_function fn)`, `fn`]
       mp_tac block_sim_function_with_pred
  \\ BETA_TAC
  \\ impl_tac
  >- (rpt conj_tac \\ rpt strip_tac
      \\ metis_tac[state_equiv_refl, state_equiv_implies_exec_equiv,
                   state_equiv_implies_control, transform_block_label,
                   mm_p_preserved, mm_per_block_sim])
  \\ `?lbl. fn_entry_label fn = SOME lbl` by
       (fs[wf_function_def, fn_has_entry_def] >>
        Cases_on `fn.fn_blocks` >> gvs[entry_block_def, fn_entry_label_def])
  \\ disch_then (qspecl_then [`fuel`, `ctx`,
       `s with <|vs_current_bb := lbl; vs_inst_idx := 0|>`]
       mp_tac)
  \\ BETA_TAC \\ simp[]
  \\ strip_tac
  \\ `fn_entry_label
       (function_map_transform (transform_block (dfg_build_function fn)) fn) =
     SOME lbl` by (
    qpat_x_assum `fn_entry_label fn = SOME lbl` mp_tac >>
    simp[function_map_transform_def, fn_entry_label_def, entry_block_def] >>
    Cases_on `fn.fn_blocks` >> simp[transform_block_label])
  \\ simp[Once run_function_def]
  \\ simp[Once run_function_def]
  \\ simp[Once run_function_def]
QED

(* ===== Pass correctness ===== *)

Theorem run_function_fuel_mono[local]:
  !fuel ctx fn s.
    terminates (run_function fuel ctx fn s) ==>
    !k. run_function (fuel + k) ctx fn s = run_function fuel ctx fn s
Proof
  rpt strip_tac >>
  simp[Once run_function_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  Cases_on `fn_entry_label fn` >> gvs[] >>
  irule run_blocks_fuel_mono >>
  fs[run_function_def]
QED

(* Fuel monotonicity implies fuel determinism *)
Theorem run_function_fuel_det[local]:
  !ctx fn s fuel fuel'.
    terminates (run_function fuel ctx fn s) /\
    terminates (run_function fuel' ctx fn s) ==>
    run_function fuel ctx fn s = run_function fuel' ctx fn s
Proof
  rpt strip_tac >>
  `fuel <= fuel' \/ fuel' <= fuel` by simp[] >> gvs[]
  >- (`fuel' = fuel + (fuel' - fuel)` by simp[] >>
      metis_tac[run_function_fuel_mono])
  >- (`fuel = fuel' + (fuel - fuel')` by simp[] >>
      metis_tac[run_function_fuel_mono])
QED

(* Helper: Error ∨ lift_result at function level + original terminates ⟹
   both terminate and results are equivalent.
   This bridges the gap between block_sim_function_proof's conclusion
   and pass_correct's requirements. *)
Theorem eol_function_pass_correct[local]:
  !fresh exec1 exec2.
    (!fuel. (?e. exec1 fuel = Error e) \/
            lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
              (exec1 fuel) (exec2 fuel)) /\
    (!fuel fuel'. terminates (exec1 fuel) /\ terminates (exec1 fuel') ==>
      exec1 fuel = exec1 fuel') /\
    (!fuel fuel'. terminates (exec2 fuel) /\ terminates (exec2 fuel') ==>
      exec2 fuel = exec2 fuel') /\
    (?f0. terminates (exec1 f0)) ==>
    pass_correct (state_equiv fresh) (execution_equiv fresh)
      (execution_equiv fresh) exec1 exec2
Proof
  rw[pass_correct_def]
  >- ((* Goal 1: ∃fuel'. terminates (exec2 fuel') *)
      qpat_x_assum `!fuel. _ \/ lift_result _ _ _ _ _`
        (qspec_then `f0` mp_tac) >>
      strip_tac >> gvs[]
      >- (Cases_on `exec1 f0` >> gvs[terminates_def]) >>
      qexists_tac `f0` >>
      Cases_on `exec1 f0` >> Cases_on `exec2 f0` >>
      gvs[lift_result_def, terminates_def])
  >- ((* Goal 2: lift_result when both terminate *)
      qpat_x_assum `!fuel. _ \/ lift_result _ _ _ _ _`
        (qspec_then `fuel` mp_tac) >>
      strip_tac >> gvs[]
      >- (Cases_on `exec1 fuel` >> gvs[terminates_def]) >>
      `terminates (exec2 fuel)` by
        (Cases_on `exec1 fuel` >> Cases_on `exec2 fuel` >>
         gvs[lift_result_def, terminates_def]) >>
      `exec2 fuel' = exec2 fuel` by metis_tac[] >>
      gvs[])
QED

Theorem mm_pass_correct:
  !fn fresh ctx s.
    let dfg = dfg_build_function fn in
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    fn_inst_wf fn /\
    wf_function fn /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    (?f0. terminates (run_function f0 ctx fn s)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      mm_block_fresh dfg bb SUBSET fresh) /\
    (!bb. MEM bb fn.fn_blocks ==>
      EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
        (find_dload_pairs dfg bb.bb_instructions)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      memzero_block_wf dfg (transform_block_dload dfg bb)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      mode_block_wf dfg CalldataMerge
        (transform_block_memzero dfg (transform_block_dload dfg bb))) /\
    (!bb. MEM bb fn.fn_blocks ==>
      mode_block_wf dfg DloadMerge
        (transform_block_mode dfg CalldataMerge
          (transform_block_memzero dfg (transform_block_dload dfg bb)))) /\
    (!bb. MEM bb fn.fn_blocks ==>
      mode_block_wf dfg Mem2Mem
        (transform_block_mode dfg DloadMerge
          (transform_block_mode dfg CalldataMerge
            (transform_block_memzero dfg
              (transform_block_dload dfg bb))))) /\
    (!bb inst x. MEM bb fn.fn_blocks /\
                 MEM inst bb.bb_instructions /\
                 MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    pass_correct (state_equiv fresh) (execution_equiv fresh)
      (execution_equiv fresh)
      (\fuel. run_function fuel ctx fn s)
      (\fuel. run_function fuel ctx (transform_function fn) s)
Proof
  rw[LET_THM] >>
  irule eol_function_pass_correct >>
  BETA_TAC >> rpt conj_tac
  >- (metis_tac[run_function_fuel_det])
  >- (metis_tac[run_function_fuel_det])
  >- (gen_tac >>
      qspecl_then [`fn`, `fresh`] mp_tac mm_function_correct >>
      simp[LET_THM] >>
      (impl_tac >- fs[]) >>
      disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
      simp[])
  >- (metis_tac[])
QED

