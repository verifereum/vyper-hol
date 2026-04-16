(*
 * Dead Store Elimination — Correctness Statement
 *)

Theory deadStoreElimCorrectness
Ancestors
  deadStoreElimProofs deadStoreElimDefs venomWf basePtrProps
  venomInst venomEffects
  passSimulationProps passSimulationDefs passSharedProps passSharedDefs

Theorem dse_function_correct:
  !analysis_fn aliases fuel ctx fn s bp.
    bp_ptr_sound bp s /\ bp_ptrs_bounded bp fn s /\
    (!space fn'.
      all_dead_stores (analysis_fn space fn')
        (cfg_analyze fn') aliases (bp_analyze (cfg_analyze fn') fn')
        space fn') ==>
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function analysis_fn fn) s)
Proof
  ACCEPT_TAC dse_function_correct_proof
QED

(* ===== Structural helpers for dse_inst ===== *)

Triviality dsei_preserves_id:
  !dead_ids space inst.
    (dse_inst dead_ids space inst).inst_id = inst.inst_id
Proof
  rw[dse_inst_def] >> rpt CASE_TAC >> simp[mk_nop_inst_def]
QED

Triviality dsei_terminator_identity:
  !dead_ids space inst.
    is_terminator inst.inst_opcode ==>
    dse_inst dead_ids space inst = inst
Proof
  rpt strip_tac >> simp[dse_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  Cases_on `space` >>
  simp[is_memory_def_opcode_def, write_effects_def, empty_effects_def]
QED

Triviality dsei_non_term:
  !dead_ids space inst.
    ~is_terminator inst.inst_opcode ==>
    ~is_terminator (dse_inst dead_ids space inst).inst_opcode
Proof
  rw[dse_inst_def] >> rpt CASE_TAC >>
  gvs[mk_nop_inst_def, is_terminator_def]
QED

Triviality dsei_phi:
  !dead_ids space inst.
    inst.inst_opcode = PHI ==>
    (dse_inst dead_ids space inst).inst_opcode = PHI
Proof
  rpt strip_tac >> simp[dse_inst_def] >>
  Cases_on `space` >>
  simp[is_memory_def_opcode_def, write_effects_def, empty_effects_def]
QED

Triviality dsei_non_phi:
  !dead_ids space inst.
    inst.inst_opcode <> PHI ==>
    (dse_inst dead_ids space inst).inst_opcode <> PHI
Proof
  rw[dse_inst_def] >> rpt CASE_TAC >>
  gvs[mk_nop_inst_def]
QED

Triviality dsei_preserves_outputs:
  !dead_ids space inst.
    (dse_inst dead_ids space inst).inst_outputs = inst.inst_outputs \/
    (dse_inst dead_ids space inst).inst_outputs = []
Proof
  rw[dse_inst_def] >> rpt CASE_TAC >> simp[mk_nop_inst_def]
QED

Triviality fn_insts_blocks_flat:
  !l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* dse_single_pass preserves wf_function *)
Triviality dse_single_pass_preserves_wf:
  !dead_ids space fn.
    wf_function fn ==> wf_function (dse_single_pass dead_ids space fn)
Proof
  rpt strip_tac >> simp[dse_single_pass_def] >>
  irule map_transform_preserves_wf >>
  simp[dsei_preserves_id, dsei_terminator_identity,
       dsei_non_term, dsei_phi, dsei_non_phi]
QED


(* dse_inst preserves outputs (subset) *)
Triviality dsei_block_outputs_subset:
  !dead_ids space l x.
    MEM x (FLAT (MAP (\i. i.inst_outputs) (MAP (dse_inst dead_ids space) l))) ==>
    MEM x (FLAT (MAP (\i. i.inst_outputs) l))
Proof
  Induct_on `l` >> simp[] >> rpt gen_tac >>
  simp[listTheory.MEM_APPEND] >> strip_tac >> gvs[]
  >- (DISJ1_TAC >>
      DISJ_CASES_TAC (Q.SPECL [`dead_ids`,`space`,`h`] dsei_preserves_outputs)
      >> gvs[])
  >- metis_tac[]
QED

Triviality dsei_block_all_distinct_outputs:
  !dead_ids space l.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) l)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (MAP (dse_inst dead_ids space) l)))
Proof
  ntac 2 gen_tac >> Induct_on `l` >> simp[] >>
  rpt gen_tac >> DISCH_TAC >>
  fs[listTheory.ALL_DISTINCT_APPEND] >>
  DISJ_CASES_TAC (Q.SPECL [`dead_ids`,`space`,`h`] dsei_preserves_outputs) >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >>
  metis_tac[dsei_block_outputs_subset]
QED

(* Blocks-level subset for DSE *)
Triviality dsei_blocks_outputs_subset:
  !bbs dead_ids space x.
    MEM x (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (MAP (block_map_transform (dse_inst dead_ids space))
                            bbs)))) ==>
    MEM x (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
Proof
  Induct >> simp[fn_insts_blocks_def, block_map_transform_def,
                  listTheory.MEM_APPEND] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (DISJ1_TAC >> metis_tac[dsei_block_outputs_subset])
  >- (DISJ2_TAC >> metis_tac[])
QED

(* dse_single_pass preserves ssa_form *)
Triviality dse_single_pass_preserves_ssa:
  !dead_ids space fn.
    ssa_form fn ==> ssa_form (dse_single_pass dead_ids space fn)
Proof
  rpt strip_tac >>
  fs[ssa_form_def, fn_insts_def, dse_single_pass_def,
     function_map_transform_def] >>
  pop_assum mp_tac >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def, block_map_transform_def] >>
  rpt gen_tac >>
  simp_tac std_ss [listTheory.ALL_DISTINCT_APPEND] >>
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (MAP (dse_inst dead_ids space) h.bb_instructions)))`
    by metis_tac[dsei_block_all_distinct_outputs] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (MAP (block_map_transform (dse_inst dead_ids space))
                            bbs))))`
    by (first_x_assum match_mp_tac >> simp[]) >>
  simp[listTheory.ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  `MEM e (FLAT (MAP (\i. i.inst_outputs) h.bb_instructions))`
    by metis_tac[dsei_block_outputs_subset] >>
  `~MEM e (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))`
    by res_tac >>
  metis_tac[dsei_blocks_outputs_subset]
QED

(* Apply OWHILE_INV_IND via mp_tac *)
Triviality dse_owhile_wf:
  !analysis_fn space fn fn'.
    wf_function fn /\
    OWHILE (\fn'. analysis_fn fn' <> {})
            (\fn'. dse_single_pass (analysis_fn fn') space fn')
            fn = SOME fn' ==>
    wf_function fn'
Proof
  rpt strip_tac >>
  mp_tac (WhileTheory.OWHILE_INV_IND
    |> INST_TYPE [alpha |-> ``:ir_function``]
    |> Q.INST [`P` |-> `wf_function`]) >>
  disch_then irule >>
  qexistsl [`\fn'. analysis_fn fn' <> {}`,
            `\fn'. dse_single_pass (analysis_fn fn') space fn'`,
            `fn`] >>
  simp[dse_single_pass_preserves_wf]
QED

Triviality dse_owhile_ssa:
  !analysis_fn space fn fn'.
    ssa_form fn /\
    OWHILE (\fn'. analysis_fn fn' <> {})
            (\fn'. dse_single_pass (analysis_fn fn') space fn')
            fn = SOME fn' ==>
    ssa_form fn'
Proof
  rpt strip_tac >>
  mp_tac (WhileTheory.OWHILE_INV_IND
    |> INST_TYPE [alpha |-> ``:ir_function``]
    |> Q.INST [`P` |-> `ssa_form`]) >>
  disch_then irule >>
  qexistsl [`\fn'. analysis_fn fn' <> {}`,
            `\fn'. dse_single_pass (analysis_fn fn') space fn'`,
            `fn`] >>
  simp[dse_single_pass_preserves_ssa]
QED

Triviality dse_function_space_preserves_wf:
  !analysis_fn space fn.
    wf_function fn ==> wf_function (dse_function_space analysis_fn space fn)
Proof
  rpt strip_tac >> simp[dse_function_space_def, dse_iterate_def] >>
  CASE_TAC >> simp[clear_nops_function_preserves_wf]
  >- (irule clear_nops_function_preserves_wf >> metis_tac[dse_owhile_wf])
QED

Triviality dse_function_space_preserves_ssa:
  !analysis_fn space fn.
    ssa_form fn ==> ssa_form (dse_function_space analysis_fn space fn)
Proof
  rpt strip_tac >> simp[dse_function_space_def, dse_iterate_def] >>
  CASE_TAC >> simp[clear_nops_function_preserves_ssa]
  >- (irule clear_nops_function_preserves_ssa >> metis_tac[dse_owhile_ssa])
QED

(* ===== Obligations ===== *)

Theorem dse_preserves_ssa_form:
  ∀analysis_fn fn. ssa_form fn ⇒ ssa_form (dse_function analysis_fn fn)
Proof
  rpt strip_tac >> simp[dse_function_def] >>
  irule dse_function_space_preserves_ssa >>
  irule dse_function_space_preserves_ssa >>
  irule dse_function_space_preserves_ssa >> simp[]
QED

Theorem dse_preserves_wf_function:
  ∀analysis_fn fn. wf_function fn ⇒ wf_function (dse_function analysis_fn fn)
Proof
  rpt strip_tac >> simp[dse_function_def] >>
  irule dse_function_space_preserves_wf >>
  irule dse_function_space_preserves_wf >>
  irule dse_function_space_preserves_wf >> simp[]
QED
