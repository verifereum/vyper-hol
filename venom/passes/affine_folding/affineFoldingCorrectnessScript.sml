Theory affineFoldingCorrectness
Ancestors
  affineFoldingProofs affineFoldingDefs
  venomWf venomInst passSimulationProps passSimulationDefs

(* Affine folding preserves function execution semantics:
   running a function before and after the transform produces
   equivalent results under state_equiv and execution_equiv. *)
Theorem af_transform_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (af_transform_function fn) s)
Proof
  ACCEPT_TAC af_transform_function_correct_proof
QED

(* ===== Structural helpers for af_transform_inst ===== *)

Triviality af_rewrite_preserves:
  !dfg vi inst r.
    af_rewrite_inst dfg vi inst = SOME r ==>
    r.inst_id = inst.inst_id /\
    r.inst_outputs = inst.inst_outputs /\
    ~is_terminator r.inst_opcode /\
    r.inst_opcode <> PHI
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB` >>
  simp[af_rewrite_inst_def] >>
  rpt (CASE_TAC >> simp[is_terminator_def]) >>
  rpt strip_tac >> gvs[is_terminator_def]
QED

Triviality afi_preserves_id:
  !dfg vi inst. (af_transform_inst dfg vi inst).inst_id = inst.inst_id
Proof
  rw[af_transform_inst_def] >> rpt CASE_TAC >> gvs[] >>
  imp_res_tac af_rewrite_preserves >> gvs[]
QED

Triviality afi_terminator_identity:
  !dfg vi inst. is_terminator inst.inst_opcode ==>
                af_transform_inst dfg vi inst = inst
Proof
  rpt strip_tac >>
  `af_rewrite_inst dfg vi inst = NONE` by
    (simp[af_rewrite_inst_def] >>
     Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  simp[af_transform_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def]
QED

Triviality afi_non_term:
  !dfg vi inst. ~is_terminator inst.inst_opcode ==>
                ~is_terminator (af_transform_inst dfg vi inst).inst_opcode
Proof
  rw[af_transform_inst_def] >> rpt CASE_TAC >> gvs[is_terminator_def] >>
  imp_res_tac af_rewrite_preserves >> gvs[]
QED

Triviality afi_phi:
  !dfg vi inst. inst.inst_opcode = PHI ==>
                (af_transform_inst dfg vi inst).inst_opcode = PHI
Proof
  simp[af_transform_inst_def]
QED

Triviality afi_non_phi:
  !dfg vi inst. inst.inst_opcode <> PHI ==>
                (af_transform_inst dfg vi inst).inst_opcode <> PHI
Proof
  rw[af_transform_inst_def] >> rpt CASE_TAC >> gvs[] >>
  imp_res_tac af_rewrite_preserves >> gvs[]
QED

Triviality afi_preserves_outputs:
  !dfg vi inst.
    (af_transform_inst dfg vi inst).inst_outputs = inst.inst_outputs
Proof
  rw[af_transform_inst_def] >> rpt CASE_TAC >> gvs[] >>
  imp_res_tac af_rewrite_preserves >> gvs[]
QED

Triviality fn_insts_blocks_flat:
  !l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Triviality afi_insts_outputs_eq:
  !dfg vi l. FLAT (MAP (\i. i.inst_outputs)
    (MAP (af_transform_inst dfg vi) l)) =
    FLAT (MAP (\i. i.inst_outputs) l)
Proof
  ntac 2 gen_tac >> Induct >> simp[afi_preserves_outputs]
QED

Triviality afi_outputs_blocks_eq:
  !dfg vi bbs.
    FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (MAP (af_transform_block dfg vi) bbs))) =
    FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))
Proof
  ntac 2 gen_tac >> Induct >>
  simp[fn_insts_blocks_def, af_transform_block_def, afi_insts_outputs_eq]
QED

(* ===== Obligations ===== *)

Theorem af_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (af_transform_function fn)
Proof
  simp[ssa_form_def, fn_insts_def, af_transform_function_def,
       afi_outputs_blocks_eq]
QED

Theorem af_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (af_transform_function fn)
Proof
  rpt strip_tac >>
  simp[af_transform_function_def, af_transform_block_def] >>
  qmatch_goalsub_abbrev_tac `MAP bt fn.fn_blocks` >>
  `bt = block_map_transform (af_transform_inst
      (dfg_build_function fn) (af_compute_fn_var_info fn))`
    by simp[Abbr `bt`, FUN_EQ_THM, block_map_transform_def,
            af_transform_block_def] >>
  pop_assum SUBST1_TAC >>
  simp[GSYM function_map_transform_def] >>
  irule map_transform_preserves_wf >>
  simp[afi_preserves_id, afi_terminator_identity,
       afi_non_term, afi_phi, afi_non_phi]
QED
