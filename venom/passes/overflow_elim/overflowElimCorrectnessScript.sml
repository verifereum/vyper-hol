(*
 * Overflow Check Elimination — Correctness Statement
 *)

Theory overflowElimCorrectness
Ancestors
  overflowElimProofs venomWf
  overflowElimDefs overflowElimHelpers overflowElimHelpers2
  passSharedDefs passSimulationProps passSharedProps
  passSimulationDefs venomInst dfgDefs
  rangeAnalysisDefs dfAnalyzeWidenDefs stateEquiv

Libs
  BasicProvers

Theorem overflow_elim_function_correct:
  !fuel ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    assert_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_ext_sound (dfg_build_function fn) s.vs_vars /\
    range_sound (df_widen_at NONE (range_analyze fn) s.vs_current_bb 0) s ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (overflow_elim_function fn) s)
Proof
  ACCEPT_TAC overflow_elim_function_correct_proof
QED

(* ===== Core structural lemma: identity or mk_nop ===== *)

Theorem overflow_elim_inst_cases[local]:
  !dfg ra lbl idx inst.
    overflow_elim_inst dfg ra lbl idx inst = inst \/
    overflow_elim_inst dfg ra lbl idx inst = mk_nop_inst inst
Proof
  rpt gen_tac >> simp[overflow_elim_inst_def] >>
  rpt (BasicProvers.PURE_CASE_TAC >> simp[])
QED

(* ===== Derived structural properties ===== *)

Theorem overflow_elim_inst_id[local]:
  !dfg ra lbl idx inst.
    (overflow_elim_inst dfg ra lbl idx inst).inst_id = inst.inst_id
Proof
  rpt gen_tac >>
  strip_assume_tac (Q.SPECL [`dfg`, `ra`, `lbl`, `idx`, `inst`]
    overflow_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

Theorem overflow_elim_inst_terminator[local]:
  !dfg ra lbl idx inst.
    is_terminator inst.inst_opcode ==>
    overflow_elim_inst dfg ra lbl idx inst = inst
Proof
  rpt strip_tac >> simp[overflow_elim_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  fs[is_terminator_def]
QED

Theorem overflow_elim_inst_not_terminator[local]:
  !dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode ==>
    ~is_terminator (overflow_elim_inst dfg ra lbl idx inst).inst_opcode
Proof
  rpt gen_tac >> strip_tac >>
  strip_assume_tac (Q.SPECL [`dfg`, `ra`, `lbl`, `idx`, `inst`]
    overflow_elim_inst_cases) >>
  simp[mk_nop_inst_def, is_terminator_def]
QED

Theorem overflow_elim_inst_phi[local]:
  !dfg ra lbl idx inst.
    inst.inst_opcode = PHI ==>
    (overflow_elim_inst dfg ra lbl idx inst).inst_opcode = PHI
Proof
  rpt strip_tac >> simp[overflow_elim_inst_def]
QED

Theorem overflow_elim_inst_not_phi[local]:
  !dfg ra lbl idx inst.
    inst.inst_opcode <> PHI ==>
    (overflow_elim_inst dfg ra lbl idx inst).inst_opcode <> PHI
Proof
  rpt gen_tac >> strip_tac >>
  strip_assume_tac (Q.SPECL [`dfg`, `ra`, `lbl`, `idx`, `inst`]
    overflow_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

Theorem overflow_elim_inst_outputs[local]:
  !dfg ra lbl idx inst.
    (overflow_elim_inst dfg ra lbl idx inst).inst_outputs = inst.inst_outputs \/
    (overflow_elim_inst dfg ra lbl idx inst).inst_outputs = []
Proof
  rpt gen_tac >>
  strip_assume_tac (Q.SPECL [`dfg`, `ra`, `lbl`, `idx`, `inst`]
    overflow_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

(* ===== Rewrite to function_map_transform form ===== *)

Theorem overflow_elim_function_eq_fmt[local]:
  !fn. overflow_elim_function fn =
    clear_nops_function
      (function_map_transform
        (\bb. bb with bb_instructions :=
          MAPi (\idx inst.
            overflow_elim_inst (dfg_build_function fn) (range_analyze fn)
              bb.bb_label idx inst) bb.bb_instructions) fn)
Proof
  simp[overflow_elim_function_def, function_map_transform_def,
       ir_function_component_equality, clear_nops_function_def] >>
  gen_tac >> irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  simp[overflow_elim_block_def, basic_block_component_equality,
       overflow_elim_block_insts_eq_mapi, clear_nops_block_def]
QED

(* ===== Obligations ===== *)

Theorem overflow_elim_preserves_ssa_form:
  ∀fn. wf_function fn ∧ ssa_form fn ⇒ ssa_form (overflow_elim_function fn)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[overflow_elim_function_eq_fmt] >>
  irule clear_nops_function_preserves_ssa >>
  mp_tac (Q.SPECL
    [`\bb idx inst. overflow_elim_inst (dfg_build_function fn)
        (range_analyze fn) bb.bb_label idx inst`,
     `fn`] mapi_transform_preserves_ssa_bb) >>
  simp[overflow_elim_inst_id, overflow_elim_inst_outputs]
QED

Theorem overflow_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (overflow_elim_function fn)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[overflow_elim_function_eq_fmt] >>
  irule clear_nops_function_preserves_wf >>
  mp_tac (Q.SPECL
    [`\bb idx inst. overflow_elim_inst (dfg_build_function fn)
        (range_analyze fn) bb.bb_label idx inst`,
     `fn`] mapi_transform_preserves_wf_bb) >>
  simp[overflow_elim_inst_id, overflow_elim_inst_terminator,
       overflow_elim_inst_not_terminator, overflow_elim_inst_phi,
       overflow_elim_inst_not_phi]
QED
