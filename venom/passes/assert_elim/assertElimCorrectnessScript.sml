(*
 * Assert Elimination — Correctness Statement
 *)

Theory assertElimCorrectness
Ancestors
  assertElimProofs
  assertElimDefs
  analysisSimDefs
  indexedLists
  passSharedDefs
  passSharedProps
  passSimulationDefs
  passSimulationProps
  rangeAnalysisProofs
  venomExecSemantics
  venomInst
  venomWf
Libs
  BasicProvers

Theorem assert_elim_function_correct:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\ dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb cond true_lbl false_lbl.
      MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!vv dinst u.
      dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
      vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
      MEM (Var u) dinst.inst_operands ==>
      u IN FDOM s.vs_vars) /\
    range_sound (df_widen_at NONE (range_analyze fn) s.vs_current_bb 0) s ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assert_elim_function fn) s)
Proof
  rpt strip_tac >>
  `fn.fn_blocks <> []` by fs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label (assert_elim_function fn) = fn_entry_label fn` by
    (pop_assum mp_tac >> ntac 12 (pop_assum kall_tac) >>
     simp[fn_entry_label_def, entry_block_def, assert_elim_function_def,
          clear_nops_function_def, analysis_function_transform_widen_def,
          function_map_transform_def, clear_nops_block_def,
          analysis_block_transform_widen_def, LET_THM,
          listTheory.NULL_EQ, rich_listTheory.MAP_HD, listTheory.MAP_EQ_NIL]) >>
  once_rewrite_tac[run_function_def] >> simp[] >>
  `s with vs_current_bb := s.vs_current_bb = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  irule assert_elim_function_correct_proof >>
  metis_tac[]
QED

(* ===== Core structural lemma: identity or mk_nop ===== *)

Theorem assert_elim_inst_cases[local]:
  !v inst. assert_elim_inst v inst = inst \/
           assert_elim_inst v inst = mk_nop_inst inst
Proof
  rpt gen_tac >> simp[assert_elim_inst_def] >>
  rpt (BasicProvers.PURE_CASE_TAC >> simp[])
QED

(* ===== Derived structural properties ===== *)

Theorem assert_elim_inst_id[local]:
  !v inst. (assert_elim_inst v inst).inst_id = inst.inst_id
Proof
  rpt gen_tac >>
  DISJ_CASES_TAC (SPECL [``v : range_state option``, ``inst : instruction``]
                        assert_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

Theorem assert_elim_inst_terminator[local]:
  !v inst. is_terminator inst.inst_opcode ==> assert_elim_inst v inst = inst
Proof
  rpt strip_tac >> simp[assert_elim_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  fs[is_terminator_def]
QED

Theorem assert_elim_inst_not_terminator[local]:
  !v inst. ~is_terminator inst.inst_opcode ==>
           ~is_terminator (assert_elim_inst v inst).inst_opcode
Proof
  rpt gen_tac >> strip_tac >>
  DISJ_CASES_TAC (SPECL [``v : range_state option``, ``inst : instruction``]
                        assert_elim_inst_cases) >>
  simp[mk_nop_inst_def, is_terminator_def]
QED

Theorem assert_elim_inst_phi[local]:
  !v inst. inst.inst_opcode = PHI ==>
           (assert_elim_inst v inst).inst_opcode = PHI
Proof
  rpt strip_tac >> simp[assert_elim_inst_def]
QED

Theorem assert_elim_inst_not_phi[local]:
  !v inst. inst.inst_opcode <> PHI ==>
           (assert_elim_inst v inst).inst_opcode <> PHI
Proof
  rpt gen_tac >> strip_tac >>
  DISJ_CASES_TAC (SPECL [``v : range_state option``, ``inst : instruction``]
                        assert_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

Theorem assert_elim_inst_outputs[local]:
  !v inst. (assert_elim_inst v inst).inst_outputs = inst.inst_outputs \/
           (assert_elim_inst v inst).inst_outputs = []
Proof
  rpt gen_tac >>
  DISJ_CASES_TAC (SPECL [``v : range_state option``, ``inst : instruction``]
                        assert_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

(* Key: the widen singleton transform equals function_map_transform with MAPi. *)
Theorem aftw_singleton_eq_fmt_mapi[local]:
  !bottom result (f : 'a -> instruction -> instruction) fn.
    analysis_function_transform_widen bottom result (\v inst. [f v inst]) fn =
    function_map_transform
      (\bb. bb with bb_instructions :=
        MAPi (\idx inst. f (df_widen_at bottom result bb.bb_label idx) inst)
             bb.bb_instructions) fn
Proof
  rw[analysis_function_transform_widen_def, function_map_transform_def,
     ir_function_component_equality] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  simp[analysis_block_transform_widen_def,
       basic_block_component_equality, flat_mapi_singleton]
QED

(* ===== Obligations ===== *)

Theorem assert_elim_preserves_ssa_form:
  ∀fn. wf_function fn ∧ ssa_form fn ⇒ ssa_form (assert_elim_function fn)
Proof
  rpt strip_tac >>
  simp[assert_elim_function_def] >>
  irule clear_nops_function_preserves_ssa >>
  ONCE_REWRITE_TAC[aftw_singleton_eq_fmt_mapi] >>
  mp_tac (Q.SPECL
    [`\bb idx inst. assert_elim_inst (df_widen_at NONE (range_analyze fn) bb.bb_label idx) inst`,
     `fn`] mapi_transform_preserves_ssa_bb) >>
  simp[assert_elim_inst_id, assert_elim_inst_outputs]
QED

Theorem assert_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (assert_elim_function fn)
Proof
  rpt strip_tac >>
  simp[assert_elim_function_def] >>
  irule clear_nops_function_preserves_wf >>
  ONCE_REWRITE_TAC[aftw_singleton_eq_fmt_mapi] >>
  mp_tac (Q.SPECL
    [`\bb idx inst. assert_elim_inst (df_widen_at NONE (range_analyze fn) bb.bb_label idx) inst`,
     `fn`] mapi_transform_preserves_wf_bb) >>
  simp[assert_elim_inst_id, assert_elim_inst_terminator,
       assert_elim_inst_not_terminator, assert_elim_inst_phi,
       assert_elim_inst_not_phi]
QED
