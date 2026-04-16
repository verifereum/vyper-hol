(*
 * Overflow Check Elimination — Correctness Statement
 *)

Theory overflowElimCorrectness
Ancestors
  overflowElimProofs overflowElimDefs
  venomWf venomInst passSimulationProps passSimulationDefs
  passSharedProps passSharedDefs


Theorem overflow_elim_function_correct:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (overflow_elim_function fn) s)
Proof
  ACCEPT_TAC overflow_elim_function_correct_proof
QED

(* ===== Structural helpers for overflow_elim_inst ===== *)

Triviality oei_preserves_id:
  !dfg ra lbl idx inst.
    (overflow_elim_inst dfg ra lbl idx inst).inst_id = inst.inst_id
Proof
  rw[overflow_elim_inst_def] >> rpt CASE_TAC >> simp[mk_nop_inst_def]
QED

Triviality oei_terminator_identity:
  !dfg ra lbl idx inst.
    is_terminator inst.inst_opcode ==>
    overflow_elim_inst dfg ra lbl idx inst = inst
Proof
  rpt strip_tac >> simp[overflow_elim_inst_def] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def]
QED

Triviality oei_non_term:
  !dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode ==>
    ~is_terminator (overflow_elim_inst dfg ra lbl idx inst).inst_opcode
Proof
  rw[overflow_elim_inst_def] >> rpt CASE_TAC >>
  gvs[mk_nop_inst_def, is_terminator_def]
QED

Triviality oei_phi:
  !dfg ra lbl idx inst.
    inst.inst_opcode = PHI ==>
    (overflow_elim_inst dfg ra lbl idx inst).inst_opcode = PHI
Proof
  simp[overflow_elim_inst_def]
QED

Triviality oei_non_phi:
  !dfg ra lbl idx inst.
    inst.inst_opcode <> PHI ==>
    (overflow_elim_inst dfg ra lbl idx inst).inst_opcode <> PHI
Proof
  rw[overflow_elim_inst_def] >> rpt CASE_TAC >>
  gvs[mk_nop_inst_def]
QED

Triviality oei_preserves_outputs:
  !dfg ra lbl idx inst.
    (overflow_elim_inst dfg ra lbl idx inst).inst_outputs = inst.inst_outputs \/
    (overflow_elim_inst dfg ra lbl idx inst).inst_outputs = []
Proof
  rw[overflow_elim_inst_def] >> rpt CASE_TAC >> simp[mk_nop_inst_def]
QED

(* ===== Block-level helpers ===== *)

Triviality oei_block_insts_length:
  !insts dfg ra lbl n.
    LENGTH (overflow_elim_block_insts dfg ra lbl n insts) = LENGTH insts
Proof
  Induct >> simp[overflow_elim_block_insts_def]
QED

Triviality oei_block_insts_el:
  !insts dfg ra lbl n i. i < LENGTH insts ==>
    EL i (overflow_elim_block_insts dfg ra lbl n insts) =
    overflow_elim_inst dfg ra lbl (n + i) (EL i insts)
Proof
  Induct >> simp[overflow_elim_block_insts_def] >>
  rpt gen_tac >> Cases_on `i` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[arithmeticTheory.ADD1]
QED

(* overflow_elim_block_insts = MAPi *)
Triviality oei_block_insts_mapi:
  !insts dfg ra lbl n.
    overflow_elim_block_insts dfg ra lbl n insts =
    MAPi (\i inst. overflow_elim_inst dfg ra lbl (n + i) inst) insts
Proof
  Induct >- simp[overflow_elim_block_insts_def] >>
  rw[overflow_elim_block_insts_def] >>
  first_x_assum (qspecl_then [`dfg`,`ra`,`lbl`,`n+1`] SUBST1_TAC) >>
  simp[combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM] >> rpt gen_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> DECIDE_TAC
QED

Triviality fn_insts_blocks_flat:
  !l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* ===== Obligations ===== *)

(* TEMPORARILY CHEATED — ALL_DISTINCT preservation through output-zeroing
   requires careful induction with DISJOINT/subset argument.
   The wf proof below works via mapi_transform_preserves_wf_bb. *)
Triviality oei_block_insts_outputs_subset:
  !insts dfg ra lbl n x.
    MEM x (FLAT (MAP (\i. i.inst_outputs)
      (overflow_elim_block_insts dfg ra lbl n insts))) ==>
    MEM x (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  Induct >> simp[overflow_elim_block_insts_def] >>
  rpt gen_tac >> simp[listTheory.MEM_APPEND] >> strip_tac
  >- (DISJ1_TAC >>
      DISJ_CASES_TAC
        (Q.SPECL [`dfg`,`ra`,`lbl`,`n`,`h`] oei_preserves_outputs) >>
      gvs[])
  >- metis_tac[]
QED

Triviality oei_block_insts_all_distinct_outputs:
  !insts dfg ra lbl n.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (overflow_elim_block_insts dfg ra lbl n insts)))
Proof
  Induct >- simp[overflow_elim_block_insts_def] >>
  rpt gen_tac >> simp[overflow_elim_block_insts_def] >>
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts))`
    by fs[listTheory.ALL_DISTINCT_APPEND] >>
  DISJ_CASES_TAC
    (Q.SPECL [`dfg`,`ra`,`lbl`,`n`,`h`] oei_preserves_outputs) >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >>
  metis_tac[oei_block_insts_outputs_subset]
QED

Triviality oei_blocks_outputs_subset:
  !bbs dfg ra x.
    MEM x (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (MAP (\bb. bb with bb_instructions :=
        overflow_elim_block_insts dfg ra bb.bb_label 0
          bb.bb_instructions) bbs)))) ==>
    MEM x (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.MEM_APPEND] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (DISJ1_TAC >> metis_tac[oei_block_insts_outputs_subset])
  >- (DISJ2_TAC >> metis_tac[])
QED

(* Block-level wrappers that avoid unfolding overflow_elim_block_def *)
Triviality oei_block_outputs_subset:
  !dfg ra lbl bb x.
    MEM x (FLAT (MAP (\i. i.inst_outputs)
      (overflow_elim_block dfg ra lbl bb).bb_instructions)) ==>
    MEM x (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  simp[overflow_elim_block_def] >> metis_tac[oei_block_insts_outputs_subset]
QED

Triviality oei_block_all_distinct_outputs:
  !dfg ra lbl bb.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (overflow_elim_block dfg ra lbl bb).bb_instructions))
Proof
  simp[overflow_elim_block_def] >> metis_tac[oei_block_insts_all_distinct_outputs]
QED

Triviality oei_blocks_outputs_subset2:
  !bbs dfg ra x.
    MEM x (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (MAP (\bb. overflow_elim_block dfg ra
                                    bb.bb_label bb) bbs)))) ==>
    MEM x (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
Proof
  simp[overflow_elim_block_def] >> metis_tac[oei_blocks_outputs_subset]
QED

Theorem overflow_elim_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (overflow_elim_function fn)
Proof
  rpt strip_tac >> simp[overflow_elim_function_def] >>
  irule clear_nops_function_preserves_ssa >>
  fs[ssa_form_def, fn_insts_def] >>
  pop_assum mp_tac >>
  qspec_tac (`range_analyze fn`, `ra`) >>
  qspec_tac (`dfg_build_function fn`, `dfg`) >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def] >>
  rpt gen_tac >>
  simp_tac std_ss [listTheory.ALL_DISTINCT_APPEND] >>
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (overflow_elim_block dfg ra h.bb_label h).bb_instructions))`
    by metis_tac[oei_block_all_distinct_outputs] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks
        (MAP (\bb. overflow_elim_block dfg ra bb.bb_label bb) bbs))))`
    by (first_x_assum match_mp_tac >> simp[]) >>
  simp[listTheory.ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  `MEM e (FLAT (MAP (\i. i.inst_outputs) h.bb_instructions))`
    by metis_tac[oei_block_outputs_subset] >>
  `~MEM e (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))`
    by res_tac >>
  metis_tac[oei_blocks_outputs_subset2]
QED

Triviality oe_as_fmt:
  !fn dfg ra.
    fn with fn_blocks :=
      MAP (\bb. overflow_elim_block dfg ra bb.bb_label bb) fn.fn_blocks =
    function_map_transform
      (\bb. bb with bb_instructions :=
        MAPi (\i inst. overflow_elim_inst dfg ra bb.bb_label i inst)
             bb.bb_instructions) fn
Proof
  simp[function_map_transform_def, overflow_elim_block_def,
       oei_block_insts_mapi]
QED

Theorem overflow_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (overflow_elim_function fn)
Proof
  rpt strip_tac >>
  simp[overflow_elim_function_def] >>
  `wf_function (fn with fn_blocks :=
      MAP (\bb. overflow_elim_block (dfg_build_function fn)
                  (range_analyze fn) bb.bb_label bb) fn.fn_blocks)`
    suffices_by simp[clear_nops_function_preserves_wf] >>
  rw[oe_as_fmt] >>
  mp_tac (Q.ISPECL [
    `\(bb:basic_block) (i:num) (inst:instruction).
       overflow_elim_inst (dfg_build_function fn)
         (range_analyze fn) bb.bb_label i inst`]
    (DB.fetch "passSimulationProps" "mapi_transform_preserves_wf_bb")) >>
  simp[oei_preserves_id, oei_terminator_identity,
       oei_non_term, oei_phi, oei_non_phi]
QED
