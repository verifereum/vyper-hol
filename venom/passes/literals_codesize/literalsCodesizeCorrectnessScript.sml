(*
 * Literals Codesize — Correctness Statement
 *
 * The transform preserves semantics: NOT(NOT(x)) = x and
 * (x >>> tz) <<< tz = x when trailing zeros are correct.
 *)

Theory literalsCodesizeCorrectness
Ancestors
  literalsCodesizeProofs venomWf
Libs
  BasicProvers

(* The literal codesize transform is correct: for any well-formed function,
   running it before and after the transform yields equivalent states and
   results. *)
Theorem lit_codesize_function_correct:
  !ctx fn s.
    fn_inst_wf fn ==>
    pass_correct (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (\fuel. run_blocks fuel ctx fn s)
      (\fuel. run_blocks fuel ctx (lit_codesize_function fn) s)
Proof
  rpt strip_tac >>
  simp[passSimulationDefsTheory.pass_correct_def] >>
  conj_tac
  >- (
    eq_tac >> strip_tac >> qexists_tac `fuel` >>
    gvs[lit_codesize_fn_eq]) >>
  rpt strip_tac >>
  `run_blocks fuel' ctx (lit_codesize_function fn) s =
   run_blocks fuel' ctx fn s` by simp[lit_codesize_fn_eq] >>
  `terminates (run_blocks fuel' ctx fn s)` by gvs[] >>
  `run_blocks fuel ctx fn s = run_blocks fuel' ctx fn s` by (
    irule crossBlockSimPropsTheory.run_blocks_deterministic >> simp[]) >>
  simp[passSimulationPropsTheory.lift_result_refl,
       stateEquivPropsTheory.state_equiv_refl,
       stateEquivPropsTheory.execution_equiv_refl]
QED

(* ===== Obligations ===== *)

(* lit_codesize_inst preserves instruction IDs — the transform only
   replaces opcodes, not identifiers. *)
Triviality lit_codesize_inst_id:
  !inst. (lit_codesize_inst inst).inst_id = inst.inst_id
Proof
  rw[literalsCodesizeDefsTheory.lit_codesize_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

(* lit_codesize_inst preserves instruction outputs — the transform only
   replaces opcodes, not result variables. *)
Triviality lit_codesize_inst_outputs:
  !inst. (lit_codesize_inst inst).inst_outputs = inst.inst_outputs
Proof
  rw[literalsCodesizeDefsTheory.lit_codesize_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

(* Terminator instructions pass through lit_codesize_inst unchanged —
   only computational opcodes are replaced. *)
Triviality lit_codesize_inst_terminator_identity:
  !inst. is_terminator inst.inst_opcode ==> lit_codesize_inst inst = inst
Proof
  rw[literalsCodesizeDefsTheory.lit_codesize_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[venomInstTheory.is_terminator_def])
QED

(* lit_codesize_inst never introduces a terminator — only non-terminator
   opcodes can result from the transform. *)
Triviality lit_codesize_inst_nonterminator:
  !inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (lit_codesize_inst inst).inst_opcode
Proof
  rw[literalsCodesizeDefsTheory.lit_codesize_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[venomInstTheory.is_terminator_def])
QED

(* PHI opcodes are unchanged by lit_codesize_inst. *)
Triviality lit_codesize_inst_phi:
  !inst. inst.inst_opcode = PHI ==> (lit_codesize_inst inst).inst_opcode = PHI
Proof
  rw[literalsCodesizeDefsTheory.lit_codesize_inst_def]
QED

(* lit_codesize_inst never produces a PHI opcode from a non-PHI input. *)
Triviality lit_codesize_inst_nonphi:
  !inst. inst.inst_opcode <> PHI ==> (lit_codesize_inst inst).inst_opcode <> PHI
Proof
  rw[literalsCodesizeDefsTheory.lit_codesize_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

(* The literal codesize transform preserves SSA form — it only replaces
   opcodes, not variable definitions. *)
Theorem lit_codesize_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (lit_codesize_function fn)
Proof
  rpt strip_tac >>
  `!bbs. FLAT (MAP (\i. i.inst_outputs)
           (fn_insts_blocks
             (MAP (block_map_transform lit_codesize_inst) bbs))) =
         FLAT (MAP (\i. i.inst_outputs)
           (fn_insts_blocks bbs))` by (
    Induct >>
    simp[venomInstTheory.fn_insts_blocks_def,
         passSimulationDefsTheory.block_map_transform_def,
         listTheory.MAP_MAP_o, combinTheory.o_DEF,
         lit_codesize_inst_outputs]) >>
  gvs[venomWfTheory.ssa_form_def,
      literalsCodesizeDefsTheory.lit_codesize_function_def,
      passSimulationDefsTheory.function_map_transform_def,
      venomInstTheory.fn_insts_def]
QED

(* The literal codesize transform preserves function well-formedness —
   it passes the map-transform preservation lemmas. *)
Theorem lit_codesize_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (lit_codesize_function fn)
Proof
  rpt strip_tac >>
  simp[literalsCodesizeDefsTheory.lit_codesize_function_def] >>
  irule passSimulationPropsTheory.map_transform_preserves_wf >>
  simp[lit_codesize_inst_id, lit_codesize_inst_terminator_identity,
       lit_codesize_inst_nonterminator, lit_codesize_inst_phi,
       lit_codesize_inst_nonphi]
QED
