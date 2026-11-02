(* Constructor-level stopping observations for indexed DFT swaps. *)
Theory dftStoppingSwap
Ancestors
  dftSuccessSwap dftCommutation analysisSimProofsBase venomExecSemantics
  venomState venomInst venomEffects venomWf instIdxIndep list

Theorem dft_abort_update_iff[local]:
  ~MEM (Var v) i.inst_operands /\ ~MEM v i.inst_outputs ==>
  ((?t. step_inst fuel C i (update_var v w s) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  strip_tac >>
  `!z. MEM (Var z) i.inst_operands ==> v <> z` by metis_tac[] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_frame >>
      disch_then (qspecl_then [`fuel`, `C`, `s`, `w`] mp_tac) >>
      Cases_on `step_inst fuel C i s` >> simp[] >> metis_tac[]) >>
  drule_all step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `w`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[map_result_state_def] >> metis_tac[]
QED

Theorem dft_abort_fold_iff:
  !us s.
  EVERY (\p. ~MEM (Var (FST p)) i.inst_operands /\
              ~MEM (FST p) i.inst_outputs) us ==>
  ((?t. step_inst fuel C i
     (FOLDL (\u p. update_var (FST p) (SND p) u) s us) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[dft_abort_update_iff]
QED

Theorem dft_invoke_halt_fold_iff:
  !us s.
  i.inst_opcode = INVOKE /\
  EVERY (\p. ~MEM (Var (FST p)) i.inst_operands /\
              ~MEM (FST p) i.inst_outputs) us ==>
  (step_inst fuel C i
     (FOLDL (\u p. update_var (FST p) (SND p) u) s us) = Halt t <=>
   step_inst fuel C i s = Halt t)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  `!z. MEM (Var z) i.inst_operands ==> FST h <> z` by metis_tac[] >>
  drule_all step_inst_invoke_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `SND h`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[] >> metis_tac[]
QED

Theorem dft_error_idx_iff:
  ~is_terminator i.inst_opcode ==>
  (step_inst fuel C i (s with vs_inst_idx := n) = Error e <=>
   step_inst fuel C i s = Error e)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE` >>
  simp[invoke_step_inst_idx_OK_only, step_inst_idx_indep] >>
  Cases_on `step_inst fuel C i s` >> simp[exec_result_map_def]
QED

Theorem dft_abort_idx_iff:
  ~is_terminator i.inst_opcode ==>
  ((?t. step_inst fuel C i (s with vs_inst_idx := n) = Abort a t) <=>
   (?t. step_inst fuel C i s = Abort a t))
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE` >>
  simp[invoke_step_inst_idx_OK_only, step_inst_idx_indep] >>
  Cases_on `step_inst fuel C i s` >> simp[exec_result_map_def] >> metis_tac[]
QED

Theorem dft_invoke_halt_idx_iff:
  i.inst_opcode = INVOKE ==>
  (step_inst fuel C i (s with vs_inst_idx := n) = Halt t <=>
   step_inst fuel C i s = Halt t)
Proof
  strip_tac >> simp[invoke_step_inst_idx_OK_only] >>
  Cases_on `step_inst fuel C i s` >> simp[]
QED

(* The proposed NoFail-only guard does not cover competing fallible errors. *)
Theorem dft_competing_assert_guard_probe:
  !s fuel C.
  FLOOKUP s.vs_vars "missing" = NONE ==>
  dft_ok_swap_pair (mk_inst 0 ASSERT [Lit 0w] [])
                   (mk_inst 1 ASSERT [Var "missing"] []) /\
  inst_wf (mk_inst 0 ASSERT [Lit 0w] []) /\
  inst_wf (mk_inst 1 ASSERT [Var "missing"] []) /\
  opcode_fail_class ASSERT <> NoFail /\
  step_inst fuel C (mk_inst 0 ASSERT [Lit 0w] []) s =
    Abort Revert_abort (revert_state (set_returndata [] s)) /\
  step_inst fuel C (mk_inst 1 ASSERT [Var "missing"] []) s =
    Error "undefined operand"
Proof
  rpt strip_tac >>
  simp[dft_ok_swap_pair_def, mk_inst_def, inst_defs_def, inst_uses_def,
       operand_vars_def, effects_independent_def, abort_compatible_def,
       read_effects_def, write_effects_def, empty_effects_def,
       is_terminator_def, is_alloca_op_def, is_pseudo_def,
       inst_wf_def, opcode_fail_class_def] >>
  gvs[opcode_fail_class_def] >>
  simp[step_inst_non_invoke, mk_inst_def] >>
  simp[step_inst_base_def, eval_operand_def, lookup_var_def]
QED

(* Operand readiness is required even for CanRevert/CanExHalt opcodes. *)
Theorem dft_assert_operand_defined:
  i.inst_opcode = ASSERT /\ inst_wf i /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  (?t. step_inst fuel C i s = OK t) \/
  (?t. step_inst fuel C i s = Abort Revert_abort t)
Proof
  strip_tac >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `v = 0w` >> simp[]
QED

(* Readiness / stopping audit (C1.7.2).
   Proposed operand guard for EACH crossing instruction i at swap state s:
     (!v. MEM (Var v) i.inst_operands ==> v IN FDOM s.vs_vars) /\
     (i.inst_opcode <> INVOKE ==>
       !l. MEM (Label l) i.inst_operands ==> l IN FDOM s.vs_labels).
   Variables follow from dft_ready_operand_defined, including fallible i:
   strict dominator availability and data-closed executed prefixes supply
   its hypotheses. Non-INVOKE labels follow from ctx_labels_bound and label
   preservation along successful prefixes. dft_operand_defined then supplies
   evaluated operands for every non-INVOKE crossing instruction. INVOKE's
   target Label is NOT a state-label read; no extra label hypothesis is added
   for it or its arguments. INVOKE argument/lookup/callee errors must instead
   be transported by the existing empty-write frame interface.

   Readiness is NOT the complete swap premise. inst_wf, dft_ok_swap_pair,
   and ORIGINAL-ORDER inversion legality must also be retained. In particular,
   ASSERT, ASSERT_UNREACHABLE and INVALID have empty declared effects and
   no outputs: dft_must_order forces them before every following instruction.
   They cannot be moved right across a runtime-error instruction. The
   NoFail runtime-error family is DELEGATECALL/CREATE/CREATE2; all read all
   effects. Their partners have empty writes, and their Error behavior has
   the dft_empty_write_error_iff frame. It would be unsound to claim a
   symmetric stopping diamond using readiness and dft_ok_swap_pair alone.

   Competing fallible audit:
   CanRevert = ASSERT only: evaluated operand yields OK or Revert (above).
   CanExHalt = ASSERT_UNREACHABLE, INVALID, RETURNDATACOPY: evaluated operands
   and inst_wf exclude structural Error; only OK or ExHalt remains. For
   RETURNDATACOPY the residual bounds test aborts, it does not Error.
   Revert/ExHalt pairs and INVOKE with either class are incompatible.
   INVOKE/INVOKE is excluded by effect conflict. INVOKE with a NoFail partner
   can still Error, Abort, IntRet or Halt internally; only OK/Abort/Halt/Error
   escape step_inst, and the empty-write partner frame must preserve exact
   Halt, not the caller's variable-updated state. NoFail non-runtime-error
   partners are total by dft_guarded_nofail_total once operands are ready.
   Thus the next stopping theorem must be DIRECTIONAL and include the root
   inversion restriction; operand readiness alone is not its full interface.
*)
