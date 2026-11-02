(* Constructor-level stopping observations for indexed DFT swaps. *)
Theory dftStoppingSwap
Ancestors
  dftSuccessSwap dftCommutation analysisSimProofsBase venomExecSemantics
  venomState venomInst venomEffects venomWf instIdxIndep list opcodeClass
  dftIndexedExec dftGuards
Libs
  stepInstBaseLib

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

Theorem dft_canexhalt_operand_defined:
  inst_wf i /\ opcode_fail_class i.inst_opcode = CanExHalt /\
  (!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  (?t. step_inst fuel C i s = OK t) \/
  (?t. step_inst fuel C i s = Abort ExHalt_abort t)
Proof
  strip_tac >>
  `i.inst_opcode = ASSERT_UNREACHABLE \/
   i.inst_opcode = RETURNDATACOPY \/ i.inst_opcode = INVALID` by
    (Cases_on `i.inst_opcode` >> gvs[opcode_fail_class_def]) >>
  gvs[inst_wf_def] >>
  simp[step_inst_non_invoke] >>
  with_opcode_clause simp >>
  gvs[LENGTH_EQ_NUM_compute] >>
  rpt IF_CASES_TAC >> simp[] >>
  `?a. eval_operand h s = SOME a` by metis_tac[] >>
  `?b. eval_operand h' s = SOME b` by metis_tac[] >>
  `?c. eval_operand h'' s = SOME c` by metis_tac[] >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem dft_nonterminator_no_intret:
  ~is_terminator i.inst_opcode ==> step_inst fuel C i s <> IntRet vs t
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (simp[step_inst_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >>
  simp[step_inst_non_invoke] >> strip_tac >>
  drule step_inst_base_intret_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem dft_exec_suffix_swap_both_ok:
  dft_ok_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  step_inst fuel C x s = OK sx /\
  step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy ==>
  dft_exec_suffix fuel C (x::y::tail) s =
  dft_exec_suffix fuel C (y::x::tail) s
Proof
  strip_tac >>
  drule_all dft_indexed_step_swap_ok >> strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_ok_swap_pair_def] >>
  simp[dft_exec_suffix_def]
QED

Theorem dft_empty_write_abort_iff:
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ write_effects x.inst_opcode = empty_effects /\
  step_inst fuel C x s = OK t /\
  (!v. MEM v x.inst_outputs ==>
       ~MEM (Var v) y.inst_operands /\ ~MEM v y.inst_outputs) ==>
  ((?u. step_inst fuel C y t = Abort a u) <=>
   (?u. step_inst fuel C y s = Abort a u))
Proof
  strip_tac >> drule_all dft_empty_write_ok_updates >> strip_tac >>
  gvs[] >> irule dft_abort_fold_iff >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem dft_empty_write_invoke_halt_iff:
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ write_effects x.inst_opcode = empty_effects /\
  step_inst fuel C x s = OK t /\ y.inst_opcode = INVOKE /\
  (!v. MEM v x.inst_outputs ==>
       ~MEM (Var v) y.inst_operands /\ ~MEM v y.inst_outputs) ==>
  (step_inst fuel C y t = Halt u <=> step_inst fuel C y s = Halt u)
Proof
  strip_tac >> drule_all dft_empty_write_ok_updates >> strip_tac >>
  gvs[] >> irule dft_invoke_halt_fold_iff >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem dft_ok_swap_pair_output_frame:
  dft_ok_swap_pair x y ==>
  (!v. MEM v x.inst_outputs ==>
       ~MEM (Var v) y.inst_operands /\ ~MEM v y.inst_outputs)
Proof
  strip_tac >>
  gvs[dft_ok_swap_pair_def, inst_defs_def, inst_uses_def,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[dftBlockSimTheory.mem_var_operand_vars]
QED

Theorem dft_exec_suffix_second_invoke_halt:
  dft_ok_swap_pair x y /\
  write_effects x.inst_opcode = empty_effects /\ y.inst_opcode = INVOKE /\
  step_inst fuel C x s = OK sx /\
  step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Halt t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Halt t /\
  dft_exec_suffix fuel C (y::x::tail) s = Halt t
Proof
  strip_tac >>
  drule dft_ok_swap_pair_output_frame >> strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo x.inst_opcode /\ x.inst_opcode <> ALLOCA` by
    (gvs[dft_ok_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
  `step_inst fuel C y sx = Halt t` by metis_tac[dft_invoke_halt_idx_iff] >>
  `step_inst fuel C y s = Halt t` by metis_tac[dft_empty_write_invoke_halt_iff] >>
  simp[dft_exec_suffix_def]
QED

Theorem dft_exec_suffix_swap_error:
  dft_ok_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  (step_inst fuel C x s = Error e \/
   (?sx. step_inst fuel C x s = OK sx /\
     step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Error e)) ==>
  (!t. dft_exec_suffix fuel C (y::x::tail) s <> OK t) /\
  (!v t. dft_exec_suffix fuel C (y::x::tail) s <> IntRet v t)
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_ok_swap_pair_def] >>
  `dft_ok_swap_pair y x` by metis_tac[dft_ok_swap_pair_sym] >>
  `(!v t. step_inst fuel C y s <> IntRet v t) /\
   (!u v t. step_inst fuel C x u <> IntRet v t)` by
    metis_tac[dft_nonterminator_no_intret] >>
  Cases_on `step_inst fuel C y s` >>
  gvs[dft_exec_suffix_def] >>
  rename1 `step_inst fuel C y s = OK sy` >>
  Cases_on `step_inst fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx)` >>
  gvs[] >>
  drule_all dft_indexed_step_swap_ok >> strip_tac >> gvs[]
QED

Theorem dft_invoke_partner_class:
  dft_ok_swap_pair x y /\ x.inst_opcode = INVOKE ==>
  write_effects y.inst_opcode = empty_effects /\
  opcode_fail_class y.inst_opcode = NoFail /\
  ~dft_runtime_error_opcode y.inst_opcode
Proof
  strip_tac >> Cases_on `y.inst_opcode` >>
  simp[write_effects_def, opcode_fail_class_def, dft_runtime_error_opcode_def] >>
  gvs[dft_ok_swap_pair_def, effects_independent_def, abort_compatible_def,
      opcode_fail_class_def, read_effects_def, write_effects_def,
      dft_runtime_error_opcode_def, all_effects_def, empty_effects_def]
QED

Theorem dft_nonterminator_halt_invoke:
  ~is_terminator i.inst_opcode /\ step_inst fuel C i s = Halt t ==>
  i.inst_opcode = INVOKE
Proof
  strip_tac >> spose_not_then assume_tac >>
  gvs[step_inst_non_invoke] >> drule step_inst_base_halt_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem dft_exec_suffix_first_invoke_halt:
  dft_ok_swap_pair x y /\ x.inst_opcode = INVOKE /\
  write_effects y.inst_opcode = empty_effects /\
  step_inst fuel C y s = OK sy /\ step_inst fuel C x s = Halt t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Halt t /\
  dft_exec_suffix fuel C (y::x::tail) s = Halt t
Proof
  strip_tac >>
  `dft_ok_swap_pair y x` by metis_tac[dft_ok_swap_pair_sym] >>
  `!v. MEM v y.inst_outputs ==>
       ~MEM (Var v) x.inst_operands /\ ~MEM v x.inst_outputs` by
    metis_tac[dft_ok_swap_pair_output_frame] >>
  `~is_terminator y.inst_opcode /\ ~is_pseudo y.inst_opcode /\
   y.inst_opcode <> ALLOCA` by
    (gvs[dft_ok_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
  `step_inst fuel C x sy = Halt t` by metis_tac[dft_empty_write_invoke_halt_iff] >>
  `step_inst fuel C x (sy with vs_inst_idx := SUC s.vs_inst_idx) = Halt t` by
    metis_tac[dft_invoke_halt_idx_iff] >>
  simp[dft_exec_suffix_def]
QED

Theorem dft_exec_suffix_swap_halt:
  dft_ok_swap_pair x y /\ inst_wf y /\
  (y.inst_opcode <> INVOKE ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  (step_inst fuel C x s = Halt t \/
   (?sx. step_inst fuel C x s = OK sx /\
     step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Halt t)) ==>
  dft_exec_suffix fuel C (x::y::tail) s = Halt t /\
  dft_exec_suffix fuel C (y::x::tail) s = Halt t
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo y.inst_opcode /\ y.inst_opcode <> ALLOCA` by
    (gvs[dft_ok_swap_pair_def] >> metis_tac[is_alloca_op_def])
  >- (`x.inst_opcode = INVOKE` by metis_tac[dft_nonterminator_halt_invoke] >>
      drule_all dft_invoke_partner_class >> strip_tac >>
      `y.inst_opcode <> INVOKE` by (strip_tac >> gvs[opcode_fail_class_def]) >>
      `?sy. step_inst fuel C y s = OK sy` by metis_tac[dft_guarded_nofail_total] >>
      irule dft_exec_suffix_first_invoke_halt >> metis_tac[]) >>
  `y.inst_opcode = INVOKE` by metis_tac[dft_nonterminator_halt_invoke] >>
  `dft_ok_swap_pair y x` by metis_tac[dft_ok_swap_pair_sym] >>
  `write_effects x.inst_opcode = empty_effects` by metis_tac[dft_invoke_partner_class] >>
  irule dft_exec_suffix_second_invoke_halt >> metis_tac[]
QED

Theorem dft_noninvoke_abort_replay:
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  (!op. MEM op i.inst_operands ==> eval_operand op s' = eval_operand op s) /\
  (i.inst_opcode = RETURNDATACOPY ==> s'.vs_returndata = s.vs_returndata) /\
  step_inst fuel C i s = Abort a t ==>
  ?t'. step_inst fuel C i s' = Abort a t'
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_terminator_def] >>
  with_opcode_clause gvs >> gvs[AllCaseEqs()]
QED

Theorem dft_pair_abort_iff:
  dft_ok_swap_pair x y /\
  step_inst fuel C x s = OK t ==>
  ((?u. step_inst fuel C y t = Abort a u) <=>
   (?u. step_inst fuel C y s = Abort a u))
Proof
  strip_tac >> drule dft_ok_swap_pair_output_frame >> strip_tac >>
  `~is_terminator y.inst_opcode /\ ~is_terminator x.inst_opcode /\
   ~is_alloca_op x.inst_opcode /\
   effects_independent x.inst_opcode y.inst_opcode` by gvs[dft_ok_swap_pair_def] >>
  Cases_on `y.inst_opcode = INVOKE`
  >- (`dft_ok_swap_pair y x` by metis_tac[dft_ok_swap_pair_sym] >>
      `write_effects x.inst_opcode = empty_effects` by
        metis_tac[dft_invoke_partner_class] >>
      irule dft_empty_write_abort_iff >>
      gvs[dft_ok_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
  `!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> irule dftBlockSimTheory.eval_operand_step_pres >>
     qexistsl_tac [`C`, `fuel`, `x`] >> simp[] >> metis_tac[]) >>
  `(y.inst_opcode = RETURNDATACOPY ==> t.vs_returndata = s.vs_returndata)` by
    (strip_tac >> irule venomInstProofsTheory.write_effects_sound_returndata >>
     qexistsl_tac [`C`, `fuel`, `x`] >> simp[] >>
     gvs[effects_independent_def, read_effects_def, empty_effects_def,
         pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  eq_tac >> strip_tac >> irule dft_noninvoke_abort_replay >>
  metis_tac[]
QED

Theorem dft_exec_suffix_second_abort:
  dft_ok_swap_pair x y /\
  step_inst fuel C x s = OK sx /\
  step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Abort a t /\
  ?u. dft_exec_suffix fuel C (y::x::tail) s = Abort a u
Proof
  strip_tac >>
  drule dft_ok_swap_pair_output_frame >> strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo x.inst_opcode /\ x.inst_opcode <> ALLOCA` by
    (gvs[dft_ok_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
  `?u. step_inst fuel C y sx = Abort a u` by metis_tac[dft_abort_idx_iff] >>
  `?u. step_inst fuel C y s = Abort a u` by metis_tac[dft_pair_abort_iff] >>
  simp[dft_exec_suffix_def]
QED

Theorem dft_nonroot_abort_class:
  inst_wf x /\ ~is_terminator x.inst_opcode /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  step_inst fuel C x s = Abort a t ==>
  x.inst_opcode = INVOKE \/ (x.inst_opcode = RETURNDATACOPY /\ a = ExHalt_abort)
Proof
  strip_tac >> Cases_on `x.inst_opcode = INVOKE` >- simp[] >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_terminator_def, inst_wf_def, read_effects_def, write_effects_def] >>
  with_opcode_clause gvs >> gvs[AllCaseEqs()]
QED

Theorem dft_returndatacopy_partner_class:
  dft_ok_swap_pair x y /\ x.inst_opcode = RETURNDATACOPY ==>
  (opcode_fail_class y.inst_opcode = NoFail /\
   ~dft_runtime_error_opcode y.inst_opcode) \/
  opcode_fail_class y.inst_opcode = CanExHalt
Proof
  strip_tac >> Cases_on `y.inst_opcode` >>
  simp[write_effects_def, opcode_fail_class_def, dft_runtime_error_opcode_def] >>
  gvs[dft_ok_swap_pair_def, effects_independent_def, abort_compatible_def,
      opcode_fail_class_def, read_effects_def, write_effects_def,
      dft_runtime_error_opcode_def, all_effects_def, empty_effects_def]
QED

Theorem dft_exec_suffix_first_abort:
  dft_ok_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  step_inst fuel C x s = Abort a t ==>
  dft_exec_suffix fuel C (x::y::tail) s = Abort a t /\
  ?u. dft_exec_suffix fuel C (y::x::tail) s = Abort a u
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo y.inst_opcode /\ y.inst_opcode <> ALLOCA` by
    (gvs[dft_ok_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
  `(?sy. step_inst fuel C y s = OK sy) \/
   (?u. step_inst fuel C y s = Abort a u)` by
    (drule_all dft_nonroot_abort_class >> strip_tac
     >- (drule_all dft_invoke_partner_class >> strip_tac >>
         `y.inst_opcode <> INVOKE` by (strip_tac >> gvs[opcode_fail_class_def]) >>
         metis_tac[dft_guarded_nofail_total]) >>
     drule_all dft_returndatacopy_partner_class >> strip_tac >>
     `y.inst_opcode <> INVOKE` by (strip_tac >> gvs[opcode_fail_class_def])
     >- metis_tac[dft_guarded_nofail_total] >>
     metis_tac[dft_canexhalt_operand_defined])
  >- (`dft_ok_swap_pair y x` by metis_tac[dft_ok_swap_pair_sym] >>
      `?u. step_inst fuel C x sy = Abort a u` by metis_tac[dft_pair_abort_iff] >>
      `?u. step_inst fuel C x
          (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort a u` by
        metis_tac[dft_abort_idx_iff] >>
      simp[dft_exec_suffix_def]) >>
  simp[dft_exec_suffix_def]
QED

Theorem dft_exec_suffix_swap:
  dft_ok_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  (!v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars) /\
  (y.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels) /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) ==>
  case dft_exec_suffix fuel C (x::y::tail) s of
    OK t => dft_exec_suffix fuel C (y::x::tail) s = OK t
  | IntRet v t => dft_exec_suffix fuel C (y::x::tail) s = IntRet v t
  | Halt t => dft_exec_suffix fuel C (y::x::tail) s = Halt t
  | Abort a t => ?a' t'. dft_exec_suffix fuel C (y::x::tail) s = Abort a' t' /\
                         (a = Revert_abort ==> a' = Revert_abort)
  | Error e => (!t. dft_exec_suffix fuel C (y::x::tail) s <> OK t) /\
               (!v t. dft_exec_suffix fuel C (y::x::tail) s <> IntRet v t)
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_ok_swap_pair_def] >>
  `(y.inst_opcode <> INVOKE ==>
    !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v)` by
    metis_tac[dft_operand_defined] >>
  reverse (Cases_on `step_inst fuel C x s`)
  >- (simp[Once dft_exec_suffix_def] >> irule dft_exec_suffix_swap_error >> metis_tac[])
  >- metis_tac[dft_nonterminator_no_intret]
  >- (`?u. dft_exec_suffix fuel C (y::x::tail) s = Abort a u` by
        metis_tac[dft_exec_suffix_first_abort] >> simp[Once dft_exec_suffix_def] >> metis_tac[])
  >- (`dft_exec_suffix fuel C (y::x::tail) s = Halt v` by
        metis_tac[dft_exec_suffix_swap_halt] >> simp[Once dft_exec_suffix_def]) >>
  rename1 `step_inst fuel C x s = OK sx` >>
  reverse (Cases_on `step_inst fuel C y (sx with vs_inst_idx := SUC s.vs_inst_idx)`)
  >- (simp[Once dft_exec_suffix_def, Once dft_exec_suffix_def] >>
      irule dft_exec_suffix_swap_error >> metis_tac[])
  >- metis_tac[dft_nonterminator_no_intret]
  >- (`?u. dft_exec_suffix fuel C (y::x::tail) s = Abort a u` by
        metis_tac[dft_exec_suffix_second_abort] >>
      simp[Once dft_exec_suffix_def, Once dft_exec_suffix_def] >> metis_tac[])
  >- (`dft_exec_suffix fuel C (y::x::tail) s = Halt v` by
        metis_tac[dft_exec_suffix_swap_halt] >>
      simp[Once dft_exec_suffix_def, Once dft_exec_suffix_def]) >>
  `dft_exec_suffix fuel C (x::y::tail) s = dft_exec_suffix fuel C (y::x::tail) s` by
    metis_tac[dft_exec_suffix_swap_both_ok] >>
  pop_assum SUBST1_TAC >> Cases_on `dft_exec_suffix fuel C (y::x::tail) s` >> simp[]
QED
