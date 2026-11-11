(* Remove-unused proof infrastructure.
 *
 * Retains instruction transport, syntactic removal/output facts, liveness and
 * SSA facts, generic relation composition and structural OWHILE interfaces.
 * The obsolete same-oracle block/function simulations have been removed:
 * deleted GAS consumes a reading, so correctness needs backward oracle
 * reconstruction. Removable instructions outside the must-preserve boundary
 * are effect-free OR GAS; ALLOCA remains protected by that boundary.
 *)

Theory removeUnusedProofs
Ancestors
  removeUnusedDefs passSimulationProps analysisSimProps venomInstProps venomWf
  opcodeClass execEquivProps livenessProofs passSharedDefs passSharedProps venomInst
  stateEquiv stateEquivProofs venomExecProofs venomExecProps
  venomState venomExecSemantics indexedLists cfgTransform cfgAnalysisProps pointerConfinedDefs
  venomWfProps
Libs
  pairLib

(* ===== Per-instruction: effect-free removable → state_equiv ===== *)

(* Outside the pass-owned must-preserve boundary, GAS is the sole
   removable opcode that is not effect-free. *)
Theorem removable_not_preserved_effect_free[local]:
  !inst. is_removable inst /\
         ~remove_unused_must_preserve_op inst.inst_opcode ==>
         is_effect_free_op inst.inst_opcode \/ inst.inst_opcode = GAS
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_removable_def, remove_unused_must_preserve_op_def,
      is_volatile_def, is_terminator_def, is_effect_free_op_def]
QED

(* Per-instruction NOP correctness: if an effect-free instruction
   steps to OK s', then s and s' agree on everything except outputs. *)
Theorem nop_removable_state_equiv:
  !fuel ctx inst s s'.
    is_effect_free_op inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  metis_tac[step_effect_free_state_equiv]
QED

(* ===== state_equiv helpers for INVOKE handling ===== *)

(* FOLDL update_var preserves state_equiv *)
Theorem foldl_update_var_state_equiv:
  !pairs s1 s2 vars.
    state_equiv vars s1 s2 ==>
    state_equiv vars
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct >> rw[] >>
  PairCases_on `h` >> gvs[] >>
  first_x_assum irule >>
  gvs[state_equiv_def, execution_equiv_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* eval_operands on state_equiv states with operand vars outside vars *)
Theorem eval_operands_state_equiv:
  !ops s1 s2 vars.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> rw[eval_operands_def] >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  `eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_equiv >> qexists_tac `vars` >> simp[] >>
     metis_tac[]) >>
  gvs[]
QED

(* setup_callee on state_equiv states gives same result *)
Theorem setup_callee_state_equiv:
  !fn args s1 s2 vars.
    state_equiv vars s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[setup_callee_def] >>
  gvs[state_equiv_def, execution_equiv_def] >>
  rw[venomStateTheory.venom_state_component_equality]
QED

(* merge_callee_state on state_equiv callers gives state_equiv result *)
Theorem merge_callee_state_equiv[local]:
  !s1 s2 callee vars.
    state_equiv vars s1 s2 ==>
    state_equiv vars (merge_callee_state s1 callee)
                     (merge_callee_state s2 callee)
Proof
  rw[state_equiv_def, execution_equiv_def, merge_callee_state_def] >>
  gvs[lookup_var_def]
QED

Theorem execution_equiv_refl[local]:
  !vars s. execution_equiv vars s s
Proof
  rw[execution_equiv_def]
QED

(* step_inst result_equiv for ALL non-terminator instructions including INVOKE.
   Extends the base step_inst_result_equiv which only covers step_inst_base. *)
Theorem step_inst_result_equiv_full:
  !vars fuel ctx inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~is_terminator inst.inst_opcode ==>
    result_equiv vars (step_inst fuel ctx inst s1)
                      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    simp[step_inst_def] >>
    Cases_on `decode_invoke inst` >> gvs[result_equiv_def] >>
    PairCases_on `x` >> gvs[] >>
    rename1 `SOME (callee_name, arg_ops)` >>
    `inst.inst_operands = Label callee_name :: arg_ops`
      by gvs[decode_invoke_def, AllCaseEqs()] >>
    `eval_operands arg_ops s1 = eval_operands arg_ops s2` by (
      irule eval_operands_state_equiv >> qexists_tac `vars` >> gvs[] >>
      rpt strip_tac >> first_x_assum irule >> gvs[]) >>
    Cases_on `lookup_function callee_name ctx.ctx_functions`
    >> gvs[result_equiv_def] >>
    Cases_on `eval_operands arg_ops s2` >> gvs[result_equiv_def] >>
    rename1 `SOME args` >>
    `setup_callee x args s1 = setup_callee x args s2`
      by (irule setup_callee_state_equiv >> metis_tac[]) >>
    Cases_on `setup_callee x args s2` >> gvs[result_equiv_def] >>
    Cases_on `run_blocks fuel ctx x x'` >> simp[] >>
    gvs[result_equiv_def, execution_equiv_refl] >>
    (* Only IntRet case remains *)
    `state_equiv vars (merge_callee_state s1 v)
                      (merge_callee_state s2 v)` by
      (irule merge_callee_state_equiv >> gvs[]) >>
    `state_equiv vars (adopt_return_fmp i (merge_callee_state s1 v))
                      (adopt_return_fmp i (merge_callee_state s2 v))` by
      (Cases_on `i.iret_adopt_fmp` >>
       gvs[adopt_return_fmp_def, state_equiv_def, execution_equiv_def,
           lookup_var_def]) >>
    simp[bind_outputs_def] >>
    IF_CASES_TAC >> gvs[result_equiv_def] >>
    irule foldl_update_var_state_equiv >> gvs[])
  >> (irule step_inst_result_equiv >> gvs[])
QED

(* ===== state_equiv composition for NOP'd instruction case ===== *)

(* When s1≈s2 on vars, and s1≈s1' on outs where outs⊆vars,
   then s1'≈s2 on vars. Used when NOP'ing: s1' is original post-state
   (only outputs changed), s2 is NOP'd post-state (unchanged). *)
Theorem state_equiv_effect_free_compose:
  !vars outs s1 s1' s2.
    state_equiv vars s1 s2 /\
    state_equiv outs s1 s1' /\
    outs SUBSET vars ==>
    state_equiv vars s1' s2
Proof
  rpt strip_tac >>
  `state_equiv vars s1 s1'` by metis_tac[state_equiv_subset] >>
  `state_equiv vars s1' s1` by metis_tac[state_equiv_sym] >>
  metis_tac[state_equiv_trans]
QED

(* When s1≈s2 on V, and s1≈s1' on W (e.g. effect-free step outputs),
   then s1'≈s2 on V∪W. For any x ∉ V∪W: x ∉ V so s1(x)=s2(x), and
   x ∉ W so s1(x)=s1'(x), hence s1'(x)=s2(x). *)
Theorem state_equiv_union_compose:
  !V W s1 s1' s2.
    state_equiv V s1 s2 /\
    state_equiv W s1 s1' ==>
    state_equiv (V UNION W) s1' s2
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  metis_tac[lookup_var_def]
QED

(* ===== Block-level ===== *)

(* Outputs NOP'd by remove_unused_block *)
Definition block_nop_outputs_def:
  block_nop_outputs lr bb =
    set (FLAT (MAPi (\idx inst.
      let live = live_after_at lr bb.bb_label idx
                   (LENGTH bb.bb_instructions) in
      if ~remove_unused_must_preserve_op inst.inst_opcode /\
         is_removable inst /\
         EVERY (\v. ~MEM v live) inst.inst_outputs
      then inst.inst_outputs
      else [])
      bb.bb_instructions))
End

(* Helper: get_instruction on transformed block *)
Theorem get_instruction_remove_unused:
  !lr bb idx.
    get_instruction (remove_unused_block lr bb) idx =
    if idx < LENGTH bb.bb_instructions then
      SOME (remove_unused_inst
              (live_after_at lr bb.bb_label idx
                (LENGTH bb.bb_instructions))
              (EL idx bb.bb_instructions))
    else NONE
Proof
  rw[get_instruction_def, remove_unused_block_def, LENGTH_MAPi] >>
  simp[EL_MAPi]
QED

(* Helper: NOP'd instruction outputs are in block_nop_outputs *)
Theorem nop_outputs_in_block_nop_outputs:
  !lr bb idx inst.
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    remove_unused_inst
      (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions))
      inst = mk_nop_inst inst ==>
    set inst.inst_outputs SUBSET block_nop_outputs lr bb
Proof
  rpt strip_tac >>
  simp[block_nop_outputs_def, pred_setTheory.SUBSET_DEF,
       listTheory.MEM_FLAT, MEM_MAPi] >>
  rpt strip_tac >>
  qexists_tac `inst.inst_outputs` >> simp[] >>
  qexists_tac `idx` >> simp[] >>
  gvs[remove_unused_inst_def, mk_nop_inst_def] >>
  rpt (pop_assum mp_tac) >>
  rpt IF_CASES_TAC >> simp[instruction_component_equality] >> gvs[]
QED

(* Helper: remove_unused_inst either returns inst or mk_nop_inst inst *)
Theorem remove_unused_inst_cases:
  !live inst.
    remove_unused_inst live inst = inst \/
    remove_unused_inst live inst = mk_nop_inst inst
Proof
  rw[remove_unused_inst_def] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Triviality resolve_phi_MEM:
  !prev ops op. resolve_phi prev ops = SOME op ==> MEM op ops
Proof
  recInduct resolve_phi_ind >> rw[resolve_phi_def] >> metis_tac[]
QED

Triviality eval_one_phi_state_equiv:
  !vars s1 s2 inst out v.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    eval_one_phi s1 inst = SOME (out,v) ==>
    eval_one_phi s2 inst = SOME (out,v)
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def, AllCaseEqs()] >>
  rename1 `resolve_phi prev inst.inst_operands = SOME op` >>
  `MEM op inst.inst_operands` by metis_tac[resolve_phi_MEM] >>
  sg `eval_operand op s1 = eval_operand op s2`
  >- (irule stateEquivProofsTheory.eval_operand_equiv >>
      qexists_tac `vars` >> simp[] >> Cases_on `op` >> gvs[]) >>
  gvs[state_equiv_def] >> metis_tac[]
QED

(* NOP'd instruction is effect-free: either it was already NOP,
   or it was removable and not ALLOCA. *)
Theorem remove_unused_inst_nop_effect_free:
  !live inst.
    remove_unused_inst live inst = mk_nop_inst inst ==>
    is_effect_free_op inst.inst_opcode \/ inst.inst_opcode = GAS
Proof
  rw[remove_unused_inst_def] >>
  rpt (pop_assum mp_tac) >>
  rpt IF_CASES_TAC >> gvs[mk_nop_inst_def,
    instruction_component_equality] >>
  gvs[is_removable_def, is_volatile_def]
  >- simp[is_effect_free_op_def]
  >- simp[is_effect_free_op_def]
  >- (rpt strip_tac >>
      irule removable_not_preserved_effect_free >>
      simp[is_removable_def, remove_unused_must_preserve_op_def])
QED

(* NOP'd instruction is not a terminator *)
Theorem remove_unused_inst_nop_not_terminator:
  !live inst.
    remove_unused_inst live inst = mk_nop_inst inst ==>
    ~is_terminator inst.inst_opcode
Proof
  rw[remove_unused_inst_def] >>
  rpt (pop_assum mp_tac) >>
  rpt IF_CASES_TAC >> gvs[mk_nop_inst_def,
    instruction_component_equality, is_removable_def] >>
  simp[is_terminator_def]
QED

Triviality exec_result_helpers_no_halt_abort[simp]:
  (!f inst s s'. exec_pure1 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure1 f inst s <> Abort a s') /\
  (!f inst s s'. exec_pure2 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure2 f inst s <> Abort a s') /\
  (!f inst s s'. exec_pure3 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure3 f inst s <> Abort a s') /\
  (!f inst s s'. exec_read0 f inst s <> Halt s') /\
  (!f inst s a s'. exec_read0 f inst s <> Abort a s') /\
  (!f inst s s'. exec_read1 f inst s <> Halt s') /\
  (!f inst s a s'. exec_read1 f inst s <> Abort a s') /\
  (!f inst s s'. exec_write2 f inst s <> Halt s') /\
  (!f inst s a s'. exec_write2 f inst s <> Abort a s') /\
  (!inst s alloc_size s'. exec_alloca inst s alloc_size <> Halt s') /\
  (!inst s alloc_size a s'. exec_alloca inst s alloc_size <> Abort a s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_gas_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_result_helpers_not_intret[simp]:
  (!f inst s vs s'. exec_pure1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure2 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure3 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read0 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_write2 f inst s <> IntRet vs s') /\
  (!inst s alloc_size vs s'. exec_alloca inst s alloc_size <> IntRet vs s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_gas_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_not_intret[simp]:
  (!inst s g a v ao as_ ro rs is_s vs s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> IntRet vs s') /\
  (!inst s g a ao as_ ro rs vs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> IntRet vs s') /\
  (!inst s v off sz salt vs s'.
     exec_create inst s v off sz salt <> IntRet vs s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_no_halt_abort[simp]:
  (!inst s g a v ao as_ ro rs is_s s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Halt s') /\
  (!inst s g a v ao as_ ro rs is_s ab s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Abort ab s') /\
  (!inst s g a ao as_ ro rs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Halt s') /\
  (!inst s g a ao as_ ro rs ab s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Abort ab s') /\
  (!inst s v off sz salt s'.
     exec_create inst s v off sz salt <> Halt s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

val step_base_result_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def];

Theorem step_inst_base_no_halt[local]:
  !inst s s'. step_inst_base inst s = Halt s' ==>
              is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  drule opcodeClassTheory.step_inst_base_halt_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem step_inst_base_no_intret[local]:
  !inst s vs s'. step_inst_base inst s = IntRet vs s' ==>
                 is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  drule opcodeClassTheory.step_inst_base_intret_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem step_inst_base_no_abort[local]:
  !inst s a s'. step_inst_base inst s = Abort a s' /\
                ~is_terminator inst.inst_opcode ==>
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = CREATE \/
    inst.inst_opcode = CREATE2 \/
    inst.inst_opcode = RETURNDATACOPY \/
    (s.vs_call_ctx.cc_static /\
     (inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE \/
      inst.inst_opcode = LOG \/ inst.inst_opcode = SELFDESTRUCT \/
      inst.inst_opcode = CALL))
Proof
  rpt strip_tac >>
  drule opcodeClassTheory.step_inst_base_abort_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

(* Effect-free non-INVOKE step_inst can only return OK or Error. *)
Theorem effect_free_step_ok_or_error:
  !fuel ctx inst s.
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  `~is_terminator inst.inst_opcode`
    by metis_tac[is_effect_free_not_terminator] >>
  Cases_on `step_inst_base inst s` >> gvs[]
  >- (imp_res_tac step_inst_base_no_halt >> gvs[])
  >- (imp_res_tac step_inst_base_no_abort >>
      gvs[is_effect_free_op_def])
  >- (imp_res_tac step_inst_base_no_intret >> gvs[])
QED

(* result_equiv is exactly lift_result with the standard relations *)
Theorem result_equiv_is_lift_result[local]:
  !vars r1 r2.
    result_equiv vars r1 r2 ==>
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[result_equiv_def, lift_result_def]
QED

(* Shared tactic: apply block_sim IH with given V and s2 term *)
fun apply_block_ih_tac s2_term =
  first_x_assum (qspec_then
    `LENGTH bb.bb_instructions - SUC s1.vs_inst_idx` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `lr`, `V`, `bb`,
    `s1' with vs_inst_idx := SUC s1.vs_inst_idx`,
    s2_term] mp_tac) >>
  simp[] >>
  (impl_tac >- (
    conj_tac >- gvs[] >>
    gvs[state_equiv_def, execution_equiv_def] >>
    rw[] >> gvs[lookup_var_def])) >>
  simp[];

(* Block-level simulation parameterized over divergent set V.
   V must contain the NOP'd outputs (block_nop_outputs ⊆ V) and
   operand vars must not be in V. V is preserved through the block.
   
   WHY TRUE: At each instruction position:
   - Kept instruction: same code, operands ∉ V (by hypothesis) →
     step_inst_result_equiv gives result_equiv V.
   - NOP'd instruction: original runs effect-free inst, outputs ⊆ V.
     NOP identity on transformed. Compose via state_equiv_effect_free_compose. *)
(* Fixed-V same-state block simulation and its wrapper removed for consuming GAS. *)

(* ===== Function-level building blocks ===== *)

(* Weakening lift_result — copied from assignElimProofs *)
Theorem lift_result_weaken[local]:
  !R1_ok R2_ok R1_term R2_term r1 r2.
    (!s1 s2. R1_ok s1 s2 ==> R2_ok s1 s2) /\
    (!s1 s2. R1_term s1 s2 ==> R2_term s1 s2) /\
    lift_result R1_ok R1_term R1_term r1 r2 ==>
    lift_result R2_ok R2_term R2_term r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def]
QED

(* Compose lift_result with result_equiv: if r1 ~ r2 via lift_result
   and r2 ~ r3 via result_equiv (subset), then r1 ~ r3 via lift_result.
   Key pattern: NOP-insertion phase (lift_result) + NOP-cleanup (result_equiv). *)
Theorem lift_result_compose_result_equiv:
  !vars r1 r2 r3.
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars) r1 r2 /\
    result_equiv {} r2 r3 ==>
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars) r1 r3
Proof
  rpt strip_tac >>
  irule (REWRITE_RULE [AND_IMP_INTRO]
    passSimulationPropsTheory.lift_result_trans) >>
  rpt conj_tac
  >- metis_tac[stateEquivPropsTheory.state_equiv_trans]
  >- metis_tac[stateEquivPropsTheory.execution_equiv_trans] >>
  qexists_tac `r2` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule lift_result_weaken >>
  qexistsl_tac [`state_equiv {}`, `execution_equiv {}`] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      irule stateEquivPropsTheory.state_equiv_subset >>
      qexists_tac `{}` >> simp[])
  >- (rpt strip_tac >>
      irule stateEquivPropsTheory.execution_equiv_subset >>
      qexists_tac `{}` >> simp[])
  >- gvs[stateEquivPropsTheory.result_equiv_is_lift_result]
QED

(* ===== Function-level ===== *)

(* All NOP'd outputs across all blocks in one pass *)
Definition single_pass_nop_outputs_def:
  single_pass_nop_outputs fn =
    let lr = protect_liveness fn (remove_unused_phi_vars fn)
               (liveness_analyze fn) in
    BIGUNION (set (MAP (\bb.
      block_nop_outputs lr bb)
      fn.fn_blocks))
End

(* Label preservation for remove_unused_block *)
Theorem remove_unused_block_label:
  !lr bb. (remove_unused_block lr bb).bb_label = bb.bb_label
Proof
  rw[remove_unused_block_def]
QED

(* Block NOP outputs are subset of single_pass_nop_outputs *)
Theorem block_nop_outputs_subset_single_pass:
  !fn bb.
    MEM bb fn.fn_blocks ==>
    let lr = protect_liveness fn (remove_unused_phi_vars fn)
               (liveness_analyze fn) in
    let cfg = cfg_analyze fn in
    block_nop_outputs lr bb SUBSET single_pass_nop_outputs fn
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  simp[single_pass_nop_outputs_def, LET_THM] >>
  irule pred_setTheory.SUBSET_BIGUNION_I >>
  simp[listTheory.MEM_MAP] >> qexists_tac `bb` >> simp[]
QED

(* Helper: MEM (Var v) in a list implies MEM v (operand_vars list) *)
Theorem mem_var_operand_vars[local]:
  !ops v. MEM (Var v) ops ==> MEM v (operand_vars ops)
Proof
  Induct >> rw[operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_var_def]
QED

(* Helper: MEM (Var v) operands implies MEM v (inst_uses inst) *)
Theorem operand_var_in_inst_uses[local]:
  !inst v. MEM (Var v) inst.inst_operands ==>
           MEM v (inst_uses inst)
Proof
  rw[inst_uses_def] >> irule mem_var_operand_vars >> gvs[]
QED

(* live_after_at at position idx equals live_vars_at at SUC idx *)
Theorem live_after_at_suc:
  !lr lbl idx n. idx < n ==>
    live_after_at lr lbl idx n = live_vars_at lr lbl (SUC idx)
Proof
  rw[live_after_at_def, arithmeticTheory.ADD1] >>
  `idx + 1 = n` by simp[] >> gvs[]
QED

(* ===== Growing V block simulation with SSA + liveness ===== *)


(* ALL_DISTINCT inst_ids for a single block in a wf_function *)
Theorem block_inst_ids_distinct[local]:
  !bbs bb. MEM bb bbs /\
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id)
                                      bb.bb_instructions) bbs)) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  Induct >> rw[] >> gvs[listTheory.ALL_DISTINCT_APPEND]
QED

(* Block simulation with growing divergent set.
   Generalized with V (current excluded set) and two invariants:
   (1) V vars not live at current position
   (2) V vars not defined from current position onward
   The output is V_in ∪ block_nop_outputs (the full set for the block).
   V_in tracks vars from prior blocks (not defined in this block). *)
(* Per-position same-state SSA simulation removed for consuming GAS. *)

(* ===== SSA dead variable propagation ===== *)

(* ===== Path / dominance infrastructure ===== *)

(* Converting RTC to is_fn_path *)

(* ===== cfg_exec_path infrastructure for operand condition ===== *)

(* Helper: ALL_DISTINCT labels + MEM bb → lookup finds bb *)
Theorem lookup_block_all_distinct_mem[local]:
  !bbs bb. ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
           MEM bb bbs ==>
    lookup_block bb.bb_label bbs = SOME bb
Proof
  Induct >> simp[lookup_block_def, listTheory.FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  `bb.bb_label <> h.bb_label` by (
    spose_not_then strip_assume_tac >>
    `MEM bb.bb_label (MAP (\b. b.bb_label) bbs)` by
      (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
    gvs[]) >>
  fs[lookup_block_def]
QED

(* If ALL_DISTINCT (FLAT (MAP f ls)) and x in f(a) and x in f(b), then a = b *)

Theorem lookup_block_label[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >> rw[lookup_block_def, listTheory.FIND_thm] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Under ssa_form, var_defined_at for v determines the block and index *)
Theorem ssa_unique_var_defined_at:
  !fn def_bb def_idx v lbl idx.
    wf_function fn /\ ssa_form fn /\
    MEM def_bb fn.fn_blocks /\
    def_idx < LENGTH def_bb.bb_instructions /\
    MEM v (EL def_idx def_bb.bb_instructions).inst_outputs /\
    var_defined_at fn.fn_blocks lbl idx v ==>
    lbl = def_bb.bb_label /\ idx = def_idx
Proof
  rpt gen_tac >> strip_tac >>
  fs[livenessDefsTheory.var_defined_at_def, inst_defs_def] >>
  (* bb = def_bb via all_distinct_flat_map_inj on per-block outputs *)
  mp_tac (Q.ISPECL [
    `\(bb:basic_block). FLAT (MAP (\(i:instruction). i.inst_outputs) bb.bb_instructions)`,
    `fn.fn_blocks`, `bb:basic_block`, `def_bb:basic_block`, `v:string`
  ] all_distinct_flat_map_inj) >>
  (impl_tac >- (
    drule ssa_form_per_block >> simp[] >> strip_tac >>
    simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
    metis_tac[venomExecPropsTheory.lookup_block_MEM, listTheory.MEM_EL])) >>
  disch_then (fn th => FULL_SIMP_TAC (srw_ss()) [th]) >>
  (* idx = def_idx via all_distinct_outputs_unique_pos *)
  mp_tac (Q.SPECL [`fn.fn_blocks`, `def_bb`] all_distinct_outputs_block) >>
  (impl_tac >- fs[ssa_form_def, fn_insts_def]) >>
  strip_tac >>
  conj_tac >- metis_tac[lookup_block_label] >>
  fs[ssa_form_def, fn_insts_def] >>
  metis_tac[all_distinct_outputs_unique_pos]
QED

(* ===== Operand condition from wf_ssa ===== *)

Theorem protected_liveness_points_value[local]:
  !fn protected lr point live.
    MEM (point,live) (protected_liveness_points fn protected lr) ==>
    live = protected ++ live_vars_at lr (FST point) (SND point)
Proof
  rw[protected_liveness_points_def, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[PULL_EXISTS, listTheory.MEM_GENLIST] >> PairCases_on `point` >> gvs[]
QED

Theorem protected_liveness_points_key[local]:
  !fn protected lr bb idx.
    MEM bb fn.fn_blocks /\ idx <= LENGTH bb.bb_instructions ==>
    MEM (bb.bb_label,idx)
      (MAP FST (protected_liveness_points fn protected lr))
Proof
  rw[protected_liveness_points_def, listTheory.MEM_MAP,
     listTheory.MEM_FLAT] >>
  qexists_tac `((bb.bb_label,idx),
    protected ++ live_vars_at lr bb.bb_label idx)` >> simp[] >>
  qexists_tac `GENLIST
    (\i. ((bb.bb_label,i),protected ++ live_vars_at lr bb.bb_label i))
    (SUC (LENGTH bb.bb_instructions))` >> conj_tac
  >- (qexists_tac `bb` >> simp[])
  >- (simp[listTheory.MEM_GENLIST] >> qexists_tac `idx` >> simp[])
QED

Theorem live_vars_at_protect_liveness[local]:
  !fn protected lr bb idx.
    MEM bb fn.fn_blocks /\ idx <= LENGTH bb.bb_instructions ==>
    live_vars_at (protect_liveness fn protected lr) bb.bb_label idx =
    protected ++ live_vars_at lr bb.bb_label idx
Proof
  rpt strip_tac >>
  qspecl_then [`fn`, `protected`, `lr`, `bb`, `idx`]
    mp_tac protected_liveness_points_key >>
  impl_tac >- simp[] >> strip_tac >>
  rw[livenessDefsTheory.live_vars_at_def, protect_liveness_def,
     dfAnalyzeDefsTheory.df_at_def, alistTheory.FLOOKUP_FUPDATE_LIST] >>
  Cases_on `ALOOKUP
    (REVERSE (protected_liveness_points fn protected lr))
    (bb.bb_label,idx)`
  >- (gvs[alistTheory.ALOOKUP_NONE, listTheory.MEM_MAP] >> metis_tac[]) >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  `MEM ((bb.bb_label,idx),x)
     (protected_liveness_points fn protected lr)` by gvs[] >>
  drule protected_liveness_points_value >> strip_tac >>
  gvs[livenessDefsTheory.live_vars_at_def, dfAnalyzeDefsTheory.df_at_def]
QED

Theorem live_after_protect_liveness:
  !fn protected lr bb idx.
    MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions ==>
    live_after_at (protect_liveness fn protected lr) bb.bb_label idx
      (LENGTH bb.bb_instructions) =
    protected ++ live_after_at lr bb.bb_label idx
      (LENGTH bb.bb_instructions)
Proof
  rw[live_after_at_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  irule live_vars_at_protect_liveness >> simp[]
QED

(* Split a list at the LAST occurrence of an element *)
Theorem last_occurrence_split[local]:
  !(l:'a list) d.
    MEM d l ==>
    ?prefix suffix. l = prefix ++ [d] ++ suffix /\ ~MEM d suffix
Proof
  Induct >> rw[] >-
   (Cases_on `MEM d l` >-
     (res_tac >> qexistsl_tac [`d::prefix`, `suffix`] >> gvs[]) >>
    qexistsl_tac [`[]`, `l`] >> gvs[]) >>
  res_tac >> qexistsl_tac [`h::prefix`, `suffix`] >> gvs[]
QED

(* Suffix of an is_fn_path is still an is_fn_path *)
Theorem is_fn_path_suffix[local]:
  !fn prefix suffix.
    is_fn_path fn (prefix ++ suffix) ==>
    is_fn_path fn suffix
Proof
  gen_tac >> Induct >- simp[] >>
  rpt strip_tac >>
  Cases_on `prefix` >- (
    gvs[] >> Cases_on `suffix` >> gvs[is_fn_path_def]) >>
  gvs[] >>
  Cases_on `t ++ suffix` >- (
    gvs[is_fn_path_def] >> Cases_on `suffix` >> gvs[is_fn_path_def]) >>
  gvs[is_fn_path_def]
QED

(* From dominance + reachability: path from d to n not revisiting d (except at start) *)
Theorem dominates_path_no_revisit:
  !fn d n.
    wf_function fn /\ fn_dominates fn d n ==>
    ?path. is_fn_path fn (d :: path) /\ LAST (d :: path) = n /\ ~MEM d path
Proof
  rpt strip_tac >>
  fs[fn_dominates_def, fn_reachable_def] >>
  drule_then strip_assume_tac rtc_to_fn_path >>
  `MEM d path` by (
    first_x_assum (qspec_then `path` mp_tac) >> simp[]) >>
  drule_then strip_assume_tac last_occurrence_split >>
  `is_fn_path fn ([d] ++ suffix)` by (
    irule is_fn_path_suffix >> qexists_tac `prefix` >> fs[]) >>
  qexists_tac `suffix` >> gvs[] >>
  Cases_on `suffix` >>
  gvs[listTheory.LAST_DEF, listTheory.LAST_APPEND_CONS] >>
  `prefix ++ [d;h] ++ t = prefix ++ d :: h :: t` by simp[] >>
  simp[listTheory.LAST_APPEND_CONS, listTheory.LAST_DEF]
QED



(* Main bridge: NOP'd outputs are never used as operands in reachable blocks.
   Proof outline:
     - nop_output_has_def: v is output of removable inst at (def_bb, def_idx), not live after
     - nop_output_not_live_suc: v ∉ live_vars_at at (def_lbl, SUC def_idx)
     - live_vars_at_uses: v ∈ live_vars_at at (use_lbl, use_idx) from MEM (Var v) inst.inst_operands
     - Contrapositive of liveness_sound_proof: v ∉ live at p → ∀ cfg_exec_path from p: ¬ubd
     - Construct cfg_exec_path from (def_lbl, SUC def_idx) to (use_lbl, use_idx)
     - Show used_before_defined on this path (SSA unique def ≠ PHI excluded by var_defined_at)
     - Contradiction *)

(* ===== Function-level correctness ===== *)

(* ----- CFG reachability helpers ----- *)

Theorem wf_lookup_block:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==>
    lookup_block bb.bb_label fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  irule lookup_block_all_distinct_mem >> simp[] >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[venomWfTheory.wf_function_def] >>
  gvs[venomInstTheory.fn_labels_def]
QED


Triviality eval_phis_no_phi:
  !s l.
    (!i. i < LENGTH l ==> (EL i l).inst_opcode <> PHI) ==>
    eval_phis s l = OK s
Proof
  Induct_on `l` >- simp[eval_phis_def] >>
  rpt strip_tac >>
  `h.inst_opcode <> PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[eval_phis_def]
QED

Triviality eval_phis_filter_no_phi:
  !s P l.
    (!i. i < LENGTH l ==> (EL i l).inst_opcode <> PHI) ==>
    eval_phis s (FILTER P l) = OK s
Proof
  Induct_on `l` >- simp[eval_phis_def] >>
  rpt strip_tac >>
  Cases_on `P h` >> gvs[] >>
  `h.inst_opcode <> PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[eval_phis_def] >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem eval_phis_remove_unused:
  !lr insts V s1 s2 s1'.
    state_equiv V s1 s2 /\
    (!inst v. MEM inst insts /\ MEM (Var v) inst.inst_operands ==> v NOTIN V) /\
    (!idx. idx < LENGTH insts /\
       remove_unused_inst (lr idx) (EL idx insts) =
       mk_nop_inst (EL idx insts) ==>
       set (EL idx insts).inst_outputs SUBSET V) /\
    (!i j. i < j /\ j < LENGTH insts /\
       (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) /\
    eval_phis s1 insts = OK s1' ==>
    ?s2'. eval_phis s2
       (FILTER (\inst. inst.inst_opcode <> NOP)
          (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)) = OK s2' /\
      state_equiv V s1' s2'
Proof
  rpt gen_tac >>
  MAP_EVERY qid_spec_tac [`s1'`, `s2`, `s1`, `V`, `lr`] >>
  Induct_on `insts`
  >- (rpt strip_tac >> qexists_tac `s2` >> gvs[eval_phis_def]) >>
  rpt strip_tac >>
  rename1 `h::t` >>
  simp[MAPi_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    fs[eval_phis_def] >>
    Cases_on `eval_one_phi s1 h` >> gvs[] >>
    PairCases_on `x` >> gvs[] >>
    Cases_on `eval_phis s1 t` >> gvs[] >>
    rename1 `eval_phis s1 t = OK s1_tail` >>
    `eval_one_phi s2 h = SOME (x0,x1)` by (
      irule eval_one_phi_state_equiv >> gvs[] >>
      rpt strip_tac >> metis_tac[]) >>
    qpat_x_assum `!lr0 V0 ss1 ss2 ss1'. _`
      (fn th => ASSUME_TAC th >> ASSUME_TAC th) >>
    Cases_on `remove_unused_inst (lr 0) h = h`
    >- (
      (* kept PHI *)
      `(!inst v. MEM inst t /\ MEM (Var v) inst.inst_operands ==> v NOTIN V)` by
        metis_tac[] >>
      `(!idx. idx < LENGTH t /\
          remove_unused_inst (lr (SUC idx)) (EL idx t) =
          mk_nop_inst (EL idx t) ==>
          set (EL idx t).inst_outputs SUBSET V)` by (
        rpt strip_tac >>
        qpat_x_assum `!idx. _ ==> set _ SUBSET V`
          (qspec_then `SUC idx` mp_tac) >> simp[]) >>
      `(!i j. i < j /\ j < LENGTH t /\ (EL j t).inst_opcode = PHI ==>
          (EL i t).inst_opcode = PHI)` by (
        rpt strip_tac >>
        qpat_x_assum `!i j. _ ==> _`
          (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      qpat_x_assum `!lr0 V0 ss1 ss2 ss1'. _`
        (fn th => mp_tac (Q.SPECL
          [`\idx. lr (SUC idx)`, `V`, `s1`, `s2`, `s1_tail`] th)) >>
      impl_tac >- (
        rpt conj_tac
        >- (qpat_x_assum `state_equiv V s1 s2` ACCEPT_TAC)
        >- (qpat_x_assum `!inst v. MEM inst t /\ _ ==> _` ACCEPT_TAC)
        >- (simp[] >> qpat_x_assum `!idx. idx < LENGTH t /\ _ ==> _` ACCEPT_TAC)
        >- (qpat_x_assum `!i j. i < j /\ j < LENGTH t /\ _ ==> _` ACCEPT_TAC)
        >- (qpat_x_assum `eval_phis s1 t = OK s1_tail` ACCEPT_TAC)) >>
      strip_tac >>
      `MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t =
       MAPi (\idx inst. remove_unused_inst (lr (SUC idx)) inst) t` by
        simp[combinTheory.o_DEF] >>
      gvs[mk_nop_inst_def] >>
      rename1 `eval_phis s2 _ = OK s2_tail` >>
      qexists_tac `update_var x0 x1 s2_tail` >>
      simp[eval_phis_def] >>
      rpt (conj_tac >- gvs[]) >>
      gvs[state_equiv_def, execution_equiv_def, update_var_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[] >> gvs[]) >>
    (* removed PHI: its output is in V, so only original updates it *)
    `remove_unused_inst (lr 0) h = mk_nop_inst h` by
      metis_tac[remove_unused_inst_cases] >>
    `set h.inst_outputs SUBSET V` by (
      qpat_x_assum `!idx. idx < SUC (LENGTH t) /\ _ ==> _`
        (qspec_then `0` mp_tac) >> simp[]) >>
    `(!inst v. MEM inst t /\ MEM (Var v) inst.inst_operands ==> v NOTIN V)` by
      metis_tac[] >>
    `(!idx. idx < LENGTH t /\
        remove_unused_inst (lr (SUC idx)) (EL idx t) =
        mk_nop_inst (EL idx t) ==>
        set (EL idx t).inst_outputs SUBSET V)` by (
      rpt strip_tac >>
      qpat_x_assum `!idx. _ ==> set _ SUBSET V`
        (qspec_then `SUC idx` mp_tac) >> simp[]) >>
    `(!i j. i < j /\ j < LENGTH t /\ (EL j t).inst_opcode = PHI ==>
        (EL i t).inst_opcode = PHI)` by (
      rpt strip_tac >>
      qpat_x_assum `!i j. _ ==> _`
        (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
    qpat_x_assum `!lr0 V0 ss1 ss2 ss1'. _`
      (fn th => mp_tac (Q.SPECL
        [`\idx. lr (SUC idx)`, `V`, `s1`, `s2`, `s1_tail`] th)) >>
    impl_tac >- (BETA_TAC >> gvs[] >> metis_tac[]) >>
    strip_tac >>
    `MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t =
     MAPi (\idx inst. remove_unused_inst (lr (SUC idx)) inst) t` by
      simp[combinTheory.o_DEF] >>
    gvs[mk_nop_inst_def] >>
    rename1 `eval_phis s2 _ = OK s2_tail` >>
    fs[eval_one_phi_def, AllCaseEqs(), state_equiv_def,
       execution_equiv_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, pred_setTheory.SUBSET_DEF] >>
    rw[] >> gvs[] >> metis_tac[]) >>
  (* h is not PHI: eval_phis stops on both sides; if h is removed, the tail
     has no PHIs by the prefix invariant, so transformed-tail eval_phis is OK. *)
  fs[eval_phis_def] >>
  qspecl_then [`lr 0`, `h`] strip_assume_tac
    remove_unused_inst_cases >> gvs[mk_nop_inst_def]
  >- (
    qexists_tac `s2` >>
    Cases_on `h.inst_opcode = NOP` >> gvs[eval_phis_def] >>
    irule eval_phis_filter_no_phi >> rpt strip_tac >>
    gvs[LENGTH_MAPi, EL_MAPi, combinTheory.o_DEF] >>
    qspecl_then [`lr (SUC i)`, `EL i t`]
      strip_assume_tac remove_unused_inst_cases >> gvs[mk_nop_inst_def] >>
    qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH t) /\ _ ==> _`
      (qspecl_then [`0`, `SUC i`] mp_tac) >> simp[]) >>
  last_x_assum (qspecl_then
    [`\idx. lr (SUC idx)`, `V`, `s1`, `s2`, `s1`] mp_tac) >>
  impl_tac >- (
    BETA_TAC >>
    rpt conj_tac
    >- (qpat_x_assum `state_equiv V s1 s2` ACCEPT_TAC)
    >- (rpt strip_tac >> metis_tac[])
    >- (rpt strip_tac >>
        qpat_x_assum `!idx. idx < SUC (LENGTH t) /\ _ ==> _`
          (qspec_then `SUC idx` mp_tac) >> simp[])
    >- (rpt strip_tac >>
        qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH t) /\ _ ==> _`
          (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
    >- (
      irule eval_phis_no_phi >> rpt strip_tac >>
      CCONTR_TAC >>
      qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH t) /\ _ ==> _`
        (qspecl_then [`0`, `SUC i`] mp_tac) >> simp[])) >>
  strip_tac >>
  qexists_tac `s2'` >> BETA_TAC >>
  `MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t =
   MAPi (\idx inst. remove_unused_inst (lr (SUC idx)) inst) t` by
    simp[combinTheory.o_DEF] >>
  gvs[]
QED

Triviality phi_prefix_length_no_phi:
  !l. (!i. i < LENGTH l ==> (EL i l).inst_opcode <> PHI) ==>
      phi_prefix_length l = 0
Proof
  Induct_on `l` >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  `h.inst_opcode <> PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[phi_prefix_length_def]
QED

Theorem phi_prefix_length_remove_unused_clear:
  !lr insts.
    (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) ==>
    phi_prefix_length (FILTER (\inst. inst.inst_opcode <> NOP)
      (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)) =
    LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
      (TAKE (phi_prefix_length insts)
        (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)))
Proof
  rpt gen_tac >> qid_spec_tac `lr` >>
  Induct_on `insts` >- simp[phi_prefix_length_def] >>
  rpt strip_tac >> rename1 `h::t` >> simp[MAPi_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    simp[phi_prefix_length_def] >>
    `(!i j. i < j /\ j < LENGTH t /\ (EL j t).inst_opcode = PHI ==>
        (EL i t).inst_opcode = PHI)` by (
      rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
    first_x_assum (qspecl_then [`\idx. lr (SUC idx)`] mp_tac) >>
    impl_tac >- (qpat_x_assum `!i j. i < j /\ j < LENGTH t /\ _ ==> _` ACCEPT_TAC) >>
    strip_tac >>
    `MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t =
     MAPi (\idx inst. remove_unused_inst (lr (SUC idx)) inst) t` by
      simp[combinTheory.o_DEF] >>
    qspecl_then [`lr 0`, `h`] strip_assume_tac remove_unused_inst_cases >>
    gvs[mk_nop_inst_def, phi_prefix_length_def]) >>
  simp[phi_prefix_length_def] >>
  `(!i. i < LENGTH t ==> (EL i t).inst_opcode <> PHI)` by (
    rpt strip_tac >> CCONTR_TAC >>
    first_x_assum (qspecl_then [`0`, `SUC i`] mp_tac) >> simp[]) >>
  `(!i. i < LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
           (MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t)) ==>
        (EL i (FILTER (\inst. inst.inst_opcode <> NOP)
           (MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t))).inst_opcode <> PHI)` by (
    rpt strip_tac >>
    `MEM (EL i (FILTER (\inst. inst.inst_opcode <> NOP)
           (MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t)))
       (FILTER (\inst. inst.inst_opcode <> NOP)
           (MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t))` by
      metis_tac[listTheory.MEM_EL] >>
    gvs[listTheory.MEM_FILTER, MEM_MAPi] >>
    qspecl_then [`lr (SUC n)`, `EL n t`]
      strip_assume_tac remove_unused_inst_cases >> gvs[mk_nop_inst_def] >>
    first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  qspecl_then [`lr 0`, `h`] strip_assume_tac remove_unused_inst_cases >>
  gvs[mk_nop_inst_def, phi_prefix_length_def] >>
  irule phi_prefix_length_no_phi >> rpt strip_tac >>
  Cases_on `h.inst_opcode = NOP` >> gvs[] >>
  Cases_on `i` >> gvs[] >> metis_tac[]
QED

(* Same-state block/phase/single-pass simulations removed for consuming GAS. *)

(* lift_result reflexivity *)
Theorem lift_result_refl_state_equiv:
  !vars r.
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars) r r
Proof
  gen_tac >> Cases >> simp[lift_result_def] >>
  metis_tac[stateEquivPropsTheory.state_equiv_refl,
            stateEquivPropsTheory.execution_equiv_refl]
QED

(* lift_result weakening for state_equiv/execution_equiv *)
Theorem lift_result_weaken_vars:
  !V1 V2 r1 r2.
    V1 SUBSET V2 /\
    lift_result (state_equiv V1) (execution_equiv V1) (execution_equiv V1) r1 r2 ==>
    lift_result (state_equiv V2) (execution_equiv V2) (execution_equiv V2) r1 r2
Proof
  rpt strip_tac >> irule lift_result_weaken >>
  qexistsl_tac [`state_equiv V1`, `execution_equiv V1`] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule stateEquivPropsTheory.state_equiv_subset >>
      qexists_tac `V1` >> simp[])
  >- (rpt strip_tac >> irule stateEquivPropsTheory.execution_equiv_subset >>
      qexists_tac `V1` >> simp[])
  >- first_assum ACCEPT_TAC
QED

(* Helper: lift_result with Error on right forces Error on left *)
Theorem lift_result_error_right[local]:
  !R_ok R_term r e.
    lift_result R_ok R_term R_term r (Error e) ==> ?e'. r = Error e'
Proof
  Cases_on `r` >> simp[lift_result_def]
QED

(* General OWHILE + lift_result composition.
   Proves that if each step of an OWHILE loop either produces an error
   or refines the result via lift_result, then the full iteration does too.
   Isolates the OWHILE_IND induction to avoid variable shadowing issues.
   The caller should bake any OWHILE-reachability conditions into P. *)
Theorem owhile_lift_result_compose:
  !G f R_ok R_term Q P.
    (!x. R_ok x x) /\
    (!x. R_term x x) /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!x. G x /\ P x ==>
      (?e. Q x = Error e) \/
      lift_result R_ok R_term R_term (Q x) (Q (f x))) /\
    (!x. G x /\ P x ==> P (f x)) ==>
    !x y. OWHILE G f x = SOME y ==> P x ==>
      (?e. Q x = Error e) \/
      lift_result R_ok R_term R_term (Q x) (Q y)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac WhileTheory.OWHILE_IND >> rpt conj_tac
  >- ((* Base case: ~G x, so y = x *)
    rpt gen_tac >> ntac 2 strip_tac >> DISJ2_TAC >>
    Cases_on `Q x` >> simp[lift_result_def])
  >> (* Step case: G x, IH for f x, need to compose *)
    rpt gen_tac >>
    disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
    strip_tac >>
    `(∃e. Q x = Error e) ∨ lift_result R_ok R_term R_term (Q x) (Q (f x))` by metis_tac[] >>
    `P (f x)` by metis_tac[] >>
    fs[]
    >- metis_tac[lift_result_error_right]
    >- (DISJ2_TAC >>
        Cases_on `Q (x:'a)` >> Cases_on `Q (f x)` >> Cases_on `Q (y:'a)` >>
        fs[lift_result_def] >> metis_tac[])
QED

(* Same-state iteration correctness removed: consuming GAS needs oracle reconstruction. *)

(* block_nop_outputs are a subset of the block's instruction outputs *)
Theorem block_nop_outputs_subset_block_outputs[local]:
  !lr bb.
    block_nop_outputs lr bb SUBSET
    set (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
  gvs[block_nop_outputs_def, LET_THM,
      listTheory.MEM_FLAT, indexedListsTheory.MEM_MAPi] >>
  pop_assum mp_tac >> IF_CASES_TAC >> gvs[] >>
  strip_tac >>
  simp[listTheory.MEM_MAP] >>
  metis_tac[listTheory.EL_MEM]
QED

(* single_pass_nop_outputs are a subset of fn_all_outputs *)
Theorem nop_outputs_subset_all_outputs:
  !fn. single_pass_nop_outputs fn SUBSET fn_all_outputs fn
Proof
  rw[single_pass_nop_outputs_def, fn_all_outputs_def, LET_THM,
     pred_setTheory.SUBSET_DEF] >>
  gvs[pred_setTheory.IN_BIGUNION, listTheory.MEM_MAP] >>
  rename1 `MEM bb fn.fn_blocks` >>
  mp_tac (Q.SPECL
    [`protect_liveness fn (remove_unused_phi_vars fn) (liveness_analyze fn)`,
     `bb`] block_nop_outputs_subset_block_outputs) >>
  rw[pred_setTheory.SUBSET_DEF] >>
  first_x_assum drule >> strip_tac >>
  gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM_FLAT, listTheory.MEM_MAP]
QED

(* remove_unused_inst outputs: either same or empty *)
Theorem remove_unused_inst_outputs[local]:
  !live inst.
    (remove_unused_inst live inst).inst_outputs = inst.inst_outputs \/
    (remove_unused_inst live inst).inst_outputs = []
Proof
  rw[remove_unused_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[mk_nop_inst_def]
QED

(* remove_unused_block outputs are subset of original block outputs *)
Theorem remove_unused_block_outputs_subset[local]:
  !lr bb.
    set (FLAT (MAP (\inst. inst.inst_outputs)
      (remove_unused_block lr bb).bb_instructions)) SUBSET
    set (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
  gvs[remove_unused_block_def, LET_THM,
      listTheory.MEM_FLAT, listTheory.MEM_MAP,
      indexedListsTheory.MEM_MAPi] >>
  rename1 `n < LENGTH bb.bb_instructions` >>
  qpat_x_assum `MEM x _` mp_tac >>
  simp[remove_unused_inst_def] >>
  rpt (IF_CASES_TAC >> simp[mk_nop_inst_def]) >>
  metis_tac[listTheory.EL_MEM]
QED

(* clear_nops_block outputs are subset of original block outputs *)
Theorem clear_nops_block_outputs_subset[local]:
  !bb.
    set (FLAT (MAP (\inst. inst.inst_outputs)
      (clear_nops_block bb).bb_instructions)) SUBSET
    set (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  rw[clear_nops_block_def, pred_setTheory.SUBSET_DEF,
     listTheory.MEM_FLAT, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

(* rusp outputs are subset of original outputs *)
Theorem rusp_all_outputs_subset:
  !fn. fn_all_outputs (remove_unused_single_pass fn) SUBSET fn_all_outputs fn
Proof
  gen_tac >>
  simp[fn_all_outputs_def, pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >>
  fs[remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def,
     passTransformTheory.function_map_transform_def,
     listTheory.MEM_FLAT, listTheory.MEM_MAP, listTheory.MAP_MAP_o,
     combinTheory.o_DEF] >>
  rename1 `MEM bbo _.fn_blocks` >>
  `MEM x (FLAT (MAP (\inst. inst.inst_outputs) bbo.bb_instructions))` by (
    gvs[] >>
    imp_res_tac (SRULE [pred_setTheory.SUBSET_DEF] clear_nops_block_outputs_subset) >>
    imp_res_tac (SRULE [pred_setTheory.SUBSET_DEF] remove_unused_block_outputs_subset)) >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* SSA outputs uniqueness: same output variable → same (block, position).
   Combines all_distinct_flat_map_inj (cross-block) with
   all_distinct_outputs_unique_pos (within-block). *)
Theorem ssa_form_position:
  !fn bb1 n bb2 m v.
    ssa_form fn /\
    MEM bb1 fn.fn_blocks /\ n < LENGTH bb1.bb_instructions /\
    MEM v (EL n bb1.bb_instructions).inst_outputs /\
    MEM bb2 fn.fn_blocks /\ m < LENGTH bb2.bb_instructions /\
    MEM v (EL m bb2.bb_instructions).inst_outputs ==>
    bb1 = bb2 /\ n = m
Proof
  rpt gen_tac >> strip_tac >>
  (* Cross-block: bb1 = bb2 *)
  `bb1 = bb2` by (
    mp_tac (Q.ISPECL [
      `\(bb:basic_block). FLAT (MAP (\(i:instruction). i.inst_outputs) bb.bb_instructions)`,
      `fn.fn_blocks`, `bb1:basic_block`, `bb2:basic_block`, `v:string`
    ] all_distinct_flat_map_inj) >>
    (impl_tac >- (
      drule ssa_form_per_block >> simp[] >> strip_tac >>
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      metis_tac[listTheory.EL_MEM])) >>
    simp[]) >>
  fs[] >>
  (* Within-block: n = m *)
  irule all_distinct_outputs_unique_pos >>
  qexistsl_tac [`bb1.bb_instructions`, `v`] >> simp[] >>
  irule all_distinct_outputs_block >>
  qexists_tac `fn.fn_blocks` >> simp[] >>
  fs[ssa_form_def, fn_insts_def]
QED

(* NOP'd instruction outputs are removed by rusp.
   Key insight: SSA uniqueness means each variable is defined at exactly one
   (block, position). If that position is NOP'd, no other instruction defines
   the variable, so it disappears from all outputs. *)
Theorem nop_outputs_not_in_rusp:
  !fn v. wf_function fn /\ ssa_form fn /\
         v IN single_pass_nop_outputs fn ==>
         v NOTIN fn_all_outputs (remove_unused_single_pass fn)
Proof
  rpt gen_tac >> strip_tac >>
  (* Step 1: Extract NOP'd position (bb, n) from single_pass_nop_outputs *)
  fs[single_pass_nop_outputs_def, LET_THM] >>
  gvs[pred_setTheory.IN_BIGUNION, listTheory.MEM_MAP] >>
  rename1 `MEM bb _.fn_blocks` >>
  fs[block_nop_outputs_def, LET_THM] >>
  gvs[listTheory.MEM_FLAT, indexedListsTheory.MEM_MAPi] >>
  qpat_x_assum `MEM v _` mp_tac >> IF_CASES_TAC >> gvs[] >> strip_tac >>
  rename1 `n < LENGTH bb.bb_instructions` >>
  (* Step 2: Proof by contradiction — assume v ∈ fn_all_outputs(rusp fn) *)
  SPOSE_NOT_THEN ASSUME_TAC >>
  fs[fn_all_outputs_def, remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def,
     passTransformTheory.function_map_transform_def,
     listTheory.MAP_MAP_o, combinTheory.o_DEF,
     listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rename1 `MEM bb' _.fn_blocks` >>
  (* Step 3: v appears in some transformed block outputs — extract position m *)
  gvs[clear_nops_block_def, listTheory.MEM_FILTER,
      remove_unused_block_def, LET_THM,
      indexedListsTheory.MEM_MAPi, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rename1 `m < LENGTH bb'.bb_instructions` >>
  (* Step 4: Outputs of transformed inst are either original or [].
     Since v ∈ outputs, must be original. *)
  `(remove_unused_inst
      (live_after_at
         (protect_liveness fn (remove_unused_phi_vars fn) (liveness_analyze fn))
         bb'.bb_label m (LENGTH bb'.bb_instructions))
      (EL m bb'.bb_instructions)).inst_outputs =
    (EL m bb'.bb_instructions).inst_outputs` by (
    mp_tac (Q.SPECL [
      `live_after_at
         (protect_liveness fn (remove_unused_phi_vars fn) (liveness_analyze fn))
         bb'.bb_label m (LENGTH bb'.bb_instructions)`,
      `EL m bb'.bb_instructions`] remove_unused_inst_outputs) >>
    strip_tac >> gvs[]) >>
  (* So v ∈ (EL m bb'.bb_instructions).inst_outputs *)
  fs[] >>
  (* Step 5: Position uniqueness — bb = bb' ∧ n = m *)
  (`bb = bb' /\ n = m` by
    metis_tac[ssa_form_position]) >>
  gvs[] >>
  (* Step 6: Contradiction — same remove_unused_inst call, but NOP'd (step 1)
     says is_removable ∧ dead, while kept (step 4) says it returns original. *)
  qpat_x_assum `_ = (EL n bb.bb_instructions).inst_outputs` mp_tac >>
  simp[remove_unused_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[mk_nop_inst_def]) >>
  simp[mk_nop_inst_def] >>
  metis_tac[listTheory.MEM]
QED


(* Two functions that differ only by NOP replacement of a dead ASSIGN.
   This demonstrates that pass_correct {} (which requires ALL variables
   to agree at termination) is too strong for remove_unused, because
   NOP'd variables retain their old values in the transformed program. *)

(* Original: ASSIGN v1 := 42, then STOP *)
Definition cx_ru_fn1_def:
  cx_ru_fn1 = mk_raw_function "test_fn"
    [basic_block "entry"
      [instruction 0 ASSIGN [Lit 42w] ["v1"];
       instruction 1 STOP [] []]]
End

(* Transformed: NOP (v1 assignment removed), then STOP *)
Definition cx_ru_fn2_def:
  cx_ru_fn2 = mk_raw_function "test_fn"
    [basic_block "entry"
      [instruction 0 NOP [] [];
       instruction 1 STOP [] []]]
End

(* Both functions satisfy wf_ssa (vacuously: no variable uses) *)
Theorem cx_ru_fn1_wf_ssa[local]:
  wf_ssa cx_ru_fn1
Proof
  simp[venomWfTheory.wf_ssa_def, cx_ru_fn1_def,
       venomWfTheory.ssa_form_def,
       venomWfTheory.def_dominates_uses_def] >>
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[]
QED

(* pass_correct {} is FALSE between fn1 and fn2.
   Original halts with vs_vars("v1") = 42w.
   Transformed halts with vs_vars("v1") unchanged.
   execution_equiv {} requires all vars equal => fails on "v1". *)
(* pass_correct {} is FALSE: original halts with v1=42w,
   transformed halts with v1 unchanged => execution_equiv {} fails on "v1" *)
Theorem pass_correct_empty_false_for_nop[local]:
  ~pass_correct (state_equiv {}) (execution_equiv {}) (execution_equiv {})
    (\fuel. run_blocks fuel ARB cx_ru_fn1
       ((init_venom_state "entry") with <|vs_vars := FEMPTY;
                   vs_current_bb := "entry"; vs_inst_idx := 0; vs_halted := F|>))
    (\fuel. run_blocks fuel ARB cx_ru_fn2
       ((init_venom_state "entry") with <|vs_vars := FEMPTY;
                   vs_current_bb := "entry"; vs_inst_idx := 0; vs_halted := F|>))
Proof
  simp[passSimulationDefsTheory.pass_correct_def,
       cx_ru_fn1_def, cx_ru_fn2_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  simp[passSimulationDefsTheory.terminates_def] >>
  strip_tac >>
  qexistsl_tac [`SUC 0`, `SUC 0`] >>
  EVAL_TAC >>
  simp[stateEquivTheory.lift_result_def,
       stateEquivTheory.execution_equiv_def]
QED

