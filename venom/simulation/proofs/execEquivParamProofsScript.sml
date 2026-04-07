(*
 * Parameterized Execution Equivalence — Proofs
 *
 * TOP-LEVEL:
 *   step_inst_preserves_R_proof                          — master theorem
 *   run_block_preserves_R_proof                          — mutual: run_block + run_function
 *   state_equiv_execution_equiv_valid_state_rel_proof    — instantiation
 *)

Theory execEquivParamProofs
Ancestors
  execEquivParamHelpers execEquivParamHelpers2 execEquivParamBase
  execEquivParamDefs passSimulationDefs stateEquivProps execEquivProps
  stateEquiv venomInst venomExecSemantics venomState
Libs
  finite_mapTheory listTheory rich_listTheory optionTheory pred_setTheory

open execEquivParamLib

(* Master theorem: step_inst preserves any valid (R_ok, R_term) pair.
   Non-INVOKE: step_inst_non_invoke reduces to step_inst_base, dispatch to helpers.
   INVOKE: identical callee state (setup_callee from R_ok + same args) →
   same run_function result → merge_callee_state + bind_outputs preserve R_ok. *)
Theorem step_inst_preserves_R_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fuel ctx inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE: both sides unfold to identical callee call *)
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
    simp[Once step_inst_def] >>
    Cases_on `decode_invoke inst` >> gvs[lift_result_def] >>
    Cases_on `x` >> gvs[] >>
    rename1 `decode_invoke inst = SOME (callee_name, arg_ops)` >>
    `!x. MEM (Var x) arg_ops ==> MEM (Var x) inst.inst_operands` by
      (gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
    Cases_on `lookup_function callee_name ctx.ctx_functions` >>
    gvs[lift_result_def] >>
    rename1 `lookup_function _ _ = SOME callee_fn` >>
    `eval_operands arg_ops s1 = eval_operands arg_ops s2` by
      (irule vsr_eval_operands >> simp[] >> metis_tac[]) >>
    gvs[] >>
    Cases_on `eval_operands arg_ops s2` >> gvs[lift_result_def] >>
    rename1 `eval_operands _ _ = SOME args` >>
    `setup_callee callee_fn args s1 = setup_callee callee_fn args s2` by
      (irule vsr_setup_callee_eq >> metis_tac[]) >>
    gvs[] >>
    Cases_on `setup_callee callee_fn args s2` >> gvs[lift_result_def] >>
    rename1 `setup_callee _ _ _ = SOME callee_s` >>
    (* Same callee state → same run_function result *)
    Cases_on `run_function fuel ctx callee_fn callee_s` >> gvs[lift_result_def]
    >- metis_tac[vsr_R_term_refl]
    >- metis_tac[vsr_R_term_refl]
    >- (
      (* IntRet: merge_callee + bind_outputs preserve R_ok *)
      rename1 `run_function _ _ _ _ = IntRet vals callee_s'` >>
      sg `OPTREL R_ok
            (bind_outputs inst.inst_outputs vals (merge_callee_state s1 callee_s'))
            (bind_outputs inst.inst_outputs vals (merge_callee_state s2 callee_s'))`
      >- (`R_ok (merge_callee_state s1 callee_s') (merge_callee_state s2 callee_s')` by
            (irule vsr_merge_callee_R_ok >> metis_tac[]) >>
          drule_all vsr_bind_outputs_R_ok >>
          disch_then (qspecl_then [`inst.inst_outputs`, `vals`] mp_tac) >> simp[])
      >>
      gvs[optionTheory.OPTREL_def, lift_result_def])
  )
  >>
  (* Non-INVOKE: reduce to step_inst_base, dispatch to opcode helpers *)
  `step_inst fuel ctx inst s1 = step_inst_base inst s1 /\
   step_inst fuel ctx inst s2 = step_inst_base inst s2` by
    (conj_tac >> irule step_inst_non_invoke >> simp[]) >>
  gvs[] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  FIRST [
    irule vsr_step_inst_pure2 >> simp[] >> metis_tac[],
    irule vsr_step_inst_pure1 >> simp[] >> metis_tac[],
    irule vsr_step_inst_pure3 >> simp[] >> metis_tac[],
    irule vsr_step_inst_read0 >> simp[] >> metis_tac[],
    irule vsr_step_inst_read1 >> simp[] >> metis_tac[],
    irule vsr_step_inst_extcodehash >> simp[] >> metis_tac[],
    irule vsr_step_inst_write2 >> simp[] >> metis_tac[],
    irule vsr_step_inst_terminator >> simp[] >> metis_tac[],
    irule vsr_step_inst_return >> simp[] >> metis_tac[],
    irule vsr_step_inst_revert >> simp[] >> metis_tac[],
    irule vsr_step_inst_control >> simp[] >> metis_tac[],
    irule vsr_step_inst_djmp >> simp[] >> metis_tac[],
    irule vsr_step_inst_ssa >> simp[] >> metis_tac[],
    irule vsr_step_inst_assert >> simp[] >> metis_tac[],
    irule vsr_step_inst_sha3 >> simp[] >> metis_tac[],
    irule vsr_step_inst_mcopy >> simp[] >> metis_tac[],
    irule vsr_step_inst_istore >> simp[] >> metis_tac[],
    irule vsr_step_inst_data_copy >> simp[] >> metis_tac[],
    irule vsr_step_inst_extcodecopy >> simp[] >> metis_tac[],
    irule vsr_step_inst_copy >> simp[] >> metis_tac[],
    irule vsr_step_inst_param >> simp[] >> metis_tac[],
    irule vsr_step_inst_ret >> simp[] >> metis_tac[],
    irule vsr_step_inst_log >> simp[] >> metis_tac[],
    irule vsr_step_inst_selfdestruct >> simp[] >> metis_tac[],
    irule vsr_step_inst_invalid >> simp[] >> metis_tac[],
    irule vsr_step_inst_ext_call >> simp[] >> metis_tac[],
    irule vsr_step_inst_delegatecall >> simp[] >> metis_tac[],
    irule vsr_step_inst_create >> simp[] >> metis_tac[],
    irule vsr_step_inst_alloca >> simp[] >> metis_tac[]
  ]
QED

(* run_block/run_function preserve R. Mutual induction via run_block_ind.
   New run_block is simpler (no INVOKE special case - step_inst handles it).
   Uses vs_inst_idx := SUC s.vs_inst_idx (not next_inst). *)

(* Generalized: run_block preserves R with auxiliary invariant Q.
   Q tracks additional agreement (e.g., fresh variable agreement) that R_ok
   alone doesn't capture. Operand agreement uses R_ok AND Q; Q is preserved
   by non-terminator steps. *)
Theorem run_block_same_preserves_RQ_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (Q : venom_state -> venom_state -> bool)
   bb fuel ctx s1 s2.
    valid_state_rel R_ok R_term /\
    R_ok s1 s2 /\ Q s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!inst. MEM inst bb.bb_instructions ==>
            inst.inst_opcode <> INVOKE) /\
    (* Operand agreement using R_ok AND Q *)
    (!i s1' s2'. i < LENGTH bb.bb_instructions /\
       R_ok s1' s2' /\ Q s1' s2' /\
       s1'.vs_inst_idx = i /\ s2'.vs_inst_idx = i ==>
       !x. MEM (Var x) (EL i bb.bb_instructions).inst_operands ==>
           lookup_var x s1' = lookup_var x s2') /\
    (* Q preserved by non-terminator steps *)
    (!i s1' s2' v1 v2.
       i < LENGTH bb.bb_instructions /\
       ~is_terminator (EL i bb.bb_instructions).inst_opcode /\
       R_ok s1' s2' /\ Q s1' s2' /\
       s1'.vs_inst_idx = i /\ s2'.vs_inst_idx = i /\
       step_inst fuel ctx (EL i bb.bb_instructions) s1' = OK v1 /\
       step_inst fuel ctx (EL i bb.bb_instructions) s2' = OK v2 /\
       R_ok v1 v2 ==>
       Q (v1 with vs_inst_idx := SUC i)
         (v2 with vs_inst_idx := SUC i)) ==>
    lift_result R_ok R_term R_term
      (run_block fuel ctx bb s1)
      (run_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  ntac 6 (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
  gvs[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx`
  >- simp[lift_result_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `s2.vs_inst_idx < LENGTH bb.bb_instructions /\
   inst = EL s2.vs_inst_idx bb.bb_instructions` by
    fs[get_instruction_def] >>
  `!x. MEM (Var x) inst.inst_operands ==>
       lookup_var x s1 = lookup_var x s2` by
    (rpt strip_tac >> first_x_assum irule >> gvs[]) >>
  `lift_result R_ok R_term R_term (step_inst fuel ctx inst s1)
     (step_inst fuel ctx inst s2)` by
    (match_mp_tac step_inst_preserves_R_proof >> fs[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  fs[lift_result_def] >>
  IF_CASES_TAC >> fs[]
  >- (imp_res_tac vsr_R_ok_R_term >>
      imp_res_tac vsr_R_ok_fields >> fs[] >>
      Cases_on `v.vs_halted` >> fs[lift_result_def])
  >>
  (* Substitute inst = EL ... so IH guard matches *)
  qpat_x_assum `inst = _` SUBST_ALL_TAC >>
  (* Apply IH: spec s'' := v, discharge step_inst guard *)
  qpat_x_assum `!s''. _ ==> !s2'. _ ==> _ ==> _ ==> _ ==>
    lift_result _ _ (run_block _ _ _ _) (run_block _ _ _ _)`
    (qspec_then `v` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `v' with vs_inst_idx := SUC s2.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- metis_tac[]
  >- (irule vsr_inst_idx_R_ok >> metis_tac[])
QED

(* Helper: run_block preserves R. By induction on the instruction list via
   run_defs_ind, using step_inst_preserves_R at each step. *)
Triviality run_block_preserves_R_helper:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx bb s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
  gvs[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[lift_result_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def] >> irule listTheory.EL_MEM >> simp[]) >>
  `lift_result R_ok R_term R_term (step_inst fuel ctx inst s1)
     (step_inst fuel ctx inst s2)` by
    (irule step_inst_preserves_R_proof >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[lift_result_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[lift_result_def]
  >- (`v.vs_halted <=> v'.vs_halted` by
        (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
      Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
      metis_tac[vsr_R_ok_R_term])
  >>
  first_x_assum irule >> irule vsr_inst_idx_R_ok >> simp[] >> metis_tac[]
QED

Theorem run_block_preserves_R_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    (!fuel ctx bb s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx bb s2)) /\
    (!fuel ctx s1 s2.
       R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_function fuel ctx fn s1)
                                (run_function fuel ctx fn s2))
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      drule_all run_block_preserves_R_helper >> simp[])
  >>
  Induct_on `fuel` >> rw[]
  >- simp[run_function_def, lift_result_def]
  >>
  simp[Once run_function_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  `s1.vs_current_bb = s2.vs_current_bb` by
    (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
  gvs[] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks` >>
  gvs[lift_result_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by
    (fs[lookup_block_def] >> metis_tac[FIND_MEM]) >>
  `lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
     (run_block fuel ctx bb s2)` by
    (drule_all run_block_preserves_R_helper >> simp[]) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx bb s2` >>
  gvs[lift_result_def] >>
  `v.vs_halted <=> v'.vs_halted` by
    (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
  Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
  metis_tac[vsr_R_ok_R_term]
QED

Theorem state_equiv_execution_equiv_valid_state_rel_proof:
  !vars. valid_state_rel (state_equiv vars) (execution_equiv vars)
Proof
  rw[valid_state_rel_def] >>
  fs[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def] >>
  rpt strip_tac >>
  simp[FLOOKUP_UPDATE, eval_operand_def, lookup_var_def] >>
  TRY (Cases_on `op` >> fs[eval_operand_def, lookup_var_def] >> NO_TAC) >>
  TRY (rw[] >> first_x_assum irule >> simp[] >> NO_TAC) >>
  metis_tac[]
QED

(* Generalized: R_ok vars can differ from R_term vars' when vars SUBSET vars' *)
Theorem valid_state_rel_mixed_proof:
  !vars vars'. vars SUBSET vars' ==>
    valid_state_rel (state_equiv vars) (execution_equiv vars')
Proof
  rw[valid_state_rel_def] >>
  fs[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def, SUBSET_DEF] >>
  rpt strip_tac >>
  simp[FLOOKUP_UPDATE, eval_operand_def, lookup_var_def] >>
  TRY (Cases_on `op` >> fs[eval_operand_def, lookup_var_def] >> NO_TAC) >>
  TRY (rw[] >> first_x_assum irule >> simp[] >> NO_TAC) >>
  metis_tac[]
QED
