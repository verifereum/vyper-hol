(*
 * DFG soundness through execution
 *
 * The DFG-based passes (assert_elim, overflow_elim) need to know that what
 * the DFG says about variable values (dfgSoundDefs) still holds after
 * running a block. Within a block only the prefix form is preserved step
 * by step (dfg_prefix_sound_step): mid-block, an entry defined later in a
 * loop body can be stale. At the block's end the prefix covers the whole
 * block, and entries defined in other blocks are untouched because their
 * variables and operands are not written here (SSA + dfg_block_local).
 *
 * TOP-LEVEL:
 *   dfg_prefix_sound_step    — one non-terminator step extends the prefix
 *   dfg_prefix_sound_phi_prefix — the prefix holds over the PHIs
 *   dfg_sound_run_block      — dfg_sound + operand closure survive run_block
 *   dfg_ext_sound_run_block  — dfg_ext_sound survives run_block
 *)

Theory dfgSoundProofs
Ancestors
  dfgSoundDefs dfgDefs dfgAnalysisProps
  venomExecSemantics venomExecProps venomExecProofs venomInst venomInstProps
  venomState venomWf
  finite_map list integer_word
Libs
  BasicProvers stepInstBaseLib

(* ===== Function structure ===== *)

(* Convenience: extract dfg_block_local consequence for a specific (v, inst, u, inst_u).
   Avoids expanding dfg_block_local_def in contexts with 7-way opcode disjunction. *)
Theorem dfg_block_local_elim:
  !fn v inst u inst_u bb.
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    MEM (Var u) inst.inst_operands /\
    dfg_tracked_opcode inst.inst_opcode /\
    dfg_get_def (dfg_build_function fn) u = SOME inst_u /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst_u bb.bb_instructions /\
    !i j. i < LENGTH bb.bb_instructions /\
          j < LENGTH bb.bb_instructions /\
          EL i bb.bb_instructions = inst_u /\
          EL j bb.bb_instructions = inst ==>
          i < j
Proof
  REWRITE_TAC[dfg_block_local_def] >> metis_tac[]
QED

(* Operand's defining instruction is in the same block as the tracked inst.
   Contrapositive: if dinst not in bb, then inst_u not in bb. *)
Theorem operand_inst_same_block[local]:
  !fn bb v dinst u inst_u.
    dfg_block_local fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    MEM (Var u) dinst.inst_operands /\
    dfg_tracked_opcode dinst.inst_opcode /\
    dfg_get_def (dfg_build_function fn) u = SOME inst_u /\
    MEM dinst bb.bb_instructions ==>
    MEM inst_u bb.bb_instructions
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`,`v`,`dinst`,`u`,`inst_u`,`bb`] dfg_block_local_elim) >>
  simp[]
QED

(* Tracked DFG instruction always has singleton output list.
   Combines dfg_build_function_correct + fn_inst_wf + inst_wf. *)
Theorem dfg_tracked_inst_outputs:
  !fn v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    dfg_tracked_opcode inst.inst_opcode /\
    fn_inst_wf fn ==>
    inst.inst_outputs = [v]
Proof
  rpt strip_tac >>
  `MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    metis_tac[fn_insts_mem_block] >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  gvs[dfg_tracked_opcode_def, inst_wf_def] >>
  Cases_on `inst.inst_outputs` >> gvs[LENGTH_NIL]
QED

(* If dinst not in bb, then inst_u (operand's defining inst) not in bb either.
   Uses dfg_block_local (same block) + fn_inst_ids_distinct (unique IDs). *)
Theorem operand_not_in_block[local]:
  !fn bb v dinst u inst_u.
    dfg_block_local fn /\ wf_function fn /\
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    ~MEM dinst bb.bb_instructions /\
    MEM (Var u) dinst.inst_operands /\
    dfg_tracked_opcode dinst.inst_opcode /\
    dfg_get_def (dfg_build_function fn) u = SOME inst_u ==>
    ~MEM inst_u bb.bb_instructions
Proof
  rpt strip_tac >>
  `MEM dinst (fn_insts fn)` by metis_tac[dfg_build_function_correct] >>
  `?bb_d. MEM bb_d fn.fn_blocks /\ MEM dinst bb_d.bb_instructions` by
    metis_tac[fn_insts_mem_block] >>
  `MEM inst_u bb_d.bb_instructions` by
    metis_tac[operand_inst_same_block] >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  `bb = bb_d` by metis_tac[inst_in_unique_block] >>
  gvs[]
QED

(* SSA: two different instructions in the same block have disjoint outputs *)
Theorem block_ssa_disjoint_outputs:
  !bb fn k1 k2 v.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    k1 < LENGTH bb.bb_instructions /\ k2 < LENGTH bb.bb_instructions /\
    k1 <> k2 /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    MEM v (EL k1 bb.bb_instructions).inst_outputs ==>
    ~MEM v (EL k2 bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `EL k1 bb.bb_instructions <> EL k2 bb.bb_instructions` by
    (fs[wf_function_def] >> metis_tac[inst_ids_el_eq]) >>
  `MEM (EL k1 bb.bb_instructions) (fn_insts fn)` by
    metis_tac[MEM_fn_insts, MEM_EL] >>
  `MEM (EL k2 bb.bb_instructions) (fn_insts fn)` by
    metis_tac[MEM_fn_insts, MEM_EL] >>
  metis_tac[]
QED

(* ===== One step ===== *)


(* The key step lemma: executing a non-terminator instruction preserves
   FLOOKUP for variables that are outputs of OTHER instructions in the block. *)
Theorem step_preserves_other_output:
  !fn bb idx k v fuel ctx s s'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    idx < LENGTH bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\ k <> idx /\
    MEM v (EL k bb.bb_instructions).inst_outputs /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt strip_tac >>
  `~MEM v (EL idx bb.bb_instructions).inst_outputs` by
    metis_tac[block_ssa_disjoint_outputs] >>
  `lookup_var v s' = lookup_var v s` by
    metis_tac[step_preserves_non_output_vars] >>
  fs[lookup_var_def]
QED

(* eval_op_env transfers when FLOOKUP agrees on Var operands *)
Theorem eval_op_env_transfer:
  !op env env' w. eval_op_env op env = SOME w /\
    (!u. op = Var u ==> FLOOKUP env' u = FLOOKUP env u) ==>
    eval_op_env op env' = SOME w
Proof
  Cases >> simp[eval_op_env_def]
QED

(* Operand FLOOKUP preservation: executing a different instruction
   at position idx preserves FLOOKUP for operands of an earlier entry. *)
Theorem operand_flookup_preserved_dinst:
  !fn bb idx k v dinst u' fuel ctx s s'.
    wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    idx < LENGTH bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\ k < idx /\
    EL k bb.bb_instructions = dinst /\
    dfg_tracked_opcode dinst.inst_opcode /\
    MEM (Var u') dinst.inst_operands /\
    MEM v dinst.inst_outputs /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    FLOOKUP s'.vs_vars u' = FLOOKUP s.vs_vars u'
Proof
  rpt strip_tac >>
  Cases_on `dfg_get_def (dfg_build_function fn) u'`
  >- (
    `~MEM u' (EL idx bb.bb_instructions).inst_outputs` by (
      CCONTR_TAC >> gvs[] >>
      `MEM (EL idx bb.bb_instructions) (fn_insts fn)` by
        metis_tac[MEM_fn_insts, MEM_EL] >>
      imp_res_tac dfg_build_function_defs_complete >> gvs[]) >>
    `lookup_var u' s' = lookup_var u' s` by
      metis_tac[step_preserves_non_output_vars] >>
    fs[lookup_var_def])
  >- (
    rename1 `SOME inst_u` >>
    `MEM dinst bb.bb_instructions` by metis_tac[MEM_EL] >>
    mp_tac dfg_block_local_elim >>
    disch_then (qspecl_then [`fn`,`v`,`dinst`,`u'`,`inst_u`,`bb`] mp_tac) >>
    (impl_tac >- fs[]) >>
    strip_tac >>
    `?ku. ku < LENGTH bb.bb_instructions /\ EL ku bb.bb_instructions = inst_u` by
      metis_tac[MEM_EL] >>
    `ku < k` by metis_tac[] >>
    `ku <> idx` by simp[] >>
    `MEM u' inst_u.inst_outputs` by metis_tac[dfg_build_function_correct] >>
    metis_tac[step_preserves_other_output])
QED

(* For a tracked instruction, the output variable cannot be an operand variable. *)
Theorem dfg_output_neq_operand_var:
  !fn v inst u bb idx.
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    MEM (Var u) inst.inst_operands /\
    dfg_tracked_opcode inst.inst_opcode /\
    MEM bb fn.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst ==> v <> u
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  mp_tac dfg_block_local_elim >>
  disch_then (qspecl_then [`fn`,`u`,`bb.bb_instructions❲idx❳`,
    `u`,`bb.bb_instructions❲idx❳`,`bb`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[MEM_EL]) >>
  strip_tac >> `idx < idx` by metis_tac[] >> DECIDE_TAC
QED

(* Rewrite step_inst_base inst _ to the arm of the opcode an assumption
   names; never expand unrelated opcodes. *)
val step_inst_base_opcode_tac =
  qpat_assum `inst.inst_opcode = _` (fn eq =>
    PURE_ONCE_REWRITE_TAC [MATCH_MP (opcode_clause (rhs (concl eq))) eq]);

(* Only the operand/result spine reduces: computed words, comparisons and
   updated states must remain opaque, including in the EQ/SLT/SGT branches. *)
val pure_step_ss = pure_ss ++ boolSimps.BOOL_ss ++
  simpLib.type_ssfrag ``:operand list`` ++
  simpLib.type_ssfrag ``:string list`` ++
  simpLib.type_ssfrag ``:bytes32 option`` ++
  simpLib.type_ssfrag ``:bytes32 option # bytes32 option`` ++
  simpLib.type_ssfrag ``:exec_result``;

(* For tracked opcodes, if step_inst_base succeeds with single output,
   then every operand evaluates in the pre-state. *)
val tracked_assign_eval_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >> asm_simp_tac pure_step_ss [] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[];

val tracked_pure1_eval_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >> strip_tac >>
  imp_res_tac exec_pure1_output >> gvs[];

val tracked_pure2_eval_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >> strip_tac >>
  imp_res_tac exec_pure2_output >> gvs[];

Theorem tracked_step_operand_evaluable:
  !inst s s' v op.
    dfg_tracked_opcode inst.inst_opcode /\
    inst.inst_outputs = [v] /\
    step_inst_base inst s = OK s' /\
    MEM op inst.inst_operands ==>
    ?w. eval_operand op s = SOME w
Proof
  rpt strip_tac >>
  qpat_x_assum `dfg_tracked_opcode _`
    (strip_assume_tac o REWRITE_RULE[dfg_tracked_opcode_def]) >> gvs[]
  >- tracked_assign_eval_tac
  >- tracked_pure1_eval_tac
  >- tracked_pure2_eval_tac
  >- tracked_pure2_eval_tac
  >- tracked_pure2_eval_tac
  >- tracked_pure2_eval_tac
  >- tracked_pure2_eval_tac
  >- tracked_pure2_eval_tac
  >- tracked_pure2_eval_tac
QED

(* Derive step_inst_base from tracked opcode + step_inst *)
Theorem tracked_step_inst_base:
  !inst fuel ctx s s'.
    dfg_tracked_opcode inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst_base inst s = OK s'
Proof
  rpt strip_tac >>
  qpat_x_assum `dfg_tracked_opcode _`
    (strip_assume_tac o REWRITE_RULE[dfg_tracked_opcode_def]) >>
  gvs[step_inst_non_invoke]
QED

(* Derive FLOOKUP preservation for non-output vars from tracked step *)
Theorem tracked_step_flookup:
  !inst v fuel ctx s s'.
    dfg_tracked_opcode inst.inst_opcode /\
    inst.inst_outputs = [v] /\
    step_inst fuel ctx inst s = OK s' ==>
    !u. u <> v ==> FLOOKUP s'.vs_vars u = FLOOKUP s.vs_vars u
Proof
  rpt strip_tac >>
  `~is_terminator inst.inst_opcode` by
    gvs[dfg_tracked_opcode_def, is_terminator_def] >>
  `lookup_var u s' = lookup_var u s` by
    metis_tac[step_preserves_non_output_vars, MEM] >>
  fs[lookup_var_def]
QED

val entry_defs = [dfg_entry_sound_def, dfg_entry_base_sound_def];

(* An entry's soundness depends only on its variable and its operands. *)
(* Transfer the n-th clause of the entry predicate from env to env'. *)
fun entry_transfer_tac n =
  qpat_x_assum `_ env v dinst`
    (mp_tac o el n o CONJUNCTS o REWRITE_RULE entry_defs) >>
  rpt strip_tac >>
  `dfg_tracked_opcode dinst.inst_opcode` by simp[dfg_tracked_opcode_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac[eval_op_env_transfer, FDOM_FLOOKUP];

Theorem dfg_entry_base_sound_transfer:
  !env env' v dinst.
    dfg_entry_base_sound env v dinst /\ v IN FDOM env' /\
    FLOOKUP env' v = FLOOKUP env v /\
    (dfg_tracked_opcode dinst.inst_opcode ==>
       !u. MEM (Var u) dinst.inst_operands ==>
           FLOOKUP env' u = FLOOKUP env u) ==>
    dfg_entry_base_sound env' v dinst
Proof
  rpt strip_tac >> REWRITE_TAC [dfg_entry_base_sound_def] >> rpt conj_tac
  >- (rpt strip_tac >> fs[dfg_entry_base_sound_def] >> metis_tac[FDOM_FLOOKUP])
  >- entry_transfer_tac 2
  >- entry_transfer_tac 3
  >- entry_transfer_tac 4
  >- entry_transfer_tac 5
QED

Theorem dfg_entry_sound_transfer:
  !env env' v dinst.
    dfg_entry_sound env v dinst /\ v IN FDOM env' /\
    FLOOKUP env' v = FLOOKUP env v /\
    (dfg_tracked_opcode dinst.inst_opcode ==>
       !u. MEM (Var u) dinst.inst_operands ==>
           FLOOKUP env' u = FLOOKUP env u) ==>
    dfg_entry_sound env' v dinst
Proof
  rpt strip_tac >> REWRITE_TAC [dfg_entry_sound_def] >> rpt conj_tac
  >- (qspecl_then [`env`, `env'`, `v`, `dinst`] mp_tac
        dfg_entry_base_sound_transfer >>
      fs[dfg_entry_sound_def])
  >- entry_transfer_tac 6
  >- entry_transfer_tac 7
QED

Theorem dfg_entry_sound_untracked:
  !env v dinst.
    ~dfg_tracked_opcode dinst.inst_opcode ==> dfg_entry_sound env v dinst
Proof
  rw entry_defs >> gvs[dfg_tracked_opcode_def]
QED

(* The entry an executed tracked instruction defines is sound right after it. *)
Theorem dfg_entry_sound_step[local]:
  !fn bb idx v fuel ctx s s'.
    fn_inst_wf fn /\ dfg_block_local fn /\ MEM bb fn.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    dfg_get_def (dfg_build_function fn) v = SOME (EL idx bb.bb_instructions) /\
    dfg_tracked_opcode (EL idx bb.bb_instructions).inst_opcode ==>
    dfg_entry_sound s'.vs_vars v (EL idx bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst.inst_outputs = [v]` by metis_tac[dfg_tracked_inst_outputs] >>
  `step_inst_base inst s = OK s'` by metis_tac[tracked_step_inst_base] >>
  `!u. MEM (Var u) inst.inst_operands ==> u <> v` by
    metis_tac[dfg_output_neq_operand_var] >>
  simp entry_defs >> rpt conj_tac
  >- (rpt strip_tac >>
      `?w. eval_operand (Var u) s = SOME w` by
        metis_tac[tracked_step_operand_evaluable] >>
      `FLOOKUP s'.vs_vars u = FLOOKUP s.vs_vars u` by
        metis_tac[tracked_step_flookup] >>
      gvs[eval_operand_def, lookup_var_def, FDOM_FLOOKUP]) >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >>
  asm_simp_tac pure_step_ss [exec_pure1_def, exec_pure2_def, CaseEq "option"] >>
  strip_tac >> gvs[update_var_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `op1`) >> TRY (Cases_on `op2`) >>
  TRY (Cases_on `lhs`) >> TRY (Cases_on `rhs`) >> TRY (Cases_on `op`) >>
  gvs[eval_operand_def, lookup_var_def, eval_op_env_def, FLOOKUP_UPDATE,
      DISJ_IMP_THM, FORALL_AND_THM, bool_to_word_neq_0w, bool_to_word_eq_0w,
      WORD_LTi, WORD_GTi] >>
  rw[]
QED

(* dfg_prefix_sound is preserved by executing one non-terminator instruction. *)
Theorem dfg_prefix_sound_step:
  !fn bb idx fuel ctx s s'.
    dfg_prefix_sound (dfg_build_function fn) bb s.vs_vars idx /\
    fn_inst_wf fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' ==>
    dfg_prefix_sound (dfg_build_function fn) bb s'.vs_vars (SUC idx)
Proof
  rpt gen_tac >> strip_tac >>
  simp[dfg_prefix_sound_def] >> rpt strip_tac >>
  drule_then strip_assume_tac dfg_build_function_correct >>
  `k < idx \/ k = idx` by decide_tac
  >- (
    `FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v` by
      (qspecl_then [`fn`, `bb`, `idx`, `k`, `v`, `fuel`, `ctx`, `s`, `s'`]
         mp_tac step_preserves_other_output >> simp[] >>
       disch_then irule >> first_assum ACCEPT_TAC) >>
    irule dfg_entry_sound_transfer >> simp[] >> qexists_tac `s.vs_vars` >>
    simp[] >>
    conj_tac
    >- (rpt strip_tac >>
        qspecl_then [`fn`, `bb`, `idx`, `k`, `v`, `EL k bb.bb_instructions`,
                     `u`, `fuel`, `ctx`, `s`, `s'`]
          mp_tac operand_flookup_preserved_dinst >> simp[] >>
        disch_then irule >> first_assum ACCEPT_TAC)
    >> qpat_x_assum `dfg_prefix_sound _ _ _ _` mp_tac >>
    simp[dfg_prefix_sound_def] >>
    disch_then (qspecl_then [`v`, `k`] mp_tac) >>
    simp[] >> metis_tac[FDOM_FLOOKUP]) >>
  gvs[] >>
  Cases_on `dfg_tracked_opcode (EL idx bb.bb_instructions).inst_opcode`
  >- metis_tac[dfg_entry_sound_step] >>
  metis_tac[dfg_entry_sound_untracked]
QED

(* ===== One block ===== *)

Theorem dfg_prefix_sound_phi_prefix:
  !dfg bb env idx.
    idx <= phi_prefix_length bb.bb_instructions ==>
    dfg_prefix_sound dfg bb env idx
Proof
  rw[dfg_prefix_sound_def] >>
  `k < phi_prefix_length bb.bb_instructions` by decide_tac >>
  `(EL k bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  irule dfg_entry_sound_untracked >> simp[dfg_tracked_opcode_def]
QED

(* Over the rest of a block, the prefix grows to the whole block. *)
Theorem dfg_prefix_sound_exec_block[local]:
  !fn bb fuel ctx s r.
    exec_block fuel ctx bb s = OK r /\
    dfg_prefix_sound (dfg_build_function fn) bb s.vs_vars s.vs_inst_idx /\
    fn_inst_wf fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    dfg_prefix_sound (dfg_build_function fn) bb r.vs_vars
      (LENGTH bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  `!n t. n = LENGTH bb.bb_instructions - t.vs_inst_idx /\
         exec_block fuel ctx bb t = OK r /\
         dfg_prefix_sound (dfg_build_function fn) bb t.vs_vars t.vs_inst_idx ==>
         dfg_prefix_sound (dfg_build_function fn) bb r.vs_vars
           (LENGTH bb.bb_instructions)` suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `t.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  Cases_on `step_inst fuel ctx (EL t.vs_inst_idx bb.bb_instructions) t` >>
  simp[] >>
  rename1 `step_inst _ _ _ _ = OK t1` >>
  Cases_on `is_terminator (EL t.vs_inst_idx bb.bb_instructions).inst_opcode` >>
  simp[]
  >- (
    rw[] >>
    `SUC t.vs_inst_idx = LENGTH bb.bb_instructions` by
      (CCONTR_TAC >>
       qpat_x_assum `!i. i < _ - 1 ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
       simp[]) >>
    `r.vs_vars = t.vs_vars` by
      (drule_all step_terminator_preserves_vars >>
       simp[lookup_var_def, fmap_eq_flookup]) >>
    qpat_x_assum `dfg_prefix_sound _ _ _ _` mp_tac >>
    simp[dfg_prefix_sound_def] >> rpt strip_tac >>
    `k < t.vs_inst_idx \/ k = t.vs_inst_idx` by decide_tac >- metis_tac[] >>
    gvs[] >>
    `~dfg_tracked_opcode (EL t.vs_inst_idx bb.bb_instructions).inst_opcode` by
      (strip_tac >> gvs[dfg_tracked_opcode_def, is_terminator_def]) >>
    metis_tac[dfg_entry_sound_untracked]) >>
  strip_tac >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC t.vs_inst_idx`
    mp_tac) >> simp[] >>
  disch_then (qspec_then `t1 with vs_inst_idx := SUC t.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >>
  qspecl_then [`fn`, `bb`, `t.vs_inst_idx`, `fuel`, `ctx`, `t`, `t1`]
    mp_tac dfg_prefix_sound_step >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem dfg_prefix_sound_run_block[local]:
  !fn bb fuel ctx s r.
    run_block fuel ctx bb s = OK r /\
    fn_inst_wf fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    dfg_prefix_sound (dfg_build_function fn) bb r.vs_vars
      (LENGTH bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >>
  qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
  simp[Once run_block_def] >> rename1 `eval_phis _ _ = OK s_phi` >>
  strip_tac >>
  qspecl_then [`fn`, `bb`, `fuel`, `ctx`,
    `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `r`]
    mp_tac dfg_prefix_sound_exec_block >>
  impl_tac >- (simp[dfg_prefix_sound_phi_prefix] >> metis_tac[]) >> simp[]
QED

(* For a tracked variable whose defining inst is NOT in bb,
   FLOOKUP is preserved through run_block for both v and its operands. *)
Theorem run_block_tracked_not_in_bb[local]:
  !fn bb fuel ctx s r v dinst.
    run_block fuel ctx bb s = OK r /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    ~MEM dinst bb.bb_instructions /\
    wf_function fn /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) ==>
    FLOOKUP r.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt strip_tac >>
  irule run_block_non_output_flookup >>
  qexistsl_tac [`bb`, `ctx`, `fuel`] >> simp[] >>
  rpt strip_tac >>
  `MEM v dinst.inst_outputs /\ MEM dinst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `MEM inst (fn_insts fn)` by metis_tac[MEM_fn_insts] >>
  `inst = dinst` by metis_tac[] >>
  gvs[]
QED

(* For a variable where dfg_get_def = NONE (untracked),
   no instruction in fn_insts outputs it, so FLOOKUP preserved. *)
Theorem run_block_untracked_flookup[local]:
  !fn bb fuel ctx s r u.
    run_block fuel ctx bb s = OK r /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) u = NONE ==>
    FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u
Proof
  rpt strip_tac >>
  irule run_block_non_output_flookup >>
  qexistsl_tac [`bb`, `ctx`, `fuel`] >> simp[] >>
  rpt strip_tac >>
  CCONTR_TAC >> gvs[] >>
  `MEM inst (fn_insts fn)` by metis_tac[MEM_fn_insts] >>
  `?inst'. dfg_get_def (dfg_build_function fn) u = SOME inst'` by
    metis_tac[dfg_build_function_defs_complete] >>
  gvs[]
QED

(* If dinst not in bb and u is a Var operand of dinst (tracked opcode),
   then FLOOKUP u is preserved through run_block. *)
Theorem operand_flookup_preserved_not_in_bb[local]:
  !fn bb fuel ctx s r v dinst u.
    run_block fuel ctx bb s = OK r /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    ~MEM dinst bb.bb_instructions /\
    MEM (Var u) dinst.inst_operands /\
    dfg_tracked_opcode dinst.inst_opcode /\
    dfg_block_local fn /\ wf_function fn /\ fn_inst_wf fn /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) ==>
    FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u
Proof
  rpt gen_tac >> strip_tac >>
  (Cases_on `dfg_get_def (dfg_build_function fn) u`
   >- (irule run_block_untracked_flookup >> metis_tac[])) >>
  rename1 `dfg_get_def _ u = SOME inst_u` >>
  `~MEM inst_u bb.bb_instructions` by
    metis_tac[operand_not_in_block] >>
  irule run_block_non_output_flookup >>
  qexistsl_tac [`bb`, `ctx`, `fuel`] >> simp[] >>
  rpt strip_tac >>
  `MEM u inst_u.inst_outputs /\ MEM inst_u (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `MEM inst (fn_insts fn)` by metis_tac[MEM_fn_insts] >>
  `inst = inst_u` by metis_tac[] >>
  metis_tac[]
QED

(* After run_block, a defined entry is sound if its instruction is in bb;
   otherwise its variable and its operands kept their values. *)
Theorem dfg_run_block_entries:
  !fn bb fuel ctx s r.
    run_block fuel ctx bb s = OK r /\
    fn_inst_wf fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    !v dinst.
      dfg_get_def (dfg_build_function fn) v = SOME dinst /\
      v IN FDOM r.vs_vars ==>
      if MEM dinst bb.bb_instructions then dfg_entry_sound r.vs_vars v dinst
      else FLOOKUP r.vs_vars v = FLOOKUP s.vs_vars v /\
           (dfg_tracked_opcode dinst.inst_opcode ==>
            !u. MEM (Var u) dinst.inst_operands ==>
                FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC
  >- (drule_all dfg_prefix_sound_run_block >>
      simp[dfg_prefix_sound_def] >> metis_tac[MEM_EL]) >>
  conj_tac >- metis_tac[run_block_tracked_not_in_bb] >>
  metis_tac[operand_flookup_preserved_not_in_bb]
QED

(* dfg_sound with the operand closure, and dfg_ext_sound, are the
   entry predicates for every defined entry. Both sides split into the
   same clauses in the same order; and_cong pairs them up. *)
val and_cong = METIS_PROVE []
  ``(a <=> b) /\ (c <=> d) ==> (a /\ c <=> b /\ d)``;

Theorem dfg_sound_entries:
  !dfg env.
    dfg_sound dfg env /\
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       vv IN FDOM env /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM env) <=>
    !v dinst. dfg_get_def dfg v = SOME dinst /\ v IN FDOM env ==>
      dfg_entry_base_sound env v dinst
Proof
  rpt gen_tac >> CONV_TAC (LAND_CONV (REWR_CONV CONJ_COMM)) >>
  simp[dfg_sound_def, dfg_assign_sound_def, dfg_iszero_sound_def,
       dfg_eq_sound_def, dfg_compare_sound_def, dfg_entry_base_sound_def,
       IMP_CONJ_THM, FORALL_AND_THM] >>
  rpt (irule and_cong >> conj_tac) >> eq_tac >> rpt strip_tac >>
  imp_res_tac FDOM_FLOOKUP >> first_x_assum drule >> gvs[]
QED

Theorem dfg_ext_sound_entries:
  !dfg env.
    dfg_ext_sound dfg env <=>
    !v dinst. dfg_get_def dfg v = SOME dinst /\ v IN FDOM env ==>
      dfg_entry_sound env v dinst
Proof
  rpt gen_tac >>
  `dfg_ext_sound dfg env <=>
     (dfg_sound dfg env /\
      (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
         vv IN FDOM env /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
         u IN FDOM env)) /\
     dfg_arith_sound dfg env /\ dfg_compare_full_sound dfg env` by
    (rw[dfg_ext_sound_def] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >> REWRITE_TAC [dfg_sound_entries] >>
  simp[dfg_entry_sound_def, dfg_arith_sound_def, dfg_compare_full_sound_def,
       IMP_CONJ_THM, FORALL_AND_THM] >>
  rpt (irule and_cong >> conj_tac) >> eq_tac >> rpt strip_tac >>
  imp_res_tac FDOM_FLOOKUP >> first_x_assum drule >> gvs[]
QED

(* dfg_sound + operand closure preserved through run_block.
   Requires dfg_block_local to handle the overwrite case in loops. *)
Theorem dfg_sound_run_block:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s.vs_vars) /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    run_block fuel ctx bb s = OK r ==>
    dfg_sound (dfg_build_function fn) r.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM r.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM r.vs_vars)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`] mp_tac
    dfg_run_block_entries >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `!v dinst. dfg_get_def (dfg_build_function fn) v = SOME dinst /\
     v IN FDOM s.vs_vars ==> dfg_entry_base_sound s.vs_vars v dinst` by
    (qspecl_then [`dfg_build_function fn`, `s.vs_vars`]
       (mp_tac o iffLR) dfg_sound_entries >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  REWRITE_TAC [dfg_sound_entries] >> rpt strip_tac >>
  qpat_x_assum `!v dinst. _ ==> if MEM _ _ then _ else _`
    (qspecl_then [`v`, `dinst`] mp_tac) >>
  simp[] >> IF_CASES_TAC >- simp[dfg_entry_sound_def] >>
  strip_tac >> irule dfg_entry_base_sound_transfer >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `s.vs_vars` >> gvs[] >> metis_tac[FDOM_FLOOKUP]
QED

(* dfg_ext_sound preserved through run_block *)
Theorem dfg_ext_sound_run_block:
  !fn bb fuel ctx s r.
    dfg_ext_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> i1 = i2) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    run_block fuel ctx bb s = OK r ==>
    dfg_ext_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`] mp_tac
    dfg_run_block_entries >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  fs[dfg_ext_sound_entries] >> rpt strip_tac >>
  qpat_x_assum `!v dinst. _ ==> if MEM _ _ then _ else _`
    (qspecl_then [`v`, `dinst`] mp_tac) >>
  simp[] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> irule dfg_entry_sound_transfer >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `s.vs_vars` >> gvs[] >> metis_tac[FDOM_FLOOKUP]
QED

(* Extraction lemmas for dfg_prefix_sound: clause n of dfg_entry_sound *)
fun prefix_entry_tac n =
  rpt strip_tac >>
  qpat_x_assum `dfg_prefix_sound _ _ _ _`
    (mp_tac o REWRITE_RULE [dfg_prefix_sound_def]) >>
  disch_then (qspecl_then [`v`, `inst`, `k`] mp_tac) >> simp[] >>
  disch_then (mp_tac o el n o CONJUNCTS o REWRITE_RULE entry_defs) >>
  simp[];

Theorem dfg_prefix_iszero_sound:
  !dfg bb env idx v inst inp k.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME inst /\
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Var inp] /\
    v IN FDOM env /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst ==>
    !w. FLOOKUP env v = SOME w ==>
      (w <> 0w ==> FLOOKUP env inp = SOME 0w) /\
      (w = 0w ==> !w'. FLOOKUP env inp = SOME w' ==> w' <> 0w)
Proof
  prefix_entry_tac 3
QED

Theorem dfg_prefix_arith_sound:
  !dfg bb env idx v inst op1 op2 k.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME inst /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    inst.inst_operands = [op1; op2] /\
    (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) /\
    v IN FDOM env /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst ==>
    ?w1 w2.
      eval_op_env op1 env = SOME w1 /\
      eval_op_env op2 env = SOME w2 /\
      FLOOKUP env v = SOME
        (if inst.inst_opcode = ADD then word_add w1 w2 else word_sub w1 w2)
Proof
  prefix_entry_tac 6
QED

Theorem dfg_prefix_compare_sound:
  !dfg bb env idx v inst op1 op2 k.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME inst /\
    (inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
    inst.inst_operands = [op1; op2] /\
    (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) /\
    v IN FDOM env /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst ==>
    ?w1 w2.
      eval_op_env op1 env = SOME w1 /\
      eval_op_env op2 env = SOME w2 /\
      FLOOKUP env v = SOME (bool_to_word
        (if inst.inst_opcode = LT
         then w2n w1 < w2n w2
         else w2n w1 > w2n w2))
Proof
  prefix_entry_tac 7
QED

Theorem dfg_prefix_fdom_closure:
  !dfg bb env idx v inst u k.
    dfg_prefix_sound dfg bb env idx /\
    dfg_get_def dfg v = SOME inst /\
    dfg_tracked_opcode inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\
    v IN FDOM env /\
    k < idx /\ k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst ==>
    u IN FDOM env
Proof
  prefix_entry_tac 1
QED
