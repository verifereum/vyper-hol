(* Structural boundaries for revert forwarding. *)
Theory fnFrameStepsRevertForward
Ancestors
  contextCodegenRel dfgDefs list dfgAnalysisProps allocaRemapSSA venomWf
  stackPlanGen venomExecProofs removeUnusedSsaProofs frameRel
  frameViewFacts instSimHelpers emitSim venomExecSemantics venomInst
  strongPrefixSim asmFrameHelpers planExec prefixExec stackOpAsmSim
  stackOpSim blockSimHelpers asmSem stackModel rich_list codegenRel planWf
  reorderSim genBlockSim doSwapSim planAlign livenessAnalysisProps stackPlanOps
  fnFrameTerminalHalt fnFrameTerminalAbort genericInputReady

Theorem resolve_block_assigns_cong:
  !insts at h.
    (!inst v op. MEM inst insts /\ inst.inst_opcode = ASSIGN /\
       inst.inst_outputs = [v] /\ inst.inst_operands = [op] ==>
       h (Var v) = h op) ==>
    h (resolve_block_assigns insts at) = h at
Proof
  Induct_on `insts` >- simp[resolve_block_assigns_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `resolve_block_assigns (inst :: insts) at` >>
  Cases_on `at` >> rw[resolve_block_assigns_def]
  >- (Cases_on `inst.inst_operands` >> gvs[] >>
      first_x_assum (qspecl_then [`h`, `h'`] mp_tac) >>
      (impl_tac >- metis_tac[]) >>
      disch_then SUBST1_TAC >>
      sym_tac >> first_x_assum irule >> qexists_tac `inst` >> simp[]) >>
  first_x_assum irule >> metis_tac[MEM]
QED

Theorem normalize_operand_rank_visited:
  !dfg (rank : string -> num) v visited.
    (!x inst y. FLOOKUP dfg.dfg_defs x = SOME inst /\
       inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] ==>
       rank y < rank x) /\
    (!w. MEM w visited ==> rank v < rank w) ==>
    normalize_operand dfg visited (Var v) =
    normalize_operand dfg [] (Var v)
Proof
  rpt gen_tac >> qid_spec_tac `visited` >>
  completeInduct_on `rank v` >> rpt strip_tac >>
  `~MEM v visited` by (strip_tac >> first_x_assum drule >> simp[]) >>
  simp[Ntimes normalize_operand_def 2] >>
  Cases_on `FLOOKUP dfg.dfg_defs v` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `inst.inst_opcode = ASSIGN` >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h`
  >- simp[normalize_operand_def]
  >- (rename1 `inst.inst_operands = [Var y]` >>
      `rank y < rank v` by (first_x_assum irule >> metis_tac[]) >>
      `normalize_operand dfg (v :: visited) (Var y) =
       normalize_operand dfg [] (Var y)` by
        (first_x_assum irule >> qexistsl_tac [`rank y`, `rank`] >>
         simp[] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
      `normalize_operand dfg [v] (Var y) =
       normalize_operand dfg [] (Var y)` by
        (first_x_assum irule >> qexistsl_tac [`rank y`, `rank`] >> simp[]) >>
      simp[]) >>
  simp[normalize_operand_def]
QED

Theorem dfg_build_function_ssa_def:
  !fn inst v.
    ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
    dfg_get_def (dfg_build_function fn) v = SOME inst
Proof
  rpt strip_tac >>
  drule_all dfg_build_function_defs_complete >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `inst' = inst` by (irule ssa_unique_output >> metis_tac[]) >>
  gvs[]
QED

Theorem dfg_ordinary_use_available:
  !fn bb use v def.
    ssa_form fn /\ def_dominates_uses fn /\
    MEM bb fn.fn_blocks /\ MEM use bb.bb_instructions /\
    use.inst_opcode <> PHI /\ MEM (Var v) use.inst_operands /\
    dfg_get_def (dfg_build_function fn) v = SOME def ==>
    ?db. MEM db fn.fn_blocks /\ MEM def db.bb_instructions /\
      MEM v def.inst_outputs /\ fn_dominates fn db.bb_label bb.bb_label /\
      (db = bb ==> ?p q. p < q /\ q < LENGTH bb.bb_instructions /\
        EL p bb.bb_instructions = def /\ EL q bb.bb_instructions = use)
Proof
  rpt strip_tac >>
  `def_available_at fn bb (SOME use) v` by
    (gvs[def_dominates_uses_def] >> metis_tac[]) >>
  gvs[def_available_at_def] >>
  `MEM def_inst (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
  drule_all dfg_build_function_ssa_def >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem dfg_assign_input_available:
  !fn bb use v def.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM use bb.bb_instructions /\ use.inst_opcode = ASSIGN /\
    use.inst_operands = [Var v] /\
    dfg_get_def (dfg_build_function fn) v = SOME def ==>
    ?db. MEM db fn.fn_blocks /\ MEM def db.bb_instructions /\
      MEM v def.inst_outputs /\ fn_dominates fn db.bb_label bb.bb_label /\
      (db = bb ==> ?p q. p < q /\ q < LENGTH bb.bb_instructions /\
        EL p bb.bb_instructions = def /\ EL q bb.bb_instructions = use)
Proof
  rpt strip_tac >> irule dfg_ordinary_use_available >>
  gvs[codegen_ready_fn_def] >> metis_tac[MEM]
QED

Theorem is_fn_path_proper_prefix:
  !fn path d. is_fn_path fn path /\ MEM d path /\ d <> LAST path ==>
    ?pre. is_fn_path fn pre /\ pre <> [] /\ HD pre = HD path /\
      LAST pre = d /\ LENGTH pre < LENGTH path
Proof
  Induct_on `path` >- simp[] >>
  rpt gen_tac >> Cases_on `path` >- simp[] >>
  rename1 `h :: x :: xs` >>
  Cases_on `d = h`
  >- (strip_tac >> qexists_tac `[h]` >> simp[is_fn_path_def]) >>
  simp[is_fn_path_def] >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `d`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `h :: pre` >>
  Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem fn_dominates_strict_measure:
  !fn. ?depth : string -> num.
    !d n. fn_dominates fn d n /\ d <> n ==> depth d < depth n
Proof
  gen_tac >>
  qabbrev_tac `P = \lbl k. ?path. is_fn_path fn path /\ path <> [] /\
    (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
    LAST path = lbl /\ LENGTH path = k` >>
  `!lbl. fn_reachable fn lbl ==> ?k. P lbl k` by
    (rpt strip_tac >> gvs[fn_reachable_def] >>
     drule rtc_to_fn_path >> strip_tac >>
     qexists_tac `LENGTH path` >> simp[Abbr `P`] >> metis_tac[]) >>
  qexists_tac `\lbl. LEAST k. P lbl k` >> rpt strip_tac >>
  `fn_reachable fn n` by gvs[fn_dominates_def] >>
  `?k. P n k` by metis_tac[] >>
  `P n (LEAST k. P n k)` by
    (numLib.LEAST_ELIM_TAC >> metis_tac[]) >>
  `?path. is_fn_path fn path /\ path <> [] /\
     (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
     LAST path = n /\ LENGTH path = (LEAST k. P n k)` by
    (qpat_x_assum `P n _` mp_tac >> simp[Abbr `P`]) >>
  `MEM d path` by (gvs[fn_dominates_def] >> metis_tac[]) >>
  `d <> LAST path` by simp[] >>
  drule_all is_fn_path_proper_prefix >> strip_tac >>
  `P d (LENGTH pre)` by (simp[Abbr `P`] >> metis_tac[]) >>
  ` (LEAST k. P d k) <= LENGTH pre` by
    (numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >>
     rpt strip_tac >> spose_not_then assume_tac >>
     first_x_assum (qspec_then `LENGTH pre` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem ssa_output_location:
  !fn. ssa_form fn /\ fn_inst_ids_distinct fn ==>
    ?loc : string -> basic_block # num.
      !bb p v. MEM bb fn.fn_blocks /\ p < LENGTH bb.bb_instructions /\
        MEM v (EL p bb.bb_instructions).inst_outputs ==> loc v = (bb,p)
Proof
  rpt strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==>
     ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (rpt strip_tac >> irule all_distinct_flat_map_member >>
     qexists_tac `MAP (\bb. bb.bb_instructions) fn.fn_blocks` >>
     gvs[fn_inst_ids_distinct_def, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP] >>
     metis_tac[]) >>
  `!bb p cc q v.
     MEM bb fn.fn_blocks /\ p < LENGTH bb.bb_instructions /\
     MEM v (EL p bb.bb_instructions).inst_outputs /\
     MEM cc fn.fn_blocks /\ q < LENGTH cc.bb_instructions /\
     MEM v (EL q cc.bb_instructions).inst_outputs ==> bb = cc /\ p = q` by
    (rpt strip_tac >>
     `bb = cc /\ EL p bb.bb_instructions = EL q cc.bb_instructions` by
       (irule ssa_unique_output_block >> metis_tac[EL_MEM]) >>
     gvs[] >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by metis_tac[] >>
     `EL p (MAP (\i. i.inst_id) bb.bb_instructions) =
      EL q (MAP (\i. i.inst_id) bb.bb_instructions)` by simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  qexists_tac `\v. @bp. MEM (FST bp) fn.fn_blocks /\
    SND bp < LENGTH (FST bp).bb_instructions /\
    MEM v (EL (SND bp) (FST bp).bb_instructions).inst_outputs` >>
  rpt strip_tac >> simp[] >> SELECT_ELIM_TAC >> conj_tac
  >- (qexists_tac `(bb,p)` >> simp[]) >>
  Cases >> simp[] >> metis_tac[]
QED

Theorem codegen_assign_rank:
  !fn. codegen_ready_fn fn ==> ?rank : string -> num.
    !x inst y. FLOOKUP (dfg_build_function fn).dfg_defs x = SOME inst /\
      inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var y] ==>
      rank y < rank x
Proof
  rpt strip_tac >>
  `ssa_form fn /\ fn_inst_ids_distinct fn` by
    gvs[codegen_ready_fn_def, wf_function_def] >>
  drule_all ssa_output_location >> strip_tac >>
  qspec_then `fn` strip_assume_tac fn_dominates_strict_measure >>
  qabbrev_tac `M = SUC (SUM (MAP (\bb. LENGTH bb.bb_instructions) fn.fn_blocks))` >>
  `!bb. MEM bb fn.fn_blocks ==> LENGTH bb.bb_instructions < M` by
    (simp[Abbr `M`] >>
     `!bbs bb:basic_block. MEM bb bbs ==>
       LENGTH bb.bb_instructions <= SUM (MAP (\cc. LENGTH cc.bb_instructions) bbs)`
       suffices_by (simp[arithmeticTheory.LESS_EQ_IFF_LESS_SUC]) >>
     Induct >> simp[] >> rpt strip_tac >> gvs[] >>
     first_x_assum drule >> simp[]) >>
  qexists_tac `\v. if IS_SOME (dfg_get_def (dfg_build_function fn) v)
    then depth (FST (loc v)).bb_label * M + SND (loc v) + 1 else 0` >>
  rpt strip_tac >>
  `dfg_get_def (dfg_build_function fn) x = SOME inst` by
    simp[dfg_get_def_def] >>
  drule dfg_build_function_correct >> strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[venomInstTheory.fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  `?p. p < LENGTH bb.bb_instructions /\ EL p bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  `loc x = (bb,p)` by metis_tac[] >>
  Cases_on `dfg_get_def (dfg_build_function fn) y`
  >- simp[] >>
  rename1 `dfg_get_def (dfg_build_function fn) y = SOME def` >>
  drule_all dfg_assign_input_available >> strip_tac >>
  Cases_on `db = bb`
  >- (gvs[] >>
      `loc x = (bb,q) /\ loc y = (bb,p')` by
        (conj_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
      qpat_x_assum `!bb p v. _` kall_tac >> gvs[]) >>
  `?q. q < LENGTH db.bb_instructions /\ EL q db.bb_instructions = def` by
    metis_tac[MEM_EL] >>
  `loc y = (db,q)` by metis_tac[] >>
  `db.bb_label <> bb.bb_label` by
    (strip_tac >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       gvs[codegen_ready_fn_def, wf_function_def, venomInstTheory.fn_labels_def] >>
     `?a. a < LENGTH fn.fn_blocks /\ EL a fn.fn_blocks = bb` by metis_tac[MEM_EL] >>
     `?b. b < LENGTH fn.fn_blocks /\ EL b fn.fn_blocks = db` by metis_tac[MEM_EL] >>
     `EL a (MAP (\b. b.bb_label) fn.fn_blocks) =
      EL b (MAP (\b. b.bb_label) fn.fn_blocks)` by simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  `depth db.bb_label < depth bb.bb_label` by metis_tac[] >>
  `q < M` by metis_tac[arithmeticTheory.LESS_TRANS] >>
  simp[] >>
  `M * SUC (depth db.bb_label) <= M * depth bb.bb_label` by
    simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  qpat_x_assum `M * SUC _ <= _` mp_tac >>
  pure_rewrite_tac[arithmeticTheory.MULT_SUC] >> decide_tac
QED

Theorem normalize_operand_codegen_assign:
  !fn x inst op. codegen_ready_fn fn /\
    dfg_get_def (dfg_build_function fn) x = SOME inst /\
    inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] ==>
    normalize_operand (dfg_build_function fn) [] (Var x) =
    normalize_operand (dfg_build_function fn) [] op
Proof
  rpt strip_tac >> drule codegen_assign_rank >> strip_tac >>
  `FLOOKUP (dfg_build_function fn).dfg_defs x = SOME inst` by
    gvs[dfg_get_def_def] >>
  simp[Once normalize_operand_def] >>
  Cases_on `op`
  >- simp[normalize_operand_def]
  >- (irule normalize_operand_rank_visited >>
      qexists_tac `rank` >> simp[] >> metis_tac[]) >>
  simp[normalize_operand_def]
QED

Theorem normalize_operand_resolve_block_assigns:
  !fn insts op. codegen_ready_fn fn /\
    EVERY (\inst. MEM inst (fn_insts fn)) insts ==>
    normalize_operand (dfg_build_function fn) [] (resolve_block_assigns insts op) =
    normalize_operand (dfg_build_function fn) [] op
Proof
  rpt strip_tac >> irule resolve_block_assigns_cong >> rpt strip_tac >>
  irule normalize_operand_codegen_assign >> conj_tac >- simp[] >>
  qexists_tac `inst` >> simp[] >>
  irule dfg_build_function_ssa_def >>
  gvs[codegen_ready_fn_def, EVERY_MEM] >> metis_tac[]
QED

Theorem owned_operand_resolved_value:
  !fn insts op root s lo owned.
    codegen_ready_fn fn /\ EVERY (\inst. MEM inst (fn_insts fn)) insts /\
    resolve_block_assigns insts op = root /\
    (is_var_operand op ==> owned op) /\
    (!at. owned at ==> operand_val s lo at =
      operand_val s lo (normalize_operand (dfg_build_function fn) [] at)) ==>
    operand_val s lo op =
    operand_val s lo (normalize_operand (dfg_build_function fn) [] root)
Proof
  rpt strip_tac >>
  `normalize_operand (dfg_build_function fn) [] root =
   normalize_operand (dfg_build_function fn) [] op` by
    metis_tac[normalize_operand_resolve_block_assigns] >>
  simp[] >> Cases_on `op` >>
  gvs[stackPlanTypesTheory.is_var_operand_def, normalize_operand_def]
QED

(* Future uses whose value has not yet been supplied by a suffix definition. *)
Definition rf_live_use_def:
  rf_live_use bb k j op <=>
    ?r inst. k <= r /\ r <= j /\ get_instruction bb r = SOME inst /\
      MEM op (compute_operands inst) /\
      (!t di x. k <= t /\ t < r /\ get_instruction bb t = SOME di /\
                op = Var x ==> ~MEM x di.inst_outputs)
End

Definition rf_value_inv_def:
  rf_value_inv fn ra bb j lo entry k s <=>
    !op. rf_live_use bb k j op ==>
      operand_val (frame_view fn ra s) lo op =
      operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)
End

Theorem rf_live_use_current:
  get_instruction bb k = SOME inst /\ k <= j /\
  MEM op (compute_operands inst) ==> rf_live_use bb k j op
Proof
  strip_tac >> simp[rf_live_use_def] >>
  qexistsl_tac [`k`, `inst`] >> simp[] >> rpt strip_tac >> decide_tac
QED

Theorem rf_live_use_backward:
  rf_live_use bb (SUC k) j op /\ get_instruction bb k = SOME inst /\
  (!x. op = Var x ==> ~MEM x inst.inst_outputs) ==>
  rf_live_use bb k j op
Proof
  simp[rf_live_use_def] >> rpt strip_tac >>
  qexistsl_tac [`r`, `inst'`] >> simp[] >>
  rpt strip_tac >> Cases_on `t = k` >- gvs[] >>
  `SUC k <= t` by decide_tac >> metis_tac[]
QED

Theorem rf_value_inv_entry:
  (!r inst op. i <= r /\ get_instruction bb r = SOME inst /\
    MEM op (compute_operands inst) /\ is_var_operand op /\
    (!t di x. i <= t /\ t < r /\ get_instruction bb t = SOME di /\
              op = Var x ==> ~MEM x di.inst_outputs) ==> owned op) /\
  (!op. owned op ==>
    operand_val (frame_view fn ra s) lo op =
    operand_val (frame_view fn ra s) lo
      (normalize_operand (dfg_build_function fn) [] op)) ==>
  rf_value_inv fn ra bb j lo (frame_view fn ra s) i s
Proof
  simp[rf_value_inv_def, rf_live_use_def] >> rpt strip_tac >>
  Cases_on `is_var_operand op`
  >- (`owned op` by (first_x_assum irule >> metis_tac[]) >> simp[]) >>
  Cases_on `op` >>
  gvs[stackPlanTypesTheory.is_var_operand_def, normalize_operand_def]
QED

Theorem rf_value_inv_assign:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  get_instruction bb k = SOME inst /\ k <= j /\
  inst.inst_opcode = ASSIGN /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  step_inst fuel ctx inst s = OK s' /\
  rf_value_inv fn ra bb j lo entry k s ==>
  rf_value_inv fn ra bb j lo entry (SUC k) s'
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
  simp[Once step_inst_def, Once step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 `inst.inst_outputs = [x]` >>
  rename1 `inst.inst_operands = [rhs]` >>
  rename1 `eval_operand rhs s = SOME v` >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `normalize_operand (dfg_build_function fn) [] (Var x) =
   normalize_operand (dfg_build_function fn) [] rhs` by
    (irule normalize_operand_codegen_assign >> simp[] >> qexists_tac `inst` >>
     simp[] >> irule dfg_build_function_ssa_def >> simp[] >> metis_tac[]) >>
  `rf_live_use bb k j rhs` by
    (irule rf_live_use_current >>
     simp[compute_operands_def, python_stack_operands_def]) >>
  `operand_val (frame_view fn ra s) lo rhs =
   operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs)` by
    metis_tac[rf_value_inv_def] >>
  `MEM x inst.inst_outputs` by simp[] >>
  `eval_operand rhs (frame_view fn ra s) =
   SOME (if retpc_var fn x then ra else v)` by
    (drule_all assign_eval_frame_view >>
     disch_then (qspecl_then [`ra`, `s.vs_memory`] mp_tac) >>
     Cases_on `rhs` >>
     simp[frame_view_def, venomStateTheory.eval_operand_def,
          venomStateTheory.lookup_var_def]) >>
  simp[rf_value_inv_def] >> rpt strip_tac >>
  Cases_on `op = Var x`
  >- (gvs[frame_view_update_var, operand_val_update_var_eq] >>
      metis_tac[operand_val_eq_eval]) >>
  `rf_live_use bb k j op` by
    (irule rf_live_use_backward >> simp[] >> metis_tac[]) >>
  `operand_val (frame_view fn ra s) lo op =
   operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)` by
    metis_tac[rf_value_inv_def] >>
  simp[frame_view_update_var] >>
  irule EQ_TRANS >> goal_assum (drule_at Any) >>
  irule operand_val_update_var >> Cases_on `op` >> gvs[]
QED

Theorem rf_value_inv_index[simp]:
  rf_value_inv fn ra bb j lo entry k (s with vs_inst_idx := q) <=>
  rf_value_inv fn ra bb j lo entry k s
Proof
  simp[rf_value_inv_def] >> eq_tac >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `op` >>
  simp[frame_view_def, codegenRelTheory.operand_val_def,
       venomStateTheory.lookup_var_def]
QED

Theorem rf_value_inv_output_free:
  get_instruction bb k = SOME inst /\ inst.inst_outputs = [] /\
  s'.vs_vars = s.vs_vars /\ rf_value_inv fn ra bb j lo entry k s ==>
  rf_value_inv fn ra bb j lo entry (SUC k) s'
Proof
  strip_tac >> simp[rf_value_inv_def] >> rpt strip_tac >>
  `rf_live_use bb k j op` by
    (irule rf_live_use_backward >> simp[] >> metis_tac[MEM]) >>
  `operand_val (frame_view fn ra s) lo op =
   operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)` by
    metis_tac[rf_value_inv_def] >>
  `operand_val (frame_view fn ra s') lo op =
   operand_val (frame_view fn ra s) lo op` by
    (Cases_on `op` >>
     simp[NoAsms, frame_view_def, codegenRelTheory.operand_val_def,
          venomStateTheory.lookup_var_def] >> gvs[]) >>
  simp[]
QED

Theorem rf_value_inv_returndatacopy:
  get_instruction bb k = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  step_inst fuel ctx inst s = OK s' /\
  rf_value_inv fn ra bb j lo entry k s ==>
  rf_value_inv fn ra bb j lo entry (SUC k)
    (s' with vs_inst_idx := SUC k)
Proof
  strip_tac >> simp[] >> irule rf_value_inv_output_free >>
  simp[] >> qexists_tac `s` >> simp[] >>
  qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
  simp[Once step_inst_def, Once step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[venomStateTheory.write_memory_with_expansion_def]
QED

Theorem simple_op_stack_frame:
  !initial_fmp lo o2pc prog op ps vs st stk rest.
    is_simple_stack_op op /\
    FST (stack_op_wf lo op (LENGTH ps.ps_stack)) /\
    plan_stack_rel lo vs ps.ps_stack stk /\
    st.as_stack = stk ++ rest /\
    asm_block_at prog st.as_pc (exec_stack_op initial_fmp op) ==>
    ?stk'.
      asm_steps lo o2pc prog (LENGTH (exec_stack_op initial_fmp op)) st =
        AsmOK (st with <| as_stack := stk' ++ rest;
          as_pc := st.as_pc + LENGTH (exec_stack_op initial_fmp op) |>) /\
      plan_stack_rel lo vs (apply_simple_op lo op ps).ps_stack stk'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  gvs[is_simple_stack_op_def]
  >- (Cases_on `o'` >> gvs[is_simple_stack_op_def]
      >- suspend "push_lit"
      >> suspend "push_label")
  >- suspend "pop"
  >- suspend "swap"
  >- suspend "dup"
  >- suspend "label"
  >> suspend "pushlabel"
QED

Resume simple_op_stack_frame[push_lit]:
  gvs[exec_stack_op_def, stack_op_wf_def, apply_simple_op_def] >>
  qexists_tac `c :: stk` >>
  conj_tac
  >- (once_rewrite_tac[DECIDE ``1 = SUC 0``] >>
      simp[Once asm_steps_def] >>
      gvs[asm_block_at_def, asm_step_push_ok, asm_steps_def, asm_next_def,
          GSYM asmIRTheory.encode_num_bytes_w2n_compute,
          push_encode_roundtrip]) >>
  irule plan_stack_rel_push >> simp[operand_val_def]
QED

Resume simple_op_stack_frame[push_label]:
  gvs[exec_stack_op_def, stack_op_wf_def, apply_simple_op_def] >>
  Cases_on `FLOOKUP lo s` >> gvs[] >>
  qexists_tac `n2w x :: stk` >> conj_tac
  >- (once_rewrite_tac[DECIDE ``1 = SUC 0``] >>
      simp[Once asm_steps_def] >>
      drule asm_step_pushlabel_ok >>
      disch_then (qspecl_then [`o2pc`, `st`] assume_tac) >>
      gvs[asm_block_at_def, asm_steps_def, asm_next_def]) >>
  irule plan_stack_rel_push >> simp[operand_val_def]
QED

Resume simple_op_stack_frame[label]:
  gvs[exec_stack_op_def, stack_op_wf_def, apply_simple_op_def] >>
  qexists_tac `stk` >> simp[] >>
  once_rewrite_tac[DECIDE ``1 = SUC 0``] >>
  simp[Once asm_steps_def] >>
  gvs[asm_block_at_def, asm_step_label_ok, asm_steps_def, asm_next_def] >>
  qpat_x_assum `st.as_stack = _` (SUBST1_TAC o SYM) >>
  simp[asm_state_component_equality]
QED

Resume simple_op_stack_frame[pushlabel]:
  gvs[exec_stack_op_def, stack_op_wf_def, apply_simple_op_def] >>
  Cases_on `FLOOKUP lo s` >> gvs[] >>
  qexists_tac `n2w x :: stk` >> conj_tac
  >- (once_rewrite_tac[DECIDE ``1 = SUC 0``] >>
      simp[Once asm_steps_def] >>
      drule asm_step_pushlabel_ok >>
      disch_then (qspecl_then [`o2pc`, `st`] assume_tac) >>
      gvs[asm_block_at_def, asm_steps_def, asm_next_def]) >>
  irule plan_stack_rel_push >> simp[operand_val_def]
QED

Resume simple_op_stack_frame[dup]:
  gvs[exec_stack_op_def, stack_op_wf_def, apply_simple_op_def] >>
  rename1 `dup_name k` >>
  `LENGTH stk = LENGTH ps.ps_stack` by gvs[plan_stack_rel_def] >>
  qexists_tac `EL (k - 1) stk :: stk` >> conj_tac
  >- (once_rewrite_tac[DECIDE ``1 = SUC 0``] >>
      simp[Once asm_steps_def] >>
      qspecl_then [`lo`, `o2pc`, `k - 1`, `st`] mp_tac asm_step_dup_ok >>
      simp[] >> strip_tac >>
      gvs[asm_block_at_def, asm_steps_def, asm_next_def, EL_APPEND_EQN]) >>
  irule plan_stack_rel_push >> simp[] >>
  drule plan_stack_rel_el >>
  disch_then (qspec_then `k - 1` mp_tac) >>
  `PRE (LENGTH ps.ps_stack + 1 - k) = LENGTH ps.ps_stack - k` by decide_tac >>
  simp[EL_REVERSE]
QED

Resume simple_op_stack_frame[swap]:
  gvs[exec_stack_op_def, stack_op_wf_def, apply_simple_op_def] >>
  `LENGTH stk = LENGTH ps.ps_stack` by gvs[plan_stack_rel_def] >>
  qexists_tac `LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk)` >>
  conj_tac
  >- (once_rewrite_tac[DECIDE ``1 = SUC 0``] >>
      simp[Once asm_steps_def] >>
      gvs[asm_block_at_def, asm_step_swap_ok, asm_steps_def, asm_next_def,
          EL_APPEND_EQN, LUPDATE_APPEND1, HD_APPEND] >>
      Cases_on `stk` >> gvs[]) >>
  simp[Once LUPDATE_commutes] >>
  irule plan_stack_rel_swap >> simp[]
QED

Resume simple_op_stack_frame[pop]:
  gvs[exec_stack_op_def, stack_op_wf_def, apply_simple_op_def] >>
  `LENGTH stk = LENGTH ps.ps_stack` by gvs[plan_stack_rel_def] >>
  qexists_tac `DROP n stk` >> conj_tac
  >- (`!k st. k <= LENGTH st.as_stack /\
          asm_block_at prog st.as_pc (REPLICATE k (AsmOp "POP")) ==>
          asm_steps lo o2pc prog k st =
          AsmOK (st with <|as_stack := DROP k st.as_stack;
                          as_pc := k + st.as_pc|>)` by
        (Induct >- simp[asm_steps_def, asm_state_component_equality] >>
         qx_gen_tac `s` >> strip_tac >>
         Cases_on `s.as_stack` >> gvs[] >>
         gvs[Once REPLICATE, asm_block_at_cons] >>
         simp[Once asm_steps_def, asm_step_def, asm_step_op_def,
              asm_step_memory_def, asm_step_arith_def, asm_step_compare_def,
              asm_step_bitwise_def, asm_pop_def, asm_next_def] >>
         `k + (s.as_pc + 1) = SUC k + s.as_pc` by decide_tac >>
         asm_rewrite_tac[]) >>
      first_x_assum (qspec_then `n` mp_tac) >>
      disch_then (qspec_then `st` mp_tac) >>
      `n - LENGTH ps.ps_stack = 0` by decide_tac >>
      simp[DROP_APPEND]) >>
  irule plan_stack_rel_pop >> simp[]
QED

Finalise simple_op_stack_frame

Theorem simple_prefix_stack_frame:
  !ops initial_fmp lo o2pc prog ps vs st stk rest.
    EVERY is_simple_stack_op ops /\
    prefix_wf lo (LENGTH ps.ps_stack) ops /\
    plan_stack_rel lo vs ps.ps_stack stk /\
    st.as_stack = stk ++ rest /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?stk'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
        AsmOK (st with <|as_stack := stk' ++ rest;
          as_pc := st.as_pc + LENGTH (execute_plan initial_fmp ops)|>) /\
      plan_stack_rel lo vs (apply_simple_ops lo ops ps).ps_stack stk'
Proof
  Induct_on `ops`
  >- (rpt strip_tac >> qexists_tac `stk` >>
      gvs[execute_plan_def, asm_steps_def, apply_simple_ops_def,
          asm_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  gvs[EVERY_DEF, apply_simple_ops_def, execute_plan_def,
      asm_block_at_append] >>
  `FST (stack_op_wf lo h (LENGTH ps.ps_stack)) /\
   prefix_wf lo (SND (stack_op_wf lo h (LENGTH ps.ps_stack))) ops` by
    (gvs[prefix_wf_cons] >> pairarg_tac >> gvs[]) >>
  drule_all simple_op_stack_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  first_x_assum (qspecl_then [`initial_fmp`, `lo`, `o2pc`, `prog`,
    `apply_simple_op lo h ps`, `vs`,
    `st with <|as_stack := stk' ++ rest;
               as_pc := st.as_pc + LENGTH (exec_stack_op initial_fmp h)|>`,
    `stk'`, `rest`] mp_tac) >>
  simp[apply_simple_op_length, execute_plan_def] >> strip_tac >>
  qexists_tac `stk''` >> simp[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule asm_steps_compose_ok >>
  qexists_tac `st with <|as_stack := stk' ++ rest;
    as_pc := st.as_pc + LENGTH (exec_stack_op initial_fmp h)|>` >>
  gvs[]
QED

(* Syntax enclosure: spills are allowed here and eliminated by consumers. *)
Definition simple_or_spill_def:
  simple_or_spill s <=>
    is_simple_stack_op s \/ (?off. s = SOSpill off) \/
    (?off. s = SORestore off)
End

Theorem simple_or_spill_no_spills:
  EVERY simple_or_spill ops /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  EVERY is_simple_stack_op ops
Proof
  simp[EVERY_MEM, simple_or_spill_def] >> metis_tac[]
QED

Theorem do_spill_tos_enclosed:
  EVERY simple_or_spill (FST (do_spill_tos ps))
Proof
  simp[stackPlanOpsTheory.do_spill_tos_def] >>
  pairarg_tac >> simp[simple_or_spill_def]
QED

Theorem do_spill_at_enclosed:
  EVERY simple_or_spill (FST (do_spill_at dist ps))
Proof
  simp[stackPlanOpsTheory.do_spill_at_def] >>
  IF_CASES_TAC >- simp[do_spill_tos_enclosed] >>
  pairarg_tac >> simp[simple_or_spill_def, is_simple_stack_op_def] >>
  metis_tac[do_spill_tos_enclosed, pairTheory.FST]
QED

Theorem do_restore_enclosed:
  !at ps ops ps'. do_restore at ps = (ops,ps') ==>
    EVERY simple_or_spill ops
Proof
  rpt strip_tac >>
  `EVERY simple_or_spill (FST (do_restore at ps))` suffices_by gvs[] >> pop_assum kall_tac >>
  simp[stackPlanOpsTheory.do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled at` >>
  simp[simple_or_spill_def]
QED

Theorem spill_fold_enclosed[local]:
  !items ops offs al.
    EVERY simple_or_spill ops ==>
    EVERY simple_or_spill (FST
      (FOLDL (\(ops, offs, al) item.
        (ops ++ [SOSpill (FST (alloc_spill_slot al))],
         SNOC (FST (alloc_spill_slot al)) offs, SND (alloc_spill_slot al)))
        (ops, offs, al) items))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  simp[simple_or_spill_def]
QED

Theorem do_swap_enclosed:
  !dist ps ops ps'. do_swap dist ps = (ops,ps') ==>
    EVERY simple_or_spill ops
Proof
  rpt strip_tac >>
  `EVERY simple_or_spill (FST (do_swap dist ps))` suffices_by gvs[] >> pop_assum kall_tac >>
  simp[stackPlanOpsTheory.do_swap_def] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- simp[simple_or_spill_def, is_simple_stack_op_def] >>
  pairarg_tac >> simp[EVERY_MAP, simple_or_spill_def] >>
  qspecl_then [`top_n (dist + 1) ps.ps_stack`, `[]`, `[]`, `ps.ps_alloc`]
    mp_tac spill_fold_enclosed >> gvs[LET_THM, pairTheory.UNCURRY]
QED

Theorem do_dup_enclosed:
  EVERY simple_or_spill (FST (do_dup dist ps))
Proof
  simp[stackPlanOpsTheory.do_dup_def] >>
  IF_CASES_TAC >- simp[simple_or_spill_def, is_simple_stack_op_def] >>
  pairarg_tac >>
  simp[EVERY_FLAT, EVERY_MAP, simple_or_spill_def, is_simple_stack_op_def] >>
  qspecl_then [`REVERSE (top_n (dist - 15) ps.ps_stack)`, `[]`, `[]`, `ps.ps_alloc`]
    mp_tac spill_fold_enclosed >> gvs[LET_THM, pairTheory.UNCURRY] >>
  Cases_on `dist <= 31` >> simp[simple_or_spill_def, is_simple_stack_op_def]
QED

Theorem reduce_depth_plan_enclosed:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops,ps') ==>
    EVERY simple_or_spill ops
Proof
  Induct >> simp[stackPlanOpsTheory.reduce_depth_plan_def] >>
  rpt gen_tac >> IF_CASES_TAC >- simp[] >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack`
  >- simp[] >>
  simp[] >> IF_CASES_TAC >- simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len`
  >- simp[] >>
  simp[] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[EVERY_APPEND] >>
  conj_tac >- metis_tac[do_spill_at_enclosed, pairTheory.FST] >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem emit_one_input_enclosed:
  EVERY simple_or_spill (FST (emit_one_input opc nl at ps))
Proof
  Cases_on `at`
  >- simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
          simple_or_spill_def, is_simple_stack_op_def]
  >- (rename1 `Var v` >>
      Cases_on `FLOOKUP ps.ps_spilled (Var v)` >>
      simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def,
           stackPlanOpsTheory.do_restore_def] >>
      rpt IF_CASES_TAC >> simp[] >>
      gvs[pairTheory.UNCURRY, simple_or_spill_def] >>
      BasicProvers.CASE_TAC >> simp[do_dup_enclosed, simple_or_spill_def]) >>
  simp[emit_one_input_def, stackPlanTypesTheory.is_var_operand_def] >>
  IF_CASES_TAC >> simp[simple_or_spill_def, is_simple_stack_op_def]
QED

Theorem emit_input_plan_enclosed:
  !inputs ps. EVERY simple_or_spill (FST (emit_input_plan opc inputs nl ps))
Proof
  Induct_on `inputs` >> simp[emit_input_plan_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[emit_one_input_enclosed, pairTheory.FST]
QED


Theorem reorder_one_enclosed:
  !dfg targets idx op ps ops ps'.
    reorder_one dfg targets idx op ps = (ops,ps') ==>
    EVERY simple_or_spill ops
Proof
  rpt gen_tac >> simp[stackPlanOpsTheory.reorder_one_def] >>
  pairarg_tac >>
  `EVERY simple_or_spill restore_ops` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
        (LENGTH targets) ps.ps_stack` >> gvs[] >>
     Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >>
     drule do_restore_enclosed >> simp[]) >>
  simp[] >> BasicProvers.CASE_TAC >- (strip_tac >> gvs[]) >>
  pairarg_tac >>
  `EVERY simple_or_spill reduce_ops` by
    (Cases_on `x > 16` >> gvs[] >>
     drule reduce_depth_plan_enclosed >> simp[]) >>
  simp[] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps2.ps_stack` >- (strip_tac >> gvs[]) >>
  simp[] >> IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC
  >- (IF_CASES_TAC >- (strip_tac >> gvs[]) >>
      pairarg_tac >> simp[] >> drule do_swap_enclosed >> strip_tac >>
      pairarg_tac >> simp[] >> drule do_swap_enclosed >> strip_tac >>
      strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >> drule do_swap_enclosed >> strip_tac >>
  pairarg_tac >> simp[] >> drule do_swap_enclosed >> strip_tac >>
  strip_tac >> gvs[]
QED

Theorem reorder_fold_enclosed[local]:
  !items ops ps.
    EVERY simple_or_spill ops ==>
    EVERY simple_or_spill (FST
      (FOLDL (\(ops,ps) (idx,op).
        (\(step_ops,ps'). (ops ++ step_ops,ps'))
          (reorder_one dfg targets idx op ps)) (ops,ps) items))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> simp[] >> pairarg_tac >> simp[] >>
  first_x_assum irule >> simp[] >>
  drule reorder_one_enclosed >> simp[]
QED

Theorem reorder_plan_enclosed:
  !dfg targets ps ops ps'.
    reorder_plan dfg targets ps = (ops,ps') ==>
    EVERY simple_or_spill ops
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`MAPi (\i op. (i,op)) targets`, `[]`, `ps`]
    reorder_fold_enclosed) >>
  gvs[stackPlanOpsTheory.reorder_plan_def]
QED

Theorem popmany_fold_enclosed[local]:
  !items ops ps.
    EVERY simple_or_spill ops ==>
    EVERY simple_or_spill (FST
      (FOLDL (\(ops,ps) v.
        case stack_get_depth v ps.ps_stack of
          NONE => (ops,ps)
        | SOME dist =>
          (\(swap_ops,ps'). (ops ++ swap_ops ++ [SOPop 1],
            ps' with ps_stack := stack_pop 1 ps'.ps_stack))
          (if dist = 0 then ([],ps) else do_swap dist ps))
        (ops,ps) items))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_depth h ps.ps_stack`
  >- (simp[] >> first_x_assum irule >> simp[]) >>
  simp[] >> pairarg_tac >> simp[] >>
  first_x_assum irule >> simp[simple_or_spill_def, is_simple_stack_op_def] >>
  Cases_on `x = 0` >> gvs[] >> drule do_swap_enclosed >> simp[]
QED

Theorem popmany_individual_enclosed:
  !items ps ops ps'. popmany_individual items ps = (ops,ps') ==>
    EVERY simple_or_spill ops
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac `popmany_individual items ps = result` >>
  `EVERY simple_or_spill (FST (popmany_individual items ps))`
    suffices_by gvs[Abbr `result`] >>
  pop_assum kall_tac >> pop_assum kall_tac >>
  simp[stackPlanOpsTheory.popmany_individual_def] >>
  irule popmany_fold_enclosed >> simp[]
QED

Theorem popmany_plan_enclosed:
  !items ps ops ps'. popmany_plan items ps = (ops,ps') ==>
    EVERY simple_or_spill ops
Proof
  Cases_on `items` >> simp[stackPlanOpsTheory.popmany_plan_def] >>
  rpt gen_tac >> IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          simp[simple_or_spill_def, is_simple_stack_op_def] >>
          drule do_swap_enclosed >> simp[]) >>
      metis_tac[popmany_individual_enclosed]) >>
  metis_tac[popmany_individual_enclosed]
QED

Theorem optimistic_swap_plan_enclosed:
  !dfg inst nl nt ps ops ps'.
    optimistic_swap_plan dfg inst nl nt ps = (ops,ps') ==>
    EVERY simple_or_spill ops
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >> simp[] >>
  metis_tac[do_swap_enclosed]
QED

Theorem spill_free_preparation_simple:
  !opc inputs nl ps input_ops ps1 dfg targets reorder_ops ps2.
    emit_input_plan opc inputs nl ps = (input_ops,ps1) /\
    reorder_plan dfg targets ps1 = (reorder_ops,ps2) /\
    (!off. ~MEM (SOSpill off) (input_ops ++ reorder_ops) /\
           ~MEM (SORestore off) (input_ops ++ reorder_ops)) ==>
    EVERY is_simple_stack_op (input_ops ++ reorder_ops)
Proof
  rpt gen_tac >> strip_tac >>
  irule simple_or_spill_no_spills >> reverse conj_tac
  >- (simp[EVERY_APPEND] >>
      metis_tac[emit_input_plan_enclosed, reorder_plan_enclosed, pairTheory.FST]) >>
  simp[]
QED

Theorem spill_free_postfix_simple:
  !do_pop items ps pop_ops ps1 no_opt dfg inst nl nt opt_ops ps2.
    (if do_pop then popmany_plan items ps else ([],ps)) = (pop_ops,ps1) /\
    (if no_opt then ([],ps1) else optimistic_swap_plan dfg inst nl nt ps1) =
      (opt_ops,ps2) /\
    (!off. ~MEM (SOSpill off) (pop_ops ++ opt_ops) /\
           ~MEM (SORestore off) (pop_ops ++ opt_ops)) ==>
    EVERY is_simple_stack_op (pop_ops ++ opt_ops)
Proof
  rpt gen_tac >> strip_tac >>
  irule simple_or_spill_no_spills >> reverse conj_tac
  >- (simp[EVERY_APPEND] >> conj_tac
      >- (Cases_on `do_pop` >> gvs[] >>
          drule popmany_plan_enclosed >> simp[]) >>
      Cases_on `no_opt` >> gvs[] >>
      drule optimistic_swap_plan_enclosed >> simp[]) >>
  simp[]
QED

Theorem spill_free_preparation_value_replay:
  emit_input_plan opc inputs nl ps = (input_ops,ps1) /\
  reorder_plan dfg targets ps1 = (reorder_ops,ps2) /\
  opc <> INVOKE /\
  (!off. ~MEM (SOSpill off) (input_ops ++ reorder_ops) /\
         ~MEM (SORestore off) (input_ops ++ reorder_ops)) /\
  (!x a y b. FLOOKUP ps.ps_spilled x = SOME a /\
              FLOOKUP ps.ps_spilled y = SOME b /\ x <> y ==>
              a + 32 <= b \/ b + 32 <= a) /\
  LENGTH targets <= 16 /\ LENGTH targets <= LENGTH ps1.ps_stack /\
  (!x. MEM x targets ==> LIST_ELEM_COUNT x targets <= LIST_ELEM_COUNT x ps1.ps_stack) /\
  (!op. MEM op targets ==> op <> dead_stack_marker /\
       !at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  (!op at. MEM op targets /\
       (MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled) /\
       operand_equiv dfg op at ==>
       operand_val vs lo op = operand_val vs lo at) ==>
  plan_stack_sem_eq lo vs
    (apply_prefix_ops initial_fmp lo (input_ops ++ reorder_ops) ps).ps_stack
    ps2.ps_stack
Proof
  strip_tac >>
  `EVERY is_simple_stack_op (input_ops ++ reorder_ops)` by
    (metis_tac[spill_free_preparation_simple]) >>
  fs[EVERY_APPEND] >>
  `prefix_spill_wf initial_fmp lo input_ops ps` by
    (irule simple_prefix_spill_wf >> simp[]) >>
  `plan_stack_sem_eq lo vs
    (apply_prefix_ops initial_fmp lo input_ops ps).ps_stack ps1.ps_stack` by
    (metis_tac[emit_input_plan_same_initial_stack_value_replay,
               pairTheory.FST, pairTheory.SND]) >>
  simp[apply_prefix_ops_append] >>
  irule reorder_plan_materialised_stack_value_replay >> conj_tac
  >- (match_mp_tac safe_prefix_spilled_separated >> asm_rewrite_tac[]) >>
  conj_tac
  >- (qexistsl_tac [`dfg`, `targets`, `ps1`] >> asm_rewrite_tac[] >>
      simp[]) >>
  irule simple_prefix_spill_wf >> simp[]
QED

Theorem list_elem_count_dom_length:
  !xs ys. (!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x ys) ==>
    LENGTH xs <= LENGTH ys
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `MEM h ys` by
    (first_x_assum (qspec_then `h` mp_tac) >>
     Cases_on `MEM h ys` >> simp[LIST_ELEM_COUNT_THM] >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  qpat_x_assum `MEM h ys` mp_tac >>
  rewrite_tac[listTheory.MEM_SPLIT] >> strip_tac >> gvs[] >>
  `!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x (l1 ++ l2)` by
    (gen_tac >> first_x_assum (qspec_then `x` mp_tac) >>
     simp[LIST_ELEM_COUNT_DEF, FILTER_APPEND] >>
     Cases_on `h = x` >> simp[] >> decide_tac) >>
  first_x_assum drule >> simp[]
QED

Theorem available_input_plan_length:
  !opc inputs nl ps input_ops ps1.
    emit_input_plan opc inputs nl ps = (input_ops,ps1) /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
    LENGTH inputs <= LENGTH ps1.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  irule list_elem_count_dom_length >>
  drule_all emit_input_plan_materialised >> simp[]
QED

Theorem available_preparation_prefix_wf:
  !opc inputs nl ps input_ops ps1 dfg reorder_ops ps2 lo.
    emit_input_plan opc inputs nl ps = (input_ops,ps1) /\
    reorder_plan dfg inputs ps1 = (reorder_ops,ps2) /\
    opc <> INVOKE /\ LENGTH inputs <= 16 /\
    (!op. MEM op inputs /\ is_var_operand op ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!l. MEM (Label l) inputs ==> IS_SOME (FLOOKUP lo l)) ==>
    prefix_wf lo (LENGTH ps.ps_stack) (input_ops ++ reorder_ops)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH inputs <= LENGTH ps1.ps_stack` by
    (metis_tac[available_input_plan_length]) >>
  `prefix_wf lo (LENGTH ps.ps_stack) input_ops /\
   prefix_end_len lo (LENGTH ps.ps_stack) input_ops = LENGTH ps1.ps_stack` by
    (metis_tac[emit_input_plan_wf_len, pairTheory.FST, pairTheory.SND]) >>
  `prefix_wf lo (LENGTH ps1.ps_stack) reorder_ops` by
    (qspecl_then [`dfg`, `inputs`, `ps1`, `lo`] mp_tac reorder_plan_wf_len >>
     simp[]) >>
  metis_tac[prefix_wf_len_append, prefix_wf_append]
QED

Theorem rf_preparation_replay:
  !opc inputs nl ps input_ops ps1 dfg reorder_ops ps2 lo current entry initial_fmp.
  emit_input_plan opc inputs nl ps = (input_ops,ps1) /\
  reorder_plan dfg inputs ps1 = (reorder_ops,ps2) /\
  opc <> INVOKE /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op /\
    normalize_operand dfg [] op <> dead_stack_marker) inputs /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at inputs ==>
    operand_val current lo at = operand_val entry lo (normalize_operand dfg [] at)) /\
  (!x a y b. FLOOKUP ps.ps_spilled x = SOME a /\
    FLOOKUP ps.ps_spilled y = SOME b /\ x <> y ==> a + 32 <= b \/ b + 32 <= a) /\
  (!off. ~MEM (SOSpill off) (input_ops ++ reorder_ops) /\
    ~MEM (SORestore off) (input_ops ++ reorder_ops)) ==>
  EVERY is_simple_stack_op (input_ops ++ reorder_ops) /\
  prefix_wf lo (LENGTH ps.ps_stack) (input_ops ++ reorder_ops) /\
  plan_stack_sem_eq lo current
    (apply_prefix_ops initial_fmp lo (input_ops ++ reorder_ops) ps).ps_stack ps2.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[spill_free_preparation_simple] >>
  conj_tac
  >- (irule available_preparation_prefix_wf >>
      qexistsl_tac [`dfg`, `inputs`, `nl`, `opc`, `ps1`, `ps2`] >>
      fs[EVERY_MEM] >>
      metis_tac[stackPlanTypesTheory.is_label_operand_def]) >>
  `LENGTH inputs <= LENGTH ps1.ps_stack` by
    metis_tac[available_input_plan_length] >>
  `!x. LIST_ELEM_COUNT x inputs <= LIST_ELEM_COUNT x ps1.ps_stack` by
    (drule_all emit_input_plan_materialised >> simp[]) >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at inputs` by
    (drule emit_input_plan_inventory_subset >> simp[]) >>
  irule spill_free_preparation_value_replay >> asm_rewrite_tac[] >>
  qexistsl_tac [`dfg`, `inputs`, `nl`, `opc`, `ps1`, `inputs`] >>
  asm_rewrite_tac[] >>
  fs[EVERY_MEM, operand_equiv_def, dead_stack_marker_def] >>
  simp[normalize_operand_def] >>
  conj_tac
  >- metis_tac[] >>
  metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem normalize_operand_not_dead_marker:
  !dfg visited op.
    (!x inst. FLOOKUP dfg.dfg_defs x = SOME inst ==>
      ~MEM dead_stack_marker inst.inst_operands) /\
    op <> dead_stack_marker ==>
    normalize_operand dfg visited op <> dead_stack_marker
Proof
  recInduct normalize_operand_ind >>
  rw[Once normalize_operand_def, dead_stack_marker_def] >>
  simp[Once normalize_operand_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `MEM v visited` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[] >> metis_tac[MEM]
QED

Theorem codegen_normalize_operand_not_dead_marker:
  !fn visited op.
    codegen_ready_fn fn /\ op <> dead_stack_marker ==>
    normalize_operand (dfg_build_function fn) visited op <> dead_stack_marker
Proof
  rpt gen_tac >> strip_tac >>
  irule normalize_operand_not_dead_marker >> simp[] >>
  rpt strip_tac >>
  `MEM inst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct, dfg_get_def_def] >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)`
    by (Induct >> simp[fn_insts_blocks_def]) >>
  gvs[codegen_ready_fn_def, fn_insts_def, MEM_FLAT, MEM_MAP,
      EVERY_MEM, codegen_ready_inst_def] >>
  metis_tac[]
QED

Theorem rf_entry_preparation_replay:
  !fn ra vs lo base ps opc inputs nl input_ops ps1 reorder_ops ps2 initial_fmp.
    codegen_ready_fn fn /\ generated_plan_state_wf base ps /\
    emit_input_plan opc inputs nl ps = (input_ops,ps1) /\
    reorder_plan (dfg_build_function fn) inputs ps1 = (reorder_ops,ps2) /\
    opc <> INVOKE /\ LENGTH inputs <= 16 /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    EVERY (\op. ~is_label_operand op) inputs /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra vs) lo at =
      operand_val (frame_view fn ra vs) lo
        (normalize_operand (dfg_build_function fn) [] at)) /\
    (!off. ~MEM (SOSpill off) (input_ops ++ reorder_ops) /\
      ~MEM (SORestore off) (input_ops ++ reorder_ops)) ==>
    EVERY is_simple_stack_op (input_ops ++ reorder_ops) /\
    prefix_wf lo (LENGTH ps.ps_stack) (input_ops ++ reorder_ops) /\
    plan_stack_sem_eq lo (frame_view fn ra vs)
      (apply_prefix_ops initial_fmp lo (input_ops ++ reorder_ops) ps).ps_stack ps2.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  irule rf_preparation_replay >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac
  >- (gvs[generated_plan_state_wf_def] >>
      drule spill_alloc_layout_wf_spilled_separated >> simp[]) >>
  qexistsl_tac [`dfg_build_function fn`, `frame_view fn ra vs`, `inputs`,
    `nl`, `opc`, `ps1`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      Cases_on `is_var_operand at`
      >- metis_tac[] >>
      Cases_on `at` >>
      fs[stackPlanTypesTheory.is_var_operand_def] >>
      simp[NoAsms, Once normalize_operand_def]) >>
  fs[EVERY_MEM] >>
  metis_tac[codegen_normalize_operand_not_dead_marker,
    dead_stack_marker_def, stackPlanTypesTheory.is_label_operand_def]
QED

(* Forwarding use-site audit (C1.3.12).
   Proposed suffix inventory invariant, with entry fixed throughout:
     !at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra s) lo at =
       operand_val entry lo (normalize_operand (dfg_build_function fn) [] at).
   This is separate from rf_value_inv, whose domain is future source uses.

   Initial preparation: rf_entry_preparation_replay checks the inventory
   premise from the frozen normalization hypothesis, and extends it to inputs
   by ownership (non-variables normalize identically).  generated_plan_state_wf
   supplies spill separation.  At the concrete COPY call, inputs are
   compute_operands inst; its wf arity supplies the bound 16, suffix no-label
   supplies input no-labelness, and suffix availability specializes at k=i.
   The block-plan append equation supplies absence of spills/restores in this
   prefix.  These concrete block-to-call specializations remain integration
   work; the checked entry theorem does not assume a new inventory invariant.

   Exact remaining transition obligations against generate_regular_inst_plan:
   - Preparation output ps4: transport the invariant through emit_input_plan
     inventory subset and reorder's value-preserving equivalent-name swaps.
     rf_value_inv supplies equations for the current inputs, not stale slots.
   - COPY success: ps5 = ps4 with stack_pop 3, no outputs.  Source variable
     valuation is unchanged, so the invariant must survive this subset and
     release_dead_spills.  No source/assembly memory agreement is used.
   - ASSIGN [rhs] [x]: ps5 pops one input, ps6 pushes Var x; generated emit
     code is empty.  The prepared physical TOS must become the value of x.
     For every retained at, prove the invariant in update_var x v s, including
     a stale at = Var x.  This special case is not justified by SSA freshness:
     it needs normalized x = normalized rhs (normalize_operand_codegen_assign)
     and the input's common-entry equation.  Other operands use
     operand_val_update_var.  Then transport through popmany, optimistic swap,
     and release_dead_spills, preserving separation and input availability.
   - REVERT: inputs are two operands; terminal replay needs the copied interval
     equality plus input agreement, not a reconstructed fn_frame_inv.

   Dead slots: these three regular branches never invoke clean_stack_plan or
   its marker-producing maps.  Any initial dead_stack_marker normalizes to
   itself and evaluates as the same fixed label in both source views.  Root
   exclusion for searched inputs is codegen_normalize_operand_not_dead_marker;
   no blanket non-label-root claim is needed.  The retained inventory premise
   is sufficient for reorder_one's alias check at final_dist; replacing it by
   a candidate-only premise is not currently necessary, but preservation above
   is still unproved.  This audit is not terminal-integration evidence.
*)

Definition rf_inventory_inv_def:
  rf_inventory_inv fn ra lo entry ps s <=>
    !at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra s) lo at =
      operand_val entry lo (normalize_operand (dfg_build_function fn) [] at)
End

Theorem rf_inventory_inv_entry:
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra s) lo at =
    operand_val (frame_view fn ra s) lo
      (normalize_operand (dfg_build_function fn) [] at)) ==>
  rf_inventory_inv fn ra lo (frame_view fn ra s) ps s
Proof
  simp[rf_inventory_inv_def]
QED

Theorem rf_inventory_inv_transport:
  rf_inventory_inv fn ra lo entry ps s /\
  (!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
  (!at. operand_val (frame_view fn ra s') lo at =
        operand_val (frame_view fn ra s) lo at) ==>
  rf_inventory_inv fn ra lo entry ps' s'
Proof
  simp[rf_inventory_inv_def] >> metis_tac[]
QED

Theorem rf_inventory_inv_index[simp]:
  rf_inventory_inv fn ra lo entry ps (s with vs_inst_idx := k) <=>
  rf_inventory_inv fn ra lo entry ps s
Proof
  simp[rf_inventory_inv_def] >> eq_tac >> rpt strip_tac >>
  first_x_assum (qspec_then `at` mp_tac) >> simp[] >> Cases_on `at` >>
  simp[frame_view_def, codegenRelTheory.operand_val_def,
       venomStateTheory.lookup_var_def]
QED

Theorem rf_inventory_inv_assign:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [x] /\ ~is_label_operand rhs /\
  step_inst fuel ctx inst s = OK s' /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  ps' = ps with ps_stack := stack_push (Var x) (stack_pop 1 ps.ps_stack) ==>
  rf_inventory_inv fn ra lo entry ps' s'
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
  simp[Once step_inst_def, Once step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `normalize_operand (dfg_build_function fn) [] (Var x) =
   normalize_operand (dfg_build_function fn) [] rhs` by
    (irule normalize_operand_codegen_assign >> simp[] >> qexists_tac `inst` >>
     simp[] >> irule dfg_build_function_ssa_def >> simp[] >> metis_tac[]) >>
  `MEM x inst.inst_outputs` by simp[] >>
  `eval_operand rhs (frame_view fn ra s) =
   SOME (if retpc_var fn x then ra else v)` by
    (drule_all assign_eval_frame_view >>
     disch_then (qspecl_then [`ra`, `s.vs_memory`] mp_tac) >>
     Cases_on `rhs` >>
     simp[frame_view_def, venomStateTheory.eval_operand_def,
          venomStateTheory.lookup_var_def]) >>
  simp[rf_inventory_inv_def] >> gen_tac >> disch_tac >>
  Cases_on `at = Var x`
  >- (gvs[frame_view_update_var, operand_val_update_var_eq] >>
      metis_tac[operand_val_eq_eval]) >>
  `MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (gvs[stack_push_def, stack_pop_def, MEM_SNOC] >>
     metis_tac[MEM_TAKE]) >>
  `operand_val (frame_view fn ra s) lo at =
   operand_val entry lo (normalize_operand (dfg_build_function fn) [] at)` by
    metis_tac[rf_inventory_inv_def] >>
  simp[frame_view_update_var] >>
  irule EQ_TRANS >> goal_assum (drule_at Any) >>
  irule operand_val_update_var >> Cases_on `at` >> gvs[]
QED

Theorem rf_inventory_inv_vars_subset:
  rf_inventory_inv fn ra lo entry ps s /\ s'.vs_vars = s.vs_vars /\
  (!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) ==>
  rf_inventory_inv fn ra lo entry ps' s'
Proof
  strip_tac >> irule rf_inventory_inv_transport >>
  qexistsl_tac [`ps`, `s`] >> asm_rewrite_tac[] >>
  Cases >> simp[frame_view_def, codegenRelTheory.operand_val_def,
    venomStateTheory.lookup_var_def]
QED

Theorem rf_reorder_steps_inventory_subset:
  !items ps ops ps' tops dfg.
    EVERY (\(idx,op). idx < LENGTH tops /\ MEM op tops) items /\
    LENGTH tops <= LENGTH ps.ps_stack /\ LENGTH tops <= 16 /\
    plan_steps (\(idx,op) ps. reorder_one dfg tops idx op ps) items ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Induct >> simp[foldlSimTheory.plan_steps_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `reorder_one dfg tops idx op ps = (step_ops,ps1)` >>
  `LENGTH tops <= LENGTH ps1.ps_stack` by
    (qspec_then `dfg` mp_tac reorder_one_wf_len >>
     disch_then (qspecl_then [`tops`, `idx`, `op`, `ps`, `lo`] mp_tac) >>
     simp[]) >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (drule_at (Pat `reorder_one _ _ _ _ _ = _`) reorder_one_inventory_subset >>
     simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!ps ops ps' tops dfg. _` drule >> simp[] >>
  metis_tac[]
QED

Theorem rf_reorder_inventory_subset:
  reorder_plan dfg inputs ps = (ops,ps') /\
  LENGTH inputs <= LENGTH ps.ps_stack /\ LENGTH inputs <= 16 ==>
  !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  strip_tac >>
  match_mp_tac rf_reorder_steps_inventory_subset >>
  qexistsl_tac [`MAPi (\i op. (i,op)) inputs`, `ops`, `inputs`, `dfg`] >>
  simp[GSYM reorder_plan_eq_plan_steps] >>
  simp[EVERY_EL, indexedListsTheory.LENGTH_MAPi, indexedListsTheory.EL_MAPi,
    EL_MEM]
QED

Theorem rf_inventory_inv_preparation:
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. MEM op inputs ==>
    operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  opc <> INVOKE /\ LENGTH inputs <= 16 /\
  emit_input_plan opc inputs nl ps = (input_ops,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (reorder_ops,ps2) ==>
  rf_inventory_inv fn ra lo entry ps2 s
Proof
  strip_tac >>
  `LENGTH inputs <= LENGTH ps1.ps_stack` by
    metis_tac[available_input_plan_length] >>
  `!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
    MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled` by
    (drule_at (Pat `reorder_plan _ _ _ = _`) rf_reorder_inventory_subset >> simp[]) >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at inputs` by
    (drule emit_input_plan_inventory_subset >> simp[]) >>
  fs[rf_inventory_inv_def] >> metis_tac[]
QED

Theorem rf_inventory_inv_release:
  rf_inventory_inv fn ra lo entry ps s ==>
  rf_inventory_inv fn ra lo entry (release_dead_spills nl ps) s
Proof
  `!dead (ps0:plan_state). rf_inventory_inv fn ra lo entry ps0 s ==>
    rf_inventory_inv fn ra lo entry
      (FOLDL (\ps' (op:operand,off:num).
        ps' with <|ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc|>) ps0 dead) s` by
    (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     PairCases_on `h` >> simp[] >> first_x_assum irule >>
     gvs[rf_inventory_inv_def, finite_mapTheory.FDOM_DOMSUB] >> metis_tac[]) >>
  simp[stackPlanOpsTheory.release_dead_spills_def]
QED

Theorem rf_inventory_inv_copy_pop:
  rf_inventory_inv fn ra lo entry ps s /\ s'.vs_vars = s.vs_vars /\
  ps' = release_dead_spills nl (ps with ps_stack := stack_pop n ps.ps_stack) ==>
  rf_inventory_inv fn ra lo entry ps' s'
Proof
  strip_tac >> gvs[] >> irule rf_inventory_inv_release >>
  irule rf_inventory_inv_vars_subset >> qexistsl_tac [`ps`, `s`] >>
  asm_rewrite_tac[] >> simp[stack_pop_def] >> metis_tac[MEM_TAKE]
QED

(* Future source ownership is protected by intra-block liveness. *)
Theorem rf_live_use_liveness:
  !fn bb k j x.
    wf_function fn /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    rf_live_use bb k j (Var x) ==>
    MEM x (live_vars_at (liveness_analyze fn) bb.bb_label k)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[rf_live_use_def, get_instruction_def] >>
  `MEM (Var x) (EL r bb.bb_instructions).inst_operands` by
    (qpat_x_assum `MEM _ (compute_operands _)` mp_tac >>
     simp[compute_operands_def] >>
     rpt (IF_CASES_TAC >> simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER]) >>
     metis_tac[MEM_TL]) >>
  `MEM x (inst_uses (EL r bb.bb_instructions))` by
    metis_tac[operand_var_in_inst_uses] >>
  `MEM x (live_vars_at (liveness_analyze fn) bb.bb_label r)` by
    (irule (SRULE [LET_THM] live_vars_at_uses) >>
     simp[] >> qexists_tac `bb` >> simp[]) >>
  irule (SRULE [LET_THM] live_vars_at_propagate_range) >>
  simp[] >> qexists_tac `r` >> simp[inst_defs_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem rf_copy_plan_result:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan dfg (compute_operands inst) ps1 = (ros,ps2) ==>
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps =
    (ins ++ ros ++ [SOEmit "RETURNDATACOPY"],
     release_dead_spills nl
       (ps2 with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps2.ps_stack))
Proof
  strip_tac >>
  simp[generate_regular_inst_plan_def, venomEffectsTheory.is_commutative_def,
    generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def]
QED

Theorem rf_copy_plan_inventory:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  LENGTH (compute_operands inst) <= 16 /\
  rf_inventory_inv fn ra lo entry ps s /\ s'.vs_vars = s.vs_vars /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') ==>
  rf_inventory_inv fn ra lo entry ps' s'
Proof
  strip_tac >>
  Cases_on `emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps` >>
  rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) ps1` >>
  rename1 `_ = (ros,ps2)` >>
  `rf_inventory_inv fn ra lo entry ps2 s` by
    (drule_at (Pat `reorder_plan _ _ _ = _`) rf_inventory_inv_preparation >>
     simp[] >> disch_then irule >> asm_rewrite_tac[] >>
     qexistsl_tac [`ins`, `nl`, `RETURNDATACOPY`, `ps`] >> simp[]) >>
  drule_all rf_copy_plan_result >> strip_tac >> gvs[] >>
  irule rf_inventory_inv_copy_pop >> metis_tac[]
QED

Theorem rf_emit_live_reserve:
  !inputs opc nl ps iops ps1 x.
    MEM x nl /\
    (MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    emit_input_plan opc inputs nl ps = (iops,ps1) ==>
    LIST_ELEM_COUNT (Var x) ps.ps_stack +
      (if Var x IN FDOM ps.ps_spilled then 1 else 0) +
      LIST_ELEM_COUNT (Var x) inputs <=
    LIST_ELEM_COUNT (Var x) ps1.ps_stack +
      (if Var x IN FDOM ps1.ps_spilled then 1 else 0)
Proof
  Induct >- simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  Cases_on `emit_one_input opc (operand_vars inputs ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,ps_mid)` >>
  Cases_on `emit_input_plan opc inputs nl ps_mid` >>
  gnvs[emit_input_plan_cons] >>
  qspecl_then [`opc`, `operand_vars inputs ++ nl`, `h`, `ps`, `Var x`]
    mp_tac emit_one_input_inventory_mono_aux >> simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  disch_then (qspec_then `x` mp_tac) >> asm_rewrite_tac[] >>
  (impl_tac >-
    (Cases_on `Var x IN FDOM ps.ps_spilled` >>
     Cases_on `Var x IN FDOM ps_mid.ps_spilled` >>
     gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac)) >> strip_tac >>
  Cases_on `h = Var x`
  >- (gvs[LIST_ELEM_COUNT_THM] >>
      qspecl_then [`opc`, `operand_vars inputs ++ nl`, `Var x`, `ps`]
        mp_tac emit_one_input_inventory_inc >> simp[] >>
      Cases_on `Var x IN FDOM ps.ps_spilled` >>
      Cases_on `Var x IN FDOM ps_mid.ps_spilled` >>
      Cases_on `Var x IN FDOM ps1.ps_spilled` >> gvs[] >> decide_tac) >>
  gvs[LIST_ELEM_COUNT_THM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >>
  Cases_on `Var x IN FDOM ps_mid.ps_spilled` >>
  Cases_on `Var x IN FDOM ps1.ps_spilled` >> gvs[] >> decide_tac
QED

Theorem rf_reduce_spill_free[local]:
  !fuel pending op f n ps ops ps'.
    reduce_depth_plan fuel pending op f n ps = (ops,ps') /\
    (!off. ~MEM (SOSpill off) ops) ==> ps' = ps /\ ops = []
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  Cases_on `dist <= 16` >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending dist n` >> simp[] >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  Cases_on `do_spill_at cand ps` >> rename1 `do_spill_at _ _ = (sops,ps_mid)` >>
  Cases_on `reduce_depth_plan fuel pending op f n ps_mid` >>
  simp[MEM_APPEND] >> strip_tac >>
  qpat_x_assum `do_spill_at _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [do_spill_at_def, do_spill_tos_def]) >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  Cases_on `cand = 0` >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem rf_reorder_one_spill_free[local]:
  !dfg pending idx op ps ops ps' d.
    idx < LENGTH pending /\ LENGTH pending <= LENGTH ps.ps_stack /\
    stack_get_unfixed_depth op (LENGTH pending - 1 - idx)
      (LENGTH pending) ps.ps_stack = SOME d /\
    reorder_one dfg pending idx op ps = (ops,ps') /\
    (!off. ~MEM (SOSpill off) ops) ==>
    ps'.ps_spilled = ps.ps_spilled /\
    (!x. LIST_ELEM_COUNT x ps'.ps_stack = LIST_ELEM_COUNT x ps.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH pending - 1 - idx = LENGTH pending - (idx + 1)` by decide_tac >>
  gvs[] >>
  `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `ps2 = ps /\ reduce_ops = []` by
    (Cases_on `d > 16` >> fs[] >>
     irule rf_reduce_spill_free >>
     reverse conj_tac >- (goal_assum (drule_at Any)) >>
     rpt strip_tac >>
     qpat_x_assum `!off. ~MEM _ ops` (qspec_then `off` mp_tac) >>
     RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)) >>
     fs[AllCaseEqs(), MEM_APPEND] >> gvs[]) >>
  gvs[] >>
  `LENGTH pending - (idx + 1) < LENGTH ps.ps_stack` by decide_tac >>
  qspecl_then [`dfg`, `stack_peek d ps.ps_stack`, `d`,
    `LENGTH pending - (idx + 1)`, `ps`]
    mp_tac reorder_place_phase_multiplicity >> simp[] >>
  Cases_on `d = LENGTH pending - (idx + 1)` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek d ps.ps_stack)
    (stack_peek (LENGTH pending - (idx + 1)) ps.ps_stack)` >> gvs[] >>
  Cases_on `do_swap d ps` >>
  rename1 `do_swap d ps = (s1,ps1)` >>
  Cases_on `do_swap (LENGTH pending - (idx + 1)) ps1` >> gvs[] >>
  metis_tac[do_swap_spilled_unchanged, pairTheory.SND]
QED

Theorem rf_reorder_steps_spill_free[local]:
  !items k dfg pending ps ops ps'.
    k + LENGTH items = LENGTH pending /\
    (!j. j < LENGTH items ==>
      EL j items = (k + j, EL (k + j) pending)) /\
    LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    (!i. i < k ==>
      stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps)
      items ps = (ops,ps') /\
    (!off. ~MEM (SOSpill off) ops) ==>
    ps'.ps_spilled = ps.ps_spilled /\
    (!x. LIST_ELEM_COUNT x ps'.ps_stack = LIST_ELEM_COUNT x ps.ps_stack)
Proof
  Induct
  >- (simp[foldlSimTheory.plan_steps_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `h = (k, EL k pending)` by
    (qpat_x_assum `!j. j < LENGTH (h::items) ==> _`
       (qspec_then `0` mp_tac) >> simp[]) >>
  `k < LENGTH pending` by (fs[] >> decide_tac) >>
  drule plan_steps_cons_result >> strip_tac >>
  qpat_x_assum `h = _` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)) >>
  rename1 `reorder_one dfg pending k (EL k pending) ps = (step_ops,ps1)` >>
  `?d. stack_get_unfixed_depth (EL k pending)
    (LENGTH pending - 1 - k) (LENGTH pending) ps.ps_stack = SOME d` by
    metis_tac[materialised_pending_next_on_stack_window] >>
  `ps1.ps_spilled = ps.ps_spilled /\
   (!x. LIST_ELEM_COUNT x ps1.ps_stack = LIST_ELEM_COUNT x ps.ps_stack)` by
    (irule rf_reorder_one_spill_free >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM_APPEND]) >>
  `LENGTH pending <= LENGTH ps1.ps_stack` by
    metis_tac[reorder_one_materialised_length_floor] >>
  `!i. i < SUC k ==>
    stack_peek (LENGTH pending - 1 - i) ps1.ps_stack = EL i pending` by
    (drule_at (Pat `reorder_one _ _ _ _ _ = _`)
       reorder_one_advances_fixed_window >> simp[]) >>
  qpat_x_assum `!k dfg pending ps ops ps'. _`
    (qspec_then `SUC k` mp_tac) >>
  disch_then (qspecl_then [`dfg`, `pending`, `ps1`, `rest_ops`, `ps'`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (fs[] >> decide_tac) >>
      conj_tac
      >- (gen_tac >> strip_tac >>
          qpat_x_assum `!j. j < LENGTH (_::items) ==> _`
            (qspec_then `SUC j` mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]) >>
      metis_tac[MEM_APPEND]) >>
  metis_tac[]
QED

Theorem rf_reorder_spill_free:
  !dfg pending ps ops ps'.
    LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack /\
    (!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x ps.ps_stack) /\
    reorder_plan dfg pending ps = (ops,ps') /\
    (!off. ~MEM (SOSpill off) ops) ==>
    ps'.ps_spilled = ps.ps_spilled /\
    (!x. LIST_ELEM_COUNT x ps'.ps_stack = LIST_ELEM_COUNT x ps.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`MAPi (\i op. (i,op)) pending`, `0`]
    mp_tac rf_reorder_steps_spill_free >>
  disch_then (qspecl_then [`dfg`, `pending`, `ps`, `ops`, `ps'`] mp_tac) >>
  simp[reorder_plan_eq_plan_steps, indexedListsTheory.LENGTH_MAPi,
       indexedListsTheory.EL_MAPi] >>
  metis_tac[reorder_plan_eq_plan_steps]
QED

Theorem rf_release_live_owned:
  !nl x ps.
    MEM x nl /\ (MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) ==>
    MEM (Var x) (release_dead_spills nl ps).ps_stack \/
    Var x IN FDOM (release_dead_spills nl ps).ps_spilled
Proof
  rpt gen_tac >>
  `!dead (ps0:plan_state).
    EVERY (\p:operand # num. FST p <> Var x) dead /\
    (MEM (Var x) ps0.ps_stack \/ Var x IN FDOM ps0.ps_spilled) ==>
    MEM (Var x)
      (FOLDL (\ps' (op:operand,off:num).
        ps' with <|ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc|>) ps0 dead).ps_stack \/
    Var x IN FDOM
      (FOLDL (\ps' (op:operand,off:num).
        ps' with <|ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc|>) ps0 dead).ps_spilled` by
    (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     PairCases_on `h` >> first_x_assum irule >>
     gvs[finite_mapTheory.FDOM_DOMSUB]) >>
  strip_tac >> simp[release_dead_spills_def] >> first_x_assum irule >>
  simp[EVERY_MEM, MEM_FILTER] >> Cases >> simp[] >>
  rpt strip_tac >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem rf_preparation_arranged:
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  LENGTH inputs <= 16 /\
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) ==>
  ps2.ps_stack = stack_pop (LENGTH inputs) ps2.ps_stack ++ inputs
Proof
  strip_tac >>
  `!at. LIST_ELEM_COUNT at inputs <= LIST_ELEM_COUNT at ps1.ps_stack` by
    (drule_all emit_input_plan_materialised >> simp[]) >>
  `LENGTH inputs <= LENGTH ps1.ps_stack` by
    (irule list_elem_count_dom_length >> simp[]) >>
  `!at. MEM at inputs ==>
     LIST_ELEM_COUNT at inputs <= LIST_ELEM_COUNT at ps1.ps_stack` by simp[] >>
  match_mp_tac fixed_suffix_decompose >> conj_tac
  >- (drule_all reorder_plan_materialised_length_floor >> simp[]) >>
  drule_at (Pat `reorder_plan _ _ _ = _`)
    reorder_plan_materialised_order >> simp[]
QED

Theorem rf_preparation_live_owned_before_release:
  !nl x ps opc inputs iops ps1 dfg rops ps2.
    MEM x nl /\
    (MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    LENGTH inputs <= 16 /\
    emit_input_plan opc inputs nl ps = (iops,ps1) /\
    reorder_plan dfg inputs ps1 = (rops,ps2) /\
    (!off. ~MEM (SOSpill off) (iops ++ rops) /\
            ~MEM (SORestore off) (iops ++ rops)) ==>
    MEM (Var x) (stack_pop (LENGTH inputs) ps2.ps_stack) \/
    Var x IN FDOM ps2.ps_spilled
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `!at. LIST_ELEM_COUNT at inputs <= LIST_ELEM_COUNT at ps1.ps_stack` by
    (drule_all emit_input_plan_materialised >> simp[]) >>
  `LENGTH inputs <= LENGTH ps1.ps_stack` by
    (irule list_elem_count_dom_length >> simp[]) >>
  `ps2.ps_spilled = ps1.ps_spilled /\
   (!at. LIST_ELEM_COUNT at ps2.ps_stack = LIST_ELEM_COUNT at ps1.ps_stack)` by
    (drule_at (Pat `reorder_plan _ _ _ = _`) rf_reorder_spill_free >>
     impl_tac >- (fs[MEM_APPEND]) >> simp[]) >>
  `ps2.ps_stack = stack_pop (LENGTH inputs) ps2.ps_stack ++ inputs` by
    (drule_all rf_preparation_arranged >> simp[]) >>
  drule_all rf_emit_live_reserve >> strip_tac >>
  Cases_on `Var x IN FDOM ps2.ps_spilled` >> simp[] >>
  `0 < LIST_ELEM_COUNT (Var x) ps.ps_stack +
       (if Var x IN FDOM ps.ps_spilled then 1 else 0)` by
    (Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[] >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  `LIST_ELEM_COUNT (Var x) ps1.ps_stack =
    LIST_ELEM_COUNT (Var x) (stack_pop (LENGTH inputs) ps2.ps_stack) +
    LIST_ELEM_COUNT (Var x) inputs` by
    metis_tac[elem_count_append] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem rf_preparation_live_retained:
  !nl x ps opc inputs iops ps1 dfg rops ps2.
    MEM x nl /\
    (MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    LENGTH inputs <= 16 /\
    emit_input_plan opc inputs nl ps = (iops,ps1) /\
    reorder_plan dfg inputs ps1 = (rops,ps2) /\
    (!off. ~MEM (SOSpill off) (iops ++ rops) /\
            ~MEM (SORestore off) (iops ++ rops)) ==>
    MEM (Var x)
      (release_dead_spills nl
        (ps2 with ps_stack := stack_pop (LENGTH inputs) ps2.ps_stack)).ps_stack \/
    Var x IN FDOM
      (release_dead_spills nl
        (ps2 with ps_stack := stack_pop (LENGTH inputs) ps2.ps_stack)).ps_spilled
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule rf_release_live_owned >> simp[] >>
  drule_at (Pat `emit_input_plan _ _ _ _ = _`)
    rf_preparation_live_owned_before_release >>
  disch_then (qspecl_then [`x`, `dfg`, `rops`, `ps2`] mp_tac) >> simp[]
QED

(* Physical preparation above arbitrary caller stack; no memory relation. *)
Theorem rf_preparation_stack_frame:
  EVERY is_simple_stack_op ops /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  plan_stack_sem_eq lo current
    (apply_prefix_ops initial_fmp lo ops ps).ps_stack ps2.ps_stack /\
  plan_stack_rel lo current ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK (st with <|as_stack := stk' ++ rest;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp ops)|>) /\
    plan_stack_rel lo current ps2.ps_stack stk'
Proof
  strip_tac >>
  drule_all simple_prefix_stack_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `stk'` >> asm_rewrite_tac[] >>
  irule plan_stack_rel_sem_eq >>
  qexists_tac `(apply_simple_ops lo ops ps).ps_stack` >>
  metis_tac[apply_prefix_ops_eq_simple]
QED

Theorem rf_copy_plan_live_retained:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  LENGTH (compute_operands inst) <= 16 /\ MEM x nl /\
  (MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  MEM (Var x) ps'.ps_stack \/ Var x IN FDOM ps'.ps_spilled
Proof
  strip_tac >>
  Cases_on `emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps` >>
  rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan dfg (compute_operands inst) ps1` >>
  rename1 `_ = (ros,ps2)` >>
  drule_all rf_copy_plan_result >> strip_tac >> gvs[] >>
  irule rf_preparation_live_retained >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`dfg`, `ins`, `RETURNDATACOPY`, `ps`, `ps1`, `ros`] >>
  fs[MEM_APPEND]
QED

Theorem rf_simple_do_swap_shallow[local]:
  do_swap d ps = (ops,ps') /\ EVERY is_simple_stack_op ops ==> d <= 16
Proof
  strip_tac >> spose_not_then assume_tac >>
  qpat_x_assum `do_swap _ _ = _` mp_tac >>
  simp[do_swap_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  fs[EVERY_APPEND, EVERY_MAP, EVERY_MEM, is_simple_stack_op_def] >>
  metis_tac[MEM_APPEND, MEM_REVERSE, MEM]
QED

Theorem rf_optimistic_stack_frame:
  optimistic_swap_plan dfg inst nl term ps = (ops,ps') /\
  EVERY is_simple_stack_op ops /\
  plan_stack_rel lo current ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK (st with <|as_stack := stk' ++ rest;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp ops)|>) /\
    plan_stack_rel lo current ps'.ps_stack stk'
Proof
  strip_tac >>
  qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >> simp[] >>
  strip_tac >> gvs[] >>
  TRY (qexists_tac `stk` >>
       simp[execute_plan_def, asm_steps_def, asm_state_component_equality] >> NO_TAC) >>
  `x <= 16` by metis_tac[rf_simple_do_swap_shallow] >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  `apply_prefix_ops initial_fmp lo ops ps = ps'` by
    metis_tac[do_swap_align] >>
  `prefix_wf lo (LENGTH ps.ps_stack) ops` by
    (qpat_x_assum `do_swap _ _ = _` mp_tac >>
     Cases_on `x = 0` >> simp[do_swap_def] >> strip_tac >> gvs[] >>
     simp[prefix_wf_def, stack_op_wf_def]) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule rf_preparation_stack_frame >>
  asm_rewrite_tac[] >> qexistsl_tac [`ps`, `stk`] >>
  simp[plan_stack_sem_eq_refl]
QED

Theorem rf_release_stack[simp]:
  (release_dead_spills nl ps).ps_stack = ps.ps_stack
Proof
  `!dead (ps0:plan_state).
    (FOLDL (\ps' (op:operand,off:num).
       ps' with <|ps_spilled := ps'.ps_spilled \\ op;
                  ps_alloc := free_spill_slot off ps'.ps_alloc|>) ps0 dead).ps_stack =
    ps0.ps_stack` by
    (Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[]) >>
  simp[release_dead_spills_def]
QED

Theorem rf_assign_postfix_stack_frame:
  ps.ps_stack = stack_push (Var out) tail /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  EVERY is_simple_stack_op (pops ++ opts) /\
  plan_stack_rel lo current ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (pops ++ opts)) ==>
  ?stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (pops ++ opts))) st =
      AsmOK (st with <|as_stack := stk' ++ rest;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp (pops ++ opts))|>) /\
    plan_stack_rel lo current (release_dead_spills nl ps9).ps_stack stk'
Proof
  strip_tac >> Cases_on `MEM out nl`
  >- (`pops = [] /\ ps8 = ps` by
        (Cases_on `halting` >> gvs[popmany_plan_def]) >>
      gvs[] >>
      `plan_stack_rel lo current ps.ps_stack stk` by simp[] >>
      drule_all rf_optimistic_stack_frame >>
      disch_then (qspec_then `o2pc` mp_tac) >> simp[]) >>
  gvs[] >> Cases_on `halting`
  >- (gvs[] >> qexists_tac `stk` >>
      simp[execute_plan_def, asm_steps_def, asm_state_component_equality]) >>
  `stack_get_depth (Var out) ps.ps_stack = SOME 0` by
    simp[stack_push_def, REVERSE_SNOC, stack_get_depth_def, stack_find_def] >>
  `popmany_plan [Var out] ps =
     ([SOPop 1],ps with ps_stack := stack_pop 1 ps.ps_stack)` by
    metis_tac[regularPostfixSimTheory.popmany_plan_top_singleton] >>
  gvs[] >>
  `prefix_wf lo (LENGTH ps.ps_stack) [SOPop 1]` by
    simp[prefix_wf_def, stack_op_wf_def, stack_push_def] >>
  `plan_stack_rel lo current ps.ps_stack stk` by simp[] >>
  `EVERY is_simple_stack_op [SOPop 1]` by simp[] >>
  drule_all simple_prefix_stack_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `stk'` >>
  gvs[apply_simple_ops_def, apply_simple_op_def, stack_pop_def, stack_push_def]
QED

Theorem rf_copy_future_owned:
  wf_function fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  get_instruction bb k = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  k <= j /\
  generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
    halting term bb.bb_label ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  !op. rf_live_use bb (SUC k) j op /\ is_var_operand op ==>
    MEM op ps'.ps_stack \/ op IN FDOM ps'.ps_spilled
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `op` >> gvs[stackPlanTypesTheory.is_var_operand_def] >>
  rename1 `rf_live_use bb (SUC k) j (Var x)` >>
  `MEM x (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))` by
    metis_tac[rf_live_use_liveness] >>
  `rf_live_use bb k j (Var x)` by
    (irule rf_live_use_backward >> simp[] >> metis_tac[MEM]) >>
  `!at. MEM at (compute_operands inst) /\ is_var_operand at ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule rf_live_use_current >> metis_tac[]) >>
  `MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled` by
    metis_tac[stackPlanTypesTheory.is_var_operand_def] >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    rf_copy_plan_live_retained >> simp[]
QED

Theorem rf_copy_stack_frame:
  plan_stack_rel lo current (tail ++ [zop;sop;dop]) stk /\
  dop <> dead_stack_marker /\ sop <> dead_stack_marker /\ zop <> dead_stack_marker /\
  operand_val current lo dop = SOME dst /\
  operand_val current lo sop = SOME src /\
  operand_val current lo zop = SOME sz /\
  st.as_stack = stk ++ rest /\
  w2n src + w2n sz <= LENGTH st.as_returndata /\
  asm_block_at prog st.as_pc [AsmOp "RETURNDATACOPY"] ==>
  ?stk'.
    asm_steps lo o2pc prog 1 st =
      AsmOK (st with <|as_stack := stk' ++ rest; as_pc := st.as_pc + 1;
        as_memory :=
          TAKE (w2n dst)
            (if sz = 0w then st.as_memory
             else asm_expand_memory (w2n dst + w2n sz) st.as_memory) ++
          TAKE (w2n sz) (DROP (w2n src) st.as_returndata) ++
          DROP (w2n dst + w2n sz)
            (if sz = 0w then st.as_memory
             else asm_expand_memory (w2n dst + w2n sz) st.as_memory)|>) /\
    plan_stack_rel lo current tail stk'
Proof
  strip_tac >>
  `?d s z residual. stk = d :: s :: z :: residual /\
    operand_val current lo dop = SOME d /\
    operand_val current lo sop = SOME s /\
    operand_val current lo zop = SOME z` by
    (irule asm_stack_top3_from_plan >> simp[] >>
     qexists_tac `tail` >> simp[]) >>
  gvs[] >> qexists_tac `residual` >> conj_tac
  >- (once_rewrite_tac[DECIDE ``1 = SUC 0``] >>
      simp[Once asm_steps_def] >>
      gvs[asm_block_at_def, asm_step_def, asm_step_op_def,
        asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
        asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
        asm_step_copy_def, asm_returndatacopy_def, asm_next_def,
        asm_steps_def, asm_state_component_equality]) >>
  drule plan_stack_rel_pop >>
  disch_then (qspec_then `3` mp_tac) >> simp[TAKE_APPEND]
QED

Theorem rf_assign_stack_transfer:
  ps.ps_stack = tail ++ [rhs] /\ rhs <> dead_stack_marker /\
  ps' = ps with ps_stack := stack_push (Var x) tail /\
  rf_inventory_inv fn ra lo entry ps s /\
  rf_inventory_inv fn ra lo entry ps' s' /\
  normalize_operand (dfg_build_function fn) [] (Var x) =
    normalize_operand (dfg_build_function fn) [] rhs /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk ==>
  plan_stack_rel lo (frame_view fn ra s') ps'.ps_stack stk
Proof
  strip_tac >> gvs[] >>
  `?v residual. stk = v :: residual /\
    operand_val (frame_view fn ra s) lo rhs = SOME v` by
    (irule asm_stack_top1_from_plan >> simp[] >> qexists_tac `tail` >> simp[]) >>
  gvs[] >>
  `plan_stack_rel lo (frame_view fn ra s) tail residual` by
    (drule plan_stack_rel_pop >> disch_then (qspec_then `1` mp_tac) >>
     simp[TAKE_APPEND]) >>
  `operand_val (frame_view fn ra s') lo (Var x) = SOME v` by
    (gvs[rf_inventory_inv_def, stack_push_def, MEM_SNOC, MEM_APPEND] >>
     metis_tac[]) >>
  simp[stack_push_def] >> irule plan_stack_rel_push >> simp[] >>
  gvs[plan_stack_rel_def] >> rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH tail ==> _` (qspec_then `i` mp_tac) >>
  strip_tac >> simp[] >>
  `MEM (EL i (REVERSE tail)) tail` by
    (pure_once_rewrite_tac[GSYM MEM_REVERSE] >>
     pure_rewrite_tac[MEM_EL] >> qexists_tac `i` >> simp[]) >>
  gvs[rf_inventory_inv_def, stack_push_def, MEM_SNOC, MEM_APPEND] >>
  metis_tac[]
QED

(* Disconnected forwarding fixture: distinct SSA copies satisfy single use. *)
Definition rf_probe_bb_def:
  rf_probe_bb = <|bb_label := "dead"; bb_instructions :=
    [mk_inst 1 ASSIGN [Lit 32w] ["p"];
     mk_inst 2 ASSIGN [Lit 32w] ["q"];
     mk_inst 3 RETURNDATACOPY [Var "p"; Lit 0w; Lit 1w] [];
     mk_inst 4 REVERT [Var "q"; Lit 1w] []]|>
End
Definition rf_probe_fn_def:
  rf_probe_fn = mk_raw_function "probe"
    [<|bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []]|>;
     rf_probe_bb]
End
Definition rf_probe_ps_def:
  rf_probe_ps = (init_plan_state 0) with ps_stack := [Var "q"; Var "p"]
End
Theorem rf_probe_pair:
  revert_forward_pair rf_probe_bb 2 3
Proof
  simp[revert_forward_pair_def, rf_probe_bb_def, get_instruction_def,
       mk_inst_def] >>
  simp[resolve_block_assigns_def, same_after_assigns_def,
       step_back_assign_def]
QED
Theorem rf_probe_word_ne[local]:
  (0w : 256 word) <> 1w
Proof
  wordsLib.WORD_DECIDE_TAC
QED
val _ = computeLib.add_funs
  [normalize_operand_def, rf_probe_word_ne, listTheory.SET_TO_LIST_EMPTY];

Theorem rf_probe_plan:
  generate_block_insts_plan (liveness_analyze rf_probe_fn)
    (dfg_build_function rf_probe_fn) (cfg_analyze rf_probe_fn)
    rf_probe_fn "dead" T 0 4 2
    (DROP 2 rf_probe_bb.bb_instructions) rf_probe_ps =
    SOME ([SOPush (Lit 1w); SOPush (Lit 0w); SOSwap 1; SOSwap 2;
           SOEmit "RETURNDATACOPY"; SOPush (Lit 1w); SOSwap 1; SOEmit "REVERT"],
          (init_plan_state 0))
Proof
  EVAL_TAC
QED

Definition rf_probe_assign_bb_def:
  rf_probe_assign_bb = <|bb_label := "dead"; bb_instructions :=
    [mk_inst 1 ASSIGN [Lit 32w] ["p"];
     mk_inst 2 RETURNDATACOPY [Var "p"; Lit 0w; Lit 1w] [];
     mk_inst 3 ASSIGN [Var "p"] ["q"];
     mk_inst 4 REVERT [Var "q"; Lit 1w] []]|>
End
Definition rf_probe_assign_fn_def:
  rf_probe_assign_fn = mk_raw_function "probe"
    [<|bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []]|>;
     rf_probe_assign_bb]
End
Definition rf_probe_assign_ps_def:
  rf_probe_assign_ps = (init_plan_state 0) with ps_stack := [Var "p"]
End
Theorem rf_probe_assign_plan:
  generate_block_insts_plan (liveness_analyze rf_probe_assign_fn)
    (dfg_build_function rf_probe_assign_fn) (cfg_analyze rf_probe_assign_fn)
    rf_probe_assign_fn "dead" T 0 4 1
    (DROP 1 rf_probe_assign_bb.bb_instructions) rf_probe_assign_ps =
    SOME ([SOPush (Lit 1w); SOPush (Lit 0w); SOSwap 1; SOSwap 2;
           SOEmit "RETURNDATACOPY"; SOPush (Lit 1w); SOSwap 1; SOEmit "REVERT"],
          init_plan_state 0)
Proof
  EVAL_TAC
QED
(* The only failed readiness clause is dominance: it includes reachability. *)
Theorem rf_probe_assign_readiness_audit:
  [canonical_param_prefix rf_probe_assign_fn;
   wf_function rf_probe_assign_fn; fn_inst_wf rf_probe_assign_fn;
   ssa_form rf_probe_assign_fn; def_dominates_uses rf_probe_assign_fn;
   single_use_form rf_probe_assign_fn;
   cfg_is_normalized (cfg_analyze rf_probe_assign_fn) rf_probe_assign_fn;
   block_entries_ready (cfg_analyze rf_probe_assign_fn) rf_probe_assign_fn;
   phi_operands_ready rf_probe_assign_fn;
   EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions)
     rf_probe_assign_fn.fn_blocks] = [T; T; T; T; F; T; T; T; T; T]
Proof
  EVAL_TAC
QED

Theorem rf_probe_assign_pair:
  revert_forward_pair rf_probe_assign_bb 1 3
Proof
  simp[revert_forward_pair_def, rf_probe_assign_bb_def, get_instruction_def,
       mk_inst_def] >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    `k = 2` by decide_tac >> gvs[]) >>
  simp[resolve_block_assigns_def, same_after_assigns_def,
       step_back_assign_def]
QED
Theorem rf_probe_assign_liveness:
  ~MEM "dead" (cfg_analyze rf_probe_assign_fn).cfg_dfs_pre /\
  live_vars_at (liveness_analyze rf_probe_assign_fn) "dead" 2 = [] /\
  live_vars_at (liveness_analyze rf_probe_assign_fn) "dead" 3 = []
Proof
  EVAL_TAC
QED

Theorem rf_probe_assign_excluded:
  ~codegen_ready_fn rf_probe_assign_fn
Proof
  EVAL_TAC
QED

(* Readiness itself excludes ordinary variable uses in disconnected blocks. *)
Theorem ready_ordinary_use_reachable:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI /\
  MEM (Var x) inst.inst_operands ==>
  fn_reachable fn bb.bb_label
Proof
  strip_tac >> fs[codegen_ready_fn_def, def_dominates_uses_def] >>
  `def_available_at fn bb (SOME inst) x` by metis_tac[] >>
  gvs[def_available_at_def, fn_dominates_def]
QED

Theorem rf_live_use_ready_liveness:
  codegen_ready_fn fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!r inst. k <= r /\ r <= j /\ get_instruction bb r = SOME inst ==>
     inst.inst_opcode <> PHI) /\
  rf_live_use bb k j (Var x) ==>
  MEM x (live_vars_at (liveness_analyze fn) bb.bb_label k)
Proof
  strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  `MEM bb fn.fn_blocks` by
    metis_tac[lookup_block_MEM] >>
  `fn_reachable fn bb.bb_label` by
    (qpat_x_assum `rf_live_use _ _ _ _` mp_tac >>
     simp[rf_live_use_def] >> strip_tac >>
     irule ready_ordinary_use_reachable >>
     simp[] >> qexistsl_tac [`inst`, `x`] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (gvs[get_instruction_def] >> metis_tac[EL_MEM]) >>
     qpat_x_assum `MEM _ (compute_operands _)` mp_tac >>
     simp[compute_operands_def] >>
     rpt (IF_CASES_TAC >> simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER]) >>
     metis_tac[MEM_TL]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  metis_tac[rf_live_use_liveness]
QED

Theorem rf_copy_ready_future_owned:
  codegen_ready_fn fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
     ti.inst_opcode <> PHI) /\
  get_instruction bb k = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  k <= j /\
  generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
    halting term bb.bb_label ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  !op. rf_live_use bb (SUC k) j op /\ is_var_operand op ==>
    MEM op ps'.ps_stack \/ op IN FDOM ps'.ps_spilled
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `op` >> gvs[stackPlanTypesTheory.is_var_operand_def] >>
  rename1 `rf_live_use bb (SUC k) j (Var x)` >>
  `MEM x (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))` by
    (irule rf_live_use_ready_liveness >> simp[] >> qexists_tac `j` >> metis_tac[]) >>
  `rf_live_use bb k j (Var x)` by
    (irule rf_live_use_backward >> simp[] >> metis_tac[MEM]) >>
  `!at. MEM at (compute_operands inst) /\ is_var_operand at ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule rf_live_use_current >> metis_tac[]) >>
  `MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled` by
    metis_tac[stackPlanTypesTheory.is_var_operand_def] >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    rf_copy_plan_live_retained >> simp[]
QED

Theorem rf_optimistic_owned:
  optimistic_swap_plan dfg inst nl term ps = (ops,ps') /\
  EVERY is_simple_stack_op ops /\
  (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) ==>
  MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled
Proof
  strip_tac >>
  qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >> simp[] >>
  strip_tac >> gvs[] >>
  `x <= 16` by metis_tac[rf_simple_do_swap_shallow] >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  `PERM ps'.ps_stack ps.ps_stack` by
    (drule doSwapSimTheory.do_swap_stack_perm >> simp[]) >>
  `ps'.ps_spilled = ps.ps_spilled` by
    (qpat_x_assum `do_swap _ _ = _` mp_tac >>
     Cases_on `x = 0` >> simp[do_swap_def] >> strip_tac >> gvs[]) >>
  metis_tac[sortingTheory.PERM_MEM_EQ]
QED

Theorem rf_assign_postfix_live_owned:
  ps.ps_stack = stack_push (Var out) tail /\ MEM x nl /\
  (MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  EVERY is_simple_stack_op (pops ++ opts) ==>
  MEM (Var x) (release_dead_spills nl ps9).ps_stack \/
  Var x IN FDOM (release_dead_spills nl ps9).ps_spilled
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule rf_release_live_owned >> simp[] >>
  Cases_on `MEM out nl`
  >- (`pops = [] /\ ps8 = ps` by
        (Cases_on `halting` >> gvs[popmany_plan_def]) >>
      gvs[] >>
      `MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled` by simp[] >>
      drule rf_optimistic_owned >> simp[] >>
      disch_then (qspec_then `Var x` mp_tac) >> simp[]) >>
  gvs[] >> Cases_on `halting` >- gvs[] >>
  `stack_get_depth (Var out) ps.ps_stack = SOME 0` by
    simp[stack_push_def, REVERSE_SNOC, stack_get_depth_def, stack_find_def] >>
  `popmany_plan [Var out] ps =
    ([SOPop 1],ps with ps_stack := stack_pop 1 ps.ps_stack)` by
    metis_tac[regularPostfixSimTheory.popmany_plan_top_singleton] >>
  gvs[stack_pop_def, stack_push_def, SNOC_APPEND, TAKE_APPEND]
QED

Theorem rf_assign_plan_result:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\
  emit_input_plan ASSIGN [rhs] nl ps = (ins,ps1) /\
  reorder_plan dfg [rhs] ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,ps') ==>
  ?pops ps8 opts ps9.
    (if halting then ([],ps2 with ps_stack :=
       stack_push (Var out) (stack_pop 1 ps2.ps_stack))
     else popmany_plan (if MEM out nl then [] else [Var out])
       (ps2 with ps_stack := stack_push (Var out) (stack_pop 1 ps2.ps_stack))) =
       (pops,ps8) /\
    (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
     else ([],ps8)) = (opts,ps9) /\
    ops = ins ++ ros ++ pops ++ opts /\ ps' = release_dead_spills nl ps9
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       python_stack_operands_def, generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  Cases_on `halting` >> Cases_on `MEM out nl` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED


Theorem rf_assign_plan_live_retained:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ MEM x nl /\
  (x = out \/ MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  MEM (Var x) ps'.ps_stack \/ Var x IN FDOM ps'.ps_spilled
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `emit_input_plan ASSIGN [rhs] nl ps` >> rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan dfg [rhs] ps1` >> rename1 `_ = (ros,ps2)` >>
  drule_all rf_assign_plan_result >> strip_tac >> gnvs[Excl "rf_release_stack"] >>
  qabbrev_tac `pushed = ps2 with ps_stack :=
    stack_push (Var out) (stack_pop 1 ps2.ps_stack)` >>
  `MEM (Var x) pushed.ps_stack \/ Var x IN FDOM pushed.ps_spilled` by
    (Cases_on `x = out` >- simp[Abbr `pushed`, stack_push_def] >>
     `MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled` by metis_tac[] >>
     drule_at (Pat `emit_input_plan _ _ _ _ = _`)
       rf_preparation_live_owned_before_release >>
     disch_then (qspecl_then [`x`, `dfg`, `ros`, `ps2`] mp_tac) >>
     simp[MEM_APPEND, Abbr `pushed`, stack_push_def]) >>
  `EVERY is_simple_stack_op (pops ++ opts)` by
    (irule simple_or_spill_no_spills >> simp[MEM_APPEND] >>
     simp[EVERY_APPEND] >> conj_tac
     >- (Cases_on `halting` >> gvs[] >>
         drule popmany_plan_enclosed >> simp[]) >>
     Cases_on `MEM out nl` >> gvs[] >>
     drule optimistic_swap_plan_enclosed >> simp[]) >>
  `pushed.ps_stack = stack_push (Var out) (stack_pop 1 ps2.ps_stack)` by
    simp[Abbr `pushed`] >>
  drule_at (Pat `_.ps_stack = stack_push _ _`) rf_assign_postfix_live_owned >>
  disch_then drule >> simp[] >>
  disch_then (drule_at (Pat `(if _ then ([],_) else popmany_plan _ _) = _`)) >>
  disch_then (drule_at (Pat `(if _ then optimistic_swap_plan _ _ _ _ _ else _) = _`)) >>
  simp[GSYM EVERY_APPEND]
QED

Theorem rf_assign_ready_future_owned:
  codegen_ready_fn fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
     ti.inst_opcode <> PHI) /\
  get_instruction bb k = SOME inst /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  k <= j /\
  generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
    halting term bb.bb_label ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  !op. rf_live_use bb (SUC k) j op /\ is_var_operand op ==>
    MEM op ps'.ps_stack \/ op IN FDOM ps'.ps_spilled
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `op` >> gvs[stackPlanTypesTheory.is_var_operand_def] >>
  rename1 `rf_live_use bb (SUC k) j (Var x)` >>
  `MEM x (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))` by
    (irule rf_live_use_ready_liveness >> simp[] >> qexists_tac `j` >> metis_tac[]) >>
  `x = out \/ MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled` by
    (Cases_on `x = out` >> simp[] >>
     `rf_live_use bb k j (Var x)` by
       (irule rf_live_use_backward >> simp[] >> metis_tac[MEM]) >>
     metis_tac[stackPlanTypesTheory.is_var_operand_def]) >>
  `(is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled)` by
    (strip_tac >> first_x_assum irule >> simp[] >>
     irule rf_live_use_current >> simp[] >>
     simp[compute_operands_def, python_stack_operands_def]) >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    rf_assign_plan_live_retained >> simp[]
QED

Theorem rf_block_plan_step:
  get_instruction bb k = SOME inst /\ n_params <= k /\
  generate_block_insts_plan lv dfg cfg fn bb.bb_label halting n_params
    (LENGTH bb.bb_instructions) (k - n_params)
    (DROP k bb.bb_instructions) ps = SOME (ops,ps_end) ==>
  ?step_ops ps1 rest_ops.
    generate_inst_plan lv dfg cfg fn inst
      (live_vars_at lv bb.bb_label (SUC k)) halting
      (case DROP (SUC k) bb.bb_instructions of
         [] => F | next_i :: _ => is_terminator next_i.inst_opcode)
      bb.bb_label ps = SOME (step_ops,ps1) /\
    generate_block_insts_plan lv dfg cfg fn bb.bb_label halting n_params
      (LENGTH bb.bb_instructions) (SUC k - n_params)
      (DROP (SUC k) bb.bb_instructions) ps1 = SOME (rest_ops,ps_end) /\
    ops = step_ops ++ rest_ops
Proof
  strip_tac >>
  `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst` by
    gvs[get_instruction_def] >>
  `DROP k bb.bb_instructions = inst :: DROP (SUC k) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL] >>
  `k - n_params + n_params + 1 = SUC k /\
   k - n_params + 1 = SUC k - n_params` by decide_tac >>
  `DROP (SUC k) bb.bb_instructions = [] ==>
   LENGTH bb.bb_instructions = SUC k` by
    (strip_tac >> fs[DROP_EQ_NIL] >> decide_tac) >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_block_insts_plan_def] >>
  Cases_on `DROP (SUC k) bb.bb_instructions = []` >> simp[] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem rf_forward_instruction_opcode:
  revert_forward_pair bb i j /\ i <= k /\ k <= j /\
  get_instruction bb k = SOME inst ==>
  inst.inst_opcode =
    (if k = i then RETURNDATACOPY else if k = j then REVERT else ASSIGN)
Proof
  simp[revert_forward_pair_def] >> strip_tac >>
  Cases_on `k = i` >- gvs[] >>
  Cases_on `k = j` >- gvs[] >>
  simp[] >> first_x_assum irule >> qexists_tac `k` >> simp[]
QED

Theorem rf_forward_instruction_exists:
  revert_forward_pair bb i j /\ i <= k /\ k <= j ==>
  ?inst. get_instruction bb k = SOME inst
Proof
  simp[revert_forward_pair_def] >> strip_tac >>
  `j < LENGTH bb.bb_instructions` by gvs[get_instruction_def] >>
  simp[get_instruction_def]
QED

Theorem rf_forward_instruction_shape:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ i <= k /\ k <= j /\
  get_instruction bb k = SOME inst ==>
  (k = i ==> inst.inst_outputs = [] /\ LENGTH inst.inst_operands = 3) /\
  (k = j ==> inst.inst_outputs = [] /\ LENGTH inst.inst_operands = 2) /\
  (i < k /\ k < j ==> ?rhs out.
    inst.inst_operands = [rhs] /\ inst.inst_outputs = [out]) /\
  LENGTH (compute_operands inst) <= 3 /\
  inst.inst_opcode <> PHI
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[codegen_ready_fn_def, fn_inst_wf_def] >>
     first_x_assum irule >> qexists_tac `bb` >>
     conj_tac >- metis_tac[lookup_block_MEM] >>
     gvs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  `i < j` by fs[revert_forward_pair_def] >>
  drule_all rf_forward_instruction_opcode >> strip_tac >>
  Cases_on `k = i` >> Cases_on `k = j` >>
  gvs[inst_wf_def, compute_operands_def, python_stack_operands_def,
      venomInstTheory.ir_specific_operand_order_def, LENGTH_EQ_NUM_compute]
QED

Theorem rf_forward_regular_plan:
  revert_forward_pair bb i j /\ i <= k /\ k <= j /\
  get_instruction bb k = SOME inst ==>
  generate_inst_plan lv dfg cfg fn inst nl halting term lbl ps =
    SOME (generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps)
Proof
  strip_tac >> drule_all rf_forward_instruction_opcode >> strip_tac >>
  Cases_on `k = i` >> Cases_on `k = j` >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
      is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
      is_raw_fmp_opcode_def]
QED

Theorem rf_forward_regular_plan_result:
  revert_forward_pair bb i j /\ i <= k /\ k <= j /\
  get_instruction bb k = SOME inst /\
  generate_inst_plan lv dfg cfg fn inst nl halting term lbl ps = SOME result ==>
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = result
Proof
  metis_tac[rf_forward_regular_plan, optionTheory.SOME_11]
QED

Theorem rf_forward_exec_abort_cases:
  revert_forward_pair bb i j /\ i <= vs.vs_inst_idx /\ vs.vs_inst_idx <= j /\
  get_instruction bb vs.vs_inst_idx = SOME inst /\
  exec_block fuel ctx bb vs = Abort a vs_end ==>
  step_inst fuel ctx inst vs = Abort a vs_end \/
  (?vs1. vs.vs_inst_idx < j /\ step_inst fuel ctx inst vs = OK vs1 /\
    exec_block fuel ctx bb (vs1 with vs_inst_idx := SUC vs.vs_inst_idx) =
      Abort a vs_end)
Proof
  strip_tac >>
  `i < j` by fs[revert_forward_pair_def] >>
  drule_all rf_forward_instruction_opcode >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `step_inst fuel ctx inst vs` >> simp[] >>
  Cases_on `vs.vs_inst_idx = i` >> Cases_on `vs.vs_inst_idx = j` >>
  gvs[is_terminator_def] >> simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem rf_suffix_instruction_no_labels:
  EVERY (\ti. EVERY (\op. ~is_label_operand op) ti.inst_operands)
    (DROP i bb.bb_instructions) /\ i <= k /\
  get_instruction bb k = SOME inst ==>
  EVERY (\op. ~is_label_operand op) inst.inst_operands
Proof
  strip_tac >>
  `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst` by
    gvs[get_instruction_def] >>
  `MEM inst (DROP i bb.bb_instructions)` by
    (`k - i < LENGTH (DROP i bb.bb_instructions)` by simp[] >>
     `EL (k - i) (DROP i bb.bb_instructions) = inst` by simp[EL_DROP] >>
     metis_tac[EL_MEM]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem rf_resolve_prefix_normalize:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb ==>
  normalize_operand (dfg_build_function fn) []
    (resolve_block_assigns (REVERSE (TAKE k bb.bb_instructions)) op) =
  normalize_operand (dfg_build_function fn) [] op
Proof
  strip_tac >> irule normalize_operand_resolve_block_assigns >> simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule mem_fn_insts_intro >> qexists_tac `bb` >>
  conj_tac >- metis_tac[lookup_block_MEM] >>
  metis_tac[MEM_REVERSE, MEM_TAKE]
QED

Theorem step_back_assign_normalize:
  !fn inst op op'. codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
    step_back_assign inst op = SOME op' ==>
    normalize_operand (dfg_build_function fn) [] op' =
    normalize_operand (dfg_build_function fn) [] op
Proof
  rpt strip_tac >>
  `op' = resolve_block_assigns [inst] op` by
    (qpat_x_assum `step_back_assign _ _ = _` mp_tac >>
     Cases_on `op` >> rw[step_back_assign_def, resolve_block_assigns_def]) >>
  simp[] >> irule normalize_operand_resolve_block_assigns >> simp[]
QED

Theorem same_after_assigns_normalize:
  !insts fn op1 op2. codegen_ready_fn fn /\
    EVERY (\inst. MEM inst (fn_insts fn)) insts /\
    same_after_assigns insts op1 op2 ==>
    normalize_operand (dfg_build_function fn) [] op1 =
    normalize_operand (dfg_build_function fn) [] op2
Proof
  Induct >> simp[same_after_assigns_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `op1 = op2` >> gvs[] >>
  Cases_on `step_back_assign h op1` >> gvs[] >>
  Cases_on `step_back_assign h op2` >> gvs[] >>
  rename1 `step_back_assign h op1 = SOME op1'` >>
  rename1 `step_back_assign h op2 = SOME op2'` >>
  `normalize_operand (dfg_build_function fn) [] op1' =
   normalize_operand (dfg_build_function fn) [] op2'` by
    (first_x_assum irule >> simp[]) >>
  metis_tac[step_back_assign_normalize]
QED

Theorem rf_forward_normalized_operands:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [dst;src;sz] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [dst';sz'] ==>
  normalize_operand (dfg_build_function fn) [] src = Lit 0w /\
  normalize_operand (dfg_build_function fn) [] dst =
    normalize_operand (dfg_build_function fn) [] dst' /\
  normalize_operand (dfg_build_function fn) [] sz =
    normalize_operand (dfg_build_function fn) [] sz'
Proof
  strip_tac >>
  `!insts. (!x. MEM x insts ==> MEM x bb.bb_instructions) ==>
     EVERY (\inst. MEM inst (fn_insts fn)) insts` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     irule mem_fn_insts_intro >> qexists_tac `bb` >>
     metis_tac[lookup_block_MEM]) >>
  `EVERY (\inst. MEM inst (fn_insts fn))
     (REVERSE (TAKE i bb.bb_instructions))` by
    (first_x_assum irule >> metis_tac[MEM_REVERSE, MEM_TAKE]) >>
  `EVERY (\inst. MEM inst (fn_insts fn))
     (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)))` by
    (first_x_assum irule >>
     metis_tac[MEM_REVERSE, MEM_TAKE, rich_listTheory.MEM_DROP_IMP]) >>
  `!op1 op2. same_after_assigns (REVERSE (TAKE i bb.bb_instructions)) op1 op2 ==>
     normalize_operand (dfg_build_function fn) [] op1 =
     normalize_operand (dfg_build_function fn) [] op2` by
    (rpt strip_tac >> irule same_after_assigns_normalize >> simp[] >>
     qexists_tac `REVERSE (TAKE i bb.bb_instructions)` >> simp[]) >>
  `!op. normalize_operand (dfg_build_function fn) []
     (resolve_block_assigns
        (REVERSE (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions))) op) =
     normalize_operand (dfg_build_function fn) [] op` by
    (gen_tac >> irule normalize_operand_resolve_block_assigns >> simp[]) >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  pure_rewrite_tac[revert_forward_pair_def] >> strip_tac >> gvs[] >>
  `normalize_operand (dfg_build_function fn) [] (Lit 0w) = Lit 0w` by
    simp[normalize_operand_def] >>
  metis_tac[]
QED

Theorem rf_written_interval:
  off <= LENGTH mem ==>
  TAKE (LENGTH bytes) (DROP off
    (TAKE off mem ++ bytes ++ DROP (off + LENGTH bytes) mem)) = bytes
Proof
  strip_tac >> simp[DROP_APPEND, LENGTH_TAKE, TAKE_APPEND]
QED

Theorem rf_source_written_interval:
  TAKE (LENGTH bytes) (DROP off
    (write_memory_with_expansion off bytes vs).vs_memory) = bytes
Proof
  simp[venomStateTheory.write_memory_with_expansion_def] >>
  irule rf_written_interval >> IF_CASES_TAC >> simp[]
QED

Theorem rf_asm_written_interval:
  LENGTH (bytes : byte list) = sz ==>
  TAKE sz (DROP off
    (TAKE off (if sz = 0 then mem else asm_expand_memory (off + sz) mem) ++
     bytes ++ DROP (off + sz)
       (if sz = 0 then mem else asm_expand_memory (off + sz) mem))) = bytes
Proof
  strip_tac >> Cases_on `sz = 0` >- gvs[LENGTH_NIL] >>
  gvs[] >> irule rf_written_interval >>
  mp_tac (Q.SPECL [`off + LENGTH (bytes : byte list)`, `mem`] spillSimTheory.asm_expand_memory_length) >>
  decide_tac
QED

Theorem rf_source_copy_result:
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  eval_operand dop vs = SOME dst /\ eval_operand sop vs = SOME src /\
  eval_operand zop vs = SOME sz ==>
  step_inst fuel ctx inst vs =
    if w2n src + w2n sz <= LENGTH vs.vs_returndata then
      OK (write_memory_with_expansion (w2n dst)
        (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs)
    else Abort ExHalt_abort (halt_state (set_returndata [] vs))
Proof
  strip_tac >> simp[Once step_inst_def] >>
  simp[Once step_inst_base_def] >>
  Cases_on `w2n src + w2n sz <= LENGTH vs.vs_returndata` >> simp[]
QED

Theorem rf_copy_interval_agreement:
  w2n src + w2n sz <= LENGTH data ==>
  TAKE (w2n sz) (DROP (w2n dst)
    (write_memory_with_expansion (w2n dst)
      (TAKE (w2n sz) (DROP (w2n src) data)) vs).vs_memory) =
  TAKE (w2n sz) (DROP (w2n dst)
    (TAKE (w2n dst)
       (if sz = 0w then mem else asm_expand_memory (w2n dst + w2n sz) mem) ++
     TAKE (w2n sz) (DROP (w2n src) data) ++
     DROP (w2n dst + w2n sz)
       (if sz = 0w then mem else asm_expand_memory (w2n dst + w2n sz) mem)))
Proof
  strip_tac >>
  `LENGTH (TAKE (w2n sz) (DROP (w2n src) data)) = w2n sz` by simp[] >>
  `TAKE (w2n sz) (DROP (w2n dst)
    (write_memory_with_expansion (w2n dst)
      (TAKE (w2n sz) (DROP (w2n src) data)) vs).vs_memory) =
    TAKE (w2n sz) (DROP (w2n src) data)` by
    metis_tac[rf_source_written_interval] >>
  simp[] >> sym_tac >>
  Cases_on `sz = 0w` >- simp[] >>
  simp[] >>
  drule rf_asm_written_interval >>
  disch_then (qspecl_then [`w2n dst`, `mem`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem rf_source_copy_ok_cases:
  inst.inst_opcode = RETURNDATACOPY /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?dop sop zop dst src sz.
    inst.inst_operands = [dop;sop;zop] /\
    eval_operand dop vs = SOME dst /\ eval_operand sop vs = SOME src /\
    eval_operand zop vs = SOME sz /\
    w2n src + w2n sz <= LENGTH vs.vs_returndata /\
    vs' = write_memory_with_expansion (w2n dst)
      (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def] >> simp[Once step_inst_base_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem rf_copy_success_boundary:
  plan_stack_rel lo (frame_view fn ra vs) (tail ++ [zop;sop;dop]) stk /\
  dop <> dead_stack_marker /\ sop <> dead_stack_marker /\ zop <> dead_stack_marker /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  w2n src + w2n sz <= LENGTH vs.vs_returndata /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  asm_block_at prog st.as_pc [AsmOp "RETURNDATACOPY"] ==>
  ?st' stk'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
    st'.as_pc = st.as_pc + 1 /\ st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') tail stk' /\
    venom_asm_terminal_rel vs' st' /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) st'.as_memory)
Proof
  strip_tac >>
  `st.as_returndata = vs.vs_returndata` by fs[venom_asm_terminal_rel_def] >>
  `!op. operand_val (frame_view fn ra vs') lo op =
         operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[frame_view_def,
      venomStateTheory.write_memory_with_expansion_def,
      codegenRelTheory.operand_val_def, venomStateTheory.lookup_var_def]) >>
  `w2n src + w2n sz <= LENGTH st.as_returndata` by simp[] >>
  drule_all rf_copy_stack_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (qpat_x_assum `vs' = _` SUBST_ALL_TAC >> fs[plan_stack_rel_def]) >>
  conj_tac
  >- gvs[venom_asm_terminal_rel_def,
         venomStateTheory.write_memory_with_expansion_def] >>
  gvs[] >> irule rf_copy_interval_agreement >> simp[]
QED

Theorem rf_copy_fault_boundary:
  plan_stack_rel lo current (tail ++ [zop;sop;dop]) stk /\
  dop <> dead_stack_marker /\ sop <> dead_stack_marker /\ zop <> dead_stack_marker /\
  operand_val current lo dop = SOME dst /\
  operand_val current lo sop = SOME src /\
  operand_val current lo zop = SOME sz /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  w2n src + w2n sz > LENGTH vs.vs_returndata /\
  asm_block_at prog st.as_pc [AsmOp "RETURNDATACOPY"] ==>
  ?st'. asm_steps lo o2pc prog 1 st = AsmFault st' /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) st'
Proof
  strip_tac >>
  `?d s z residual. stk = d :: s :: z :: residual /\
    operand_val current lo dop = SOME d /\
    operand_val current lo sop = SOME s /\
    operand_val current lo zop = SOME z` by
    (irule asm_stack_top3_from_plan >> simp[] >>
     qexists_tac `tail` >> simp[]) >>
  gvs[] >> irule terminal_returndatacopy_fault_step >> simp[] >>
  qexistsl_tac [`dst`, `src`, `sz`, `residual ++ rest`] >> simp[]
QED

Theorem rf_entry_preparation_execution:
  !base. codegen_ready_fn fn /\ generated_plan_state_wf base ps /\
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (ros,ps2) /\
  opc <> INVOKE /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inputs /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  (!off. ~MEM (SOSpill off) (ins ++ ros) /\
    ~MEM (SORestore off) (ins ++ ros)) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (ins ++ ros)) ==>
  ?stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (ins ++ ros))) st =
      AsmOK (st with <|as_stack := stk' ++ rest;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros))|>) /\
    plan_stack_rel lo (frame_view fn ra vs) ps2.ps_stack stk' /\
    ps2.ps_stack = stack_pop (LENGTH inputs) ps2.ps_stack ++ inputs
Proof
  gen_tac >> strip_tac >>
  drule_all rf_entry_preparation_replay >>
  disch_then (qspec_then `initial_fmp` strip_assume_tac) >>
  drule_all rf_preparation_stack_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `stk'` >> asm_rewrite_tac[] >>
  drule_all rf_preparation_arranged >> simp[]
QED


(* The opaque return-PC representation is invisible to ordinary non-label uses. *)
Theorem rf_ordinary_operand_value:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\ MEM op inst.inst_operands /\
  ~is_label_operand op ==>
  operand_val (frame_view fn ra vs) lo op = eval_operand op vs
Proof
  strip_tac >> simp[operand_val_eq_eval] >>
  drule_all ordinary_inst_operand_frame_view >>
  disch_then (qspecl_then [`vs`, `ra`, `(frame_view fn ra vs).vs_memory`] mp_tac) >>
  simp[frame_view_def]
QED



Theorem rf_preparation_postpop_generated_wf:
  !base opc inputs nl ps ins ps1 dfg ros ps2.
  generated_plan_state_wf base ps /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  LENGTH inputs <= 16 /\
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan dfg inputs ps1 = (ros,ps2) ==>
  generated_plan_state_wf base
    (ps2 with ps_stack := stack_pop (LENGTH inputs) ps2.ps_stack)
Proof
  rpt gen_tac >> strip_tac >> rename1 `generated_plan_state_wf spillbase ps` >>
  `residual_budget_wf spillbase [] ps` by
    metis_tac[generated_plan_state_wf_residual_nil] >>
  `residual_budget_wf spillbase inputs ps1` by
    metis_tac[emit_input_plan_residual_budget_nil] >>
  `!at. LIST_ELEM_COUNT at inputs <= LIST_ELEM_COUNT at ps1.ps_stack` by
    (drule_all emit_input_plan_materialised >> simp[]) >>
  `LENGTH inputs <= LENGTH ps1.ps_stack` by
    (irule list_elem_count_dom_length >> simp[]) >>
  drule_all reorder_plan_materialised_arranged >> strip_tac >>
  drule plan_state_residual_wf_pop >>
  simp[generated_plan_state_wf_def]
QED

Theorem rf_copy_plan_generated_wf:
  !base.
  generated_plan_state_wf base ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') ==>
  generated_plan_state_wf base ps'
Proof
  gen_tac >> strip_tac >>
  Cases_on `emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps` >>
  rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) ps1` >>
  rename1 `_ = (ros,ps2)` >>
  drule_all rf_copy_plan_result >>
  disch_then (fn th => fs[th]) >>
  qpat_x_assum `release_dead_spills _ _ = ps'` (SUBST1_TAC o SYM) >>
  irule generated_plan_state_wf_release_dead_spills >>
  drule_all rf_preparation_postpop_generated_wf >> simp[]
QED


Theorem rf_copy_source_alignment:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz ==>
  step_inst fuel ctx inst vs =
    if w2n src + w2n sz <= LENGTH vs.vs_returndata then
      OK (write_memory_with_expansion (w2n dst)
        (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs)
    else Abort ExHalt_abort (halt_state (set_returndata [] vs))
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    operand_val (frame_view fn ra vs) lo op = eval_operand op vs` by
    (rpt strip_tac >> irule rf_ordinary_operand_value >> simp[] >>
     conj_tac >- gvs[EVERY_MEM] >>
     qexists_tac `inst` >> gvs[]) >>
  irule rf_source_copy_result >> simp[] >>
  metis_tac[listTheory.MEM]
QED

Definition rf_spills_separated_def:
  rf_spills_separated (ps:plan_state) <=>
    !x a y b. FLOOKUP ps.ps_spilled x = SOME a /\
      FLOOKUP ps.ps_spilled y = SOME b /\ x <> y ==>
      a + 32 <= b \/ b + 32 <= a
End

Theorem rf_suffix_preparation_execution:
  codegen_ready_fn fn /\ rf_spills_separated ps /\
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (ros,ps2) /\
  opc <> INVOKE /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inputs /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. MEM op inputs ==>
    operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) (ins ++ ros) /\
    ~MEM (SORestore off) (ins ++ ros)) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (ins ++ ros)) ==>
  ?stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (ins ++ ros))) st =
      AsmOK (st with <|as_stack := stk' ++ rest;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros))|>) /\
    plan_stack_rel lo (frame_view fn ra s) ps2.ps_stack stk' /\
    ps2.ps_stack = stack_pop (LENGTH inputs) ps2.ps_stack ++ inputs /\
    rf_inventory_inv fn ra lo entry ps2 s
Proof
  strip_tac >>
  `EVERY is_simple_stack_op (ins ++ ros) /\
   prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros) /\
   plan_stack_sem_eq lo (frame_view fn ra s)
     (apply_prefix_ops initial_fmp lo (ins ++ ros) ps).ps_stack ps2.ps_stack` by
    (irule rf_preparation_replay >> asm_rewrite_tac[] >>
     conj_tac
     >- fs[rf_spills_separated_def] >>
     qexistsl_tac [`dfg_build_function fn`, `entry`, `inputs`, `nl`, `opc`, `ps1`] >>
     asm_rewrite_tac[] >> conj_tac
     >- (fs[rf_inventory_inv_def] >> metis_tac[]) >>
     fs[EVERY_MEM] >> metis_tac[codegen_normalize_operand_not_dead_marker,
       dead_stack_marker_def, stackPlanTypesTheory.is_label_operand_def]) >>
  drule_all rf_preparation_stack_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `stk'` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (drule_all rf_preparation_arranged >> simp[]) >>
  drule_at (Pat `reorder_plan _ _ _ = _`) rf_inventory_inv_preparation >>
  simp[] >> disch_then irule >> asm_rewrite_tac[] >>
  qexistsl_tac [`ins`, `nl`, `opc`, `ps`] >> simp[]
QED

Theorem rf_assign_prepared_stack:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  step_inst fuel ctx inst s = OK s' /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  ps.ps_stack = tail ++ [rhs] /\
  pushed = ps with ps_stack := stack_push (Var out) tail /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk ==>
  rf_inventory_inv fn ra lo entry pushed s' /\
  plan_stack_rel lo (frame_view fn ra s') pushed.ps_stack stk
Proof
  strip_tac >>
  `stack_pop 1 ps.ps_stack = tail` by simp[stack_pop_def, TAKE_APPEND] >>
  `rf_inventory_inv fn ra lo entry pushed s'` by
    (qpat_assum `pushed = _` SUBST1_TAC >>
     qpat_assum `stack_pop 1 ps.ps_stack = tail`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     drule_at (Pat `step_inst _ _ _ _ = OK _`) rf_inventory_inv_assign >>
     disch_then irule >> simp[] >> qexists_tac `ps` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule rf_assign_stack_transfer >>
  qexistsl_tac [`entry`, `ps`, `rhs`, `s`, `tail`, `out`] >> simp[] >>
  conj_tac >- (strip_tac >> gvs[dead_stack_marker_def,
    stackPlanTypesTheory.is_label_operand_def]) >>
  irule normalize_operand_codegen_assign >> simp[] >> qexists_tac `inst` >>
  simp[] >> irule dfg_build_function_ssa_def >> simp[] >>
  fs[codegen_ready_fn_def] >> metis_tac[]
QED

Theorem rf_assign_plan_execution:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  step_inst fuel ctx inst s = OK s' /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK (st with <|as_stack := stk' ++ rest;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp ops)|>) /\
    plan_stack_rel lo (frame_view fn ra s') ps'.ps_stack stk'
Proof
  strip_tac >>
  Cases_on `emit_input_plan ASSIGN [rhs] nl ps` >> rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) [rhs] ps1` >>
  rename1 `_ = (ros,ps2)` >>
  drule_all rf_assign_plan_result >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp (ins ++ ros)) /\
   asm_block_at prog
     (st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros)))
     (execute_plan initial_fmp (pops ++ opts))` by
    gvs[execute_plan_append, asm_block_at_append, APPEND_ASSOC] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
    ~MEM (SORestore off) (ins ++ ros)` by fs[MEM_APPEND] >>
  `ASSIGN <> INVOKE /\ LENGTH [rhs] <= 16 /\
   EVERY (\op. ~is_label_operand op) [rhs] /\
   (!op. MEM op [rhs] /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
   (!op. MEM op [rhs] ==>
     operand_val (frame_view fn ra s) lo op =
     operand_val entry lo (normalize_operand (dfg_build_function fn) [] op))` by
    simp[] >>
  drule_all rf_suffix_preparation_execution >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `AsmOK mid` >>
  qabbrev_tac `pushed = ps2 with ps_stack :=
    stack_push (Var out) (stack_pop 1 ps2.ps_stack)` >>
  qpat_x_assum `ps2.ps_stack = _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `rf_inventory_inv fn ra lo entry pushed s' /\
   plan_stack_rel lo (frame_view fn ra s') pushed.ps_stack stk'` by
    (drule_at (Pat `step_inst _ _ _ _ = OK _`) rf_assign_prepared_stack >>
     disch_then irule >> simp[] >>
     qexistsl_tac [`ps2`, `stack_pop 1 ps2.ps_stack`] >>
     simp[Abbr `pushed`]) >>
  `EVERY is_simple_stack_op (pops ++ opts)` by
    (irule spill_free_postfix_simple >>
     conj_tac >- fs[MEM_APPEND] >>
     qexistsl_tac [`dfg_build_function fn`, `~halting`, `inst`,
       `if MEM out nl then [] else [Var out]`, `nl`, `~MEM out nl`,
       `term`, `pushed`, `ps8`, `ps9`] >>
     conj_tac >- (Cases_on `halting` >> gvs[]) >>
     Cases_on `MEM out nl` >> gvs[]) >>
  qpat_x_assum `ps2.ps_stack = _` kall_tac >>
  `mid.as_stack = stk' ++ rest /\
   asm_block_at prog mid.as_pc (execute_plan initial_fmp (pops ++ opts))` by
    (simp[Abbr `mid`] >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  `pushed.ps_stack = stack_push (Var out) (stack_pop 1 ps2.ps_stack)` by
    simp[Abbr `pushed`] >>
  drule_all rf_assign_postfix_stack_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `stk''` >> conj_tac
  >- (qpat_x_assum `asm_steps _ _ _ _ st = AsmOK mid`
        (mp_then Any (qspec_then
          `LENGTH (execute_plan initial_fmp (pops ++ opts))` mp_tac)
          asm_steps_add_ok) >>
      simp[execute_plan_append, APPEND_ASSOC] >>
      disch_then SUBST1_TAC >>
      simp[Abbr `mid`, NoAsms] >>
      simp[NoAsms, execute_plan_append]) >>
  fs[]
QED

(* Abstract planner audit, not a counterexample to the frozen theorem. *)
Theorem rf_assign_stale_stack_audit:
  ~ALL_DISTINCT
    (SND (generate_regular_inst_plan
      (liveness_analyze rf_probe_fn) (dfg_build_function rf_probe_fn)
      (cfg_analyze rf_probe_fn) rf_probe_fn
      (mk_inst 10 ASSIGN [Lit 7w] ["o"]) ["o"] F T "dead"
      ((init_plan_state 0) with ps_stack := [Var "o"]))).ps_stack
Proof
  EVAL_TAC
QED

Theorem rf_assign_stale_spill_audit:
  ~DISJOINT
    (set (SND (generate_regular_inst_plan
      (liveness_analyze rf_probe_fn) (dfg_build_function rf_probe_fn)
      (cfg_analyze rf_probe_fn) rf_probe_fn
      (mk_inst 10 ASSIGN [Lit 7w] ["o"]) ["o"] F T "dead"
      ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "o",0)))).ps_stack)
    (FDOM (SND (generate_regular_inst_plan
      (liveness_analyze rf_probe_fn) (dfg_build_function rf_probe_fn)
      (cfg_analyze rf_probe_fn) rf_probe_fn
      (mk_inst 10 ASSIGN [Lit 7w] ["o"]) ["o"] F T "dead"
      ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "o",0)))).ps_spilled)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_SING] >> EVAL_TAC
QED

Theorem rf_spills_separated_entry:
  !base ps. generated_plan_state_wf base ps ==> rf_spills_separated ps
Proof
  rpt strip_tac >> fs[generated_plan_state_wf_def] >>
  drule spill_alloc_layout_wf_spilled_separated >>
  simp[rf_spills_separated_def]
QED

Theorem rf_spills_separated_transfer:
  rf_spills_separated ps /\
  (!x off. FLOOKUP qs.ps_spilled x = SOME off ==>
    FLOOKUP ps.ps_spilled x = SOME off) ==>
  rf_spills_separated qs
Proof
  rw[rf_spills_separated_def] >> metis_tac[]
QED

Theorem rf_release_spill_lookup:
  !ps nl x off.
  FLOOKUP (release_dead_spills nl ps).ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  `!dead (ps:plan_state) x off.
    FLOOKUP (FOLDL (\ps' (op:operand,addr:num).
      ps' with <|ps_spilled := ps'.ps_spilled \\ op;
        ps_alloc := free_spill_slot addr ps'.ps_alloc|>) ps dead).ps_spilled x = SOME off ==>
    FLOOKUP ps.ps_spilled x = SOME off` by
    (Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
     simp[] >> strip_tac >> first_x_assum (drule_then mp_tac) >>
     simp[finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
     Cases_on `x = h0` >> simp[]) >>
  simp[release_dead_spills_def] >> rpt strip_tac >>
  first_x_assum (drule_then ACCEPT_TAC)
QED

Theorem rf_do_spill_at_has_spill:
  ?off. MEM (SOSpill off) (FST (do_spill_at dist ps))
Proof
  simp[do_spill_at_def, do_spill_tos_def] >>
  Cases_on `dist = 0` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> gvs[]
QED

Theorem rf_do_restore_spill_lookup:
  do_restore op ps = (ops,ps') /\
  FLOOKUP ps'.ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def] >> strip_tac >>
  gvs[finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  Cases_on `x = op` >> gvs[]
QED

Theorem rf_do_dup_spilled:
  (SND (do_dup dist ps)).ps_spilled = ps.ps_spilled
Proof
  simp[do_dup_def] >> IF_CASES_TAC >- simp[] >>
  pairarg_tac >> simp[]
QED

Theorem rf_reduce_depth_spilled:
  !fuel targets op fixed len ps ops ps'.
  reduce_depth_plan fuel targets op fixed len ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops) ==>
  ps'.ps_spilled = ps.ps_spilled
Proof
  Cases >> simp[reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >- simp[] >>
  Cases_on `stack_get_unfixed_depth op fixed len ps.ps_stack` >- simp[] >>
  simp[] >> IF_CASES_TAC >- simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x len` >- simp[] >>
  simp[] >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[MEM_APPEND] >>
  metis_tac[rf_do_spill_at_has_spill, pairTheory.FST]
QED

Theorem rf_emit_one_input_spill_lookup:
  emit_one_input opc live op ps = (ops,ps') /\
  FLOOKUP ps'.ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  simp[emit_one_input_def] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `op` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[rf_do_restore_spill_lookup, rf_do_dup_spilled, pairTheory.SND]
QED

Theorem rf_emit_input_plan_spill_lookup:
  !args ps ops ps'.
  emit_input_plan opc args live ps = (ops,ps') /\
  FLOOKUP ps'.ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  drule rf_emit_one_input_spill_lookup >> simp[]
QED



Theorem rf_reorder_one_spill_lookup:
  reorder_one dfg targets idx op ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops) /\
  FLOOKUP ps'.ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  simp[reorder_one_def] >> rpt (pairarg_tac >> simp[]) >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (irule rf_do_restore_spill_lookup >>
      qexistsl [`op`, `ops`, `ps'`] >> simp[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `dist > 16` >> gvs[] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1)) (LENGTH targets) ps2.ps_stack` >>
  gvs[AllCaseEqs(), MEM_APPEND] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs(), MEM_APPEND]) >>
  rpt (rename1 `do_swap d p = (cops,q)` >>
       qspecl_then [`d`, `p`] mp_tac do_swap_spilled_unchanged >>
       simp[] >> disch_then assume_tac >>
       qpat_x_assum `do_swap d p = _` kall_tac) >> gvs[] >>
  rpt (rename1 `do_swap d2 p2 = (cops2,q2)` >>
       qspecl_then [`d2`, `p2`] mp_tac do_swap_spilled_unchanged >>
       simp[] >> disch_then assume_tac >>
       qpat_x_assum `do_swap d2 p2 = _` kall_tac) >> gvs[] >>
  TRY (drule (REWRITE_RULE [AND_IMP_INTRO] rf_reduce_depth_spilled) >>
       simp[] >> disch_then assume_tac >> gvs[]) >>
  TRY (drule (REWRITE_RULE [AND_IMP_INTRO] rf_do_restore_spill_lookup) >> simp[] >> NO_TAC)
QED

Theorem rf_reorder_steps_spill_lookup[local]:
  !items ps ops ps'.
  plan_steps (\(idx,op) p. reorder_one dfg targets idx op p)
    items ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops) /\
  FLOOKUP ps'.ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  Induct >- simp[foldlSimTheory.plan_steps_def] >>
  rpt gen_tac >> strip_tac >>
  drule plan_steps_cons_result >> strip_tac >>
  first_x_assum (drule_at (Pos hd)) >>
  simp[] >> strip_tac >> gvs[MEM_APPEND] >>
  PairCases_on `h` >> gvs[] >>
  drule (REWRITE_RULE [AND_IMP_INTRO] rf_reorder_one_spill_lookup) >> simp[]
QED

Theorem rf_reorder_plan_spill_lookup:
  reorder_plan dfg targets ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops) /\
  FLOOKUP ps'.ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  rewrite_tac[reorder_plan_eq_plan_steps] >>
  metis_tac[rf_reorder_steps_spill_lookup]
QED

Theorem rf_optimistic_spilled:
  !dfg inst live term ps. (SND (optimistic_swap_plan dfg inst live term ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >>
  simp[do_swap_spilled_unchanged]
QED

Theorem rf_popmany_fold_spilled[local]:
  !items ops ps.
  (SND (FOLDL (\(ops,ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops,ps)
    | SOME dist =>
      (\(swap_ops,ps').
         (ops ++ swap_ops ++ [SOPop 1],
          ps' with ps_stack := stack_pop 1 ps'.ps_stack))
        (if dist = 0 then ([],ps) else do_swap dist ps))
    (ops,ps) items)).ps_spilled = ps.ps_spilled
Proof
  Induct >> simp[] >> rpt gen_tac >>
  fs[LET_THM] >>
  Cases_on `stack_get_depth h ps.ps_stack` >> simp[] >>
  Cases_on `x = 0` >> simp[] >>
  Cases_on `do_swap x ps` >> simp[] >>
  qspecl_then [`x`, `ps`] mp_tac do_swap_spilled_unchanged >> simp[]
QED

Theorem rf_popmany_spilled:
  !items ps. (SND (popmany_plan items ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> Cases_on `items` >> simp[popmany_plan_def] >>
  rpt IF_CASES_TAC >>
  simp[popmany_individual_def, LET_THM, SRULE [LET_THM] rf_popmany_fold_spilled] >>
  pairarg_tac >> simp[] >>
  qspec_then `SUC (LENGTH t)` (qspec_then `ps` mp_tac) do_swap_spilled_unchanged >>
  simp[]
QED

Theorem rf_assign_plan_spill_lookup:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,ps') /\
  (!a. ~MEM (SOSpill a) ops) /\
  FLOOKUP ps'.ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  strip_tac >>
  Cases_on `emit_input_plan ASSIGN [rhs] nl ps` >> rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan dfg [rhs] ps1` >> rename1 `_ = (ros,ps2)` >>
  drule_all rf_assign_plan_result >> strip_tac >> gvs[MEM_APPEND] >>
  `FLOOKUP ps9.ps_spilled x = SOME off` by
    metis_tac[rf_release_spill_lookup] >>
  `ps9.ps_spilled = ps8.ps_spilled` by
    (Cases_on `MEM out nl` >> gvs[] >>
     qspecl_then [`dfg`, `inst`, `nl`, `term`, `ps8`] mp_tac rf_optimistic_spilled >> simp[]) >>
  `ps8.ps_spilled = ps2.ps_spilled` by
    (Cases_on `halting` >> gvs[] >>
     qspecl_then [`if MEM out nl then [] else [Var out]`,
       `ps2 with ps_stack := stack_push (Var out) (stack_pop 1 ps2.ps_stack)`]
       mp_tac rf_popmany_spilled >> simp[]) >>
  gvs[] >>
  `FLOOKUP ps1.ps_spilled x = SOME off` by
    (drule (REWRITE_RULE [AND_IMP_INTRO] rf_reorder_plan_spill_lookup) >> simp[]) >>
  drule (REWRITE_RULE [AND_IMP_INTRO] rf_emit_input_plan_spill_lookup) >> simp[]
QED

Theorem rf_copy_plan_spill_lookup:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,ps') /\
  (!a. ~MEM (SOSpill a) ops) /\
  FLOOKUP ps'.ps_spilled x = SOME off ==>
  FLOOKUP ps.ps_spilled x = SOME off
Proof
  strip_tac >>
  Cases_on `emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps` >>
  rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan dfg (compute_operands inst) ps1` >> rename1 `_ = (ros,ps2)` >>
  drule_all rf_copy_plan_result >> strip_tac >> gvs[MEM_APPEND] >>
  `FLOOKUP ps2.ps_spilled x = SOME off` by
    (drule (REWRITE_RULE [AND_IMP_INTRO] rf_release_spill_lookup) >> simp[]) >>
  `FLOOKUP ps1.ps_spilled x = SOME off` by
    (drule (REWRITE_RULE [AND_IMP_INTRO] rf_reorder_plan_spill_lookup) >> simp[]) >>
  drule (REWRITE_RULE [AND_IMP_INTRO] rf_emit_input_plan_spill_lookup) >> simp[]
QED

Theorem rf_assign_plan_spills_separated:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ rf_spills_separated ps /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,ps') /\
  (!a. ~MEM (SOSpill a) ops) ==>
  rf_spills_separated ps'
Proof
  strip_tac >> irule rf_spills_separated_transfer >>
  qexists_tac `ps` >> simp[] >> rpt strip_tac >>
  irule rf_assign_plan_spill_lookup >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem rf_copy_plan_spills_separated:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  rf_spills_separated ps /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,ps') /\
  (!a. ~MEM (SOSpill a) ops) ==>
  rf_spills_separated ps'
Proof
  strip_tac >> irule rf_spills_separated_transfer >>
  qexists_tac `ps` >> simp[] >> rpt strip_tac >>
  irule rf_copy_plan_spill_lookup >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem rf_optimistic_inventory_subset:
  optimistic_swap_plan dfg inst nl term ps = (ops,ps') ==>
  !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >> simp[] >>
  strip_tac >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  drule_at (Pat `do_swap _ _ = _`) do_swap_inventory_subset >> simp[]
QED

Theorem rf_assign_postfix_inventory:
  ps.ps_stack = stack_push (Var out) tail /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  rf_inventory_inv fn ra lo entry ps s ==>
  rf_inventory_inv fn ra lo entry (release_dead_spills nl ps9) s
Proof
  strip_tac >> irule rf_inventory_inv_release >>
  irule rf_inventory_inv_vars_subset >> qexistsl_tac [`ps`, `s`] >> simp[] >>
  Cases_on `MEM out nl`
  >- (`pops = [] /\ ps8 = ps` by
        (Cases_on `halting` >> gvs[popmany_plan_def]) >>
      gvs[] >> drule rf_optimistic_inventory_subset >> simp[]) >>
  gvs[] >> Cases_on `halting` >- gvs[] >>
  `stack_get_depth (Var out) ps.ps_stack = SOME 0` by
    simp[stack_push_def, REVERSE_SNOC, stack_get_depth_def, stack_find_def] >>
  `popmany_plan [Var out] ps =
    ([SOPop 1],ps with ps_stack := stack_pop 1 ps.ps_stack)` by
    metis_tac[regularPostfixSimTheory.popmany_plan_top_singleton] >>
  gvs[stack_pop_def] >> metis_tac[MEM_TAKE]
QED

Theorem rf_assign_plan_inventory:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  step_inst fuel ctx inst s = OK s' /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') ==>
  rf_inventory_inv fn ra lo entry ps' s'
Proof
  strip_tac >>
  Cases_on `emit_input_plan ASSIGN [rhs] nl ps` >> rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) [rhs] ps1` >>
  rename1 `_ = (ros,ps2)` >>
  drule_all rf_assign_plan_result >> strip_tac >>
  `rf_inventory_inv fn ra lo entry ps2 s` by
    (irule rf_inventory_inv_preparation >>
     qexistsl_tac [`ins`, `[rhs]`, `nl`, `ASSIGN`, `ps`, `ps1`, `ros`] >> simp[]) >>
  qabbrev_tac `pushed = ps2 with ps_stack :=
    stack_push (Var out) (stack_pop 1 ps2.ps_stack)` >>
  `rf_inventory_inv fn ra lo entry pushed s'` by
    (drule_at (Pat `step_inst _ _ _ _ = OK _`) rf_inventory_inv_assign >>
     disch_then irule >> simp[] >> qexists_tac `ps2` >>
     simp[Abbr `pushed`]) >>
  gvs[] >> irule rf_assign_postfix_inventory >>
  qexistsl_tac [`dfg_build_function fn`, `halting`, `inst`, `opts`, `out`,
    `pops`, `pushed`, `ps8`, `stack_pop 1 ps2.ps_stack`, `term`] >>
  simp[Abbr `pushed`]
QED

Theorem rf_assign_success_invariants:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI) /\
  get_instruction bb k = SOME inst /\ k <= j /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  rf_spills_separated ps /\
  rf_value_inv fn ra bb j lo entry k s /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
    halting term bb.bb_label ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  step_inst fuel ctx inst s = OK s' ==>
  rf_spills_separated ps' /\
  rf_value_inv fn ra bb j lo entry (SUC k) (s' with vs_inst_idx := SUC k) /\
  rf_inventory_inv fn ra lo entry ps' (s' with vs_inst_idx := SUC k) /\
  (!op. rf_live_use bb (SUC k) j op /\ is_var_operand op ==>
    MEM op ps'.ps_stack \/ op IN FDOM ps'.ps_spilled)
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists_tac `bb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  `rf_live_use bb k j rhs` by
    (irule rf_live_use_current >>
     simp[compute_operands_def, python_stack_operands_def]) >>
  `(is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled)` by
    metis_tac[] >>
  `operand_val (frame_view fn ra s) lo rhs =
   operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs)` by
    metis_tac[rf_value_inv_def] >>
  `!off. ~MEM (SOSpill off) ops` by fs[] >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by simp[] >>
  conj_tac >- (drule_all rf_assign_plan_spills_separated >> simp[]) >>
  conj_tac
  >- (simp[] >> drule_all rf_value_inv_assign >> simp[]) >>
  conj_tac
  >- (simp[] >> drule_all rf_assign_plan_inventory >> simp[]) >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    rf_assign_ready_future_owned >> simp[] >>
  disch_then (qspec_then `j` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem rf_suffix_copy_prepared:
  codegen_ready_fn fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (ins ++ ros))) st =
      AsmOK (st with <|as_stack := stk' ++ rest;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros))|>) /\
    plan_stack_rel lo (frame_view fn ra vs)
      (stack_pop 3 ps2.ps_stack ++ [zop;sop;dop]) stk' /\
    asm_block_at prog
      (st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros)))
      [AsmOp "RETURNDATACOPY"] /\
    ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
    ps' = release_dead_spills nl
      (ps2 with ps_stack := stack_pop 3 ps2.ps_stack) /\
    dop <> dead_stack_marker /\ sop <> dead_stack_marker /\
    zop <> dead_stack_marker
Proof
  strip_tac >>
  `compute_operands inst = [zop;sop;dop]` by
    simp[compute_operands_def, python_stack_operands_def,
         venomInstTheory.ir_specific_operand_order_def] >>
  `ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
   ps' = release_dead_spills nl
     (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)` by
    (drule_all rf_copy_plan_result >> disch_then (fn th => fs[th])) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp (ins ++ ros)) /\
   asm_block_at prog
     (st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros)))
     [AsmOp "RETURNDATACOPY"]` by
    gvs[execute_plan_append, execute_plan_def, exec_stack_op_def, asm_block_at_append] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)` by fs[MEM_APPEND] >>
  `RETURNDATACOPY <> INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
   EVERY (\op. ~is_label_operand op) (compute_operands inst)` by gvs[] >>
  drule_all rf_suffix_preparation_execution >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `stk'` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `ps2.ps_stack = _` mp_tac >> simp[] >>
      disch_then (fn th => pure_once_rewrite_tac[GSYM th]) >> asm_rewrite_tac[]) >>
  qpat_x_assum `ps2.ps_stack = _` kall_tac >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> gvs[dead_stack_marker_def,
    stackPlanTypesTheory.is_label_operand_def]
QED

Theorem rf_suffix_copy_execution:
  codegen_ready_fn fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  if w2n src + w2n sz <= LENGTH vs.vs_returndata then
  (?st' stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk' /\
    venom_asm_terminal_rel vs' st' /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) st'.as_memory))
  else
  (?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmFault st' /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) st')
Proof
  strip_tac >>
  drule_all rf_suffix_copy_prepared >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `AsmOK mid` >>
  `mid.as_stack = stk' ++ rest /\ venom_asm_terminal_rel vs mid /\
   asm_block_at prog mid.as_pc [AsmOp "RETURNDATACOPY"]` by
    (simp[Abbr `mid`] >> fs[venom_asm_terminal_rel_def]) >>
  Cases_on `w2n src + w2n sz <= LENGTH vs.vs_returndata` >> simp[]
  >- (drule_all rf_copy_success_boundary >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qpat_assum `asm_steps _ _ _ (LENGTH _) _ = AsmOK mid`
        (mp_then Any (qspec_then `1` assume_tac) asm_steps_add_ok) >>
      qexistsl_tac [`st'`, `stk''`] >>
      gvs[execute_plan_append, execute_plan_def, exec_stack_op_def,
          Abbr `mid`]) >>
  `w2n src + w2n sz > LENGTH vs.vs_returndata` by simp[] >>
  drule_all rf_copy_fault_boundary >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qpat_assum `asm_steps _ _ _ (LENGTH _) _ = AsmOK mid`
    (mp_then Any (qspec_then `1` assume_tac) asm_steps_add_ok) >>
  qexists_tac `st'` >>
  gvs[execute_plan_append, execute_plan_def, exec_stack_op_def,
      Abbr `mid`]
QED

Theorem rf_inventory_inv_input_value:
  rf_inventory_inv fn ra lo entry ps s /\
  (is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)
Proof
  strip_tac >> Cases_on `is_var_operand op`
  >- metis_tac[rf_inventory_inv_def] >>
  Cases_on `op` >>
  gvs[stackPlanTypesTheory.is_var_operand_def, Once normalize_operand_def,
    codegenRelTheory.operand_val_def, venomStateTheory.eval_operand_def]
QED

Theorem rf_entry_copy_prepared:
  !base.
  codegen_ready_fn fn /\ generated_plan_state_wf base ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (ins ++ ros))) st =
      AsmOK (st with <|as_stack := stk' ++ rest;
        as_pc := st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros))|>) /\
    plan_stack_rel lo (frame_view fn ra vs)
      (stack_pop 3 ps2.ps_stack ++ [zop;sop;dop]) stk' /\
    asm_block_at prog
      (st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros)))
      [AsmOp "RETURNDATACOPY"] /\
    ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
    ps' = release_dead_spills nl
      (ps2 with ps_stack := stack_pop 3 ps2.ps_stack) /\
    dop <> dead_stack_marker /\ sop <> dead_stack_marker /\
    zop <> dead_stack_marker
Proof
  gen_tac >> strip_tac >>
  `rf_spills_separated ps` by metis_tac[rf_spills_separated_entry] >>
  `rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs` by
    (irule rf_inventory_inv_entry >> first_assum ACCEPT_TAC) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >> irule rf_inventory_inv_input_value >>
     qexists_tac `ps` >> simp[]) >>
  drule_all rf_suffix_copy_prepared >> simp[]
QED

Theorem rf_entry_copy_execution:
  codegen_ready_fn fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  if w2n src + w2n sz <= LENGTH vs.vs_returndata then
  (?st' stk'.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk' /\
    venom_asm_terminal_rel vs' st' /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) st'.as_memory))
  else
  (?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmFault st' /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) st')
Proof
  strip_tac >>
  `rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs` by
    (irule rf_inventory_inv_entry >> first_assum ACCEPT_TAC) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >> irule rf_inventory_inv_input_value >>
     qexists_tac `ps` >> simp[]) >>
  drule_all rf_suffix_copy_execution >> simp[]
QED

Theorem rf_suffix_copy_success_invariants:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI) /\
  get_instruction bb k = SOME inst /\ k <= j /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  LENGTH (compute_operands inst) <= 16 /\
  rf_spills_separated ps /\
  rf_value_inv fn ra bb j lo entry k s /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
    halting term bb.bb_label ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  step_inst fuel ctx inst s = OK s' ==>
  rf_spills_separated ps' /\
  rf_value_inv fn ra bb j lo entry (SUC k) (s' with vs_inst_idx := SUC k) /\
  rf_inventory_inv fn ra lo entry ps' (s' with vs_inst_idx := SUC k) /\
  (!op. rf_live_use bb (SUC k) j op /\ is_var_operand op ==>
    MEM op ps'.ps_stack \/ op IN FDOM ps'.ps_spilled)
Proof
  strip_tac >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule rf_live_use_current >> metis_tac[]) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >> fs[rf_value_inv_def] >> first_x_assum irule >>
     irule rf_live_use_current >> metis_tac[]) >>
  `s'.vs_vars = s.vs_vars` by
    (drule_all rf_source_copy_ok_cases >> strip_tac >>
     gvs[venomStateTheory.write_memory_with_expansion_def]) >>
  `!off. ~MEM (SOSpill off) ops` by fs[] >>
  conj_tac >- (drule_all rf_copy_plan_spills_separated >> simp[]) >>
  conj_tac >- (drule_all rf_value_inv_returndatacopy >> simp[]) >>
  conj_tac
  >- (simp[] >>
      drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        rf_copy_plan_inventory >> simp[] >>
      disch_then irule >> asm_rewrite_tac[] >>
      qexists_tac `s` >> simp[]) >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    rf_copy_ready_future_owned >> simp[] >>
  disch_then (qspec_then `j` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem rf_copy_success_invariants:
  !base.
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  (!r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI) /\
  get_instruction bb k = SOME inst /\ k <= j /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  LENGTH (compute_operands inst) <= 16 /\
  generated_plan_state_wf base ps /\
  rf_value_inv fn ra bb j lo entry k s /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
    halting term bb.bb_label ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  step_inst fuel ctx inst s = OK s' ==>
  generated_plan_state_wf base ps' /\
  rf_value_inv fn ra bb j lo entry (SUC k) (s' with vs_inst_idx := SUC k) /\
  rf_inventory_inv fn ra lo entry ps' (s' with vs_inst_idx := SUC k) /\
  (!op. rf_live_use bb (SUC k) j op /\ is_var_operand op ==>
    MEM op ps'.ps_stack \/ op IN FDOM ps'.ps_spilled)
Proof
  gen_tac >> strip_tac >>
  `rf_spills_separated ps` by metis_tac[rf_spills_separated_entry] >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule rf_live_use_current >> metis_tac[]) >>
  conj_tac >- (drule_all rf_copy_plan_generated_wf >> simp[]) >>
  drule_all rf_suffix_copy_success_invariants >> simp[]
QED

Theorem rf_take_padding_cong:
  TAKE n xs = TAKE n ys ==> TAKE n (xs ++ pad) = TAKE n (ys ++ pad)
Proof
  strip_tac >>
  `LENGTH (TAKE n xs) = LENGTH (TAKE n ys)` by simp[] >>
  `n - LENGTH xs = n - LENGTH ys` by
    (fs[LENGTH_TAKE_EQ] >> rpt IF_CASES_TAC >> gvs[] >> decide_tac) >>
  simp[TAKE_APPEND]
QED

Theorem rf_revert_stack_frame:
  plan_stack_rel lo current (tail ++ [zop;dop]) stk /\
  dop <> dead_stack_marker /\ zop <> dead_stack_marker /\
  operand_val current lo dop = SOME dst /\
  operand_val current lo zop = SOME sz /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  asm_block_at prog st.as_pc [AsmOp "REVERT"] ==>
  ?out. asm_steps lo o2pc prog 1 st = AsmRevert out /\
    venom_asm_terminal_rel
      (revert_state (set_returndata
        (TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory ++
          REPLICATE (w2n sz) 0w)) vs)) out
Proof
  strip_tac >>
  `?d z residual. stk = d :: z :: residual /\
    operand_val current lo dop = SOME d /\
    operand_val current lo zop = SOME z` by
    (irule asm_stack_top2_from_plan >> simp[] >>
     qexists_tac `tail` >> simp[]) >>
  gvs[] >> irule terminal_revert_step_payload >> simp[] >>
  irule rf_take_padding_cong >> first_assum ACCEPT_TAC
QED

Theorem rf_suffix_revert_execution:
  codegen_ready_fn fn /\ rf_spills_separated ps /\
  inst.inst_opcode = REVERT /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  ?out. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmRevert out /\
    venom_asm_terminal_rel
      (revert_state (set_returndata
        (TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory ++
          REPLICATE (w2n sz) 0w)) vs)) out
Proof
  strip_tac >>
  Cases_on `emit_input_plan REVERT (compute_operands inst) nl ps` >>
  rename1 `_ = (ins,ps1)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) ps1` >>
  rename1 `_ = (ros,ps2)` >>
  `compute_operands inst = [zop;dop]` by
    simp[compute_operands_def, python_stack_operands_def,
      venomInstTheory.ir_specific_operand_order_def] >>
  `ops = ins ++ ros ++ [SOEmit "REVERT"]` by
    gvs[generate_regular_inst_plan_def, venomEffectsTheory.is_commutative_def,
      generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp (ins ++ ros)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp (ins ++ ros)))
     [AsmOp "REVERT"]` by
    gvs[execute_plan_append, execute_plan_def, exec_stack_op_def, asm_block_at_append] >>
  `!off. ~MEM (SOSpill off) (ins ++ ros) /\
    ~MEM (SORestore off) (ins ++ ros)` by fs[MEM_APPEND] >>
  `REVERT <> INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
   EVERY (\op. ~is_label_operand op) (compute_operands inst)` by gvs[] >>
  drule_all rf_suffix_preparation_execution >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `AsmOK mid` >>
  `plan_stack_rel lo (frame_view fn ra vs)
    (stack_pop 2 ps2.ps_stack ++ [zop;dop]) stk'` by
    (qpat_x_assum `ps2.ps_stack = _` mp_tac >> simp[] >>
     disch_then (fn th => pure_once_rewrite_tac[GSYM th]) >> asm_rewrite_tac[]) >>
  qpat_x_assum `ps2.ps_stack = _` kall_tac >>
  `mid.as_stack = stk' ++ rest /\ venom_asm_terminal_rel vs mid /\
   TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory) =
     TAKE (w2n sz) (DROP (w2n dst) mid.as_memory) /\
   asm_block_at prog mid.as_pc [AsmOp "REVERT"]` by
    (simp[Abbr `mid`] >> fs[venom_asm_terminal_rel_def]) >>
  `dop <> dead_stack_marker /\ zop <> dead_stack_marker` by
    (rpt strip_tac >> gvs[dead_stack_marker_def,
      stackPlanTypesTheory.is_label_operand_def]) >>
  drule_all rf_revert_stack_frame >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `out` >> conj_tac >- (
    qpat_assum `asm_steps _ _ _ (LENGTH _) _ = AsmOK mid`
      (mp_then Any (qspec_then `1` assume_tac) asm_steps_add_ok) >>
    gvs[execute_plan_append, execute_plan_def, exec_stack_op_def]) >>
  first_assum ACCEPT_TAC
QED

Theorem rf_forward_revert_range:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [cdop;csop;czop] /\
  get_instruction bb j = SOME rev /\ rev.inst_operands = [dop;zop] /\
  rf_value_inv fn ra bb j lo entry j vs /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] cdop) = SOME dst /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] czop) = SOME sz ==>
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz
Proof
  strip_tac >> drule_all rf_forward_normalized_operands >> strip_tac >>
  `rev.inst_opcode = REVERT` by fs[revert_forward_pair_def] >>
  `!op. MEM op [dop;zop] ==>
    operand_val (frame_view fn ra vs) lo op =
      operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `rf_value_inv _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[rf_value_inv_def] >>
     disch_then (qspec_then `op` mp_tac) >>
     impl_tac >- (irule rf_live_use_current >>
       simp[compute_operands_def, python_stack_operands_def,
         venomInstTheory.ir_specific_operand_order_def] >> fs[]) >> simp[]) >>
  gvs[]
QED

Theorem rf_suffix_revert_abort:
  codegen_ready_fn fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = REVERT /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  a = Revert_abort /\
  ?out. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
    AsmRevert out /\ venom_asm_terminal_rel vs' out
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    operand_val (frame_view fn ra vs) lo op = eval_operand op vs` by
    (rpt strip_tac >> irule rf_ordinary_operand_value >>
     conj_tac >- simp[] >> conj_tac >- fs[EVERY_MEM] >>
     qexists_tac `inst` >> gvs[]) >>
  `eval_operand dop vs = SOME dst /\ eval_operand zop vs = SOME sz` by
    metis_tac[MEM] >>
  `a = Revert_abort /\ vs' = revert_state (set_returndata
     (TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory ++ REPLICATE (w2n sz) 0w)) vs)` by
    gvs[Once step_inst_def, step_inst_base_def] >>
  simp[] >> drule_all rf_suffix_revert_execution >> simp[]
QED

Theorem rf_strict_suffix_abort:
  !k s st ps stk ops ps_end.
  codegen_ready_fn fn /\ opaque_use_ok fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ i < k /\ k <= j /\ s.vs_inst_idx = k /\
  LENGTH (get_params bb.bb_instructions) <= k /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [cdop;csop;czop] /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] cdop) = SOME dst /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] czop) = SOME sz /\
  EVERY (\ti. EVERY (\op. ~is_label_operand op) ti.inst_operands)
    (DROP i bb.bb_instructions) /\
  rf_spills_separated ps /\ rf_value_inv fn ra bb j lo entry k s /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel s st /\
  TAKE (w2n sz) (DROP (w2n dst) s.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (k - LENGTH (get_params bb.bb_instructions)) (DROP k bb.bb_instructions)
    ps = SOME (ops,ps_end) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
  exec_block fuel ctx bb s = Abort a s_end ==>
  a = Revert_abort /\
  ?n out. asm_steps lo o2pc prog n st = AsmRevert out /\
    venom_asm_terminal_rel s_end out
Proof
  measureInduct_on `j - k` >> rpt gen_tac >> strip_tac >> disch_tac >>
  `i <= k` by decide_tac >>
  `?inst. get_instruction bb k = SOME inst` by
    (irule rf_forward_instruction_exists >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists_tac `bb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  drule_all rf_forward_instruction_opcode >> strip_tac >>
  drule_all rf_forward_instruction_shape >> strip_tac >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule rf_suffix_instruction_no_labels >> metis_tac[]) >>
  `!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)` by
    (rpt strip_tac >> fs[rf_value_inv_def] >> first_x_assum irule >>
     irule rf_live_use_current >> metis_tac[]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule rf_live_use_current >> metis_tac[]) >>
  drule_all rf_block_plan_step >> strip_tac >>
  `generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
     (cfg_analyze fn) fn inst
     (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) (bb_is_halting bb)
     (case DROP (SUC k) bb.bb_instructions of
        [] => F | next_i::tail => is_terminator next_i.inst_opcode)
     bb.bb_label ps = (step_ops,ps1)` by
    (irule rf_forward_regular_plan_result >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`,`i`,`j`,`k`] >> simp[]) >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp step_ops) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp step_ops))
     (execute_plan initial_fmp rest_ops)` by
    gvs[execute_plan_append, asm_block_at_append] >>
  `!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops` by
    fs[MEM_APPEND] >>
  Cases_on `k = j` >- suspend "revert" >>
  suspend "assign"
QED

Resume rf_strict_suffix_abort[revert]:
  pop_last_assum kall_tac >>
  `inst.inst_opcode = REVERT /\ inst.inst_outputs = []` by gvs[] >>
  `?dop zop. inst.inst_operands = [dop;zop]` by
    gvs[LENGTH_EQ_NUM_compute] >>
  `operand_val (frame_view fn ra s) lo dop = SOME dst /\
   operand_val (frame_view fn ra s) lo zop = SOME sz` by
    (irule rf_forward_revert_range >> metis_tac[]) >>
  `step_inst fuel ctx inst s = Abort a s_end` by
    (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
     gvs[Once exec_block_def, is_terminator_def, AllCaseEqs()]) >>
  drule_all rf_suffix_revert_abort >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  simp[] >> qexistsl_tac [`LENGTH (execute_plan initial_fmp step_ops)`,`out`] >> simp[]
QED

Resume rf_strict_suffix_abort[assign]:
  `k < j /\ inst.inst_opcode = ASSIGN` by gvs[] >>
  `?rhs out. inst.inst_operands = [rhs] /\ inst.inst_outputs = [out]` by
    metis_tac[] >>
  `~is_label_operand rhs` by fs[] >>
  `?s'. step_inst fuel ctx inst s = OK s' /\
    exec_block fuel ctx bb (s' with vs_inst_idx := SUC k) = Abort a s_end` by
    (qpat_x_assum `!y. _ ==> !s st ps stk ops ps_end. _` kall_tac >>
     qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
     simp[Once exec_block_def, is_terminator_def] >>
     Cases_on `eval_operand rhs s` >>
     simp[step_inst_def, step_inst_base_def]) >>
  `!r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI` by
    (rpt strip_tac >>
     `ti.inst_opcode =
       (if r = i then RETURNDATACOPY else if r = j then REVERT else ASSIGN)` by
       (irule rf_forward_instruction_opcode >>
        conj_tac >- decide_tac >> simp[] >>
        qexists_tac `bb` >> simp[]) >>
     Cases_on `r = i` >> fs[] >> Cases_on `r = j` >> fs[]) >>
  drule_all rf_assign_success_invariants >> strip_tac >>
  `is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled` by
    (strip_tac >> first_x_assum irule >>
     simp[compute_operands_def, python_stack_operands_def]) >>
  `operand_val (frame_view fn ra s) lo rhs =
   operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs)` by
    (first_x_assum irule >> simp[compute_operands_def, python_stack_operands_def]) >>
  drule_all rf_assign_plan_execution >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `AsmOK mid` >>
  `s'.vs_memory = s.vs_memory /\
   venom_asm_terminal_rel (s' with vs_inst_idx := SUC k) mid /\
   plan_stack_rel lo (frame_view fn ra (s' with vs_inst_idx := SUC k))
     ps1.ps_stack stk'` by
    (qpat_x_assum `!y. _ ==> !s st ps stk ops ps_end. _` kall_tac >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[step_inst_def, step_inst_base_def, AllCaseEqs()] >>
     strip_tac >> gvs[] >>
     fs[venom_asm_terminal_rel_def, venomStateTheory.update_var_def, Abbr `mid`] >>
     fs[codegenRelTheory.plan_stack_rel_def] >> rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH ps1.ps_stack ==> _`
       (qspec_then `i'` mp_tac) >> simp[] >>
     Cases_on `EL i' (REVERSE ps1.ps_stack)` >>
     simp[frame_view_def, codegenRelTheory.operand_val_def,
       venomStateTheory.lookup_var_def]) >>
  `j - SUC k < j - k` by decide_tac >>
  qpat_x_assum `!y. _ ==> !s st ps stk ops ps_end. _`
    (qspec_then `SUC k` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`s' with vs_inst_idx := SUC k`, `mid`, `ps1`,
    `stk'`, `rest_ops`, `ps_end`] mp_tac) >>
  `!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops` by
    fs[MEM_APPEND] >>
  `asm_block_at prog mid.as_pc (execute_plan initial_fmp rest_ops)` by
    (simp[Abbr `mid`] >>
     once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  `mid.as_stack = stk' ++ rest /\ mid.as_memory = st.as_memory` by
    simp[Abbr `mid`] >>
  simp[] >> strip_tac >> simp[] >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp step_ops) + n`, `out'`] >>
  simp[] >>
  qpat_x_assum `asm_steps _ _ _ _ st = AsmOK _`
    (mp_then Any (qspec_then `n` mp_tac) asm_steps_add_ok) >>
  simp[]
QED

Finalise rf_strict_suffix_abort

Theorem rf_owned_operand_defined:
  plan_stack_rel lo view ps.ps_stack stk /\
  plan_spill_rel lo view ps.ps_spilled mem /\
  (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  op <> dead_stack_marker ==>
  ?v. operand_val view lo op = SOME v
Proof
  strip_tac
  >- (`MEM op (REVERSE ps.ps_stack)` by simp[] >>
      `?n. n < LENGTH (REVERSE ps.ps_stack) /\
        op = EL n (REVERSE ps.ps_stack)` by metis_tac[MEM_EL] >>
      fs[plan_stack_rel_def] >>
      first_x_assum (qspec_then `n` mp_tac) >> metis_tac[]) >>
  fs[plan_spill_rel_def, finite_mapTheory.FLOOKUP_DEF] >>
  first_x_assum (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem rf_frame_input_defined:
  !ctx cp lo fn ra rest mem0 ps vs st op.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  ~is_label_operand op /\
  (is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  ?v. operand_val (frame_view fn ra vs) lo op = SOME v
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  gvs[stackPlanTypesTheory.is_var_operand_def,
      stackPlanTypesTheory.is_label_operand_def]
  >- simp[operand_val_def] >>
  irule rf_owned_operand_defined >>
  simp[dead_stack_marker_def] >>
  fs[frameRelTheory.fn_frame_inv_def,
     contextCodegenRelTheory.context_venom_asm_rel_def] >>
  qexistsl_tac [`st.as_memory`, `ps`, `top`] >> simp[]
QED

Theorem rf_entry_copy_setup:
  !ctx cp lo prog liveness dfg cfg fn bb i j ps vs ast ops
   ps_end ra rest mem0.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ rf_spills_separated ps /\
    (!k inst op. i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    ?inst dop sop zop dst src sz step_ops rest_ops ps1 stk.
      lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ i < j /\
      get_instruction bb i = SOME inst /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
      inst.inst_operands = [dop;sop;zop] /\
      EVERY (\op. ~is_label_operand op) inst.inst_operands /\
      operand_val (frame_view fn ra vs) lo dop = SOME dst /\
      operand_val (frame_view fn ra vs) lo sop = SOME src /\
      operand_val (frame_view fn ra vs) lo zop = SOME sz /\
      (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      rf_spills_separated ps /\
      rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs /\
      rf_value_inv fn ra bb j lo (frame_view fn ra vs) i vs /\
      (!op. rf_live_use bb i j op /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      ast.as_stack = stk ++ rest /\
      plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
      venom_asm_terminal_rel vs ast /\ ops = step_ops ++ rest_ops /\
      generate_regular_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (SUC i)) (bb_is_halting bb)
        (case DROP (SUC i) bb.bb_instructions of
           [] => F | next_i :: _ => is_terminator next_i.inst_opcode)
        bb.bb_label ps = (step_ops,ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (SUC i - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC i) bb.bb_instructions) ps1 = SOME (rest_ops,ps_end) /\
      (!off. ~MEM (SORestore off) step_ops /\ ~MEM (SOSpill off) step_ops /\
             ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) /\
      asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp step_ops) /\
      asm_block_at prog (ast.as_pc + LENGTH (execute_plan cp.cp_initial_fmp step_ops))
        (execute_plan cp.cp_initial_fmp rest_ops)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    metis_tac[makeSsaHelperTheory.lookup_block_label] >>
  `i < j` by fs[revert_forward_pair_def] >>
  `i <= i /\ i <= j` by decide_tac >>
  `?inst. get_instruction bb i = SOME inst` by
    (irule rf_forward_instruction_exists >> qexistsl_tac [`i`, `j`] >> simp[]) >>
  `inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
   LENGTH inst.inst_operands = 3` by
    (drule_all rf_forward_instruction_shape >> strip_tac >>
     drule_all rf_forward_instruction_opcode >> simp[]) >>
  `?dop sop zop. inst.inst_operands = [dop;sop;zop]` by
    fs[listTheory.LENGTH_EQ_NUM_compute] >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule rf_suffix_instruction_no_labels >> metis_tac[]) >>
  `rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs` by
    (irule rf_inventory_inv_entry >> gvs[]) >>
  `!op. rf_live_use bb i j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> fs[rf_live_use_def] >> first_x_assum irule >> metis_tac[]) >>
  `rf_value_inv fn ra bb j lo (frame_view fn ra vs) i vs` by
    (irule rf_value_inv_entry >>
     qexists_tac `\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` >>
     gvs[] >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all rf_block_plan_step >> strip_tac >>
  `generate_regular_inst_plan liveness dfg cfg fn inst
    (live_vars_at liveness bb.bb_label (SUC i)) (bb_is_halting bb)
    (case DROP (SUC i) bb.bb_instructions of
       [] => F | next_i :: _ => is_terminator next_i.inst_opcode)
    bb.bb_label ps = (step_ops,ps1)` by
    (irule rf_forward_regular_plan_result >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`, `i`, `j`, `i`] >> simp[]) >>
  `?stk. ast.as_stack = stk ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk` by
    (qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[frameRelTheory.fn_frame_inv_def, contextCodegenRelTheory.context_venom_asm_rel_def] >>
     metis_tac[]) >>
  `venom_asm_terminal_rel vs ast` by
    (fs[frameRelTheory.fn_frame_inv_def, contextCodegenRelTheory.context_venom_asm_rel_def,
        venom_asm_terminal_rel_def, frameRelTheory.frame_view_def]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule rf_live_use_current >> simp[] >> qexists_tac `inst` >> simp[]) >>
  `!op. MEM op inst.inst_operands ==>
    ?v. operand_val (frame_view fn ra vs) lo op = SOME v` by
    (rpt strip_tac >> irule rf_frame_input_defined >>
     conj_tac >- gvs[EVERY_MEM] >>
     qexistsl_tac [`cp'`, `ctx`, `mem0`, `ps`, `rest`, `ast`] >>
     asm_rewrite_tac[] >>
     strip_tac >> first_x_assum irule >>
     gvs[compute_operands_def, python_stack_operands_def,
         venomInstTheory.ir_specific_operand_order_def]) >>
  `?dst src sz.
    operand_val (frame_view fn ra vs) lo dop = SOME dst /\
    operand_val (frame_view fn ra vs) lo sop = SOME src /\
    operand_val (frame_view fn ra vs) lo zop = SOME sz` by
    metis_tac[listTheory.MEM] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
     qexists_tac `bb` >> conj_tac >- metis_tac[lookup_block_MEM] >>
     gvs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  qexistsl_tac [`inst`, `dop`, `sop`, `zop`, `dst`, `src`, `sz`,
    `step_ops`, `rest_ops`, `ps1`, `stk`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  fs[execute_plan_append, asm_block_at_append]
QED

Theorem rf_entry_forward_abort:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j ps vs ast ops
   ps_end ra rest mem0 a vs_end.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ rf_spills_separated ps /\
    (!k inst op. i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    exec_block fuel ctx bb vs = Abort a vs_end ==>
    ?n ast_end.
      ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
       (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
      venom_asm_terminal_rel vs_end ast_end
Proof
  rpt gen_tac >> strip_tac >>
  drule_all rf_entry_copy_setup >> strip_tac >>
  drule_all rf_copy_source_alignment >> disch_then (assume_tac o GSYM) >>
  Cases_on `emit_input_plan RETURNDATACOPY (compute_operands inst)
    (live_vars_at liveness bb.bb_label (SUC i)) ps` >>
  rename1 `_ = (ins,prep)` >>
  Cases_on `reorder_plan (dfg_build_function fn) (compute_operands inst) prep` >>
  rename1 `_ = (ros,arr)` >>
  qpat_x_assum `liveness = _` SUBST_ALL_TAC >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!k inst op. _` kall_tac >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ (DROP i _) _ = _` kall_tac >>
  qabbrev_tac `copy = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs` >>
  `copy = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs` by simp[Abbr `copy`] >>
  `!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops` by
    (qpat_x_assum `!off. _ /\ _ /\ _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  drule_all rf_entry_copy_execution >>
  disch_then (qspec_then `o2pc` mp_tac) >>
  reverse (Cases_on `w2n src + w2n sz <= LENGTH vs.vs_returndata`) >>
  pure_asm_rewrite_tac[COND_CLAUSES] >> strip_tac
  >- (`a = ExHalt_abort /\ vs_end = halt_state (set_returndata [] vs)` by
        (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
         qpat_x_assum `!fuel ctx. _ = step_inst _ _ _ _` mp_tac >>
         qpat_x_assum `get_instruction bb i = _` mp_tac >>
         qpat_x_assum `vs.vs_inst_idx = i` mp_tac >>
         qpat_x_assum `~(w2n src + w2n sz <= _)` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         qpat_x_assum `!fuel ctx. _ = step_inst _ _ _ _`
           (assume_tac o GSYM) >>
         gvs[Once exec_block_def]) >>
      metis_tac[]) >>
  `step_inst fuel ctx inst vs = OK copy` by
    (qpat_x_assum `!fuel ctx. _ = step_inst _ _ _ _` mp_tac >>
     qpat_x_assum `w2n src + w2n sz <= _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `exec_block fuel ctx bb (copy with vs_inst_idx := SUC i) = Abort a vs_end` by
    (qpat_x_assum `exec_block fuel ctx bb vs = _` mp_tac >>
     qpat_x_assum `step_inst fuel ctx inst vs = OK copy` mp_tac >>
     qpat_x_assum `get_instruction bb i = _` mp_tac >>
     qpat_x_assum `vs.vs_inst_idx = i` mp_tac >>
     qpat_x_assum `inst.inst_opcode = RETURNDATACOPY` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[Once exec_block_def, is_terminator_def]) >>
  `LENGTH (compute_operands inst) <= 16` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  `!r ti. SUC i <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
     ti.inst_opcode <> PHI` by
    (rpt strip_tac >> `i <= r` by decide_tac >>
     drule_all rf_forward_instruction_opcode >>
     simp[] >> rpt IF_CASES_TAC >> simp[]) >>
  `i <= j` by decide_tac >>
  drule_all rf_suffix_copy_success_invariants >> strip_tac >>
  `operand_val (frame_view fn ra vs) lo
     (normalize_operand (dfg_build_function fn) [] dop) = SOME dst /\
   operand_val (frame_view fn ra vs) lo
     (normalize_operand (dfg_build_function fn) [] zop) = SOME sz` by
    (qpat_x_assum `rf_value_inv _ _ _ _ _ _ i vs` mp_tac >>
     simp[rf_value_inv_def] >> strip_tac >>
     `rf_live_use bb i j dop /\ rf_live_use bb i j zop` by
       (conj_tac >> (irule rf_live_use_current >>
        (conj_tac >- decide_tac) >> qexists_tac `inst` >>
        simp[compute_operands_def, python_stack_operands_def,
          ir_specific_operand_order_def])) >>
     metis_tac[]) >>
  `i < SUC i /\ SUC i <= j /\ LENGTH (get_params bb.bb_instructions) <= SUC i` by decide_tac >>
  `!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops` by
    (qpat_x_assum `!off. _ /\ _ /\ _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `asm_block_at prog st'.as_pc (execute_plan cp'.cp_initial_fmp rest_ops)` by
    metis_tac[] >>
  `plan_stack_rel lo (frame_view fn ra (copy with vs_inst_idx := SUC i)) ps1.ps_stack stk' /\
   venom_asm_terminal_rel (copy with vs_inst_idx := SUC i) st' /\
   TAKE (w2n sz) (DROP (w2n dst) (copy with vs_inst_idx := SUC i).vs_memory) =
     TAKE (w2n sz) (DROP (w2n dst) st'.as_memory)` by
    (qpat_x_assum `copy = write_memory_with_expansion _ _ _` SUBST_ALL_TAC >>
     qpat_x_assum `plan_stack_rel _ _ ps1.ps_stack _` mp_tac >>
     qpat_x_assum `venom_asm_terminal_rel (write_memory_with_expansion _ _ _) _` mp_tac >>
     qpat_x_assum `TAKE _ (DROP _ _.vs_memory) = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venom_asm_terminal_rel_def, codegenRelTheory.plan_stack_rel_def,
       frame_view_def] >> rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH ps1.ps_stack ==> _`
       (qspec_then `i'` mp_tac) >> simp[] >>
     Cases_on `EL i' (REVERSE ps1.ps_stack)` >>
     simp[codegenRelTheory.operand_val_def, venomStateTheory.lookup_var_def]) >>
  `(copy with vs_inst_idx := SUC i).vs_inst_idx = SUC i` by simp[] >>
  drule_all rf_strict_suffix_abort >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexistsl_tac [`LENGTH (execute_plan cp'.cp_initial_fmp step_ops) + n`, `out`] >>
  simp[] >>
  qpat_x_assum `asm_steps _ _ _ _ ast = AsmOK _`
    (mp_then Any (qspec_then `n` mp_tac) asm_steps_add_ok) >>
  simp[]
QED
