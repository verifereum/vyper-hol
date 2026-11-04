(* Structural boundaries for revert forwarding. *)
Theory fnFrameStepsRevertForward
Ancestors
  contextCodegenRel dfgDefs list dfgAnalysisProps allocaRemapSSA venomWf
  stackPlanGen venomExecProofs removeUnusedSsaProofs frameRel
  frameViewFacts instSimHelpers emitSim venomExecSemantics venomInst
  strongPrefixSim asmFrameHelpers planExec prefixExec stackOpAsmSim
  stackOpSim blockSimHelpers asmSem stackModel rich_list codegenRel planWf

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
