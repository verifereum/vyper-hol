(* Structural boundaries for revert forwarding. *)
Theory fnFrameStepsRevertForward
Ancestors
  contextCodegenRel dfgDefs list dfgAnalysisProps allocaRemapSSA venomWf
  stackPlanGen venomExecProofs removeUnusedSsaProofs frameRel

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
