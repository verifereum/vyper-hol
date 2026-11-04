(* Structural boundaries for revert forwarding. *)
Theory fnFrameStepsRevertForward
Ancestors
  contextCodegenRel dfgDefs list dfgAnalysisProps allocaRemapSSA venomWf
  stackPlanGen venomExecProofs

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
