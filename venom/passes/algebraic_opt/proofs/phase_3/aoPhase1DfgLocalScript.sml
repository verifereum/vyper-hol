(* Phase 1 (ao_handle_offset_inst) preserves dfg_block_local.
 *
 * ao_handle_offset_inst rewrites only ADD [Label l; Lit v] into
 * OFFSET [Lit v; Label l].  OFFSET is NOT a dfg_tracked_opcode and the
 * rewritten instruction has no Var operands, so the structural
 * dfg_block_local constraint (tracked-opcode operands defined earlier in
 * the same block) is preserved.
 *
 * TOP-LEVEL: ao_phase1_preserves_dfg_block_local
 *)

Theory aoPhase1DfgLocal
Ancestors
  algebraicOptDefs dfgSoundStep dfgDefs dfgAnalysisProps
  venomInst venomWf list rich_list finite_map
Libs
  pairLib BasicProvers

(* ===== ao_handle_offset_inst structural facts ===== *)

Triviality ho_outputs[local]:
  !inst. (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >> every_case_tac >> simp[]
QED

Triviality ho_id[local]:
  !inst. (ao_handle_offset_inst inst).inst_id = inst.inst_id
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >> every_case_tac >> simp[]
QED

(* A tracked-opcode instruction is never the OFFSET-rewritten one. *)
Triviality ho_tracked_id[local]:
  !inst. dfg_tracked_opcode (ao_handle_offset_inst inst).inst_opcode ==>
         ao_handle_offset_inst inst = inst
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  every_case_tac >> simp[dfg_tracked_opcode_def]
QED

(* ===== dfg_defs correspondence under MAP ao_handle_offset_inst ===== *)

Triviality add_uses_defs[local]:
  !vs dfg inst. (dfg_add_uses dfg vs inst).dfg_defs = dfg.dfg_defs
Proof
  Induct >> simp[dfg_add_uses_def] >> rpt strip_tac >>
  `(dfg_add_use dfg h inst).dfg_defs = dfg.dfg_defs` by
    (simp[dfg_add_use_def] >> rw[]) >>
  simp[]
QED

Triviality add_defs_corr[local]:
  !outs inst dfg1 dfg2.
    (!w. FLOOKUP dfg2.dfg_defs w =
         OPTION_MAP ao_handle_offset_inst (FLOOKUP dfg1.dfg_defs w)) ==>
    !w. FLOOKUP (dfg_add_defs dfg2 outs (ao_handle_offset_inst inst)).dfg_defs w =
        OPTION_MAP ao_handle_offset_inst
          (FLOOKUP (dfg_add_defs dfg1 outs inst).dfg_defs w)
Proof
  Induct >> simp[dfg_add_defs_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`inst`,
    `dfg1 with dfg_defs := dfg1.dfg_defs |+ (h, inst)`,
    `dfg2 with dfg_defs := dfg2.dfg_defs |+ (h, ao_handle_offset_inst inst)`]
    mp_tac) >>
  impl_tac
  >- (gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> rw[]) >>
  disch_then (qspec_then `w` mp_tac) >> simp[]
QED

Triviality add_inst_corr[local]:
  !inst dfg1 dfg2.
    (!w. FLOOKUP dfg2.dfg_defs w =
         OPTION_MAP ao_handle_offset_inst (FLOOKUP dfg1.dfg_defs w)) ==>
    !w. FLOOKUP (dfg_add_inst dfg2 (ao_handle_offset_inst inst)).dfg_defs w =
        OPTION_MAP ao_handle_offset_inst
          (FLOOKUP (dfg_add_inst dfg1 inst).dfg_defs w)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  simp[dfg_add_inst_def, ho_outputs, add_uses_defs] >>
  qspecl_then [`inst.inst_outputs`, `inst`,
    `dfg_add_uses dfg1 (operand_vars inst.inst_operands) inst`,
    `dfg_add_uses dfg2 (operand_vars (ao_handle_offset_inst inst).inst_operands)
       (ao_handle_offset_inst inst)`] mp_tac add_defs_corr >>
  impl_tac >- simp[add_uses_defs] >>
  disch_then (qspec_then `w` mp_tac) >> simp[]
QED

Triviality build_rev_corr[local]:
  !l dfg1 dfg2.
    (!w. FLOOKUP dfg2.dfg_defs w =
         OPTION_MAP ao_handle_offset_inst (FLOOKUP dfg1.dfg_defs w)) ==>
    !w. FLOOKUP (dfg_build_insts_rev dfg2
          (MAP ao_handle_offset_inst l)).dfg_defs w =
        OPTION_MAP ao_handle_offset_inst
          (FLOOKUP (dfg_build_insts_rev dfg1 l).dfg_defs w)
Proof
  Induct >> simp[dfg_build_insts_rev_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then
    [`dfg_add_inst dfg1 h`,
     `dfg_add_inst dfg2 (ao_handle_offset_inst h)`] mp_tac) >>
  impl_tac >- (gen_tac >> irule add_inst_corr >> simp[]) >>
  disch_then (qspec_then `w` mp_tac) >> simp[]
QED

(* ===== fn_insts / MAP commutation ===== *)

Triviality fn_insts_map[local]:
  !bbs. fn_insts_blocks (MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) bbs) =
        MAP ao_handle_offset_inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.MAP_APPEND]
QED

Triviality map_id_fn_insts[local]:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
        FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.MAP_APPEND]
QED

(* ===== main correspondence ===== *)

Theorem dfg_get_def_phase1[local]:
  !fn v.
    dfg_get_def (dfg_build_function
      (fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks)) v =
    OPTION_MAP ao_handle_offset_inst
      (dfg_get_def (dfg_build_function fn) v)
Proof
  rpt strip_tac >>
  simp[dfg_get_def_def, dfg_build_function_def, fn_insts_def, fn_insts_map,
       dfg_build_insts_def, listTheory.MAP_REVERSE] >>
  qspecl_then [`REVERSE (fn_insts_blocks fn.fn_blocks)`, `dfg_empty`, `dfg_empty`]
    mp_tac build_rev_corr >>
  impl_tac >- simp[dfg_empty_def, finite_mapTheory.FLOOKUP_EMPTY] >>
  disch_then (qspec_then `v` mp_tac) >> simp[listTheory.MAP_REVERSE]
QED

(* ===== inst-id uniqueness helper ===== *)

Triviality all_distinct_map_inj[local]:
  !l f x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ f x = f y ==> x = y
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  fs[listTheory.MEM_MAP] >> metis_tac[]
QED

Triviality distinct_id_eq[local]:
  !fn a b.
    wf_function fn /\ MEM a (fn_insts fn) /\ MEM b (fn_insts fn) /\
    a.inst_id = b.inst_id ==> a = b
Proof
  rpt strip_tac >>
  fs[wf_function_def, fn_inst_ids_distinct_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    simp[fn_insts_def, map_id_fn_insts] >>
  metis_tac[all_distinct_map_inj]
QED

(* MEM in a block ==> MEM in fn_insts *)
Triviality mem_block_inst[local]:
  !inst bb fn.
    MEM inst bb.bb_instructions /\ MEM bb fn.fn_blocks ==>
    MEM inst (fn_insts fn)
Proof
  rpt strip_tac >> simp[fn_insts_def] >>
  Induct_on `fn.fn_blocks` >> simp[fn_insts_blocks_def] >> rpt strip_tac >>
  qpat_x_assum `_ = fn.fn_blocks` (SUBST_ALL_TAC o SYM) >>
  gvs[fn_insts_blocks_def, listTheory.MEM_APPEND] >>
  first_x_assum (qspec_then `fn with fn_blocks := v` mp_tac) >> simp[]
QED

(* ===== TOP-LEVEL ===== *)

Theorem ao_phase1_preserves_dfg_block_local:
  !fn.
    wf_function fn /\ dfg_block_local fn ==>
    dfg_block_local (fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks)
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `dfg_block_local fn0` >>
  `!w. dfg_get_def (dfg_build_function fn0) w =
       OPTION_MAP ao_handle_offset_inst
         (dfg_get_def (dfg_build_function fn) w)` by
    (`fn0 = fn with fn_blocks :=
        MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks` by
       simp[Abbr `fn0`] >>
     pop_assum SUBST1_TAC >> gen_tac >>
     MATCH_ACCEPT_TAC dfg_get_def_phase1) >>
  simp[dfg_block_local_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* specialize the def correspondence at v and u, then expose the fn-defs *)
  qpat_assum `!w. dfg_get_def (dfg_build_function fn0) w = _`
    (fn th => assume_tac (Q.SPEC `v` th) >> assume_tac (Q.SPEC `u` th)) >>
  Cases_on `dfg_get_def (dfg_build_function fn) v` >> gvs[] >>
  Cases_on `dfg_get_def (dfg_build_function fn) u` >> gvs[] >>
  rename1 `dfg_get_def (dfg_build_function fn) v = SOME inst_v0` >>
  rename1 `dfg_get_def (dfg_build_function fn) u = SOME inst_u0` >>
  (* inst is tracked, so it is not the OFFSET-rewrite: ho inst_v0 = inst_v0 *)
  `ao_handle_offset_inst inst_v0 = inst_v0` by (irule ho_tracked_id >> gvs[]) >>
  gvs[] >>
  (* recover the original block bb0 that maps to bb *)
  `?bb0. MEM bb0 fn.fn_blocks /\
         bb = bb0 with bb_instructions :=
           MAP ao_handle_offset_inst bb0.bb_instructions` by (
    qpat_x_assum `MEM bb fn0.fn_blocks` mp_tac >>
    simp[Abbr `fn0`, listTheory.MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
    first_assum (irule_at Any) >> simp[]) >>
  (* inst_v0 itself lives in bb0 (tracked ==> not rewritten) *)
  `MEM inst_v0 bb0.bb_instructions` by (
    qpat_x_assum `MEM inst_v0 bb.bb_instructions` mp_tac >>
    qpat_x_assum `bb = _` (fn th => simp[Once th]) >>
    simp[listTheory.MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
    rename1 `inst_v0 = ao_handle_offset_inst x0` >>
    `ao_handle_offset_inst x0 = x0` by (irule ho_tracked_id >> gvs[]) >>
    gvs[]) >>
  (* both defs are instructions of fn *)
  `MEM inst_v0 (fn_insts fn) /\ MEM inst_u0 (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  (* apply block-locality of the original fn *)
  qpat_x_assum `dfg_block_local fn` mp_tac >>
  simp[dfg_block_local_def] >>
  disch_then (qspecl_then [`v`, `inst_v0`, `u`, `inst_u0`] mp_tac) >>
  simp[] >>
  disch_then (qspec_then `bb0` mp_tac) >> simp[] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `bb = _` (fn th => simp[Once th]) >>
      simp[listTheory.MEM_MAP] >> qexists_tac `inst_u0` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH bb.bb_instructions = LENGTH bb0.bb_instructions` by
    (qpat_x_assum `bb = _` (fn th => simp[Once th])) >>
  `i < LENGTH bb0.bb_instructions /\ j < LENGTH bb0.bb_instructions` by gvs[] >>
  `EL i bb.bb_instructions = ao_handle_offset_inst (EL i bb0.bb_instructions) /\
   EL j bb.bb_instructions = ao_handle_offset_inst (EL j bb0.bb_instructions)` by
    (qpat_x_assum `bb = _` SUBST1_TAC >> gvs[listTheory.EL_MAP]) >>
  `MEM (EL i bb0.bb_instructions) (fn_insts fn) /\
   MEM (EL j bb0.bb_instructions) (fn_insts fn)` by
    (conj_tac >> irule mem_block_inst >> qexists_tac `bb0` >>
     simp[listTheory.EL_MEM]) >>
  (* match positions via inst-id uniqueness; the position hyps speak of
     EL _ (MAP ao_handle_offset_inst bb0.bb_instructions) *)
  `ao_handle_offset_inst (EL i bb0.bb_instructions) = ao_handle_offset_inst inst_u0` by (
    qpat_x_assum
      `EL i (MAP ao_handle_offset_inst bb0.bb_instructions) = ao_handle_offset_inst inst_u0`
      mp_tac >> gvs[listTheory.EL_MAP]) >>
  `ao_handle_offset_inst (EL j bb0.bb_instructions) = inst_v0` by (
    qpat_x_assum
      `EL j (MAP ao_handle_offset_inst bb0.bb_instructions) = inst_v0`
      mp_tac >> gvs[listTheory.EL_MAP]) >>
  `(EL i bb0.bb_instructions).inst_id = inst_u0.inst_id` by (
    `(ao_handle_offset_inst (EL i bb0.bb_instructions)).inst_id =
     (ao_handle_offset_inst inst_u0).inst_id` suffices_by fs[ho_id] >>
    AP_TERM_TAC >>
    qpat_x_assum
      `ao_handle_offset_inst (EL i bb0.bb_instructions) = ao_handle_offset_inst inst_u0`
      ACCEPT_TAC) >>
  `(EL j bb0.bb_instructions).inst_id = inst_v0.inst_id` by (
    `(ao_handle_offset_inst (EL j bb0.bb_instructions)).inst_id = inst_v0.inst_id`
       suffices_by fs[ho_id] >>
    qpat_x_assum `ao_handle_offset_inst (EL j bb0.bb_instructions) = inst_v0`
      (fn th => simp[th])) >>
  `EL i bb0.bb_instructions = inst_u0` by metis_tac[distinct_id_eq] >>
  `EL j bb0.bb_instructions = inst_v0` by metis_tac[distinct_id_eq] >>
  first_x_assum irule >> gvs[]
QED

val _ = export_theory();
