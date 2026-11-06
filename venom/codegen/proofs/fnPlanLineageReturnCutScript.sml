Theory fnPlanLineageReturnCut
Ancestors
  fnPlanLineagePath fnPlanLineageCallers fnPlanLineageEdge venomWf
  fnPlanLineageDemand

(* Exact copy of the local rtc_to_fn_path in removeUnusedSsaProofs.
   Its local status prevents importing the fact through the existing ancestor. *)
Theorem rtc_to_fn_path:
  !fn x y. (fn_cfg_edge fn)^* x y ==>
    ?path. is_fn_path fn path /\ path <> [] /\ HD path = x /\ LAST path = y
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[]
  >- (qexists_tac `[x]` >> simp[is_fn_path_def])
  >- (qexists_tac `x::path` >> Cases_on `path` >> gvs[is_fn_path_def])
QED

Theorem fn_path_cut:
  !pre fn x suf.
    is_fn_path fn (pre ++ x::suf) ==>
    is_fn_path fn (pre ++ [x]) /\ is_fn_path fn (x::suf) /\
    (pre <> [] ==> fn_cfg_edge fn (LAST pre) x)
Proof
  Induct >> simp[is_fn_path_def] >>
  rpt gen_tac >> Cases_on `pre` >> gvs[is_fn_path_def] >>
  metis_tac[]
QED

Theorem first_intersection_split:
  !xs ys. (?x. MEM x xs /\ MEM x ys) ==>
    ?pre j post. xs = pre ++ j::post /\ MEM j ys /\
      EVERY (\x. ~MEM x ys) pre
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `MEM h ys`
  >- (qexistsl_tac [`[]`, `h`, `xs`] >> simp[]) >>
  gvs[] >>
  first_x_assum (qspec_then `ys` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl_tac [`h::pre`, `j`, `post`] >> simp[]
QED

Theorem fn_walk_predecessor:
  !tail d j. MEM j tail ==>
    ?pre a post. d::tail = pre ++ a::j::post /\ MEM a (d::tail)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `j = h`
  >- (gvs[] >> qexistsl_tac [`[]`, `d`, `tail`] >> simp[]) >>
  `MEM j tail` by gvs[] >>
  first_x_assum (qspecl_then [`h`, `j`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`d::pre`, `a`, `post`] >> simp[]
QED

Theorem fn_return_intersection:
  !fn entry d tail.
    RTC (fn_cfg_edge fn) entry d /\ tail <> [] /\
    is_fn_path fn (d::tail) /\ LAST tail = d /\
    (!a. ~fn_cfg_edge fn a entry) ==>
    ?before a j after b path.
      d::tail = before ++ a::j::after /\
      fn_cfg_edge fn a j /\ fn_cfg_edge fn b j /\ a <> b /\
      is_fn_path fn path /\ path <> [] /\ HD path = entry /\ LAST path = j /\
      (j = d \/ ~MEM d path)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM d tail` by metis_tac[rich_listTheory.MEM_LAST_NOT_NIL] >>
  `!j. MEM j tail ==> ?a. fn_cfg_edge fn a j` by
    (rpt strip_tac >> drule fn_walk_predecessor >>
     disch_then (qspec_then `d` strip_assume_tac) >>
     `is_fn_path fn (pre ++ a::j::post)` by metis_tac[] >>
     drule fn_path_cut >> simp[is_fn_path_def] >> metis_tac[]) >>
  `~MEM entry tail` by metis_tac[] >>
  drule rtc_to_fn_path >> strip_tac >>
  `?x. MEM x path /\ MEM x tail` by
    (qexists_tac `d` >> metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  qspecl_then [`path`, `tail`] mp_tac first_intersection_split >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `pre <> []` by (Cases_on `pre` >> gvs[]) >>
  `is_fn_path fn (pre ++ [j]) /\ fn_cfg_edge fn (LAST pre) j` by
    (metis_tac[fn_path_cut]) >>
  `~MEM (LAST pre) tail` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  drule fn_walk_predecessor >>
  disch_then (qspec_then `d` strip_assume_tac) >>
  `is_fn_path fn (pre' ++ a::j::post')` by metis_tac[] >>
  `fn_cfg_edge fn a j` by
    (drule fn_path_cut >> simp[is_fn_path_def]) >>
  qexistsl_tac [`pre'`, `a`, `j`, `post'`, `LAST pre`, `pre ++ [j]`] >>
  simp[] >>
  conj_tac >- metis_tac[listTheory.MEM] >>
  conj_tac >- (Cases_on `pre` >> gvs[]) >>
  Cases_on `j = d` >> gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ready_entry_no_incoming:
  !fn entry.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry ==>
    !a. ~fn_cfg_edge fn a entry
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `cfg_preds_of (cfg_analyze fn) entry = []` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def,
         stackPlanGenTheory.codegen_ready_fn_def,
         stackPlanGenTheory.block_entries_ready_def,
         venomInstTheory.entry_block_def, listTheory.NULL_EQ]) >>
  metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze,
            cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond, listTheory.MEM]
QED

Theorem first_return_join_cut:
  !fn d tail.
    codegen_ready_fn fn /\ fn_reachable fn d /\ tail <> [] /\
    is_fn_path fn (d::tail) /\ LAST tail = d /\ ~MEM d (FRONT tail) ==>
    ?before a j after.
      d::tail = before ++ a::j::after /\
      1 < LENGTH (cfg_preds_of (cfg_analyze fn) j) /\
      (j = d \/ ~fn_dominates fn d j)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  qpat_x_assum `fn_reachable fn d` mp_tac >>
  rewrite_tac[fn_reachable_def] >> strip_tac >>
  drule_all ready_entry_no_incoming >> strip_tac >>
  drule_all fn_return_intersection >> strip_tac >>
  `MEM a (cfg_preds_of (cfg_analyze fn) j) /\
   MEM b (cfg_preds_of (cfg_analyze fn) j)` by
    metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze,
              cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) j)` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) j` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  qexistsl_tac [`before`, `a`, `j`, `after`] >> simp[] >>
  Cases_on `j = d` >> gvs[fn_dominates_def] >> metis_tac[]
QED

Theorem first_return_jmp_join_cut:
  !fn d tail.
    codegen_ready_fn fn /\ fn_reachable fn d /\ tail <> [] /\
    is_fn_path fn (d::tail) /\ LAST tail = d /\ ~MEM d (FRONT tail) ==>
    ?before a j after pa jb.
      d::tail = before ++ a::j::after /\
      1 < LENGTH (cfg_preds_of (cfg_analyze fn) j) /\
      (j = d \/ ~fn_dominates fn d j) /\
      fn_reachable fn a /\ fn_reachable fn j /\
      lookup_block a fn.fn_blocks = SOME pa /\
      lookup_block j fn.fn_blocks = SOME jb /\
      MEM j (cfg_succs_of (cfg_analyze fn) a) /\
      pa.bb_instructions <> [] /\
      (LAST pa.bb_instructions).inst_opcode = JMP
Proof
  rpt gen_tac >> strip_tac >>
  drule_all first_return_join_cut >> strip_tac >>
  `wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `fn_reachable fn a /\ fn_reachable fn j` by
    (conj_tac >> irule removeUnusedSsaProofsTheory.is_fn_path_all_reachable >>
     qexists_tac `d::tail` >>
     simp[] >> metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  `?pa. lookup_block a fn.fn_blocks = SOME pa` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_has_block] >>
  `?jb. lookup_block j fn.fn_blocks = SOME jb` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_has_block] >>
  `fn_cfg_edge fn a j` by
    (qpat_x_assum `is_fn_path fn (d::tail)` mp_tac >>
     qpat_x_assum `d::tail = _` SUBST1_TAC >>
     disch_tac >> drule fn_path_cut >> simp[is_fn_path_def]) >>
  `MEM j (cfg_succs_of (cfg_analyze fn) a)` by
    metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze] >>
  drule_all ready_join_edge_terminator >> strip_tac >>
  qexistsl_tac [`before`, `a`, `j`, `after`, `pa`, `jb`] >> simp[]
QED

(* The prefix-order condition is the PHI clause of bb_well_formed. *)
Theorem ordered_phis_ordinary_suffix:
  !insts.
    (!i j. i < j /\ j < LENGTH insts /\
      (EL j insts).inst_opcode = PHI ==> (EL i insts).inst_opcode = PHI) ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (DROP (LENGTH (collect_phis insts)) insts)
Proof
  Induct >- simp[livenessDefsTheory.collect_phis_def] >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[livenessDefsTheory.collect_phis_def] >> first_x_assum irule >>
      rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  simp[livenessDefsTheory.collect_phis_def, listTheory.EVERY_EL] >>
  rpt strip_tac >> Cases_on `n` >> gvs[] >>
  first_x_assum (qspecl_then [`0`, `SUC n'`] mp_tac) >> simp[]
QED

Theorem ordinary_output_post_phi_demand_exclusion:
  !fn d db k v j jb.
    codegen_ready_fn fn /\ lookup_block d fn.fn_blocks = SOME db /\
    k < LENGTH db.bb_instructions /\
    LENGTH (collect_phis db.bb_instructions) <= k /\
    MEM v (EL k db.bb_instructions).inst_outputs /\
    lookup_block j fn.fn_blocks = SOME jb /\ fn_reachable fn j /\
    (j = d \/ ~fn_dominates fn d j) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) j
      (LENGTH (collect_phis jb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `MEM jb fn.fn_blocks /\ jb.bb_label = j` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  `EVERY (\inst. inst.inst_opcode <> PHI)
      (DROP (LENGTH (collect_phis jb.bb_instructions)) jb.bb_instructions)` by
    (irule ordered_phis_ordinary_suffix >>
     fs[wf_function_def, bb_well_formed_def] >> metis_tac[]) >>
  `LENGTH (collect_phis jb.bb_instructions) <= LENGTH jb.bb_instructions` by
    (qspec_then `jb.bb_instructions` strip_assume_tac
       fnPlanLineageLivenessTheory.collect_phis_prefix >>
     qpat_x_assum `jb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `EVERY (demand_available fn jb (LENGTH (collect_phis jb.bb_instructions)))
    (live_vars_at (liveness_analyze fn) j (LENGTH (collect_phis jb.bb_instructions)))` by
    (qpat_assum `jb.bb_label = j` (fn th => rewrite_tac[GSYM th]) >>
     irule analyzed_ordinary_suffix_demand >> fs[]) >>
  strip_tac >>
  `demand_available fn jb (LENGTH (collect_phis jb.bb_instructions)) v` by
    metis_tac[listTheory.EVERY_MEM] >>
  `MEM db fn.fn_blocks /\ db.bb_label = d` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  gvs[fnPlanLineageDemandSupportTheory.demand_available_def] >>
  `?q. q < LENGTH db'.bb_instructions /\ EL q db'.bb_instructions = di` by
    metis_tac[listTheory.MEM_EL] >>
  `db' = db /\ q = k` by metis_tac[removeUnusedProofsTheory.ssa_form_position] >>
  gvs[] >>
  `k' < LENGTH db.bb_instructions` by decide_tac >>
  `k' = k` by metis_tac[removeUnusedProofsTheory.ssa_form_position] >> decide_tac
QED

(* Static reset boundary only: incoming PHI demands and physical resources
   are deliberately not asserted to vanish at this cut. *)
Theorem first_return_jmp_join_demand_cut:
  !fn d tail db k v.
    codegen_ready_fn fn /\ fn_reachable fn d /\ tail <> [] /\
    is_fn_path fn (d::tail) /\ LAST tail = d /\ ~MEM d (FRONT tail) /\
    lookup_block d fn.fn_blocks = SOME db /\
    k < LENGTH db.bb_instructions /\
    LENGTH (collect_phis db.bb_instructions) <= k /\
    MEM v (EL k db.bb_instructions).inst_outputs ==>
    ?before a j after pa jb.
      d::tail = before ++ a::j::after /\
      1 < LENGTH (cfg_preds_of (cfg_analyze fn) j) /\
      (j = d \/ ~fn_dominates fn d j) /\
      fn_reachable fn a /\ fn_reachable fn j /\
      lookup_block a fn.fn_blocks = SOME pa /\
      lookup_block j fn.fn_blocks = SOME jb /\
      MEM j (cfg_succs_of (cfg_analyze fn) a) /\
      pa.bb_instructions <> [] /\
      (LAST pa.bb_instructions).inst_opcode = JMP /\
      ~MEM v (live_vars_at (liveness_analyze fn) j
        (LENGTH (collect_phis jb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all first_return_jmp_join_cut >> strip_tac >>
  `~MEM v (live_vars_at (liveness_analyze fn) j
      (LENGTH (collect_phis jb.bb_instructions)))` by
    metis_tac[ordinary_output_post_phi_demand_exclusion] >>
  qexistsl_tac [`before`, `a`, `j`, `after`, `pa`, `jb`] >> simp[]
QED
