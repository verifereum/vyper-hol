Theory fnPlanLineageReturnCut
Ancestors
  fnPlanLineagePath fnPlanLineageCallers fnPlanLineageEdge venomWf

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
