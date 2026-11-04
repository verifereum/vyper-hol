Theory cseCanonProps
Ancestors cseDefs availExprDefs availExprAnalysisProps dfAnalyzeDefs dfAnalyzeProps
          worklistProps cfgAnalysisProps

(* These are syntactic matching facts, not runtime value equalities. *)
Theorem operand_ids_match_length:
 !c d i s. operand_ids_match c d i s ==>
 LENGTH i.inst_operands = LENGTH s.inst_operands
Proof
 rpt gen_tac >>
 simp[operand_ids_match_def, canonical_operand_ids_def] >>
 disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]
QED

Theorem canonical_id_update:
 !c k r a. canonical_id (c |+ (k,r)) a =
 if a = k then r else canonical_id c a
Proof
 simp[canonical_id_def, finite_mapTheory.FLOOKUP_UPDATE] >>
 rpt gen_tac >> Cases_on `a = k` >> simp[]
QED

Theorem canonical_operand_ids_update_away:
 !c d i k r.
 (!op. MEM op i.inst_operands ==> operand_producer d {} op <> SOME k) ==>
 canonical_operand_ids (c |+ (k,r)) d i = canonical_operand_ids c d i
Proof
 rpt strip_tac >> simp[canonical_operand_ids_def] >>
 irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
 rename1 `MEM op i.inst_operands` >>
 Cases_on `operand_producer d {} op` >> simp[canonical_id_update] >>
 metis_tac[]
QED

Theorem operand_ids_match_update_away:
 !c d i s k r.
 (!op. MEM op i.inst_operands ==> operand_producer d {} op <> SOME k) /\
 (!op. MEM op s.inst_operands ==> operand_producer d {} op <> SOME k) ==>
 (operand_ids_match (c |+ (k,r)) d i s <=> operand_ids_match c d i s)
Proof
 rpt strip_tac >>
 simp[operand_ids_match_def, canonical_operand_ids_update_away]
QED

Theorem operand_ids_match_nth:
 !c d i s n.
 operand_ids_match c d i s /\ n < LENGTH i.inst_operands ==>
 (operand_producer d {} (EL n i.inst_operands) = NONE /\
  operand_producer d {} (EL n s.inst_operands) = NONE) \/
 (?a b. operand_producer d {} (EL n i.inst_operands) = SOME a /\
        operand_producer d {} (EL n s.inst_operands) = SOME b /\
        canonical_id c a = canonical_id c b)
Proof
 rpt strip_tac >>
 `LENGTH i.inst_operands = LENGTH s.inst_operands` by
   metis_tac[operand_ids_match_length] >>
 qpat_x_assum `operand_ids_match _ _ _ _` mp_tac >>
 simp[operand_ids_match_def, canonical_operand_ids_def] >>
 disch_then (mp_tac o Q.AP_TERM `EL n`) >>
 simp[listTheory.EL_MAP] >>
 Cases_on `operand_producer d {} (EL n i.inst_operands)` >>
 Cases_on `operand_producer d {} (EL n s.inst_operands)` >> simp[]
QED

Theorem operand_producer_terminal:
 !d seen op k. operand_producer d seen op = SOME k ==>
 ?v inst. FLOOKUP d.dfg_defs v = SOME inst /\ inst.inst_id = k /\
 (inst.inst_opcode <> ASSIGN \/ ~(?arg. inst.inst_operands = [arg]))
Proof
 recInduct operand_producer_ind >> rpt strip_tac >>
 gvs[Once operand_producer_def, AllCaseEqs()] >>
 metis_tac[listTheory.NOT_CONS_NIL, listTheory.CONS_11]
QED

Theorem operand_producer_none_leaf_aux[local]:
 !d visited op. !seen.
 set seen = visited /\ operand_producer d visited op = NONE ==>
 (?w. mk_operand_expr d seen op = ExprLit w) \/
 (?v. mk_operand_expr d seen op = ExprVar v)
Proof
 recInduct operand_producer_ind >> rpt strip_tac >>
 gvs[Once operand_producer_def, AllCaseEqs()] >>
 simp[availExprDefsTheory.mk_operand_expr_def,
      dfgDefsTheory.dfg_get_def_def] >>
 Cases_on `is_pseudo ASSIGN` >> simp[] >>
 first_x_assum (qspec_then `v::seen` mp_tac) >> simp[]
QED

Theorem operand_producer_none_leaf:
 !d seen op. operand_producer d (set seen) op = NONE ==>
 (?w. mk_operand_expr d seen op = ExprLit w) \/
 (?v. mk_operand_expr d seen op = ExprVar v)
Proof
 metis_tac[operand_producer_none_leaf_aux]
QED

Theorem operand_producer_none_leaf_empty:
 !d op. operand_producer d {} op = NONE ==>
 (?w. mk_operand_expr d [] op = ExprLit w) \/
 (?v. mk_operand_expr d [] op = ExprVar v)
Proof
 rpt strip_tac >>
 qspecl_then [`d`, `[]`, `op`] mp_tac operand_producer_none_leaf >> simp[]
QED

(* Static fold history: these events are not execution occurrences. *)
Definition cse_canon_inputs_def:
 cse_canon_inputs result fn =
 FLAT (MAP (\bb. MAPi (\idx inst.
   (avail_unwrap (df_at NONE result bb.bb_label idx), inst))
   bb.bb_instructions) fn.fn_blocks)
End

Definition cse_canon_record_def:
 (cse_canon_record dfg c [] = (c,[])) /\
 (cse_canon_record dfg c ((ae,inst)::xs) =
   let (last,events) =
     cse_canon_record dfg (compute_canon_inst dfg c ae inst) xs
   in (last,(c,ae,inst)::events))
End

Theorem cse_canon_record_projection:
 !xs dfg c. FST (cse_canon_record dfg c xs) =
 FOLDL (\m (ae,inst). compute_canon_inst dfg m ae inst) c xs
Proof
 Induct >> simp[cse_canon_record_def] >>
 Cases_on `h` >> simp[cse_canon_record_def] >>
 rpt gen_tac >> pairarg_tac >> gvs[] >>
 first_x_assum (qspecl_then [`dfg`, `compute_canon_inst dfg c q r`] mp_tac) >>
 simp[]
QED

Theorem cse_canon_record_prefix:
 !xs dfg initial c ae inst.
 MEM (c,ae,inst) (SND (cse_canon_record dfg initial xs)) ==>
 ?pre post. xs = pre ++ (ae,inst)::post /\
 c = FOLDL (\m (a,i). compute_canon_inst dfg m a i) initial pre
Proof
 Induct >- simp[cse_canon_record_def] >>
 Cases_on `h` >> rpt gen_tac >>
 simp[cse_canon_record_def] >> pairarg_tac >> gvs[] >>
 strip_tac
 >- (qexistsl [`[]`, `xs`] >> simp[]) >>
 first_x_assum (qspecl_then
   [`dfg`, `compute_canon_inst dfg initial q r`, `c`, `ae`, `inst`] mp_tac) >>
 simp[] >> strip_tac >>
 qexistsl [`(q,r)::pre`, `post`] >> simp[]
QED

Theorem compute_canon_inst_changed:
 !dfg c ae inst. compute_canon_inst dfg c ae inst <> c ==>
 ?src. avail_get_source ae (mk_expr dfg inst) = SOME src /\
 src.inst_id <> inst.inst_id /\ operand_ids_match c dfg inst src /\
 ~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
 ~is_terminator inst.inst_opcode /\ LENGTH inst.inst_outputs <= 1 /\
 compute_canon_inst dfg c ae inst =
 c |+ (inst.inst_id, canonical_id c src.inst_id)
Proof
 rpt gen_tac >> simp[compute_canon_inst_def] >>
 IF_CASES_TAC >- simp[] >>
 IF_CASES_TAC >- simp[] >>
 Cases_on `avail_get_source ae (mk_expr dfg inst)` >> simp[] >>
 IF_CASES_TAC >- simp[] >>
 IF_CASES_TAC >> gvs[]
QED

Theorem cse_canon_indexed_fold[local]:
 !xs c n dfg result lbl.
 FOLDL (\m (ae,inst). compute_canon_inst dfg m ae inst) c
   (MAPi (\idx inst.
     (avail_unwrap (df_at NONE result lbl (n + idx)), inst)) xs) =
 FST (FOLDL (\(m,idx) inst.
   (compute_canon_inst dfg m
     (avail_unwrap (df_at NONE result lbl idx)) inst, idx + 1)) (c,n) xs)
Proof
 Induct >> simp[indexedListsTheory.MAPi_def] >>
 rpt gen_tac >>
 simp[combinTheory.o_DEF, arithmeticTheory.ADD_ASSOC] >>
 first_x_assum (qspecl_then
   [`compute_canon_inst dfg c (avail_unwrap (df_at NONE result lbl n)) h`,
    `n+1`, `dfg`, `result`, `lbl`] mp_tac) >>
 pure_rewrite_tac[GSYM arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES] >>
 disch_then ACCEPT_TAC
QED

Theorem cse_canon_block_inputs:
 !dfg result c bb.
 FOLDL (\m (ae,inst). compute_canon_inst dfg m ae inst) c
   (MAPi (\idx inst.
     (avail_unwrap (df_at NONE result bb.bb_label idx), inst))
     bb.bb_instructions) = compute_canon_block dfg result c bb
Proof
 rpt gen_tac >>
 qspecl_then [`bb.bb_instructions`, `c`, `0`, `dfg`, `result`, `bb.bb_label`]
   mp_tac cse_canon_indexed_fold >>
 simp[compute_canon_block_def]
QED

Theorem cse_canon_blocks_inputs[local]:
 !bbs c dfg result.
 FOLDL (\m (ae,inst). compute_canon_inst dfg m ae inst) c
 (FLAT (MAP (\bb. MAPi (\idx inst.
   (avail_unwrap (df_at NONE result bb.bb_label idx), inst))
   bb.bb_instructions) bbs)) =
 FOLDL (compute_canon_block dfg result) c bbs
Proof
 Induct >> simp[rich_listTheory.FOLDL_APPEND, cse_canon_block_inputs]
QED

Theorem cse_canon_record_compute_canon:
 !dfg result fn.
 FST (cse_canon_record dfg FEMPTY (cse_canon_inputs result fn)) =
 compute_canon dfg result fn
Proof
 simp[cse_canon_record_projection, cse_canon_inputs_def,
      cse_canon_blocks_inputs, compute_canon_def]
QED

(* Contraction counts keys as well as list entries: empty-valued keys matter. *)
Definition cse_avail_weight_def:
 cse_avail_weight (a : avail_exprs) =
 CARD (FDOM a) + SIGMA (\k. LENGTH (a ' k)) (FDOM a)
End

Theorem cse_avail_meet_apply:
 !a b k. k IN FDOM a /\ k IN FDOM b ==>
 (avail_meet_two a b) ' k = FILTER (\i. MEM i (b ' k)) (a ' k)
Proof
 rpt strip_tac >>
 simp[avail_meet_two_def, finite_mapTheory.FUN_FMAP_DEF,
      finite_mapTheory.FLOOKUP_DEF]
QED

Theorem cse_avail_meet_sum_le:
 !a b. SIGMA (\k. LENGTH (avail_meet_two a b ' k))
             (FDOM (avail_meet_two a b)) <=
       SIGMA (\k. LENGTH (a ' k)) (FDOM a)
Proof
 rpt gen_tac >> simp[avail_meet_two_FDOM] >>
 irule arithmeticTheory.LESS_EQ_TRANS >>
 qexists_tac `SIGMA (\k. LENGTH (a ' k)) (FDOM a INTER FDOM b)` >>
 conj_tac
 >- (irule pred_setTheory.SUM_IMAGE_MONO_LESS_EQ >>
     simp[cse_avail_meet_apply, rich_listTheory.LENGTH_FILTER_LEQ]) >>
 irule pred_setTheory.SUM_IMAGE_SUBSET_LE >>
 simp[pred_setTheory.INTER_SUBSET]
QED

Theorem cse_avail_meet_weight_le:
 !a b. cse_avail_weight (avail_meet_two a b) <= cse_avail_weight a
Proof
 rpt gen_tac >>
 mp_tac (Q.SPECL [`a`, `b`] cse_avail_meet_sum_le) >>
 `CARD (FDOM (avail_meet_two a b)) <= CARD (FDOM a)` by
   (irule pred_setTheory.CARD_SUBSET >>
    simp[avail_meet_two_FDOM, pred_setTheory.INTER_SUBSET]) >>
 simp[cse_avail_weight_def]
QED

Theorem cse_filter_length_eq[local]:
 !P xs. LENGTH (FILTER P xs) = LENGTH xs ==> FILTER P xs = xs
Proof
 gen_tac >> Induct >> simp[] >> gen_tac >>
 Cases_on `P h` >> simp[] >>
 mp_tac (Q.SPECL [`P`, `xs`] rich_listTheory.LENGTH_FILTER_LEQ) >>
 simp[]
QED

Theorem cse_avail_meet_weight_eq_domain[local]:
 !a b. cse_avail_weight (avail_meet_two a b) = cse_avail_weight a ==>
 FDOM (avail_meet_two a b) = FDOM a
Proof
 rpt strip_tac >>
 spose_not_then assume_tac >>
 `CARD (FDOM (avail_meet_two a b)) < CARD (FDOM a)` by
   (irule pred_setTheory.CARD_PSUBSET >>
    gvs[avail_meet_two_FDOM, pred_setTheory.PSUBSET_DEF,
        pred_setTheory.INTER_SUBSET]) >>
 mp_tac (Q.SPECL [`a`, `b`] cse_avail_meet_sum_le) >>
 gvs[cse_avail_weight_def]
QED

Theorem cse_avail_meet_weight_eq:
 !a b. cse_avail_weight (avail_meet_two a b) = cse_avail_weight a ==>
 avail_meet_two a b = a
Proof
 rpt strip_tac >>
 drule cse_avail_meet_weight_eq_domain >> strip_tac >>
 simp[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM] >> gen_tac >>
 rename1 `FLOOKUP a k` >> reverse (Cases_on `k IN FDOM a`)
 >- (simp[finite_mapTheory.FLOOKUP_DEF]) >>
 simp[finite_mapTheory.FLOOKUP_DEF] >>
 `k IN FDOM b` by
   metis_tac[avail_meet_two_FDOM, pred_setTheory.IN_INTER] >>
 simp[cse_avail_meet_apply] >>
 irule cse_filter_length_eq >>
 spose_not_then assume_tac >>
 `LENGTH (FILTER (\i. MEM i (b ' k)) (a ' k)) < LENGTH (a ' k)` by
   (`LENGTH (FILTER (\i. MEM i (b ' k)) (a ' k)) <= LENGTH (a ' k)` by
      simp[rich_listTheory.LENGTH_FILTER_LEQ] >> decide_tac) >>
 `SIGMA (\j. LENGTH (avail_meet_two a b ' j)) (FDOM a) <
  SIGMA (\j. LENGTH (a ' j)) (FDOM a)` by
   (irule pred_setTheory.SUM_IMAGE_MONO_LESS >> rpt conj_tac
    >- (rpt strip_tac >>
        `x IN FDOM b` by
          metis_tac[avail_meet_two_FDOM, pred_setTheory.IN_INTER] >>
        simp[cse_avail_meet_apply, rich_listTheory.LENGTH_FILTER_LEQ])
    >- (qexists_tac `k` >> simp[cse_avail_meet_apply]) >> simp[]) >>
 gvs[cse_avail_weight_def]
QED

Theorem cse_avail_meet_weight_lt:
 !a b. avail_meet_two a b <> a ==>
 cse_avail_weight (avail_meet_two a b) < cse_avail_weight a
Proof
 rpt strip_tac >>
 mp_tac (Q.SPECL [`a`, `b`] cse_avail_meet_weight_le) >>
 `cse_avail_weight (avail_meet_two a b) <> cse_avail_weight a` by
   metis_tac[cse_avail_meet_weight_eq] >> decide_tac
QED

Definition cse_boundary_rank_def:
 cse_boundary_rank U (h : string -> avail_exprs option) =
 (CARD {k | k IN U /\ h k = NONE},
  SIGMA (\k. case h k of NONE => 0 | SOME a => cse_avail_weight a) U)
End


Theorem cse_sum_split[local]:
 !U f k. FINITE U /\ k IN U ==>
 SIGMA f U = f k + SIGMA f (U DELETE k)
Proof
 rpt strip_tac >>
 `U = k INSERT (U DELETE k)` by metis_tac[pred_setTheory.INSERT_DELETE] >>
 qpat_x_assum `_ = _ INSERT _`
   (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
 simp[pred_setTheory.SUM_IMAGE_THM]
QED

Theorem cse_boundary_rank_some:
 !U h k a b. FINITE U /\ k IN U /\ h k = SOME a /\
 avail_meet_two a b <> a ==>
 FST (cse_boundary_rank U ((k =+ SOME (avail_meet_two a b)) h)) =
 FST (cse_boundary_rank U h) /\
 SND (cse_boundary_rank U ((k =+ SOME (avail_meet_two a b)) h)) <
 SND (cse_boundary_rank U h)
Proof
 rpt strip_tac
 >- (simp[cse_boundary_rank_def] >> AP_TERM_TAC >>
     simp[pred_setTheory.EXTENSION, combinTheory.APPLY_UPDATE_THM] >>
     metis_tac[optionTheory.NOT_SOME_NONE]) >>
 simp[cse_boundary_rank_def] >>
 qmatch_goalsub_abbrev_tac `SIGMA g U < SIGMA f U` >>
 `SIGMA g U = g k + SIGMA g (U DELETE k)` by
   metis_tac[cse_sum_split] >>
 `SIGMA f U = f k + SIGMA f (U DELETE k)` by
   metis_tac[cse_sum_split] >>
 `SIGMA g (U DELETE k) = SIGMA f (U DELETE k)` by
   (irule pred_setTheory.SUM_IMAGE_CONG >>
    simp[Abbr `g`, Abbr `f`, combinTheory.APPLY_UPDATE_THM]) >>
 `g k < f k` by
   simp[Abbr `g`, Abbr `f`, combinTheory.APPLY_UPDATE_THM,
        cse_avail_meet_weight_lt] >> decide_tac
QED

Theorem cse_boundary_rank_none:
 !U h k a. FINITE U /\ k IN U /\ h k = NONE ==>
 FST (cse_boundary_rank U ((k =+ SOME a) h)) <
 FST (cse_boundary_rank U h)
Proof
 rpt strip_tac >> simp[cse_boundary_rank_def] >>
 irule pred_setTheory.CARD_PSUBSET >>
 simp[pred_setTheory.PSUBSET_DEF, pred_setTheory.SUBSET_DEF,
      pred_setTheory.EXTENSION, combinTheory.APPLY_UPDATE_THM] >>
 conj_tac
 >- (irule pred_setTheory.SUBSET_FINITE >> qexists_tac `U` >>
     simp[pred_setTheory.SUBSET_DEF]) >>
 qexists_tac `k` >> simp[]
QED

Theorem cse_lex_components[local]:
 !p q : num # num. ($< LEX $<) p q <=>
 FST p < FST q \/ (FST p = FST q /\ SND p < SND q)
Proof
 rpt gen_tac >> PairCases_on `p` >> PairCases_on `q` >>
 simp[pairTheory.LEX_DEF]
QED

Theorem cse_boundary_rank_meet:
 !U h k v. FINITE U /\ k IN U /\
 avail_meet_opt (h k) v <> h k ==>
 ($< LEX $<)
   (cse_boundary_rank U ((k =+ avail_meet_opt (h k) v) h))
   (cse_boundary_rank U h)
Proof
 rpt strip_tac >> Cases_on `h k` >> Cases_on `v` >>
 gvs[avail_meet_opt_def]
 >- (simp[cse_lex_components] >>
     disj1_tac >> irule cse_boundary_rank_none >> simp[]) >>
 simp[cse_lex_components] >> disj2_tac >>
 irule cse_boundary_rank_some >> simp[]
QED

Theorem cse_boundary_update_function[local]:
 !st k v.
 df_boundary NONE (st with ds_boundary := st.ds_boundary |+ (k,v)) =
 (k =+ v) (df_boundary NONE st)
Proof
 rpt gen_tac >> simp[FUN_EQ_THM, df_boundary_def,
   finite_mapTheory.FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM] >>
 qx_gen_tac `l` >> Cases_on `k = l` >> simp[]
QED

(* Local descent includes first materialization and contraction of an existing
   boundary. The WF API below uses this lexicographic rank directly, without
   an increasing bounded scalar. Descent alone does not assert provenance. *)
Theorem cse_process_boundary_rank:
 !U dir transfer edge ctx entry cfg bbs k st.
 FINITE U /\ k IN U /\
 df_process_block dir NONE avail_meet_opt transfer edge ctx entry cfg bbs k st
   <> st ==>
 ($< LEX $<)
 (cse_boundary_rank U
   (df_boundary NONE
     (df_process_block dir NONE avail_meet_opt transfer edge ctx entry cfg bbs k st)))
 (cse_boundary_rank U (df_boundary NONE st))
Proof
 rpt gen_tac >> strip_tac >>
 gvs[df_process_block_def, LET_THM] >> pairarg_tac >> gvs[] >>
 IF_CASES_TAC >> gvs[] >>
 simp[cse_boundary_update_function] >>
 irule cse_boundary_rank_meet >> simp[]
QED

Theorem cse_avail_meet_absorb:
 !a b. avail_meet_two (avail_meet_two a b) b = avail_meet_two a b
Proof
 rpt gen_tac >>
 simp[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
      finite_mapTheory.FLOOKUP_DEF, avail_meet_two_FDOM] >>
 gen_tac >> IF_CASES_TAC >> simp[] >>
 gvs[pred_setTheory.IN_INTER] >>
 simp[cse_avail_meet_apply, avail_meet_two_FDOM,
      rich_listTheory.FILTER_FILTER]
QED

Theorem cse_avail_meet_opt_absorb:
 !a b. avail_meet_opt (avail_meet_opt a b) b = avail_meet_opt a b
Proof
 Cases >> Cases >> simp[avail_meet_opt_def, cse_avail_meet_absorb] >>
 simp[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
      finite_mapTheory.FLOOKUP_DEF, avail_meet_two_FDOM] >>
 gen_tac >> IF_CASES_TAC >> simp[cse_avail_meet_apply] >>
 simp[listTheory.FILTER_EQ_ID, listTheory.EVERY_MEM]
QED

(* This is the boundary_result of df_analyze, before df_populate_inst.
   Transfer and entry are arbitrary; only the contracting join is used here. *)
Theorem cse_boundary_result_fixpoint:
 !fn transfer edge ctx entry.
 wf_function fn ==>
 let cfg = cfg_analyze fn in
 let bbs = fn.fn_blocks in
 let st0 = init_df_state NONE (MAP (\bb. bb.bb_label) bbs) in
 let initial = case entry of NONE => st0 | SOME (lbl,v) =>
   st0 with ds_boundary := st0.ds_boundary |+ (lbl,v) in
 let process = df_process_block Forward NONE avail_meet_opt
                 transfer edge ctx entry cfg bbs in
 let changed = (\lbl old new.
   df_boundary NONE new lbl <> df_boundary NONE old lbl) in
 is_fixpoint process cfg.cfg_dfs_pre
   (SND (wl_iterate changed process (cfg_succs_of cfg) cfg.cfg_dfs_pre initial))
Proof
 rpt gen_tac >> strip_tac >> simp_tac bool_ss [LET_THM] >>
 irule (Q.ISPEC `($< LEX $<) : num # num -> num # num -> bool`
          wl_iterate_fixpoint_wf) >>
 simp[SRULE [LET_THM] df_process_changed_equiv,
      pairTheory.WF_LEX, prim_recTheory.WF_LESS] >> conj_tac
 >- (qexistsl_tac [`\st. T`,
       `\st. cse_boundary_rank (set (fn_labels fn)) (df_boundary NONE st)`,
       `\lbl. MEM lbl (fn_labels fn)`] >>
     simp[pairTheory.WF_LEX, prim_recTheory.WF_LESS, listTheory.EVERY_MEM] >>
     rpt conj_tac
     >- (rpt strip_tac >> irule cse_process_boundary_rank >> simp[])
     >- (metis_tac[cfg_analyze_succ_labels]) >>
     metis_tac[dfAnalyzePropsTheory.cfg_dfs_pre_subset_fn_labels]) >>
 irule (SRULE [LET_THM] (Q.SPEC `Forward` df_process_deps_complete)) >>
 simp[cfg_edge_symmetry_uncond, cse_avail_meet_opt_absorb]
QED

Theorem cse_avail_analyze_fixpoint:
 !fn. wf_function fn ==>
 is_fixpoint
   (df_process_block Forward NONE avail_meet_opt avail_transfer_opt
     avail_edge_transfer (dfg_build_function fn)
     (OPTION_MAP (\lbl. (lbl, SOME avail_empty)) (fn_entry_label fn))
     (cfg_analyze fn) fn.fn_blocks)
   (cfg_analyze fn).cfg_dfs_pre (avail_analyze fn)
Proof
 rpt strip_tac >> simp[avail_analyze_def, df_analyze_def] >>
 irule is_fixpoint_populate >>
 irule (SRULE [LET_THM] cse_boundary_result_fixpoint) >> simp[]
QED

Theorem cse_avail_at_intra:
 !fn lbl bb idx.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 SUC idx <= LENGTH bb.bb_instructions ==>
 df_at NONE (avail_analyze fn) lbl (SUC idx) =
 avail_transfer_opt (dfg_build_function fn) (EL idx bb.bb_instructions)
   (df_at NONE (avail_analyze fn) lbl idx)
Proof
 rpt strip_tac >> simp_tac bool_ss [avail_analyze_def, LET_THM] >>
 irule (SRULE [LET_THM] (Q.SPEC `Forward` df_at_intra_transfer)) >>
 simp[GSYM (SRULE [LET_THM] avail_analyze_def), cse_avail_analyze_fixpoint]
QED

Theorem cse_avail_at_entry:
 !fn lbl bb.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb ==>
 df_at NONE (avail_analyze fn) lbl 0 =
 df_joined_val Forward NONE avail_meet_opt avail_edge_transfer
   (dfg_build_function fn)
   (OPTION_MAP (\l. (l, SOME avail_empty)) (fn_entry_label fn))
   (cfg_analyze fn) (avail_analyze fn) lbl
Proof
 rpt strip_tac >> simp_tac bool_ss [avail_analyze_def, LET_THM] >>
 irule (SRULE [LET_THM] (Q.SPEC `Forward` df_at_inter_transfer)) >>
 simp[GSYM (SRULE [LET_THM] avail_analyze_def), cse_avail_analyze_fixpoint]
QED

Theorem cse_avail_boundary_absorb:
 !fn lbl bb.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb ==>
 df_boundary NONE (avail_analyze fn) lbl =
 avail_meet_opt (df_boundary NONE (avail_analyze fn) lbl)
   (df_at NONE (avail_analyze fn) lbl (LENGTH bb.bb_instructions))
Proof
 rpt strip_tac >> simp_tac bool_ss [avail_analyze_def, LET_THM] >>
 irule (SRULE [LET_THM] (Q.SPEC `Forward` df_boundary_fixpoint)) >>
 simp[GSYM (SRULE [LET_THM] avail_analyze_def), cse_avail_analyze_fixpoint]
QED
