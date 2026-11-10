Theory cseCanonProps
Ancestors cseDefs availExprDefs availExprProofs
          dfAnalyzeDefs dfAnalyzeProofs dfAnalyzeProps
          worklistWfProofs worklistProps cfgAnalysisProps venomExecProofs
          analysisSimProofsBase analysisSimProps

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

(* Collision boundaries include raw identity fallback, not only map keys. *)
Theorem canonical_id_update_collision_away:
 !c i r a b. a <> i /\ b <> i ==>
 (canonical_id (c |+ (i,r)) a = canonical_id (c |+ (i,r)) b <=>
  canonical_id c a = canonical_id c b)
Proof
 simp[canonical_id_update]
QED

Theorem canonical_id_update_collision_key:
 !c i j k. k <> i ==>
 (canonical_id (c |+ (i,canonical_id c j)) i =
  canonical_id (c |+ (i,canonical_id c j)) k <=>
  canonical_id c j = canonical_id c k)
Proof
 simp[canonical_id_update]
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
 (?l. mk_operand_expr d seen op = ExprLabel l) \/
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
 (?l. mk_operand_expr d seen op = ExprLabel l) \/
 (?v. mk_operand_expr d seen op = ExprVar v)
Proof
 metis_tac[operand_producer_none_leaf_aux]
QED

Theorem operand_producer_none_leaf_empty:
 !d op. operand_producer d {} op = NONE ==>
 (?w. mk_operand_expr d [] op = ExprLit w) \/
 (?l. mk_operand_expr d [] op = ExprLabel l) \/
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

(* A materialized operand of meet bounds all members of its result. *)
Theorem cse_avail_meet_some_left[local]:
 !a v. ?b. avail_meet_opt (SOME a) v = SOME b /\
 (!e src. (?xs. FLOOKUP b e = SOME xs /\ MEM src xs) ==>
          ?xs. FLOOKUP a e = SOME xs /\ MEM src xs)
Proof
 rpt gen_tac >> Cases_on `v` >> simp[avail_meet_opt_def] >>
 metis_tac[avail_meet_two_source_member]
QED

Theorem cse_avail_meet_some_right[local]:
 !v a. ?b. avail_meet_opt v (SOME a) = SOME b /\
 (!e src. (?xs. FLOOKUP b e = SOME xs /\ MEM src xs) ==>
          ?xs. FLOOKUP a e = SOME xs /\ MEM src xs)
Proof
 rpt gen_tac >> Cases_on `v` >> simp[avail_meet_opt_def] >>
 metis_tac[avail_meet_two_source_member]
QED

Theorem cse_avail_fold_some[local]:
 !vals a. ?b. FOLDL avail_meet_opt (SOME a) vals = SOME b /\
 (!e src. (?xs. FLOOKUP b e = SOME xs /\ MEM src xs) ==>
          ?xs. FLOOKUP a e = SOME xs /\ MEM src xs)
Proof
 Induct >- (simp[] >> metis_tac[]) >> simp_tac bool_ss [listTheory.FOLDL] >> rpt gen_tac >>
 qspecl_then [`a`, `h`] strip_assume_tac cse_avail_meet_some_left >>
 simp[] >> first_x_assum (qspec_then `b` strip_assume_tac) >>
 metis_tac[]
QED

Theorem cse_avail_fold_member:
 !vals a. MEM (SOME a) vals ==>
 ?b. FOLDL avail_meet_opt NONE vals = SOME b /\
 (!e src. (?xs. FLOOKUP b e = SOME xs /\ MEM src xs) ==>
          ?xs. FLOOKUP a e = SOME xs /\ MEM src xs)
Proof
 rpt strip_tac >> drule (iffLR listTheory.MEM_SPLIT) >> strip_tac >> gvs[rich_listTheory.FOLDL_APPEND] >>
 qmatch_goalsub_abbrev_tac `avail_meet_opt acc (SOME a)` >>
 qspecl_then [`acc`, `a`] strip_assume_tac cse_avail_meet_some_right >>
 simp[] >> qspecl_then [`l2`, `b`] strip_assume_tac cse_avail_fold_some >>
 metis_tac[]
QED

Theorem cse_avail_joined_predecessor:
 !d entry cfg st lbl pred a.
 MEM pred (cfg_preds_of cfg lbl) /\ df_boundary NONE st pred = SOME a ==>
 ?b. df_joined_val Forward NONE avail_meet_opt avail_edge_transfer d
       (OPTION_MAP (\l. (l,SOME avail_empty)) entry) cfg st lbl = SOME b /\
 (!e src. (?xs. FLOOKUP b e = SOME xs /\ MEM src xs) ==>
          ?xs. FLOOKUP a e = SOME xs /\ MEM src xs)
Proof
 rpt strip_tac >>
 `MEM (SOME a) (MAP (\p. df_boundary NONE st p) (cfg_preds_of cfg lbl))`
   by (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
 drule cse_avail_fold_member >> strip_tac >>
 simp[df_joined_val_def, avail_edge_transfer_def] >>
 qmatch_goalsub_abbrev_tac `case vals of [] => NONE | _ => _` >>
 `vals <> []` by (strip_tac >> gvs[Abbr `vals`]) >>
 Cases_on `vals` >> gvs[] >>
 Cases_on `entry` >> simp[] >> IF_CASES_TAC >> gvs[] >>
 qspecl_then [`SOME avail_empty`, `b`] strip_assume_tac
   cse_avail_meet_some_right >> metis_tac[]
QED

Theorem cse_avail_joined_entry_empty[local]:
 !d cfg st lbl.
 ?a. df_joined_val Forward NONE avail_meet_opt avail_edge_transfer d
       (SOME (lbl,SOME avail_empty)) cfg st lbl = SOME a /\
 (!e src. ~(?xs. FLOOKUP a e = SOME xs /\ MEM src xs))
Proof
 rpt gen_tac >> simp[df_joined_val_def] >>
 qmatch_goalsub_abbrev_tac `avail_meet_opt (SOME avail_empty) v` >>
 qspecl_then [`avail_empty`, `v`] strip_assume_tac cse_avail_meet_some_left >>
 qexists_tac `b` >> simp[] >>
 gvs[avail_empty_def, finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]
QED

Theorem cse_avail_entry_empty:
 !fn lbl bb.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\ fn_entry_label fn = SOME lbl ==>
 ?a. df_at NONE (avail_analyze fn) lbl 0 = SOME a /\
 (!e src. ~(?xs. FLOOKUP a e = SOME xs /\ MEM src xs))
Proof
 rpt strip_tac >> drule_all cse_avail_at_entry >> simp[] >>
 strip_tac >>
 qspecl_then [`dfg_build_function fn`, `cfg_analyze fn`, `avail_analyze fn`, `lbl`]
   mp_tac cse_avail_joined_entry_empty >> simp[]
QED

Theorem cse_avail_boundary_member:
 !fn lbl bb a.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 df_at NONE (avail_analyze fn) lbl (LENGTH bb.bb_instructions) = SOME a ==>
 ?b. df_boundary NONE (avail_analyze fn) lbl = SOME b /\
 (!e src. (?xs. FLOOKUP b e = SOME xs /\ MEM src xs) ==>
          ?xs. FLOOKUP a e = SOME xs /\ MEM src xs)
Proof
 rpt strip_tac >> drule_all cse_avail_boundary_absorb >> simp[] >>
 qspecl_then [`df_boundary NONE (avail_analyze fn) lbl`, `a`]
   strip_assume_tac cse_avail_meet_some_right >> simp[] >> metis_tac[]
QED

Theorem cse_avail_entry_predecessor:
 !fn lbl bb pred a.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 MEM pred (cfg_preds_of (cfg_analyze fn) lbl) /\
 df_boundary NONE (avail_analyze fn) pred = SOME a ==>
 ?b. df_at NONE (avail_analyze fn) lbl 0 = SOME b /\
 (!e src. (?xs. FLOOKUP b e = SOME xs /\ MEM src xs) ==>
          ?xs. FLOOKUP a e = SOME xs /\ MEM src xs)
Proof
 rpt strip_tac >> drule_all cse_avail_at_entry >> strip_tac >>
 simp[] >> irule cse_avail_joined_predecessor >> simp[] >>
 qexists_tac `pred` >> simp[]
QED

Theorem cse_phi_transfer_some:
 !d inst ae. inst.inst_opcode = PHI ==>
 avail_transfer_opt d inst (SOME ae) = SOME ae
Proof
 simp[avail_transfer_opt_def, avail_transfer_inst_def,
      venomInstTheory.is_pseudo_def]
QED

Theorem cse_phi_transfer_unwrap:
 !d inst v. inst.inst_opcode = PHI ==>
 avail_unwrap (avail_transfer_opt d inst v) = avail_unwrap v
Proof
 rpt gen_tac >> Cases_on `v` >>
 simp[avail_transfer_opt_def, avail_transfer_inst_def, avail_unwrap_def,
      venomInstTheory.is_pseudo_def]
QED

Theorem cse_avail_phi_prefix_unwrap:
 !k fn lbl bb.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 k <= LENGTH bb.bb_instructions /\
 (!j. j < k ==> (EL j bb.bb_instructions).inst_opcode = PHI) ==>
 ae_lookup_inst fn lbl k = ae_lookup_inst fn lbl 0
Proof
 Induct >- simp[] >> rpt gen_tac >> strip_tac >>
 `ae_lookup_inst fn lbl k = ae_lookup_inst fn lbl 0` by
   (first_x_assum irule >> simp[] ) >>
 drule_all cse_avail_at_intra >> strip_tac >>
 `((EL k bb.bb_instructions).inst_opcode = PHI)` by simp[] >>
 simp[ae_lookup_inst_def, cse_phi_transfer_unwrap] >>
 gvs[ae_lookup_inst_def]
QED

Theorem cse_avail_phi_prefix_some:
 !k fn lbl bb ae.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 k <= LENGTH bb.bb_instructions /\
 (!j. j < k ==> (EL j bb.bb_instructions).inst_opcode = PHI) /\
 df_at NONE (avail_analyze fn) lbl 0 = SOME ae ==>
 df_at NONE (avail_analyze fn) lbl k = SOME ae
Proof
 Induct >- simp[] >> rpt gen_tac >> strip_tac >>
 `df_at NONE (avail_analyze fn) lbl k = SOME ae` by
   (first_x_assum irule >> simp[]) >>
 drule_all cse_avail_at_intra >> simp[cse_phi_transfer_some]
QED

Theorem cse_avail_atomic_phi_unwrap:
 !fn lbl bb.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb ==>
 ae_lookup_inst fn lbl (phi_prefix_length bb.bb_instructions) =
 ae_lookup_inst fn lbl 0
Proof
 rpt strip_tac >> irule cse_avail_phi_prefix_unwrap >>
 simp[phi_prefix_length_le] >>
 mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi) >>
 simp[listTheory.EVERY_EL, listTheory.EL_TAKE, phi_prefix_length_le]
QED

Theorem cse_avail_atomic_phi_some:
 !fn lbl bb ae.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 df_at NONE (avail_analyze fn) lbl 0 = SOME ae ==>
 df_at NONE (avail_analyze fn) lbl (phi_prefix_length bb.bb_instructions) = SOME ae
Proof
 rpt strip_tac >> irule cse_avail_phi_prefix_some >>
 simp[phi_prefix_length_le] >>
 mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi) >>
 simp[listTheory.EVERY_EL, listTheory.EL_TAKE, phi_prefix_length_le]
QED

(* Reuse the shared source-birth and survival predicates. *)
Theorem cse_transfer_source_cases:
 !d inst a e src.
 (?xs. FLOOKUP (avail_transfer_inst d inst a) e = SOME xs /\ MEM src xs) ==>
 ((?xs. FLOOKUP a e = SOME xs /\ MEM src xs) /\
   avail_source_survives e inst) \/ avail_source_birth d e src inst
Proof
 simp[avail_transfer_inst_source_member,
      availExprProofsTheory.avail_source_survives_def,
      availExprProofsTheory.avail_source_birth_def] >>
 rpt gen_tac >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

(* A static preorder invariant; no dynamic epoch equality is asserted. *)
Theorem compute_canon_inst_preorder:
 transitive R /\ (!k. R (canonical_id c k) k) /\
 (compute_canon_inst d c ae inst <> c ==>
   !src. avail_get_source ae (mk_expr d inst) = SOME src ==>
         R src.inst_id inst.inst_id) ==>
 !k. R (canonical_id (compute_canon_inst d c ae inst) k) k
Proof
 rpt strip_tac >> Cases_on `compute_canon_inst d c ae inst = c`
 >- metis_tac[] >>
 drule compute_canon_inst_changed >> strip_tac >>
 simp[canonical_id_update] >> Cases_on `k = inst.inst_id` >> gvs[] >>
 fs[relationTheory.transitive_def] >> metis_tac[]
QED

Theorem cse_canon_record_preorder:
 !xs initial.
 transitive R /\ (!k. R (canonical_id initial k) k) /\
 (!c ae inst. MEM (c,ae,inst) (SND (cse_canon_record d initial xs)) ==>
   compute_canon_inst d c ae inst <> c ==>
   !src. avail_get_source ae (mk_expr d inst) = SOME src ==>
         R src.inst_id inst.inst_id) ==>
 !k. R (canonical_id (FST (cse_canon_record d initial xs)) k) k
Proof
 Induct >- simp[cse_canon_record_def] >>
 Cases_on `h` >> rpt gen_tac >>
 simp[cse_canon_record_def] >> pairarg_tac >> gvs[] >>
 rpt strip_tac >>
 qpat_x_assum `!initial. transitive R /\ _ ==> _` (qspec_then `compute_canon_inst d initial q r` mp_tac) >>
 simp[] >> disch_then irule >> conj_tac
 >- metis_tac[] >>
 irule compute_canon_inst_preorder >> metis_tac[]
QED

Theorem compute_canon_preorder:
 reflexive R /\ transitive R /\
 (!c ae inst.
   MEM (c,ae,inst)
     (SND (cse_canon_record d FEMPTY (cse_canon_inputs result fn))) ==>
   compute_canon_inst d c ae inst <> c ==>
   !src. avail_get_source ae (mk_expr d inst) = SOME src ==>
         R src.inst_id inst.inst_id) ==>
 !k. R (canonical_id (compute_canon d result fn) k) k
Proof
 rpt strip_tac >>
 qspecl_then [`cse_canon_inputs result fn`, `FEMPTY`] mp_tac
   cse_canon_record_preorder >>
 simp[cse_canon_record_compute_canon, canonical_id_def] >>
 fs[relationTheory.reflexive_def] >> metis_tac[]
QED

Theorem compute_canon_common_predecessor:
 reflexive R /\ transitive R /\
 (!c ae inst.
   MEM (c,ae,inst)
     (SND (cse_canon_record d FEMPTY (cse_canon_inputs result fn))) ==>
   compute_canon_inst d c ae inst <> c ==>
   !src. avail_get_source ae (mk_expr d inst) = SOME src ==>
         R src.inst_id inst.inst_id) /\
 canonical_id (compute_canon d result fn) a =
 canonical_id (compute_canon d result fn) b ==>
 ?r. R r a /\ R r b
Proof
 rpt strip_tac >> drule_all compute_canon_preorder >> strip_tac >>
 qexists_tac `canonical_id (compute_canon d result fn) a` >> metis_tac[]
QED

(* Syntactic instruction-point paths include the block-end point. *)
Inductive cse_static_trace:
 (!entry bb. fn_entry_label fn = SOME entry /\
   lookup_block entry fn.fn_blocks = SOME bb ==>
   cse_static_trace fn [(entry,0)]) /\
 (!ps lbl k bb. cse_static_trace fn ps /\ LAST ps = (lbl,k) /\
   lookup_block lbl fn.fn_blocks = SOME bb /\ k < LENGTH bb.bb_instructions ==>
   cse_static_trace fn (ps ++ [(lbl,SUC k)])) /\
 (!ps lbl bb next nb. cse_static_trace fn ps /\
   LAST ps = (lbl,LENGTH bb.bb_instructions) /\
   lookup_block lbl fn.fn_blocks = SOME bb /\ fn_cfg_edge fn lbl next /\
   lookup_block next fn.fn_blocks = SOME nb ==>
   cse_static_trace fn (ps ++ [(next,0)]))
End

Definition cse_point_has_id_def:
 cse_point_has_id fn (lbl,k) id <=>
 ?bb. lookup_block lbl fn.fn_blocks = SOME bb /\
      k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_id = id
End

Definition cse_path_preorder_def:
 cse_path_preorder fn a b <=>
 !ps p. cse_static_trace fn ps /\ LAST ps = p /\ cse_point_has_id fn p b ==>
        ?q. MEM q ps /\ cse_point_has_id fn q a
End

Theorem cse_static_trace_nonempty:
 !fn ps. cse_static_trace fn ps ==> ps <> []
Proof
 gen_tac >> ho_match_mp_tac cse_static_trace_ind >> simp[]
QED

Theorem cse_static_trace_points:
 !fn ps. cse_static_trace fn ps ==>
 !lbl k. MEM (lbl,k) ps ==>
 ?bb. lookup_block lbl fn.fn_blocks = SOME bb /\ k <= LENGTH bb.bb_instructions
Proof
 gen_tac >> ho_match_mp_tac cse_static_trace_ind >> simp[] >> rpt strip_tac >> gvs[] >>
 metis_tac[arithmeticTheory.LESS_OR_EQ, arithmeticTheory.LESS_EQ]
QED

Theorem cse_path_preorder_reflexive:
 reflexive (cse_path_preorder fn)
Proof
 simp[relationTheory.reflexive_def, cse_path_preorder_def] >> rpt strip_tac >>
 qexists_tac `LAST ps` >> simp[] >>
 drule cse_static_trace_nonempty >>
 Cases_on `ps` >> simp[rich_listTheory.MEM_LAST]
QED

Theorem cse_static_trace_front:
 cse_static_trace fn ps /\ 1 < LENGTH ps ==> cse_static_trace fn (FRONT ps)
Proof
 strip_tac >>
 qpat_x_assum `cse_static_trace fn ps`
   (strip_assume_tac o ONCE_REWRITE_RULE [cse_static_trace_cases]) >>
 gvs[] >>
 gvs[GSYM rich_listTheory.SNOC_APPEND, listTheory.FRONT_SNOC]
QED

Theorem cse_static_trace_prefix:
 !post pre. cse_static_trace fn (pre ++ post) /\ pre <> [] ==>
 cse_static_trace fn pre
Proof
 Induct_on `post` using rich_listTheory.SNOC_INDUCT >- simp[] >>
 rpt strip_tac >> first_x_assum irule >> simp[] >>
 `cse_static_trace fn (FRONT (SNOC x (pre ++ post)))` by
   (irule cse_static_trace_front >> gvs[rich_listTheory.SNOC_APPEND, listTheory.APPEND_ASSOC] >>
    Cases_on `pre` >> gvs[]) >>
 fs[listTheory.FRONT_SNOC]
QED

Theorem cse_static_trace_member_prefix:
 cse_static_trace fn ps /\ MEM p ps ==>
 ?pre post. ps = pre ++ post /\ pre <> [] /\ LAST pre = p /\
            cse_static_trace fn pre
Proof
 rpt strip_tac >>
 fs[listTheory.MEM_SPLIT] >>
 qexistsl_tac [`l1 ++ [p]`, `l2`] >>
 simp[listTheory.APPEND_ASSOC] >>
 irule cse_static_trace_prefix >> simp[] >>
 qexists_tac `l2` >> fs[listTheory.APPEND_ASSOC]
QED

Theorem cse_path_preorder_transitive:
 transitive (cse_path_preorder fn)
Proof
 rw[relationTheory.transitive_def, cse_path_preorder_def] >>
 `?q. MEM q ps /\ cse_point_has_id fn q y` by metis_tac[] >>
 drule_all cse_static_trace_member_prefix >> rpt strip_tac >>
 `?r. MEM r pre /\ cse_point_has_id fn r x` by metis_tac[] >>
 qexists_tac `r` >> simp[]
QED

Theorem cse_path_preorder_occurrence:
 cse_path_preorder fn a b /\ cse_static_trace fn ps /\
 cse_point_has_id fn (LAST ps) b ==>
 ?pre post lbl k bb.
   ps = pre ++ post /\ pre <> [] /\ LAST pre = (lbl,k) /\
   cse_static_trace fn pre /\
   lookup_block lbl fn.fn_blocks = SOME bb /\
   k < LENGTH bb.bb_instructions /\
   (EL k bb.bb_instructions).inst_id = a
Proof
 rw[cse_path_preorder_def] >>
 `?q. MEM q ps /\ cse_point_has_id fn q a` by metis_tac[] >>
 drule_all cse_static_trace_member_prefix >> rpt strip_tac >>
 Cases_on `q` >> fs[cse_point_has_id_def] >> metis_tac[]
QED

Theorem cse_static_trace_reachable:
 !fn ps. cse_static_trace fn ps ==> wf_function fn ==>
 !lbl k. MEM (lbl,k) ps ==> MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
 gen_tac >> ho_match_mp_tac cse_static_trace_strongind >> rpt conj_tac
 >- (rpt gen_tac >> strip_tac >> strip_tac >>
     gvs[venomInstTheory.fn_entry_label_def] >> Cases_on `entry_block fn` >> gvs[] >>
     drule cfg_analyze_preorder_entry_first >>
     Cases_on `(cfg_analyze fn).cfg_dfs_pre` >> simp[]) 
 >- (rpt strip_tac >> gvs[] >>
     metis_tac[cse_static_trace_nonempty, rich_listTheory.MEM_LAST, listTheory.list_CASES]) >>
 rpt strip_tac >> gvs[] >- metis_tac[] >>
 rename1 `MEM next (cfg_analyze fn).cfg_dfs_pre` >>
 `MEM (lbl,LENGTH bb.bb_instructions) ps` by
   metis_tac[cse_static_trace_nonempty, rich_listTheory.MEM_LAST, listTheory.list_CASES] >>
 `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by metis_tac[] >>
 `MEM next (cfg_succs_of (cfg_analyze fn) lbl)` by
   (gvs[venomWfTheory.fn_cfg_edge_def] >>
    irule (SIMP_RULE (srw_ss()) [LET_THM] cfgHelpersTheory.bb_succs_in_cfg_succs) >>
    fs[venomWfTheory.wf_function_def]) >>
 drule cfg_dfs_pre_succs_closed >> simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem cse_static_trace_avail_inst:
 !fn ps.
   cse_static_trace fn ps ==>
   wf_function fn /\ fn_inst_wf fn ==>
   !lbl k. LAST ps = (lbl, k) ==>
     ?a. df_at NONE (avail_analyze fn) lbl k = SOME a /\
         (!e src. (?xs. FLOOKUP a e = SOME xs /\ MEM src xs) ==>
           ?lbl0 k0 bb0.
             MEM (lbl0, k0) (FRONT ps) /\
             lookup_block lbl0 fn.fn_blocks = SOME bb0 /\
             k0 < LENGTH bb0.bb_instructions /\
             EL k0 bb0.bb_instructions = src)
Proof
 gen_tac >> ho_match_mp_tac cse_static_trace_strongind >> rpt conj_tac
 >- (rpt gen_tac >> strip_tac >> strip_tac >> simp[] >>
     `MEM entry (cfg_analyze fn).cfg_dfs_pre` by
       (gvs[venomInstTheory.fn_entry_label_def] >>
        Cases_on `entry_block fn` >> gvs[] >>
        drule cfg_analyze_preorder_entry_first >>
        Cases_on `(cfg_analyze fn).cfg_dfs_pre` >> simp[]) >>
     drule_all cse_avail_entry_empty >> simp[])
 >- (rpt gen_tac >> strip_tac >> strip_tac >> simp[] >>
     qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
     `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
       metis_tac[cse_static_trace_reachable, cse_static_trace_nonempty,
                 rich_listTheory.MEM_LAST, listTheory.list_CASES] >>
     `SUC k <= LENGTH bb.bb_instructions` by simp[] >>
     drule_all cse_avail_at_intra >> simp[] >> strip_tac >>
     qexists_tac `avail_transfer_inst (dfg_build_function fn) (EL k bb.bb_instructions) a` >>
     simp[avail_transfer_opt_def, GSYM rich_listTheory.SNOC_APPEND, listTheory.FRONT_SNOC] >>
     rpt strip_tac >>
     `((?xs. FLOOKUP a e = SOME xs /\ MEM src xs) /\
        avail_source_survives e (EL k bb.bb_instructions)) \/
       avail_source_birth (dfg_build_function fn) e src (EL k bb.bb_instructions)`
       by metis_tac[cse_transfer_source_cases]
     >- (first_x_assum (qspecl_then [`e`, `src`] mp_tac) >>
         impl_tac >- (goal_assum drule >> simp[]) >> strip_tac >>
         qexistsl_tac [`lbl0`, `k0`, `bb0`] >> simp[] >>
         qspec_then `ps` strip_assume_tac rich_listTheory.SNOC_CASES >>
         gvs[GSYM rich_listTheory.SNOC_APPEND, listTheory.FRONT_SNOC] >>
         simp[rich_listTheory.SNOC_APPEND])
     >- (fs[availExprProofsTheory.avail_source_birth_def] >>
         qexistsl_tac [`lbl`, `k`, `bb`] >> simp[] >>
         metis_tac[cse_static_trace_nonempty, rich_listTheory.MEM_LAST, listTheory.list_CASES]))
 >- (rpt gen_tac >> strip_tac >> strip_tac >> simp[] >>
     qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
     `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
       metis_tac[cse_static_trace_reachable, cse_static_trace_nonempty,
                 rich_listTheory.MEM_LAST, listTheory.list_CASES] >>
     `MEM next (cfg_succs_of (cfg_analyze fn) lbl)` by
       (gvs[venomWfTheory.fn_cfg_edge_def] >>
        irule bb_succs_in_cfg_succs >> fs[venomWfTheory.wf_function_def]) >>
     `MEM lbl (cfg_preds_of (cfg_analyze fn) next)` by
       metis_tac[cfg_edge_symmetry_uncond] >>
     `MEM next (cfg_analyze fn).cfg_dfs_pre` by
       (drule cfg_dfs_pre_succs_closed >> simp[listTheory.EVERY_MEM]) >>
     drule_all cse_avail_boundary_member >> strip_tac >>
     drule_all cse_avail_entry_predecessor >> strip_tac >>
     qexists_tac `b'` >> simp[GSYM rich_listTheory.SNOC_APPEND, listTheory.FRONT_SNOC] >>
     rpt strip_tac >>
     `?xs1. FLOOKUP b e = SOME xs1 /\ MEM src xs1` by
       (first_x_assum irule >> goal_assum drule >> simp[]) >>
     `?xs2. FLOOKUP a e = SOME xs2 /\ MEM src xs2` by
       (qpat_x_assum `!e src. (?xs. FLOOKUP b e = SOME xs /\ _) ==> _` irule >>
        goal_assum drule >> simp[]) >>
     qpat_x_assum `!e src. (?xs. FLOOKUP a e = SOME xs /\ _) ==> _`
       (qspecl_then [`e`, `src`] mp_tac) >>
     impl_tac >- (goal_assum drule >> simp[]) >> strip_tac >>
     qexistsl_tac [`lbl0`, `k0`, `bb0`] >> simp[] >>
     qspec_then `ps` strip_assume_tac rich_listTheory.SNOC_CASES >>
     gvs[GSYM rich_listTheory.SNOC_APPEND, listTheory.FRONT_SNOC] >>
     simp[rich_listTheory.SNOC_APPEND])
QED

Theorem cse_static_trace_availability:
 !fn ps. cse_static_trace fn ps ==> wf_function fn /\ fn_inst_wf fn ==>
 !lbl k. LAST ps = (lbl,k) ==>
 ?a. df_at NONE (avail_analyze fn) lbl k = SOME a /\
     (!e src. (?xs. FLOOKUP a e = SOME xs /\ MEM src xs) ==>
       ?q. MEM q (FRONT ps) /\ cse_point_has_id fn q src.inst_id)
Proof
 rpt strip_tac >> drule_all cse_static_trace_avail_inst >> strip_tac >>
 qexists_tac `a` >> simp[] >> rpt strip_tac >>
 first_x_assum (qspecl_then [`e`, `src`] mp_tac) >>
 impl_tac >- (goal_assum drule >> simp[]) >> strip_tac >>
 qexists_tac `(lbl0, k0)` >> simp[cse_point_has_id_def]
QED

Theorem cse_point_has_id_injective:
 !fn p q id. wf_function fn /\ cse_point_has_id fn p id /\
 cse_point_has_id fn q id ==> p = q
Proof
 rpt gen_tac >> PairCases_on `p` >> PairCases_on `q` >>
 strip_tac >> fs[cse_point_has_id_def] >>
 `MEM bb fn.fn_blocks /\ MEM bb' fn.fn_blocks` by
   metis_tac[lookup_block_MEM] >>
 `MEM id (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM id (MAP (\i. i.inst_id) bb'.bb_instructions)` by
   (simp[listTheory.MEM_MAP] >> metis_tac[listTheory.EL_MEM]) >>
 `?pre post. fn.fn_blocks = pre ++ bb::post` by metis_tac[listTheory.MEM_SPLIT] >>
 fs[venomWfTheory.wf_function_def, venomWfTheory.fn_inst_ids_distinct_def,
    listTheory.MAP_APPEND, listTheory.FLAT_APPEND, listTheory.ALL_DISTINCT_APPEND]
 >- (`MEM id (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) pre))` by
       (simp_tac bool_ss [listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
        qexists_tac `MAP (\i. i.inst_id) bb'.bb_instructions` >>
        simp[] >> qexists_tac `bb'` >> simp[]) >> metis_tac[])
 >- (conj_tac >- metis_tac[lookup_block_label] >>
     gvs[] >> metis_tac[listTheory.ALL_DISTINCT_EL_IMP, listTheory.EL_MAP, listTheory.LENGTH_MAP]) >>
 `MEM id (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) post))` by
   (simp_tac bool_ss [listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
    qexists_tac `MAP (\i. i.inst_id) bb'.bb_instructions` >>
        simp[] >> qexists_tac `bb'` >> simp[]) >> metis_tac[]
QED

Theorem cse_avail_source_path_preorder:
 !fn lbl k bb src e.
 wf_function fn /\ fn_inst_wf fn /\
 lookup_block lbl fn.fn_blocks = SOME bb /\ k < LENGTH bb.bb_instructions /\
 avail_get_source (ae_lookup_inst fn lbl k) e = SOME src ==>
 cse_path_preorder fn src.inst_id (EL k bb.bb_instructions).inst_id
Proof
 rpt gen_tac >> strip_tac >> rw[cse_path_preorder_def] >>
 `cse_point_has_id fn (lbl,k) (EL k bb.bb_instructions).inst_id` by
   simp[cse_point_has_id_def] >>
 `LAST ps = (lbl,k)` by metis_tac[cse_point_has_id_injective] >> gvs[] >>
 drule_all cse_static_trace_availability >>
 strip_tac >>
 gvs[ae_lookup_inst_def, avail_unwrap_def, avail_get_source_def, AllCaseEqs()] >>
 `?q. MEM q (FRONT ps) /\ cse_point_has_id fn q src.inst_id` by
   (first_x_assum irule >> goal_assum drule >> simp[]) >>
 qexists_tac `q` >> simp[] >>
 qspec_then `ps` strip_assume_tac rich_listTheory.SNOC_CASES >>
 gvs[GSYM rich_listTheory.SNOC_APPEND, listTheory.FRONT_SNOC] >>
 simp[rich_listTheory.SNOC_APPEND]
QED

Theorem compute_canon_path_preorder:
 !fn k. wf_function fn /\ fn_inst_wf fn ==>
 cse_path_preorder fn
   (canonical_id (compute_canon (dfg_build_function fn) (avail_analyze fn) fn) k) k
Proof
 rpt strip_tac >> irule compute_canon_preorder >>
 simp[cse_path_preorder_reflexive, cse_path_preorder_transitive] >>
 rpt strip_tac >> drule cse_canon_record_prefix >> strip_tac >>
 `MEM (ae,inst) (cse_canon_inputs (avail_analyze fn) fn)` by simp[] >>
 pop_assum mp_tac >>
 simp_tac bool_ss [cse_canon_inputs_def, listTheory.MEM_FLAT, listTheory.MEM_MAP,
      indexedListsTheory.MEM_MAPi, PULL_EXISTS] >>
 rpt strip_tac >> gvs[] >>
 irule cse_avail_source_path_preorder >>
 simp[ae_lookup_inst_def] >>
 qexistsl_tac [`mk_expr (dfg_build_function fn) (EL idx bb.bb_instructions)`, `bb.bb_label`] >>
 simp[] >> irule MEM_lookup_block >>
 fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]
QED

Theorem compute_canon_representative_occurrence:
 wf_function fn /\ fn_inst_wf fn /\ cse_static_trace fn ps /\
 cse_point_has_id fn (LAST ps) k ==>
 ?q. MEM q ps /\ cse_point_has_id fn q
   (canonical_id (compute_canon (dfg_build_function fn) (avail_analyze fn) fn) k)
Proof
 rpt strip_tac >>
 drule_all compute_canon_path_preorder >>
 simp[cse_path_preorder_def] >> metis_tac[]
QED

Theorem compute_canon_representative_member:
 wf_function fn /\ fn_inst_wf fn /\ cse_static_trace fn ps /\
 cse_point_has_id fn (LAST ps) k ==>
 ?r. MEM r (fn_insts fn) /\ r.inst_id =
   canonical_id (compute_canon (dfg_build_function fn) (avail_analyze fn) fn) k
Proof
 rpt strip_tac >> drule_all compute_canon_representative_occurrence >> strip_tac >>
 PairCases_on `q` >> fs[cse_point_has_id_def] >>
 qexists_tac `EL q1 bb.bb_instructions` >> simp[] >>
 `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `MEM (EL q1 bb.bb_instructions) bb.bb_instructions` by simp[listTheory.EL_MEM] >>
 simp[venomInstTheory.fn_insts_def] >>
 qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
 qspec_tac (`fn.fn_blocks`, `bbs`) >> Induct >>
 simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]
QED

Theorem compute_canon_path_common_predecessor:
 wf_function fn /\ fn_inst_wf fn /\
 canonical_id (compute_canon (dfg_build_function fn) (avail_analyze fn) fn) a =
 canonical_id (compute_canon (dfg_build_function fn) (avail_analyze fn) fn) b ==>
 ?r. cse_path_preorder fn r a /\ cse_path_preorder fn r b
Proof
 rpt strip_tac >>
 qexists_tac `canonical_id (compute_canon (dfg_build_function fn) (avail_analyze fn) fn) a` >>
 metis_tac[compute_canon_path_preorder]
QED

Theorem cse_first_matching_point[local]:
 !ps. (?p. MEM p ps /\ cse_point_has_id fn p a) ==>
 ?pre p post. ps = pre ++ [p] ++ post /\ cse_point_has_id fn p a /\
   EVERY (\q. ~cse_point_has_id fn q a) pre
Proof
 Induct >- simp[] >> gen_tac >> disch_tac >> Cases_on `cse_point_has_id fn h a`
 >- (qexistsl_tac [`[]`, `h`, `ps`] >> simp[]) >>
 `?p. MEM p ps /\ cse_point_has_id fn p a` by (fs[] >> metis_tac[]) >>
 qpat_x_assum `_ ==> ?pre p post. _` mp_tac >>
 (impl_tac >- metis_tac[]) >> strip_tac >>
 qexistsl_tac [`h::pre`, `p'`, `post`] >> simp[]
QED

Theorem cse_static_trace_first_id:
 cse_static_trace fn ps /\ cse_point_has_id fn (LAST ps) a ==>
 ?pre p. cse_static_trace fn (pre ++ [p]) /\ cse_point_has_id fn p a /\
         EVERY (\q. ~cse_point_has_id fn q a) pre
Proof
 strip_tac >>
 `?p. MEM p ps /\ cse_point_has_id fn p a` by
   metis_tac[cse_static_trace_nonempty, rich_listTheory.MEM_LAST, listTheory.list_CASES] >>
 qspec_then `ps` mp_tac cse_first_matching_point >>
 (impl_tac >- metis_tac[]) >> strip_tac >>
 qexistsl_tac [`pre`, `p'`] >> simp[] >>
 irule cse_static_trace_prefix >> simp[] >>
 qexists_tac `post` >> gvs[listTheory.APPEND_ASSOC]
QED

Theorem cse_static_trace_predecessor_barrier:
 wf_function fn /\ fn_inst_wf fn /\
 cse_path_preorder fn a src.inst_id /\ a <> src.inst_id /\
 cse_static_trace fn ps /\ cse_point_has_id fn (LAST ps) a /\
 LAST ps = (lbl,k) ==>
 ~(?xs. FLOOKUP (ae_lookup_inst fn lbl k) e = SOME xs /\ MEM src xs)
Proof
 strip_tac >> strip_tac >>
 drule_all cse_static_trace_first_id >> strip_tac >>
 `p = (lbl,k)` by metis_tac[cse_point_has_id_injective] >> gvs[] >>
 qspecl_then [`fn`, `pre ++ [(lbl,k)]`] mp_tac cse_static_trace_availability >>
 (impl_tac >- simp[]) >> (impl_tac >- simp[]) >>
 disch_then (qspecl_then [`lbl`, `k`] mp_tac) >>
 (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
 `?q. MEM q pre /\ cse_point_has_id fn q src.inst_id` by
   (gvs[availExprDefsTheory.ae_lookup_inst_def, availExprDefsTheory.avail_unwrap_def,
        GSYM rich_listTheory.SNOC_APPEND, listTheory.FRONT_SNOC] >> metis_tac[]) >>
 `pre <> []` by (Cases_on `pre` >> gvs[]) >>
 `cse_static_trace fn pre` by
   (irule cse_static_trace_prefix >> simp[] >> qexists_tac `[(lbl,k)]` >> simp[]) >>
 drule_all cse_static_trace_member_prefix >> strip_tac >>
 fs[cse_path_preorder_def, listTheory.EVERY_MEM] >> metis_tac[listTheory.MEM_APPEND]
QED

Theorem cse_static_trace_self_source_barrier:
 wf_function fn /\ fn_inst_wf fn /\
 cse_static_trace fn ps /\ cse_point_has_id fn (LAST ps) src.inst_id /\
 LAST ps = (lbl,k) ==>
 ~(?xs. FLOOKUP (ae_lookup_inst fn lbl k) e = SOME xs /\ MEM src xs)
Proof
 strip_tac >> strip_tac >>
 drule_all cse_static_trace_first_id >> strip_tac >>
 `p = (lbl,k)` by metis_tac[cse_point_has_id_injective] >> gvs[] >>
 qspecl_then [`fn`, `pre ++ [(lbl,k)]`] mp_tac cse_static_trace_availability >>
 (impl_tac >- simp[]) >> (impl_tac >- simp[]) >>
 disch_then (qspecl_then [`lbl`, `k`] mp_tac) >>
 (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
 gvs[availExprDefsTheory.ae_lookup_inst_def, availExprDefsTheory.avail_unwrap_def,
     GSYM rich_listTheory.SNOC_APPEND, listTheory.FRONT_SNOC, listTheory.EVERY_MEM] >>
 metis_tac[]
QED

Theorem cse_static_trace_splice:
 !tail pre p stem.
 cse_static_trace fn (pre ++ p::tail) /\ cse_static_trace fn stem /\
 LAST stem = p ==> cse_static_trace fn (stem ++ tail)
Proof
 Induct_on `tail` using rich_listTheory.SNOC_INDUCT
 >- simp[] >>
 rpt strip_tac >>
 `cse_static_trace fn (pre ++ p::tail)` by
   (irule cse_static_trace_prefix >>
    conj_tac >- (Cases_on `pre` >> simp[listTheory.APPEND]) >>
    qexists `[x]` >>
    metis_tac[rich_listTheory.SNOC_APPEND, listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
 `cse_static_trace fn (stem ++ tail)` by metis_tac[] >>
 qpat_x_assum `cse_static_trace fn (pre ++ p::SNOC x tail)`
   (strip_assume_tac o PURE_ONCE_REWRITE_RULE [cse_static_trace_cases]) >>
 gvs[rich_listTheory.SNOC_APPEND, listTheory.APPEND_ASSOC] >>
 Cases_on `tail` >>
 gvs[listTheory.APPEND, rich_listTheory.LAST_APPEND_NOT_NIL] >>
 FIRST [irule (cj 2 cse_static_trace_rules),
        irule (cj 3 cse_static_trace_rules)] >>
 simp[] >> qexists `bb` >> simp[]
QED

Theorem cse_static_trace_first_predecessor_excludes[local]:
 wf_function fn /\ cse_static_trace fn (left ++ [p]) /\
 cse_point_has_id fn p d /\ ~MEM p left /\ cse_path_preorder fn d a ==>
 ~(?q. MEM q left /\ cse_point_has_id fn q a)
Proof
 strip_tac >> strip_tac >>
 `cse_static_trace fn left` by
   (irule cse_static_trace_prefix >>
    conj_tac >- (Cases_on `left` >> gvs[]) >>
    qexists `[p]` >> simp[]) >>
 drule_all cse_static_trace_member_prefix >> strip_tac >>
 `?r. MEM r pre /\ cse_point_has_id fn r d` by
   metis_tac[cse_path_preorder_def] >>
 `r = p` by metis_tac[cse_point_has_id_injective] >>
 gvs[listTheory.MEM_APPEND]
QED

Theorem cse_path_preorder_suffix_crossing:
 wf_function fn /\ cse_static_trace fn (pre ++ p::tail) /\
 cse_point_has_id fn p d /\ cse_path_preorder fn d a /\ d <> a /\
 cse_path_preorder fn a c /\ cse_point_has_id fn (LAST (p::tail)) c ==>
 ?q. MEM q tail /\ cse_point_has_id fn q a
Proof
 strip_tac >>
 `MEM p (pre ++ p::tail)` by simp[listTheory.MEM_APPEND] >>
 `?left right. pre ++ p::tail = left ++ p::right /\ ~MEM p left` by
   (qpat_x_assum `MEM p (pre ++ p::tail)`
      (strip_assume_tac o PURE_ONCE_REWRITE_RULE [listTheory.MEM_SPLIT_APPEND_first]) >>
    qexistsl [`pfx`, `sfx`] >> gvs[listTheory.APPEND]) >>
 `cse_static_trace fn (left ++ [p])` by
   (irule cse_static_trace_prefix >>
    conj_tac >- (Cases_on `left` >> simp[listTheory.APPEND]) >>
    qexists `right` >> metis_tac[listTheory.APPEND, listTheory.APPEND_ASSOC]) >>
 `~(?q. MEM q left /\ cse_point_has_id fn q a)` by
   metis_tac[cse_static_trace_first_predecessor_excludes] >>
 `cse_static_trace fn ((left ++ [p]) ++ tail)` by
   (irule cse_static_trace_splice >> simp[] >>
    qexists `pre` >> simp[]) >>
 `?q. MEM q ((left ++ [p]) ++ tail) /\ cse_point_has_id fn q a` by
   (qpat_x_assum `cse_path_preorder fn a c` mp_tac >>
    pure_rewrite_tac[cse_path_preorder_def] >>
    disch_then (qspecl_then [`(left ++ [p]) ++ tail`,
                            `LAST ((left ++ [p]) ++ tail)`] mp_tac) >>
    simp[] >> Cases_on `tail` >>
    gvs[listTheory.APPEND, rich_listTheory.LAST_APPEND_NOT_NIL]) >>
 `~cse_point_has_id fn p a` by
   (PairCases_on `p` >> gvs[cse_point_has_id_def] >> metis_tac[]) >>
 gvs[listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem cse_static_trace_coverage:
 !fn ps. cse_static_trace fn ps ==> !lbl k. LAST ps = (lbl,k) ==>
 ?path entry. path <> [] /\ is_fn_path fn path /\
   fn_entry_label fn = SOME entry /\ HD path = entry /\ LAST path = lbl /\
   (!j. j <= k ==> MEM (lbl,j) ps) /\
   (!d db. MEM d path /\ d <> lbl /\ lookup_block d fn.fn_blocks = SOME db ==>
      !j. j <= LENGTH db.bb_instructions ==> MEM (d,j) ps)
Proof
 gen_tac >> ho_match_mp_tac cse_static_trace_ind >> rpt conj_tac
 >- (rpt strip_tac >> gvs[] >> qexists_tac `[entry]` >>
     simp[venomWfTheory.is_fn_path_def])
 >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
     simp[rich_listTheory.LAST_APPEND_NOT_NIL] >> strip_tac >> gvs[] >>
     qexists_tac `path` >> simp[] >>
     rpt strip_tac >> Cases_on `j = SUC k` >> simp[] >>
     `j <= k` by decide_tac >> metis_tac[]) >>
 rpt gen_tac >> strip_tac >> rpt gen_tac >>
 simp[rich_listTheory.LAST_APPEND_NOT_NIL] >> strip_tac >> gvs[] >>
 `HD (path ++ [lbl']) = HD path` by (Cases_on `path` >> gvs[]) >>
 qexists_tac `path ++ [lbl']` >>
 simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
 conj_tac >- (irule venomExecProofsTheory.is_fn_path_snoc >> simp[]) >>
 rpt strip_tac >> Cases_on `d = LAST path`
 >- (gvs[] >> metis_tac[]) >>
 metis_tac[]
QED

Theorem cse_dominates_local_order_preorder:
 wf_function fn /\
 lookup_block db.bb_label fn.fn_blocks = SOME db /\
 lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
 MEM copy db.bb_instructions /\ MEM use bb.bb_instructions /\
 fn_dominates fn db.bb_label bb.bb_label /\
 (db = bb ==> ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
    EL i bb.bb_instructions = copy /\ EL j bb.bb_instructions = use) ==>
 cse_path_preorder fn copy.inst_id use.inst_id
Proof
 strip_tac >> rewrite_tac[cse_path_preorder_def] >> rpt strip_tac >>
 `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = use` by
   metis_tac[listTheory.MEM_EL] >>
 `cse_point_has_id fn (bb.bb_label,j) use.inst_id` by
   (simp[cse_point_has_id_def] >> metis_tac[]) >>
 `p = (bb.bb_label,j)` by metis_tac[cse_point_has_id_injective] >>
 qpat_x_assum `p = _` SUBST_ALL_TAC >>
 drule_all cse_static_trace_coverage >> strip_tac >>
 `MEM db.bb_label path` by
   (qpat_x_assum `fn_dominates fn _ _` mp_tac >>
    simp[venomWfTheory.fn_dominates_def] >> metis_tac[]) >>
 Cases_on `db.bb_label = bb.bb_label`
 >- (`db = bb` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `db = bb` SUBST_ALL_TAC >>
     qpat_x_assum `bb = bb ==> _` (strip_assume_tac o SRULE []) >>
     `cse_point_has_id fn (bb.bb_label,j') use.inst_id` by
       (simp[cse_point_has_id_def] >> metis_tac[]) >>
     `j' = j` by metis_tac[cse_point_has_id_injective, pairTheory.PAIR_EQ] >>
     qexists_tac `(bb.bb_label,i)` >>
     conj_tac >- metis_tac[arithmeticTheory.LESS_OR_EQ] >>
     simp[cse_point_has_id_def] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
 `?i. i < LENGTH db.bb_instructions /\ EL i db.bb_instructions = copy` by
   metis_tac[listTheory.MEM_EL] >>
 qexists_tac `(db.bb_label,i)` >>
 conj_tac >- metis_tac[arithmeticTheory.LESS_OR_EQ] >>
 simp[cse_point_has_id_def] >> metis_tac[]
QED

Theorem cse_path_preorder_reachable_antisym:
 wf_function fn /\ cse_static_trace fn ps /\
 cse_point_has_id fn (LAST ps) b /\
 cse_path_preorder fn a b /\ cse_path_preorder fn b a ==> a = b
Proof
 strip_tac >> spose_not_then assume_tac >>
 drule_all cse_static_trace_first_id >> strip_tac >>
 `?q. MEM q pre /\ cse_point_has_id fn q a` by
   (qpat_x_assum `cse_path_preorder fn a b` mp_tac >>
    simp[cse_path_preorder_def] >>
    disch_then (qspec_then `pre ++ [p]` mp_tac) >>
    simp[] >>
    `~cse_point_has_id fn p a` by
      (PairCases_on `p` >> gvs[cse_point_has_id_def]) >>
    metis_tac[]) >>
 `pre <> []` by (Cases_on `pre` >> gvs[]) >>
 `cse_static_trace fn pre` by
   (irule cse_static_trace_prefix >> simp[] >> qexists `[p]` >> simp[]) >>
 drule_all cse_static_trace_member_prefix >> strip_tac >>
 gvs[cse_path_preorder_def, listTheory.EVERY_MEM] >>
 metis_tac[listTheory.MEM_APPEND]
QED

Theorem cse_path_preorder_reachable_strict_chain:
 wf_function fn /\ cse_static_trace fn ps /\
 cse_point_has_id fn (LAST ps) b /\
 cse_path_preorder fn r a /\ cse_path_preorder fn a b /\ a <> b ==>
 cse_path_preorder fn r b /\ r <> b
Proof
 strip_tac >> conj_tac
 >- metis_tac[cse_path_preorder_transitive, relationTheory.transitive_def] >>
 spose_not_then assume_tac >> gvs[] >>
 metis_tac[cse_path_preorder_reachable_antisym]
QED
