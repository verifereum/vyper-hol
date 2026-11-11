Theory cseReplayProps
Ancestors cseCanonProps cseHistoryProps cseSourceProps venomInstIdsProps venomWf

(* A final-map collision can be pulled back to an earlier fold stage.
   This is a static descent certificate, not a runtime value theorem. *)
Theorem cse_canon_collision_descent:
 !xs d initial a b.
 a <> b /\
 canonical_id (FOLDL (\c (ae,i). compute_canon_inst d c ae i) initial xs) a =
 canonical_id (FOLDL (\c (ae,i). compute_canon_inst d c ae i) initial xs) b ==>
 canonical_id initial a = canonical_id initial b \/
 ?pre ae inst post src other c.
   xs = pre ++ [(ae,inst)] ++ post /\
   LENGTH pre < LENGTH xs /\
   c = FOLDL (\m (av,i). compute_canon_inst d m av i) initial pre /\
   ((inst.inst_id = a /\ other = b) \/
    (inst.inst_id = b /\ other = a)) /\
   avail_get_source ae (mk_expr d inst) = SOME src /\
   src.inst_id <> inst.inst_id /\ operand_ids_match c d inst src /\
   canonical_id c src.inst_id = canonical_id c other
Proof
 ho_match_mp_tac listTheory.SNOC_INDUCT >> conj_tac
 >- simp[] >>
 rpt gen_tac >> strip_tac >>
 Cases_on `x` >>
 simp[listTheory.FOLDL_SNOC] >> rpt strip_tac >>
 qmatch_asmsub_abbrev_tac `compute_canon_inst d c q r` >>
 Cases_on `canonical_id c a = canonical_id c b`
 >- (first_x_assum (qspecl_then [`d`, `initial`, `a`, `b`] mp_tac) >>
     (impl_tac >- gvs[Abbr `c`]) >>
     strip_tac >- simp[] >> disj2_tac >>
     qexistsl [`pre`, `ae`, `inst`, `SNOC (q,r) post`, `src`, `other`] >>
     simp[listTheory.SNOC_APPEND] >> metis_tac[]) >>
 `compute_canon_inst d c q r <> c` by metis_tac[] >>
 drule compute_canon_inst_changed >> strip_tac >>
 gvs[canonical_id_update] >>
 disj2_tac >>
 Cases_on `a = r.inst_id`
 >- (gvs[] >> qexistsl [`xs`, `q`, `r`, `[]`, `src`, `b`] >>
     simp[listTheory.SNOC_APPEND, Abbr `c`]) >>
 Cases_on `b = r.inst_id` >> gvs[] >>
 qexistsl [`xs`, `q`, `r`, `[]`, `src`, `a`] >>
 simp[listTheory.SNOC_APPEND, Abbr `c`]
QED

(* Replay supplies the equality at the writer; this boundary transports it
   to a later live use, even when other loop iterations occurred. *)
Theorem cse_canonical_edge_live_binding:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 events = pre ++ [CseStep m cb inst u t] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m cb u) /\
 MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
 inst.inst_outputs = [y] /\ EVERY (\ev. ~cse_event_writes ev y) post /\
 MEM src (fn_insts fn) /\ src.inst_outputs = [x] /\
 cse_path_preorder fn src.inst_id inst.inst_id /\
 src.inst_id <> inst.inst_id /\
 cse_path_preorder fn inst.inst_id use.inst_id /\
 inst.inst_id <> use.inst_id /\
 lookup_var y t = lookup_var x u ==>
 lookup_var y s = lookup_var x s
Proof
 strip_tac >>
 `lookup_var x s = lookup_var x u` by
   (irule cse_prefix_live_ordinary_predecessor_binding >> metis_tac[listTheory.MEM]) >>
 `lookup_var y (cse_phase_state (CseExec n bb s)) =
  lookup_var y (cse_event_output (CseStep m cb inst u t))` by
   (irule cse_prefix_suffix_binding >> metis_tac[]) >>
 gvs[cse_phase_state_def, cse_event_output_def]
QED

Theorem cse_canon_input_location:
 wf_function fn /\ MEM (ae,inst) (cse_canon_inputs result fn) ==>
 ?bb k. lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
 k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
 ae = avail_unwrap (df_at NONE result bb.bb_label k)
Proof
 simp[cse_canon_inputs_def, listTheory.MEM_FLAT, listTheory.MEM_MAP,
      indexedListsTheory.MEM_MAPi, PULL_EXISTS] >>
 rpt strip_tac >> gvs[] >>
 goal_assum (drule_at Any) >> simp[] >>
 irule venomExecPropsTheory.MEM_lookup_block >>
 gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]
QED

Theorem canon_expr_root_inversion:
 canon_expr (ExprOp op args) = canon_expr (ExprOp op' bs) ==>
 op = op' /\
 (if is_commutative op then
    PERM (MAP canon_expr args) (MAP canon_expr bs)
  else MAP canon_expr args = MAP canon_expr bs)
Proof
 simp[availExprDefsTheory.canon_expr_def] >>
 Cases_on `is_commutative op` >> Cases_on `is_commutative op'` >> simp[] >>
 strip_tac >> gvs[] >>
 metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_TRANS, sortingTheory.PERM_SYM]
QED

Theorem canon_expr_binary_inversion:
 canon_expr (ExprOp op [a;b]) = canon_expr (ExprOp op [c;d]) ==>
 (canon_expr a = canon_expr c /\ canon_expr b = canon_expr d) \/
 (is_commutative op /\ canon_expr a = canon_expr d /\ canon_expr b = canon_expr c)
Proof
 strip_tac >> drule canon_expr_root_inversion >> simp[] >>
 Cases_on `is_commutative op` >> simp[] >> strip_tac >>
 Cases_on `canon_expr a = canon_expr c`
 >- gvs[sortingTheory.PERM_CONS_IFF, sortingTheory.PERM_SING] >>
 `canon_expr a = canon_expr d` by
   metis_tac[sortingTheory.PERM_MEM_EQ, listTheory.MEM] >>
 gvs[] >> metis_tac[sortingTheory.PERM_MEM_EQ, listTheory.MEM]
QED

Theorem mk_expr_root_inversion:
 mk_expr d inst = mk_expr d src ==>
 inst.inst_opcode = src.inst_opcode /\
 (if is_commutative inst.inst_opcode then
    PERM (MAP canon_expr (MAP (mk_operand_expr d []) inst.inst_operands))
         (MAP canon_expr (MAP (mk_operand_expr d []) src.inst_operands))
  else MAP canon_expr (MAP (mk_operand_expr d []) inst.inst_operands) =
       MAP canon_expr (MAP (mk_operand_expr d []) src.inst_operands))
Proof
 simp[availExprDefsTheory.mk_expr_def] >>
 once_rewrite_tac[availExprDefsTheory.mk_operand_expr_def] >>
 once_rewrite_tac[availExprDefsTheory.mk_operand_expr_def] >>
 metis_tac[canon_expr_root_inversion]
QED

Theorem inst_wf_same_opcode_output_length:
 !i j. inst_wf i /\ inst_wf j /\ i.inst_opcode = j.inst_opcode /\
 i.inst_opcode <> INVOKE ==>
 LENGTH i.inst_outputs = LENGTH j.inst_outputs
Proof
 rpt gen_tac >> strip_tac >>
 Cases_on `i.inst_opcode` >> gvs[] >>
 qpat_x_assum `inst_wf i` mp_tac >>
 qpat_x_assum `inst_wf j` mp_tac >>
 pure_rewrite_tac[venomWfTheory.inst_wf_def] >> asm_rewrite_tac[] >>
 simp[] >> metis_tac[]
QED

Theorem cse_canon_input_source_birth:
 wf_function fn /\
 MEM (ae,inst) (cse_canon_inputs (avail_analyze fn) fn) /\
 avail_get_source ae e = SOME src ==>
 MEM src (fn_insts fn) /\
 avail_source_birth (dfg_build_function fn) e src src
Proof
 strip_tac >> drule_all cse_canon_input_location >> strip_tac >> gvs[] >>
 irule cse_avail_get_source_provenance >> metis_tac[]
QED

Theorem cse_canon_input_member:
 wf_function fn /\ MEM (ae,inst) (cse_canon_inputs result fn) ==>
 MEM inst (fn_insts fn)
Proof
 strip_tac >> drule_all cse_canon_input_location >> strip_tac >>
 simp[venomInstTheory.fn_insts_def] >>
 irule venomInstTheory.fmp_fn_insts_blocks_intro >>
 metis_tac[venomExecPropsTheory.lookup_block_MEM, listTheory.EL_MEM]
QED

Theorem compute_canon_fold_representative_shape:
 !xs. EVERY (\p. MEM p (cse_canon_inputs (avail_analyze fn) fn)) xs ==>
 wf_function fn /\ fn_inst_wf fn ==>
 !i. MEM i (fn_insts fn) ==>
 ?r. MEM r (fn_insts fn) /\
 r.inst_id = canonical_id (FOLDL (\c (ae,j). compute_canon_inst
   (dfg_build_function fn) c ae j) FEMPTY xs) i.inst_id /\
 r.inst_opcode = i.inst_opcode /\
 LENGTH r.inst_outputs = LENGTH i.inst_outputs
Proof
 ho_match_mp_tac listTheory.SNOC_INDUCT >> conj_tac
 >- (simp[cseDefsTheory.canonical_id_def] >> metis_tac[]) >>
 rpt gen_tac >> strip_tac >> Cases_on `x` >>
 simp[listTheory.EVERY_SNOC, listTheory.FOLDL_SNOC] >>
 rpt strip_tac >>
 qmatch_goalsub_abbrev_tac `compute_canon_inst d c ae inst` >>
 Cases_on `compute_canon_inst d c ae inst = c`
 >- (simp[] >> first_x_assum irule >> simp[]) >>
 drule compute_canon_inst_changed >> strip_tac >>
 simp[canonical_id_update] >>
 Cases_on `i.inst_id = inst.inst_id`
 >- (`MEM inst (fn_insts fn)` by metis_tac[cse_canon_input_member] >>
     `i = inst` by metis_tac[fn_inst_ids_distinct_inj, wf_function_def] >>
     qpat_x_assum `i = inst` (SUBST_ALL_TAC) >>
     `MEM src (fn_insts fn) /\
      avail_source_birth d (mk_expr d inst) src src` by
       (simp[Abbr `d`] >> irule cse_canon_input_source_birth >> metis_tac[]) >>
     `inst.inst_opcode = src.inst_opcode` by
       metis_tac[availExprProofsTheory.avail_source_birth_def, mk_expr_root_inversion] >>
     `EVERY inst_wf (fn_insts fn)` by
       (gvs[venomWfTheory.fn_inst_wf_def, venomInstTheory.fn_insts_def] >>
        qpat_x_assum `!bb inst. _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        qspec_tac (`fn.fn_blocks`, `bbs`) >> Induct >>
        simp[venomInstTheory.fn_insts_blocks_def, listTheory.EVERY_MEM] >>
        fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
     `LENGTH src.inst_outputs = LENGTH inst.inst_outputs` by
       (irule inst_wf_same_opcode_output_length >>
        gvs[listTheory.EVERY_MEM, availExprProofsTheory.avail_source_birth_def,
            availExprDefsTheory.avail_nonidempotent_def, venomEffectsTheory.is_nonidempotent_def] >>
        metis_tac[venomEffectsTheory.is_nonidempotent_def]) >>
     metis_tac[]) >>
 simp[] >> first_x_assum irule >> simp[]
QED

Theorem compute_canon_stage_representative_shape:
 wf_function fn /\ fn_inst_wf fn /\ MEM i (fn_insts fn) ==>
 ?r. MEM r (fn_insts fn) /\
 r.inst_id = canonical_id (FOLDL (\c (ae,j). compute_canon_inst
   (dfg_build_function fn) c ae j) FEMPTY
   (TAKE k (cse_canon_inputs (avail_analyze fn) fn))) i.inst_id /\
 r.inst_opcode = i.inst_opcode /\
 LENGTH r.inst_outputs = LENGTH i.inst_outputs
Proof
 strip_tac >> irule compute_canon_fold_representative_shape >>
 simp[listTheory.EVERY_MEM] >> metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem compute_canon_fold_opaque_identity:
 !xs. EVERY (\p. MEM p (cse_canon_inputs (avail_analyze fn) fn)) xs ==>
 wf_function fn ==>
 !i. MEM i (fn_insts fn) /\
 (is_pseudo i.inst_opcode \/ i.inst_opcode = ASSIGN \/
  is_terminator i.inst_opcode \/ 1 < LENGTH i.inst_outputs) ==>
 canonical_id (FOLDL (\c (ae,j). compute_canon_inst
   (dfg_build_function fn) c ae j) FEMPTY xs) i.inst_id = i.inst_id
Proof
 ho_match_mp_tac listTheory.SNOC_INDUCT >> conj_tac
 >- simp[cseDefsTheory.canonical_id_def] >>
 rpt gen_tac >> strip_tac >> Cases_on `x` >>
 simp[listTheory.EVERY_SNOC, listTheory.FOLDL_SNOC] >> rpt strip_tac >>
 (qmatch_goalsub_abbrev_tac `compute_canon_inst d c ae inst` >>
 Cases_on `compute_canon_inst d c ae inst = c`
 >- (simp[] >> first_x_assum irule >> simp[]) >>
 drule compute_canon_inst_changed >> strip_tac >>
 `MEM inst (fn_insts fn)` by metis_tac[cse_canon_input_member] >>
 `i.inst_id <> inst.inst_id` by
   (strip_tac >> `i = inst` by metis_tac[fn_inst_ids_distinct_inj, wf_function_def] >> gvs[]) >>
 simp[canonical_id_update] >> first_x_assum irule >> simp[])
QED

Theorem compute_canon_stage_opaque_identity:
 wf_function fn /\ MEM i (fn_insts fn) /\
 (is_pseudo i.inst_opcode \/ i.inst_opcode = ASSIGN \/
  is_terminator i.inst_opcode \/ 1 < LENGTH i.inst_outputs) ==>
 canonical_id (FOLDL (\c (ae,j). compute_canon_inst
   (dfg_build_function fn) c ae j) FEMPTY
   (TAKE k (cse_canon_inputs (avail_analyze fn) fn))) i.inst_id = i.inst_id
Proof
 strip_tac >> irule compute_canon_fold_opaque_identity >>
 simp[listTheory.EVERY_MEM] >> metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem compute_canon_stage_opaque_isolation:
 wf_function fn /\ fn_inst_wf fn /\
 MEM i (fn_insts fn) /\ MEM j (fn_insts fn) /\
 (is_pseudo j.inst_opcode \/ j.inst_opcode = ASSIGN \/
  is_terminator j.inst_opcode \/ 1 < LENGTH j.inst_outputs) /\
 canonical_id (FOLDL (\c (ae,n). compute_canon_inst
   (dfg_build_function fn) c ae n) FEMPTY
   (TAKE k (cse_canon_inputs (avail_analyze fn) fn))) i.inst_id = j.inst_id ==>
 i = j
Proof
 strip_tac >>
 `?r. MEM r (fn_insts fn) /\
   r.inst_id = canonical_id (FOLDL (\c (ae,n). compute_canon_inst
     (dfg_build_function fn) c ae n) FEMPTY
     (TAKE k (cse_canon_inputs (avail_analyze fn) fn))) i.inst_id /\
   r.inst_opcode = i.inst_opcode /\
   LENGTH r.inst_outputs = LENGTH i.inst_outputs` by
   metis_tac[compute_canon_stage_representative_shape] >>
 `r = j` by metis_tac[fn_inst_ids_distinct_inj, wf_function_def] >>
 `canonical_id (FOLDL (\c (ae,n). compute_canon_inst
   (dfg_build_function fn) c ae n) FEMPTY
   (TAKE k (cse_canon_inputs (avail_analyze fn) fn))) i.inst_id = i.inst_id` by
   (irule compute_canon_stage_opaque_identity >> metis_tac[]) >>
 metis_tac[fn_inst_ids_distinct_inj, wf_function_def]
QED

Theorem operand_producer_expression_shape:
 !d visited op. !seen k.
 set seen = visited /\ operand_producer d visited op = SOME k /\
 (!v inst. FLOOKUP d.dfg_defs v = SOME inst ==> inst_wf inst) ==>
 ?v inst. FLOOKUP d.dfg_defs v = SOME inst /\ inst.inst_id = k /\
 inst.inst_opcode <> ASSIGN /\
 ((is_pseudo inst.inst_opcode \/ 1 < LENGTH inst.inst_outputs) ==>
   ?x. mk_operand_expr d seen op = ExprVar x) /\
 ((~is_pseudo inst.inst_opcode /\ LENGTH inst.inst_outputs <= 1) ==>
   ?args. mk_operand_expr d seen op = ExprOp inst.inst_opcode args)
Proof
 recInduct cseDefsTheory.operand_producer_ind >> rpt strip_tac >>
 gvs[Once cseDefsTheory.operand_producer_def, AllCaseEqs()]
 >- (res_tac >> gvs[venomWfTheory.inst_wf_def])
 >- (first_x_assum (qspec_then `v::seen` mp_tac) >>
     simp[] >> strip_tac >>
     `mk_operand_expr dfg seen (Var v) = mk_operand_expr dfg (v::seen) op` by
       simp[Once availExprDefsTheory.mk_operand_expr_def,
            dfgDefsTheory.dfg_get_def_def, venomInstTheory.is_pseudo_def] >>
     asm_rewrite_tac[] >> metis_tac[])
 >- (res_tac >> gvs[venomWfTheory.inst_wf_def]) >>
 qexistsl [`v`, `inst`] >> simp[] >>
 Cases_on `is_pseudo inst.inst_opcode`
 >- simp[Once availExprDefsTheory.mk_operand_expr_def,
         dfgDefsTheory.dfg_get_def_def] >>
 Cases_on `1 < LENGTH inst.inst_outputs` >>
 simp[availExprDefsTheory.mk_operand_expr_def,
      dfgDefsTheory.dfg_get_def_def, availExprDefsTheory.canon_expr_def] >>
 IF_CASES_TAC >> simp[]
QED

Theorem fn_operand_producer_expression_shape:
 fn_inst_wf fn /\
 operand_producer (dfg_build_function fn) {} op = SOME k ==>
 ?v inst. FLOOKUP (dfg_build_function fn).dfg_defs v = SOME inst /\
   MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs /\ inst.inst_id = k /\
   inst.inst_opcode <> ASSIGN /\
   ((is_pseudo inst.inst_opcode \/ 1 < LENGTH inst.inst_outputs) ==>
     ?x. mk_operand_expr (dfg_build_function fn) [] op = ExprVar x) /\
   ((~is_pseudo inst.inst_opcode /\ LENGTH inst.inst_outputs <= 1) ==>
     ?args. mk_operand_expr (dfg_build_function fn) [] op = ExprOp inst.inst_opcode args)
Proof
 strip_tac >>
 `!v inst. FLOOKUP (dfg_build_function fn).dfg_defs v = SOME inst ==> inst_wf inst` by
   (rpt strip_tac >>
    `!bbs. MEM inst (fn_insts_blocks bbs) ==>
       ?b. MEM b bbs /\ MEM inst b.bb_instructions` by
      (Induct >> simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]) >>
    metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct,
              dfgDefsTheory.dfg_get_def_def, venomInstTheory.fn_insts_def,
              venomWfTheory.fn_inst_wf_def]) >>
 drule_at (Pos (el 2)) operand_producer_expression_shape >>
 disch_then (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
 metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct,
           dfgDefsTheory.dfg_get_def_def]
QED

(* Positional producer matching and expression permutations are distinct:
   ordinary pairs use positional values; leaf pairs follow the expression. *)
Theorem binary_category_value_alignment:
 !P E f g a b c d.
 ((E a = E c /\ E b = E d) \/ (E a = E d /\ E b = E c)) /\
 (P a <=> P c) /\ (P b <=> P d) /\
 (!x y. MEM x [a;b] /\ MEM y [c;d] /\ E x = E y ==> (P x <=> P y)) /\
 (P a ==> f a = g c) /\ (P b ==> f b = g d) /\
 (!x y. MEM x [a;b] /\ MEM y [c;d] /\ ~P x /\ ~P y /\ E x = E y ==>
        f x = g y) ==>
 [f a;f b] = [g c;g d] \/ [f a;f b] = REVERSE [g c;g d]
Proof
 rpt gen_tac >> strip_tac >>
 Cases_on `P a` >> Cases_on `P b` >> gvs[] >>
 metis_tac[]
QED

Theorem positional_category_value_alignment:
 !xs ys P E f g.
 MAP E xs = MAP E ys /\
 LIST_REL (\x y. (P x <=> P y) /\ (P x ==> f x = g y)) xs ys /\
 (!x y. MEM x xs /\ MEM y ys /\ ~P x /\ ~P y /\ E x = E y ==>
        f x = g y) ==>
 MAP f xs = MAP g ys
Proof
 Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem canon_root_category_value_alignment:
 !xs ys opc P E f g.
 canon_expr (ExprOp opc (MAP E xs)) = canon_expr (ExprOp opc (MAP E ys)) /\
 (is_commutative opc ==> LENGTH xs = 2 /\ LENGTH ys = 2) /\
 LIST_REL (\x y. (P x <=> P y) /\ (P x ==> f x = g y)) xs ys /\
 (!x y. MEM x xs /\ MEM y ys /\ canon_expr (E x) = canon_expr (E y) ==>
        (P x <=> P y)) /\
 (!x y. MEM x xs /\ MEM y ys /\ ~P x /\ ~P y /\
        canon_expr (E x) = canon_expr (E y) ==> f x = g y) ==>
 MAP f xs = MAP g ys \/
 (is_commutative opc /\ LENGTH xs = 2 /\ LENGTH ys = 2 /\
  MAP f xs = REVERSE (MAP g ys))
Proof
 rpt gen_tac >> strip_tac >> Cases_on `is_commutative opc`
 >- (`?a b. xs = [a;b]` by
       (Cases_on `xs` >> gvs[] >> Cases_on `t` >> gvs[] >>
        Cases_on `t'` >> gvs[]) >>
     `?c d. ys = [c;d]` by
       (Cases_on `ys` >> gvs[] >> Cases_on `t` >> gvs[] >>
        Cases_on `t'` >> gvs[]) >>
     gvs[] >> drule canon_expr_binary_inversion >> strip_tac >>
     simp[] >> metis_tac[binary_category_value_alignment]) >>
 disj1_tac >> drule canon_expr_root_inversion >> simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
 strip_tac >> irule (INST_TYPE [beta |-> ``:avail_expr``]
                              positional_category_value_alignment) >>
 qexistsl [`\x. canon_expr (E x)`, `P`] >> simp[]
QED

Theorem operand_producer_expression_ordinary_iff:
 wf_function fn /\ fn_inst_wf fn /\ MEM inst (fn_insts fn) /\
 operand_producer (dfg_build_function fn) {} op = SOME inst.inst_id ==>
 ((?opc args. mk_operand_expr (dfg_build_function fn) [] op = ExprOp opc args) <=>
  ~is_pseudo inst.inst_opcode /\ LENGTH inst.inst_outputs <= 1)
Proof
 strip_tac >> drule_all fn_operand_producer_expression_shape >> strip_tac >>
 `inst' = inst` by metis_tac[fn_inst_ids_distinct_inj, wf_function_def] >> gvs[] >>
 Cases_on `is_pseudo inst.inst_opcode` >>
 Cases_on `1 < LENGTH inst.inst_outputs` >> gvs[] >> metis_tac[]
QED

Theorem compute_canon_stage_operand_category:
 wf_function fn /\ fn_inst_wf fn /\
 OPTION_MAP (canonical_id (FOLDL (\c (ae,i). compute_canon_inst
   (dfg_build_function fn) c ae i) FEMPTY
   (TAKE k (cse_canon_inputs (avail_analyze fn) fn))))
   (operand_producer (dfg_build_function fn) {} op) =
 OPTION_MAP (canonical_id (FOLDL (\c (ae,i). compute_canon_inst
   (dfg_build_function fn) c ae i) FEMPTY
   (TAKE k (cse_canon_inputs (avail_analyze fn) fn))))
   (operand_producer (dfg_build_function fn) {} sop) ==>
 ((?opc args. mk_operand_expr (dfg_build_function fn) [] op = ExprOp opc args) <=>
  (?opc args. mk_operand_expr (dfg_build_function fn) [] sop = ExprOp opc args))
Proof
 strip_tac >>
 Cases_on `operand_producer (dfg_build_function fn) {} op`
 >- (gvs[] >> imp_res_tac operand_producer_none_leaf_empty >> gvs[]) >>
 Cases_on `operand_producer (dfg_build_function fn) {} sop` >> gvs[] >>
 `?v i. FLOOKUP (dfg_build_function fn).dfg_defs v = SOME i /\
   MEM i (fn_insts fn) /\ MEM v i.inst_outputs /\ i.inst_id = x /\
   i.inst_opcode <> ASSIGN` by metis_tac[fn_operand_producer_expression_shape] >>
 `?w j. FLOOKUP (dfg_build_function fn).dfg_defs w = SOME j /\
   MEM j (fn_insts fn) /\ MEM w j.inst_outputs /\ j.inst_id = x' /\
   j.inst_opcode <> ASSIGN` by metis_tac[fn_operand_producer_expression_shape] >>
 `((?opc args. mk_operand_expr (dfg_build_function fn) [] op = ExprOp opc args) <=>
    ~is_pseudo i.inst_opcode /\ LENGTH i.inst_outputs <= 1)` by
   metis_tac[operand_producer_expression_ordinary_iff] >>
 `((?opc args. mk_operand_expr (dfg_build_function fn) [] sop = ExprOp opc args) <=>
    ~is_pseudo j.inst_opcode /\ LENGTH j.inst_outputs <= 1)` by
   metis_tac[operand_producer_expression_ordinary_iff] >>
 gvs[] >>
 `((is_pseudo i.inst_opcode \/ 1 < LENGTH i.inst_outputs) ==> i = j) /\
  ((is_pseudo j.inst_opcode \/ 1 < LENGTH j.inst_outputs) ==> i = j)` by
   metis_tac[compute_canon_stage_opaque_identity,
             compute_canon_stage_opaque_isolation] >>
 metis_tac[arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem canon_expr_has_op_iff:
 !e. (?opc args. canon_expr e = ExprOp opc args) <=>
     (?opc args. e = ExprOp opc args)
Proof
 Cases >> simp[availExprDefsTheory.canon_expr_def] >> IF_CASES_TAC >> simp[]
QED

Theorem compute_canon_stage_operand_categories:
 wf_function fn /\ fn_inst_wf fn /\
 operand_ids_match (FOLDL (\c (ae,i). compute_canon_inst
   (dfg_build_function fn) c ae i) FEMPTY
   (TAKE k (cse_canon_inputs (avail_analyze fn) fn)))
   (dfg_build_function fn) inst src ==>
 LIST_REL (\op sop.
   (?opc args. mk_operand_expr (dfg_build_function fn) [] op = ExprOp opc args) <=>
   (?opc args. mk_operand_expr (dfg_build_function fn) [] sop = ExprOp opc args))
   inst.inst_operands src.inst_operands
Proof
 strip_tac >> simp[listTheory.LIST_REL_EL_EQN] >>
 conj_tac >- metis_tac[operand_ids_match_length] >>
 rpt strip_tac >> irule compute_canon_stage_operand_category >>
 simp[] >> qexists_tac `k` >>
 drule_all operand_ids_match_nth >> strip_tac >> simp[]
QED

Theorem cse_prefix_equal_expression_none_iff:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 cse_prefix ctx' fn fuel0' s0' events' (CseExec n' bb' s') /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 get_instruction bb' s'.vs_inst_idx = SOME use' /\
 use.inst_opcode <> PHI /\ use'.inst_opcode <> PHI /\
 MEM op use.inst_operands /\ MEM op' use'.inst_operands /\
 mk_operand_expr (dfg_build_function fn) [] op =
 mk_operand_expr (dfg_build_function fn) [] op' ==>
 (operand_producer (dfg_build_function fn) {} op = NONE <=>
  operand_producer (dfg_build_function fn) {} op' = NONE)
Proof
 strip_tac >>
 Cases_on `operand_producer (dfg_build_function fn) {} op` >>
 Cases_on `operand_producer (dfg_build_function fn) {} op'` >> simp[] >>
 drule_all cse_prefix_operand_producer_none_rewind >> strip_tac >>
 drule_all fn_operand_producer_expression_shape >> strip_tac >>
 gvs[] >>
 Cases_on `is_pseudo inst.inst_opcode \/ 1 < LENGTH inst.inst_outputs` >>
 gvs[] >> metis_tac[arithmeticTheory.NOT_LESS_EQUAL,
                    availExprDefsTheory.avail_expr_distinct]
QED

Theorem cse_source_interval_leaf_operands_equal:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME use /\
 use.inst_opcode <> PHI /\ MEM op use.inst_operands /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 src.inst_opcode <> PHI /\ MEM sop src.inst_operands /\ MEM src (fn_insts fn) /\
 ~is_pseudo src.inst_opcode /\ LENGTH src.inst_outputs <= 1 /\
 mk_operand_expr (dfg_build_function fn) [] op =
 mk_operand_expr (dfg_build_function fn) [] sop /\
 ~(?opc args. mk_operand_expr (dfg_build_function fn) [] sop = ExprOp opc args) /\
 (!k ph. LENGTH pre < k /\ k <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE k events) ph ==>
   cse_phase_has_source fn ph e src) ==>
 eval_operand op s = eval_operand sop u
Proof
 strip_tac >>
 `operand_producer (dfg_build_function fn) {} op = NONE <=>
  operand_producer (dfg_build_function fn) {} sop = NONE` by
   (irule cse_prefix_equal_expression_none_iff >> metis_tac[]) >>
 Cases_on `operand_producer (dfg_build_function fn) {} sop`
 >- (irule cse_prefix_none_operands_equal >> metis_tac[]) >>
 `?a di. FLOOKUP (dfg_build_function fn).dfg_defs a = SOME di /\
   MEM di (fn_insts fn) /\ MEM a di.inst_outputs /\ di.inst_id = x /\
   di.inst_opcode <> ASSIGN` by metis_tac[fn_operand_producer_expression_shape] >>
 `is_pseudo di.inst_opcode \/ 1 < LENGTH di.inst_outputs` by
   metis_tac[operand_producer_expression_ordinary_iff, arithmeticTheory.NOT_LESS_EQUAL] >>
 `?y. MEM y di.inst_outputs /\
   mk_operand_expr (dfg_build_function fn) [] sop = ExprVar y /\
   eval_operand sop u = lookup_var y u /\
   cse_path_preorder fn di.inst_id src.inst_id` by
   (irule cse_prefix_opaque_operand_current_binding >> metis_tac[]) >>
 `?id. operand_producer (dfg_build_function fn) {} op = SOME id` by
   (Cases_on `operand_producer (dfg_build_function fn) {} op` >> gvs[]) >>
 `?a dj. FLOOKUP (dfg_build_function fn).dfg_defs a = SOME dj /\
   MEM dj (fn_insts fn) /\ MEM a dj.inst_outputs /\ dj.inst_id = id /\
   dj.inst_opcode <> ASSIGN` by metis_tac[fn_operand_producer_expression_shape] >>
 `is_pseudo dj.inst_opcode \/ 1 < LENGTH dj.inst_outputs` by
   metis_tac[operand_producer_expression_ordinary_iff, arithmeticTheory.NOT_LESS_EQUAL] >>
 `?z. MEM z dj.inst_outputs /\
   mk_operand_expr (dfg_build_function fn) [] op = ExprVar z /\
   eval_operand op s = lookup_var z s /\
   cse_path_preorder fn dj.inst_id use.inst_id` by
   (irule cse_prefix_opaque_operand_current_binding >> metis_tac[]) >>
 `z = y` by metis_tac[availExprDefsTheory.avail_expr_11] >>
 `di.inst_id <> src.inst_id` by
   (strip_tac >> `di = src` by metis_tac[fn_inst_ids_distinct_inj, wf_function_def] >> gvs[]) >>
 drule_all cse_source_interval_predecessor_binding_all >> gvs[]
QED

Theorem cse_source_interval_operand_alignment:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 d = dfg_build_function fn /\
 c = FOLDL (\c (ae,i). compute_canon_inst d c ae i) FEMPTY
       (TAKE k (cse_canon_inputs (avail_analyze fn) fn)) /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI /\
 events = pre ++ [CseStep m sb src u v] ++ post /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 src.inst_opcode <> PHI /\ MEM src (fn_insts fn) /\
 ~is_pseudo src.inst_opcode /\ LENGTH src.inst_outputs <= 1 /\
 mk_expr d inst = mk_expr d src /\ operand_ids_match c d inst src /\
 (!j ph. LENGTH pre < j /\ j <= LENGTH events /\
   cse_prefix ctx fn fuel0 s0 (TAKE j events) ph ==>
   cse_phase_has_source fn ph e src) /\
 (!op sop a b.
   MEM op inst.inst_operands /\ MEM sop src.inst_operands /\
   operand_producer d {} op = SOME a /\
   operand_producer d {} sop = SOME b /\
   (?opc args. mk_operand_expr d [] op = ExprOp opc args) /\
   (?opc args. mk_operand_expr d [] sop = ExprOp opc args) /\
   canonical_id c a = canonical_id c b ==>
   eval_operand op s = eval_operand sop u) ==>
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands \/
 (is_commutative inst.inst_opcode /\ LENGTH src.inst_operands = 2 /\
  LENGTH inst.inst_operands = 2 /\
  MAP (\op. eval_operand op u) src.inst_operands =
  REVERSE (MAP (\op. eval_operand op s) inst.inst_operands))
Proof
 strip_tac >>
 `inst.inst_opcode = src.inst_opcode` by metis_tac[mk_expr_root_inversion] >>
 irule canon_root_category_value_alignment >>
 conj_tac
 >- (`inst_wf src` by
       (drule_all cse_prefix_exec_control >> strip_tac >>
        `MEM sb fn.fn_blocks` by metis_tac[venomInstTheory.selected_block_mem] >>
        gvs[venomWfTheory.fn_inst_wf_def,
            venomInstTheory.get_instruction_def] >>
        metis_tac[listTheory.EL_MEM]) >>
     `LENGTH src.inst_operands = LENGTH inst.inst_operands` by
       metis_tac[operand_ids_match_length] >>
     simp[] >>
     qpat_x_assum `inst_wf src` mp_tac >>
     Cases_on `src.inst_opcode` >>
     simp[venomEffectsTheory.is_commutative_def, venomWfTheory.inst_wf_def]) >>
 qexistsl [`mk_operand_expr d []`,
           `\op. ?opc args. mk_operand_expr d [] op = ExprOp opc args`] >>
 simp[] >> rpt conj_tac
 >- (rpt gen_tac >> strip_tac >>
     `mk_operand_expr (dfg_build_function fn) [] x =
      mk_operand_expr (dfg_build_function fn) [] y` by
       (Cases_on `mk_operand_expr (dfg_build_function fn) [] x` >>
        Cases_on `mk_operand_expr (dfg_build_function fn) [] y` >>
        gvs[availExprDefsTheory.canon_expr_def]) >>
     sym_tac >> irule cse_source_interval_leaf_operands_equal >> metis_tac[]) 
 >- metis_tac[canon_expr_has_op_iff]
 >- (gvs[availExprDefsTheory.mk_expr_def, availExprDefsTheory.mk_operand_expr_def,
          ETA_THM] >> metis_tac[]) >>
 `LIST_REL (\op sop.
   (?opc args. mk_operand_expr d [] op = ExprOp opc args) <=>
   (?opc args. mk_operand_expr d [] sop = ExprOp opc args))
   inst.inst_operands src.inst_operands` by
   metis_tac[compute_canon_stage_operand_categories] >>
 fs[listTheory.LIST_REL_EL_EQN] >> qx_gen_tac `j` >> strip_tac >>
 conj_tac >- metis_tac[] >> strip_tac >>
 `j < LENGTH inst.inst_operands` by metis_tac[] >>
 drule_all operand_ids_match_nth >>
 strip_tac
 >- (drule operand_producer_none_leaf_empty >>
     gvs[] >> metis_tac[availExprDefsTheory.avail_expr_distinct]) >>
 metis_tac[listTheory.EL_MEM]
QED
