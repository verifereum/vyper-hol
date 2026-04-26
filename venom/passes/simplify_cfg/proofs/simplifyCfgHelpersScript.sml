(*
 * Simplify CFG — Structural Helper Lemmas
 *
 * Properties of fix_all_phis, collapse_dfs sub-operations
 * needed by the main correctness proof.
 *)

Theory simplifyCfgHelpers
Ancestors
  simplifyCfgDefs stateEquiv venomExecSemantics venomWf
  venomInst venomState cfgTransform stateEquivProps cfgTransformProps
  venomExecProps cfgTransformProofs venomExecProofs

(* ===== fix_phis_in_block preserves block labels ===== *)

Theorem fix_phis_in_block_label:
  !preds bb. (fix_phis_in_block preds bb).bb_label = bb.bb_label
Proof
  rw[fix_phis_in_block_def, LET_THM] >>
  pairarg_tac >> simp[]
QED

(* ===== fn_entry_label preserved by fix_all_phis ===== *)

Theorem fn_entry_label_fix_all_phis:
  !func. fn_entry_label (fix_all_phis func) = fn_entry_label func
Proof
  rw[fix_all_phis_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `func.fn_blocks` >> simp[fix_phis_in_block_label]
QED

(* ===== fn_labels preserved by fix_all_phis ===== *)

Theorem fn_labels_fix_all_phis:
  !func. fn_labels (fix_all_phis func) = fn_labels func
Proof
  rw[fix_all_phis_def, fn_labels_def, listTheory.MAP_MAP_o,
     combinTheory.o_DEF, fix_phis_in_block_label]
QED

(* ===== update_succ_phi_labels preserves fn_entry_label ===== *)

(* update_succ_phi_labels preserves block labels (MAP bb_label) *)
(* Helper: the FOLDL body of update_succ_phi_labels preserves MAP bb_label *)
Theorem FOLDL_update_phi_preserves_labels[local]:
  !succs old_lbl new_lbl bbs.
    MAP (\bb. bb.bb_label)
      (FOLDL (\bs s.
         case lookup_block s bs of
           NONE => bs
         | SOME sbb =>
             replace_block s
               (sbb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                              else subst_label_inst old_lbl new_lbl inst)
                      sbb.bb_instructions) bs) bbs succs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  fs[lookup_block_def] >>
  imp_res_tac venomExecPropsTheory.FIND_P >> fs[] >>
  irule cfgTransformPropsTheory.fn_labels_replace_block >> simp[]
QED

Theorem MAP_bb_label_update_succ_phi_labels:
  !old_lbl new_lbl bbs succs.
    MAP (\bb. bb.bb_label)
      (update_succ_phi_labels old_lbl new_lbl bbs succs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  rw[update_succ_phi_labels_def, FOLDL_update_phi_preserves_labels]
QED

(* General: fn_entry_label depends only on MAP bb_label *)
Theorem fn_entry_label_same_labels[local]:
  !bbs1 bbs2.
    MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) bbs2 ==>
    fn_entry_label (<| fn_blocks := bbs1 |>) =
    fn_entry_label (<| fn_blocks := bbs2 |>)
Proof
  Cases >> Cases >> simp[fn_entry_label_def, entry_block_def]
QED

Theorem fn_entry_label_update_succ_phi_labels:
  !old_lbl new_lbl bbs succs.
    fn_entry_label (<| fn_blocks :=
      update_succ_phi_labels old_lbl new_lbl bbs succs |>) =
    fn_entry_label (<| fn_blocks := bbs |>)
Proof
  rpt gen_tac >>
  irule fn_entry_label_same_labels >>
  simp[MAP_bb_label_update_succ_phi_labels]
QED

(* ===== fn_entry_label for replace_block + remove_block combo ===== *)

(* When we merge lbl's successor next_lbl into lbl:
   replace_block lbl merged (remove_block next_lbl bbs)
   The entry (first block) is preserved if:
   - next_lbl is not the first block's label (so remove doesn't drop it)
   - merged.bb_label = lbl (so replace preserves it)  *)
Theorem fn_entry_label_merge_step:
  !func lbl next_lbl merged.
    func.fn_blocks <> [] /\
    (HD func.fn_blocks).bb_label <> next_lbl /\
    merged.bb_label = lbl ==>
    fn_entry_label
      (func with fn_blocks :=
        replace_block lbl merged
          (remove_block next_lbl func.fn_blocks)) =
    fn_entry_label func
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`lbl`, `merged`,
    `func with fn_blocks := remove_block next_lbl func.fn_blocks`]
    cfgTransformPropsTheory.fn_entry_label_replace_block) >>
  simp[] >>
  mp_tac (Q.SPECL [`func`, `next_lbl`]
    cfgTransformPropsTheory.fn_entry_label_remove_neq) >>
  simp[]
QED

(* ===== try_bypass preserves fn_entry_label ===== *)

(* try_bypass uses do_merge_jump which does:
   replace_block a.bb_label a' (replace_block target_lbl target' (remove_block b.bb_label ...))
   The entry is preserved if b.bb_label is not the entry.
   b is a trivial-jump block being bypassed; it has num_preds = 1. *)

Theorem fn_entry_label_do_merge_jump:
  !func a b lm func' lm'.
    do_merge_jump func a b lm = SOME (func', lm') /\
    func.fn_blocks <> [] /\
    (HD func.fn_blocks).bb_label <> b.bb_label ==>
    fn_entry_label func' = fn_entry_label func
Proof
  rw[do_merge_jump_def] >>
  BasicProvers.every_case_tac >> gvs[LET_THM] >>
  SUBGOAL_THEN ``x.bb_label = (h:string)`` ASSUME_TAC
  >- (fs[lookup_block_def] >>
      imp_res_tac venomExecPropsTheory.FIND_P >> fs[]) >>
  rw[fn_entry_label_def, entry_block_def,
     replace_block_def, remove_block_def] >>
  Cases_on `func.fn_blocks` >> fs[] >>
  simp[listTheory.FILTER, listTheory.MAP] >>
  rpt IF_CASES_TAC >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem fn_entry_label_try_bypass:
  !succs func lm bb func' lm' bypassed.
    try_bypass func lm bb succs = (func', lm', bypassed) /\
    func.fn_blocks <> [] /\
    (!next_lbl next_bb. MEM next_lbl succs /\
      lookup_block next_lbl func.fn_blocks = SOME next_bb /\
      can_bypass_jump func bb next_bb ==>
      (HD func.fn_blocks).bb_label <> next_bb.bb_label) ==>
    fn_entry_label func' = fn_entry_label func
Proof
  Induct_on `succs` >> rw[try_bypass_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  (* try_bypass_F_unchanged case *)
  TRY (
    imp_res_tac simplifyCfgDefsTheory.try_bypass_F_unchanged >> gvs[] >> NO_TAC
  ) >>
  (* do_merge_jump success case: func' comes from do_merge_jump, not IH *)
  TRY (
    mp_tac fn_entry_label_do_merge_jump >>
    disch_then (qspecl_then [`func`, `bb`, `x`, `lm`, `func'`, `lm'`] mp_tac) >>
    impl_tac >- (
      simp[] >>
      qpat_x_assum `!next_lbl next_bb. _`
        (qspecl_then [`h`, `x`] mp_tac) >>
      simp[listTheory.MEM]
    ) >> simp[] >> NO_TAC
  ) >>
  (* Recursive cases: func' comes from try_bypass on rest *)
  qpat_x_assum `!func lm bb. _`
    (qspecl_then [`func`, `lm`, `bb`] mp_tac) >>
  simp[] >>
  disch_then irule >>
  rpt gen_tac >> strip_tac >> res_tac
QED


(* ===== collapse_dfs preserves fn_entry_label (disjunctive) ===== *)

(* Either fn_entry_label is preserved, or fn_blocks is emptied.
   The entry block is always the ABSORBER in merges (DFS processes it first).
   The only way entry gets removed is self-merge, which empties fn_blocks. *)
(*  Helper: can_merge_blocks + lookup ==> fn_blocks <> [] /\ HD.bb_label <> target *)
Theorem can_merge_entry_ne[local]:
  !func bb next_bb.
    can_merge_blocks func bb next_bb /\
    func.fn_blocks <> [] ==>
    (HD func.fn_blocks).bb_label <> next_bb.bb_label
Proof
  rw[can_merge_blocks_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `func.fn_blocks` >> fs[]
QED

Theorem can_bypass_entry_ne[local]:
  !func bb next_bb.
    can_bypass_jump func bb next_bb /\
    func.fn_blocks <> [] ==>
    (HD func.fn_blocks).bb_label <> next_bb.bb_label
Proof
  rw[can_bypass_jump_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `func.fn_blocks` >> fs[]
QED

Theorem lookup_block_fn_blocks_ne[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bbs <> []
Proof
  rw[lookup_block_def] >> Cases_on `bbs` >> fs[listTheory.FIND_thm]
QED

(* fn_entry_label of record update = fn_entry_label of record literal *)
Theorem fn_entry_label_with_fn_blocks[local]:
  !func X. fn_entry_label (func with fn_blocks := X) =
           fn_entry_label (<| fn_blocks := X |>)
Proof
  rw[fn_entry_label_def, entry_block_def]
QED

(* fn_entry_label after update_succ_phi_labels (record update form) *)
Theorem fn_entry_label_update_succ_phi_labels_with[local]:
  !func old_lbl new_lbl bbs succs.
    fn_entry_label (func with fn_blocks :=
      update_succ_phi_labels old_lbl new_lbl bbs succs) =
    fn_entry_label (func with fn_blocks := bbs)
Proof
  rw[fn_entry_label_with_fn_blocks, fn_entry_label_update_succ_phi_labels]
QED

(* fn_entry_label preserved by full merge step *)
Theorem fn_entry_label_full_merge_step[local]:
  !func bb next_bb lbl merged bbs' bbs''.
    can_merge_blocks func bb next_bb /\
    func.fn_blocks <> [] /\
    merged.bb_label = lbl /\
    bbs' = replace_block lbl merged
             (remove_block next_bb.bb_label func.fn_blocks) /\
    bbs'' = update_succ_phi_labels next_bb.bb_label lbl bbs' (bb_succs merged) ==>
    fn_entry_label (func with fn_blocks := bbs'') = fn_entry_label func
Proof
  rpt strip_tac >>
  `fn_entry_label (func with fn_blocks := bbs'') =
   fn_entry_label (func with fn_blocks := bbs')` by
    simp[fn_entry_label_update_succ_phi_labels_with] >>
  `(HD func.fn_blocks).bb_label <> next_bb.bb_label` by (
    mp_tac (Q.SPECL [`func`, `bb`, `next_bb`] can_merge_entry_ne) >> simp[]) >>
  `fn_entry_label (func with fn_blocks :=
     replace_block lbl merged (remove_block next_bb.bb_label func.fn_blocks)) =
   fn_entry_label func` by (
    mp_tac (Q.SPECL [`func`, `lbl`, `next_bb.bb_label`, `merged`]
      fn_entry_label_merge_step) >> simp[]) >>
  fs[]
QED

(*
  The proof is by recInduct on collapse_dfs_ind. Each case is a separate
  helper to avoid fragile >- chains in batch mode.
*)

(* Helper: merge case — entry label preserved through merge step + IH *)
Theorem fn_entry_label_collapse_dfs_merge_case[local]:
  !func lbl bb h next_bb func' lm' vis'.
    lookup_block lbl func.fn_blocks = SOME bb /\
    bb_succs bb = [h] /\
    lookup_block h func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    collapse_dfs
      (func with fn_blocks :=
        update_succ_phi_labels h lbl
          (replace_block lbl (merge_blocks bb next_bb)
             (remove_block h func.fn_blocks))
          (bb_succs (merge_blocks bb next_bb)))
      ((next_bb.bb_label,lbl)::label_map) visited (lbl::wl)
    = (func', lm', vis') /\
    (!fo lo vo. collapse_dfs
      (func with fn_blocks :=
        update_succ_phi_labels h lbl
          (replace_block lbl (merge_blocks bb next_bb)
             (remove_block h func.fn_blocks))
          (bb_succs (merge_blocks bb next_bb)))
      ((next_bb.bb_label,lbl)::label_map) visited (lbl::wl)
    = (fo,lo,vo) ==>
      fn_entry_label fo = fn_entry_label
        (func with fn_blocks :=
          update_succ_phi_labels h lbl
            (replace_block lbl (merge_blocks bb next_bb)
               (remove_block h func.fn_blocks))
            (bb_succs (merge_blocks bb next_bb))) \/
      fo.fn_blocks = []) ==>
    fn_entry_label func' = fn_entry_label func \/ func'.fn_blocks = []
Proof
  rpt strip_tac >>
  `func.fn_blocks <> []` by
    (mp_tac (Q.SPECL [`lbl`, `func.fn_blocks`, `bb`]
      lookup_block_fn_blocks_ne) >> simp[]) >>
  (* Derive h = next_bb.bb_label from can_merge_blocks + bb_succs *)
  `h = next_bb.bb_label` by gvs[can_merge_blocks_def] >>
  `fn_entry_label
     (func with fn_blocks :=
       update_succ_phi_labels h lbl
         (replace_block lbl (merge_blocks bb next_bb)
            (remove_block h func.fn_blocks))
         (bb_succs (merge_blocks bb next_bb))) =
   fn_entry_label func` by (
    `bb.bb_label = lbl` by
      (imp_res_tac venomExecPropsTheory.lookup_block_label) >>
    mp_tac (Q.SPECL [`func`, `bb`, `next_bb`, `lbl`,
      `merge_blocks bb next_bb`,
      `replace_block lbl (merge_blocks bb next_bb)
         (remove_block h func.fn_blocks)`,
      `update_succ_phi_labels h lbl
         (replace_block lbl (merge_blocks bb next_bb)
            (remove_block h func.fn_blocks))
         (bb_succs (merge_blocks bb next_bb))`]
      fn_entry_label_full_merge_step) >>
    simp[merge_blocks_def]) >>
  res_tac >> gvs[]
QED

(* Helper: bypass T case — entry label preserved through try_bypass + IH *)
Theorem fn_entry_label_collapse_dfs_bypass_T[local]:
  !func lm bb succs func_bp lm_bp func' lm' vis'.
    try_bypass func lm bb succs = (func_bp, lm_bp, T) /\
    func.fn_blocks <> [] /\
    (!next_lbl next_bb. MEM next_lbl succs /\
      lookup_block next_lbl func.fn_blocks = SOME next_bb /\
      can_bypass_jump func bb next_bb ==>
      (HD func.fn_blocks).bb_label <> next_bb.bb_label) /\
    collapse_dfs func_bp lm_bp vis wl = (func', lm', vis') /\
    (!fo lo vo. collapse_dfs func_bp lm_bp vis wl = (fo,lo,vo) ==>
      fn_entry_label fo = fn_entry_label func_bp \/ fo.fn_blocks = []) ==>
    fn_entry_label func' = fn_entry_label func \/ func'.fn_blocks = []
Proof
  rpt strip_tac >>
  `fn_entry_label func_bp = fn_entry_label func` by (
    mp_tac (Q.SPECL [`succs`, `func`, `lm`, `bb`,
      `func_bp`, `lm_bp`, `T`] fn_entry_label_try_bypass) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >> res_tac) >>
  res_tac >> gvs[]
QED

Theorem fn_entry_label_collapse_dfs:
  !func lm vis wl func' lm' vis'.
    collapse_dfs func lm vis wl = (func', lm', vis') ==>
    fn_entry_label func' = fn_entry_label func \/ func'.fn_blocks = []
Proof
  recInduct collapse_dfs_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once collapse_dfs_def] >>
  (* MEM lbl visited *)
  IF_CASES_TAC >> simp[] >>
  TRY (disch_tac >> res_tac >> gvs[] >> NO_TAC) >>
  (* lookup_block *)
  Cases_on `lookup_block lbl func.fn_blocks` >> simp[] >>
  TRY (disch_tac >> res_tac >> gvs[] >> NO_TAC) >>
  rename1 `SOME bb` >>
  (* bb_succs cases *)
  Cases_on `bb_succs bb` >> simp[] >>
  TRY (simp[LET_THM, try_bypass_def] >>
       disch_tac >> res_tac >> gvs[] >> NO_TAC) >>
  rename1 `h::t` >>
  Cases_on `t` >> simp[]
  (* === single successor case [h] === *)
  >- (
    Cases_on `lookup_block h func.fn_blocks` >> simp[] >>
    TRY (disch_tac >> res_tac >> gvs[] >> NO_TAC) >>
    rename1 `SOME next_bb` >>
    IF_CASES_TAC >> simp[] >>
    TRY (disch_tac >> res_tac >> gvs[] >> NO_TAC) >>
    simp[LET_THM] >> disch_tac >>
    mp_tac fn_entry_label_collapse_dfs_merge_case >>
    disch_then (qspecl_then [`func`, `lbl`, `bb`, `h`, `next_bb`,
      `func'`, `lm'`, `vis'`] mp_tac) >>
    simp[] >> disch_then irule >>
    rpt strip_tac >> res_tac >> gvs[]
  )
  (* === multi-successor case h::h2::t2 === *)
  >>
  simp[LET_THM] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> gvs[] >> disch_tac >>
  (* bypass F *)
  TRY (imp_res_tac simplifyCfgDefsTheory.try_bypass_F_unchanged >> gvs[] >>
       res_tac >> gvs[] >> NO_TAC) >>
  (* bypass T: targeted approach *)
  `func.fn_blocks <> []` by
    (imp_res_tac lookup_block_fn_blocks_ne) >>
  (* Establish: entry of try_bypass output = entry of func *)
  SUBGOAL_THEN ``!f l. try_bypass func label_map bb (bb_succs bb) = (f,l,T)
    ==> fn_entry_label f = fn_entry_label func`` ASSUME_TAC
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`bb_succs bb`, `func`, `label_map`, `bb`,
        `f`, `l`, `T`] fn_entry_label_try_bypass) >>
      simp[] >> disch_then irule >>
      rpt strip_tac >> imp_res_tac can_bypass_entry_ne >> gvs[]) >>
  (* Apply IH then chain *)
  res_tac >> gvs[]
QED


(* ================================================================
   fn_inst_wf toolkit: collapse_dfs and simplify_cfg_round preserve
   instruction well-formedness.
   ================================================================ *)

(* fn_inst_wf preserved by remove_block (subset of blocks) *)
Theorem fn_inst_wf_remove_block[local]:
  !func lbl.
    fn_inst_wf func ==>
    fn_inst_wf (func with fn_blocks := remove_block lbl func.fn_blocks)
Proof
  rw[fn_inst_wf_def] >>
  imp_res_tac cfgTransformProofsTheory.MEM_remove_block >> res_tac
QED

(* fn_inst_wf preserved by replace_block when replacement has inst_wf insts *)
Theorem fn_inst_wf_replace_block[local]:
  !func lbl new_bb.
    fn_inst_wf func /\
    (!inst. MEM inst new_bb.bb_instructions ==> inst_wf inst) ==>
    fn_inst_wf (func with fn_blocks := replace_block lbl new_bb func.fn_blocks)
Proof
  rw[fn_inst_wf_def, cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  BasicProvers.every_case_tac >> fs[] >> res_tac
QED

(* fn_inst_wf for a function built from modified fn_blocks *)
Theorem fn_inst_wf_with_fn_blocks[local]:
  !func bbs.
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==> inst_wf inst) ==>
    fn_inst_wf (func with fn_blocks := bbs)
Proof
  rw[fn_inst_wf_def]
QED

(* --- phi_well_formed preservation --- *)

(* filter_phi_ops preserves phi_well_formed *)
Theorem phi_well_formed_filter_phi_ops[local]:
  !pred_labels ops.
    phi_well_formed ops ==>
    phi_well_formed (filter_phi_ops pred_labels ops)
Proof
  recInduct filter_phi_ops_ind >>
  rw[filter_phi_ops_def, phi_well_formed_def] >>
  Cases_on `val_op` >> fs[phi_well_formed_def]
QED

(* remove_phi_label preserves phi_well_formed *)
Theorem phi_well_formed_remove_phi_label[local]:
  !lbl ops.
    phi_well_formed ops ==>
    phi_well_formed (remove_phi_label lbl ops)
Proof
  recInduct remove_phi_label_ind >>
  rw[remove_phi_label_def, phi_well_formed_def] >>
  Cases_on `val_op` >> fs[phi_well_formed_def]
QED

(* MAP subst_label_map_op preserves phi_well_formed *)
Theorem phi_well_formed_MAP_subst_label_map_op[local]:
  !m ops.
    phi_well_formed ops ==>
    phi_well_formed (MAP (subst_label_map_op m) ops)
Proof
  gen_tac >> recInduct phi_well_formed_ind >>
  rw[phi_well_formed_def, subst_label_map_op_def] >>
  BasicProvers.every_case_tac >> simp[phi_well_formed_def]
QED

(* MAP subst_label_op preserves phi_well_formed *)
Theorem phi_well_formed_MAP_subst_label_op[local]:
  !old new ops.
    phi_well_formed ops ==>
    phi_well_formed (MAP (subst_label_op old new) ops)
Proof
  ntac 2 gen_tac >> recInduct phi_well_formed_ind >>
  rw[phi_well_formed_def, subst_label_op_def] >>
  simp[phi_well_formed_def]
QED

(* MAP relabeling (lambda form used in update_phi_bypass) preserves phi_well_formed *)
Theorem phi_well_formed_MAP_relabel[local]:
  !a_label b_label ops.
    phi_well_formed ops ==>
    phi_well_formed (MAP (\op. case op of
        Label l => if l = b_label then Label a_label else Label l
      | _ => op) ops)
Proof
  ntac 2 gen_tac >> recInduct phi_well_formed_ind >>
  rw[phi_well_formed_def] >>
  simp[phi_well_formed_def]
QED

(* --- Per-instruction inst_wf preservation --- *)

(* DJMP helper: get_label preserved through subst_label_op *)
Theorem EVERY_get_label_MAP_subst_label_op[local]:
  !old new ops.
    EVERY (\op. IS_SOME (get_label op)) ops ==>
    EVERY (\op. IS_SOME (get_label op)) (MAP (subst_label_op old new) ops)
Proof
  Induct_on `ops` >> simp[] >> rw[] >>
  Cases_on `h` >> fs[get_label_def, subst_label_op_def] >>
  IF_CASES_TAC >> simp[get_label_def]
QED

(* DJMP helper: get_label preserved through subst_label_map_op *)
Theorem EVERY_get_label_MAP_subst_label_map_op[local]:
  !m ops.
    EVERY (\op. IS_SOME (get_label op)) ops ==>
    EVERY (\op. IS_SOME (get_label op)) (MAP (subst_label_map_op m) ops)
Proof
  Induct_on `ops` >> simp[] >> rw[] >>
  Cases_on `h` >> fs[get_label_def, subst_label_map_op_def] >>
  BasicProvers.every_case_tac >> simp[get_label_def]
QED

(* filter_phi_ops preserves phi_operands_wf *)
Theorem phi_operands_wf_filter_phi_ops[local]:
  !pred_labels ops.
    phi_operands_wf ops ==>
    phi_operands_wf (filter_phi_ops pred_labels ops)
Proof
  recInduct filter_phi_ops_ind >>
  rw[filter_phi_ops_def, phi_operands_wf_def] >>
  Cases_on `val_op` >> fs[phi_operands_wf_def]
QED

(* phi_pairs of filter_phi_ops is a FILTER of phi_pairs *)
Theorem phi_pairs_filter_phi_ops[local]:
  !pred_labels ops.
    phi_operands_wf ops ==>
    phi_pairs (filter_phi_ops pred_labels ops) =
    FILTER (\(l,v). MEM l pred_labels) (phi_pairs ops)
Proof
  recInduct filter_phi_ops_ind >>
  rw[filter_phi_ops_def, phi_operands_wf_def, phi_pairs_def] >>
  Cases_on `val_op` >> fs[phi_operands_wf_def, phi_pairs_def]
QED

(* ALL_DISTINCT is preserved by MAP f o FILTER P when ALL_DISTINCT (MAP f xs) *)
Theorem ALL_DISTINCT_MAP_FILTER[local]:
  !f P xs. ALL_DISTINCT (MAP f xs) ==> ALL_DISTINCT (MAP f (FILTER P xs))
Proof
  gen_tac >> gen_tac >> Induct >> rw[] >>
  fs[listTheory.MEM_MAP, listTheory.MEM_FILTER]
QED

(* filter_phi_ops preserves phi_labels_distinct *)
Theorem phi_labels_distinct_filter_phi_ops[local]:
  !pred_labels ops.
    phi_operands_wf ops /\ phi_labels_distinct ops ==>
    phi_labels_distinct (filter_phi_ops pred_labels ops)
Proof
  rw[phi_labels_distinct_def] >>
  imp_res_tac phi_pairs_filter_phi_ops >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule ALL_DISTINCT_MAP_FILTER >> simp[]
QED

(* MAP subst_label_op preserves phi_operands_wf *)
Theorem phi_operands_wf_MAP_subst_label_op[local]:
  !old new ops.
    phi_operands_wf ops ==>
    phi_operands_wf (MAP (subst_label_op old new) ops)
Proof
  ntac 2 gen_tac >> ho_match_mp_tac phi_operands_wf_ind >>
  rw[phi_operands_wf_def, subst_label_op_def]
QED

(* MAP subst_label_map_op preserves phi_operands_wf *)
Theorem phi_operands_wf_MAP_subst_label_map_op[local]:
  !m ops.
    phi_operands_wf ops ==>
    phi_operands_wf (MAP (subst_label_map_op m) ops)
Proof
  gen_tac >> ho_match_mp_tac phi_operands_wf_ind >>
  rw[phi_operands_wf_def, subst_label_map_op_def] >>
  BasicProvers.every_case_tac >> simp[phi_operands_wf_def]
QED

(* MAP relabeling preserves phi_operands_wf *)
Theorem phi_operands_wf_MAP_relabel[local]:
  !a_label b_label ops.
    phi_operands_wf ops ==>
    phi_operands_wf (MAP (\op. case op of
        Label l => if l = b_label then Label a_label else Label l
      | _ => op) ops)
Proof
  ntac 2 gen_tac >> ho_match_mp_tac phi_operands_wf_ind >>
  rw[phi_operands_wf_def]
QED

(* remove_phi_label preserves phi_operands_wf *)
Theorem phi_operands_wf_remove_phi_label[local]:
  !lbl ops.
    phi_operands_wf ops ==>
    phi_operands_wf (remove_phi_label lbl ops)
Proof
  recInduct remove_phi_label_ind >>
  rw[remove_phi_label_def, phi_operands_wf_def] >>
  Cases_on `val_op` >> fs[phi_operands_wf_def]
QED

(* fix_phi_inst preserves inst_wf *)
Theorem inst_wf_fix_phi_inst[local]:
  !actual_preds inst.
    inst_wf inst ==>
    inst_wf (fix_phi_inst actual_preds inst)
Proof
  rw[fix_phi_inst_def] >>
  BasicProvers.every_case_tac >> fs[inst_wf_def] >>
  metis_tac[phi_operands_wf_filter_phi_ops]
QED

(* subst_label_inst preserves inst_wf -- direct proof *)
Theorem inst_wf_subst_label_inst[local]:
  !old new inst.
    inst_wf inst ==>
    inst_wf (subst_label_inst old new inst)
Proof
  rw[subst_label_inst_def] >>
  Cases_on `inst.inst_opcode` >>
  fs[inst_wf_def, listTheory.LENGTH_MAP] >>
  (* PHI *)
  TRY (irule phi_operands_wf_MAP_subst_label_op >> simp[] >> NO_TAC) >>
  (* DJMP: use helper *)
  TRY (imp_res_tac EVERY_get_label_MAP_subst_label_op >> simp[] >> NO_TAC) >>
  (* All other opcodes: subst_label_op computes concretely *)
  simp[subst_label_op_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

(* subst_block_labels_inst preserves inst_wf -- direct proof *)
Theorem inst_wf_subst_block_labels_inst[local]:
  !m inst.
    inst_wf inst ==>
    inst_wf (subst_block_labels_inst m inst)
Proof
  rw[subst_block_labels_inst_def, subst_label_map_inst_def] >>
  Cases_on `inst.inst_opcode` >>
  fs[inst_wf_def, listTheory.LENGTH_MAP, is_block_label_opcode_def,
     is_terminator_def, subst_label_map_op_def] >>
  TRY (BasicProvers.every_case_tac >> simp[] >> NO_TAC) >>
  (* PHI *)
  TRY (irule phi_operands_wf_MAP_subst_label_map_op >> simp[] >> NO_TAC) >>
  (* DJMP: use helper *)
  TRY (imp_res_tac EVERY_get_label_MAP_subst_label_map_op >> simp[] >> NO_TAC)
QED

(* update_phi_bypass preserves inst_wf *)
Theorem inst_wf_update_phi_bypass:
  !a_label b_label inst.
    inst_wf inst ==>
    inst_wf (update_phi_bypass a_label b_label inst)
Proof
  rw[update_phi_bypass_def] >>
  BasicProvers.every_case_tac >> fs[inst_wf_def] >>
  TRY (imp_res_tac phi_operands_wf_remove_phi_label >>
       simp[] >> NO_TAC) >>
  imp_res_tac phi_operands_wf_MAP_relabel >> simp[listTheory.LENGTH_MAP]
QED

(* --- Pipeline step preservation --- *)

(* fix_all_phis preserves fn_inst_wf *)
Theorem fn_inst_wf_fix_all_phis[local]:
  !func.
    fn_inst_wf func ==>
    fn_inst_wf (fix_all_phis func)
Proof
  rw[fn_inst_wf_def, fix_all_phis_def, fix_phis_in_block_def,
     listTheory.MEM_MAP, LET_THM] >>
  fs[listTheory.MEM_APPEND, listTheory.MEM_FILTER, listTheory.MEM_MAP] >>
  gvs[] >> res_tac >>
  match_mp_tac inst_wf_fix_phi_inst >> simp[]
QED

(* subst_block_labels_fn preserves fn_inst_wf *)
Theorem fn_inst_wf_subst_block_labels_fn:
  !m func.
    fn_inst_wf func ==>
    fn_inst_wf (subst_block_labels_fn m func)
Proof
  rw[fn_inst_wf_def, subst_block_labels_fn_def, subst_block_labels_block_def,
     listTheory.MEM_MAP] >>
  fs[listTheory.MEM_MAP] >>
  irule inst_wf_subst_block_labels_inst >> res_tac
QED

(* FOLDL version of update_succ_phi_labels preserves inst_wf *)
Theorem inst_wf_update_succ_phi_FOLDL[local]:
  !succs old_lbl new_lbl bbs.
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==> inst_wf inst) ==>
    (!bb inst.
       MEM bb (FOLDL (\bs s.
         case lookup_block s bs of
           NONE => bs
         | SOME sbb =>
             replace_block s
               (sbb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                              else subst_label_inst old_lbl new_lbl inst)
                      sbb.bb_instructions) bs) bbs succs) /\
       MEM inst bb.bb_instructions ==> inst_wf inst)
Proof
  Induct >- rw[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`old_lbl`, `new_lbl`,
    `case lookup_block h bbs of
       NONE => bbs
     | SOME sbb =>
         replace_block h
           (sbb with bb_instructions :=
              MAP (\inst. if inst.inst_opcode <> PHI then inst
                          else subst_label_inst old_lbl new_lbl inst)
                  sbb.bb_instructions) bbs`] mp_tac) >>
  (impl_tac >- (
    rw[] >>
    BasicProvers.every_case_tac >> fs[] >>
    fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
    BasicProvers.every_case_tac >> fs[listTheory.MEM_MAP] >>
    gvs[] >>
    TRY (imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
         res_tac >> NO_TAC) >>
    rpt IF_CASES_TAC >> gvs[] >>
    TRY (imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
         res_tac >> NO_TAC) >>
    match_mp_tac inst_wf_subst_label_inst >>
    imp_res_tac venomExecPropsTheory.lookup_block_MEM >> res_tac)) >>
  disch_then (qspecl_then [`bb`, `inst`] mp_tac) >> fs[]
QED

(* update_succ_phi_labels preserves: every inst in every block is inst_wf *)
Theorem inst_wf_update_succ_phi_labels[local]:
  !old_lbl new_lbl bbs succs bb inst.
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==> inst_wf inst) /\
    MEM bb (update_succ_phi_labels old_lbl new_lbl bbs succs) /\
    MEM inst bb.bb_instructions ==>
    inst_wf inst
Proof
  rw[update_succ_phi_labels_def] >>
  imp_res_tac inst_wf_update_succ_phi_FOLDL
QED

(* merge_blocks preserves inst_wf of instructions *)
Theorem inst_wf_merge_blocks[local]:
  !a b inst.
    (!i. MEM i a.bb_instructions ==> inst_wf i) /\
    (!i. MEM i b.bb_instructions ==> inst_wf i) /\
    MEM inst (merge_blocks a b).bb_instructions ==>
    inst_wf inst
Proof
  rw[merge_blocks_def, listTheory.MEM_APPEND] >>
  TRY (res_tac >> NO_TAC) >>
  qpat_x_assum `!i. MEM i a.bb_instructions ==> _` match_mp_tac >>
  Cases_on `a.bb_instructions` >> gvs[] >>
  imp_res_tac rich_listTheory.MEM_FRONT >> gvs[]
QED

(* do_merge_jump preserves fn_inst_wf *)
Theorem fn_inst_wf_do_merge_jump:
  !func a b label_map func' lm'.
    fn_inst_wf func /\
    MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    fn_inst_wf func'
Proof
  rw[do_merge_jump_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  rw[fn_inst_wf_def] >> fs[] >>
  fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP,
     cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
  BasicProvers.every_case_tac >> fs[] >> rw[] >>
  fs[listTheory.MEM_MAP] >>
  rpt (
    TRY (irule inst_wf_update_phi_bypass) >>
    TRY (irule inst_wf_subst_label_inst) >>
    TRY (fs[fn_inst_wf_def] >>
         TRY (imp_res_tac venomExecPropsTheory.lookup_block_MEM) >>
         res_tac >> NO_TAC) >>
    BasicProvers.every_case_tac >> fs[fn_inst_wf_def] >>
    TRY (imp_res_tac venomExecPropsTheory.lookup_block_MEM) >>
    res_tac
  )
QED

(* try_bypass preserves fn_inst_wf *)
Theorem fn_inst_wf_try_bypass:
  !func label_map bb succs func' lm' flag.
    fn_inst_wf func /\
    MEM bb func.fn_blocks /\
    try_bypass func label_map bb succs = (func', lm', flag) ==>
    fn_inst_wf func'
Proof
  ntac 3 gen_tac >> Induct_on `succs` >>
  rw[try_bypass_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  imp_res_tac fn_inst_wf_do_merge_jump >> fs[]
QED

(* Helper: the full merge step in collapse_dfs preserves fn_inst_wf *)
Theorem fn_inst_wf_merge_step:
  !func lbl next_lbl bb next_bb.
    fn_inst_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb ==>
    fn_inst_wf (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)))
Proof
  rw[] >>
  irule fn_inst_wf_with_fn_blocks >> rpt strip_tac >>
  imp_res_tac inst_wf_update_succ_phi_labels >>
  pop_assum match_mp_tac >> rpt strip_tac >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP,
     cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
  BasicProvers.every_case_tac >> fs[] >> rw[] >>
  fs[fn_inst_wf_def] >>
  TRY (res_tac >> NO_TAC) >>
  mp_tac (Q.SPECL [`bb`, `next_bb`] inst_wf_merge_blocks) >>
  simp[] >> disch_then match_mp_tac >> simp[] >>
  rpt strip_tac >> res_tac
QED

(* ===== wf_function preservation through collapse_dfs operations ===== *)

(* bb_well_formed of merge_blocks *)
(* Helper: EL of FRONT ++ in the FRONT part *)
Theorem EL_FRONT_APPEND1[local]:
  !l1 l2 n. n < LENGTH (FRONT l1) /\ l1 <> [] ==>
    EL n (FRONT l1 ++ l2) = EL n l1
Proof
  rpt strip_tac >>
  `EL n (FRONT l1 ++ l2) = EL n (FRONT l1)` by
    simp[rich_listTheory.EL_APPEND1] >>
  `EL n (FRONT l1) = EL n l1` by
    simp[rich_listTheory.EL_FRONT, listTheory.NULL_EQ] >>
  fs[]
QED

(* Helper: EL in second part of FRONT l1 ++ l2 *)
Theorem EL_FRONT_APPEND2[local]:
  !l1 l2 n. LENGTH (FRONT l1) <= n /\ n < LENGTH (FRONT l1) + LENGTH l2 /\
    l1 <> [] ==>
    EL n (FRONT l1 ++ l2) = EL (n - LENGTH (FRONT l1)) l2
Proof
  rpt strip_tac >> irule rich_listTheory.EL_APPEND2 >> simp[]
QED

Theorem bb_well_formed_merge_blocks:
  !a b. bb_well_formed a /\ bb_well_formed b /\ no_phis b ==>
    bb_well_formed (merge_blocks a b)
Proof
  rpt strip_tac >>
  `a.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `b.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST b.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `!i. i < LENGTH a.bb_instructions /\
       is_terminator (EL i a.bb_instructions).inst_opcode ==>
       i = PRE (LENGTH a.bb_instructions)` by
    fs[bb_well_formed_def] >>
  `!i. i < LENGTH b.bb_instructions /\
       is_terminator (EL i b.bb_instructions).inst_opcode ==>
       i = PRE (LENGTH b.bb_instructions)` by
    fs[bb_well_formed_def] >>
  `!i j. i < j /\ j < LENGTH a.bb_instructions /\
         (EL j a.bb_instructions).inst_opcode = PHI ==>
         (EL i a.bb_instructions).inst_opcode = PHI` by
    fs[bb_well_formed_def] >>
  `LENGTH (FRONT a.bb_instructions) = PRE (LENGTH a.bb_instructions)` by
    simp[rich_listTheory.LENGTH_FRONT] >>
  qabbrev_tac `fa = FRONT a.bb_instructions` >>
  `(merge_blocks a b).bb_instructions = fa ++ b.bb_instructions` by
    simp[merge_blocks_def, Abbr `fa`] >>
  ASM_REWRITE_TAC [bb_well_formed_def] >> rpt conj_tac
  >- simp[Abbr `fa`]
  >- simp[Abbr `fa`, rich_listTheory.LAST_APPEND_NOT_NIL]
  >- (
    rpt strip_tac >>
    Cases_on `i < LENGTH fa`
    >- (
      `EL i (fa ++ b.bb_instructions) = EL i fa` by
        simp[rich_listTheory.EL_APPEND1] >>
      `EL i fa = EL i a.bb_instructions` by
        simp[Abbr `fa`, rich_listTheory.EL_FRONT, listTheory.NULL_EQ] >>
      `i < LENGTH a.bb_instructions` by DECIDE_TAC >>
      `i = PRE (LENGTH a.bb_instructions)` by (res_tac >> fs[]) >>
      DECIDE_TAC)
    >- (
      `LENGTH fa <= i` by DECIDE_TAC >>
      `EL i (fa ++ b.bb_instructions) =
       EL (i - LENGTH fa) b.bb_instructions` by
        simp[rich_listTheory.EL_APPEND2] >>
      `i - LENGTH fa < LENGTH b.bb_instructions` by
        fs[listTheory.LENGTH_APPEND] >>
      `is_terminator (EL (i - LENGTH fa) b.bb_instructions).inst_opcode` by
        fs[] >>
      qpat_x_assum `!i. i < LENGTH b.bb_instructions /\ _ ==> _`
        (qspec_then `i - LENGTH fa` mp_tac) >>
      simp[listTheory.LENGTH_APPEND]))
  >> (
    rpt strip_tac >>
    Cases_on `j < LENGTH fa`
    >- (
      `i < LENGTH fa` by DECIDE_TAC >>
      `j < LENGTH a.bb_instructions` by DECIDE_TAC >>
      `i < LENGTH a.bb_instructions` by DECIDE_TAC >>
      `(EL j a.bb_instructions).inst_opcode = PHI` by (
        `EL j (fa ++ b.bb_instructions) = EL j fa` by
          simp[rich_listTheory.EL_APPEND1] >>
        `EL j fa = EL j a.bb_instructions` by
          simp[Abbr `fa`, rich_listTheory.EL_FRONT, listTheory.NULL_EQ] >>
        fs[]) >>
      `(EL i a.bb_instructions).inst_opcode = PHI` by (res_tac >> fs[]) >>
      `EL i (fa ++ b.bb_instructions) = EL i fa` by
        simp[rich_listTheory.EL_APPEND1] >>
      `EL i fa = EL i a.bb_instructions` by
        simp[Abbr `fa`, rich_listTheory.EL_FRONT, listTheory.NULL_EQ] >>
      fs[])
    >- (
      `LENGTH fa <= j` by DECIDE_TAC >>
      `j - LENGTH fa < LENGTH b.bb_instructions` by
        fs[listTheory.LENGTH_APPEND] >>
      `(EL (j - LENGTH fa) b.bb_instructions).inst_opcode <> PHI` by
        fs[no_phis_def, listTheory.EVERY_EL] >>
      `EL j (fa ++ b.bb_instructions) =
       EL (j - LENGTH fa) b.bb_instructions` by
        (irule rich_listTheory.EL_APPEND2 >> simp[]) >>
      fs[]))
QED

(* ================================================================
   General: collapse_dfs preserves any property P that is preserved
   by merge_step (single-successor merge) and try_bypass (multi-successor).
   Abstracts the 40-line recInduct skeleton used by fn_inst_wf and wf_function.
   ================================================================ *)
Theorem collapse_dfs_preserves:
  !P.
    (* merge_step preserves P *)
    (!func lbl next_lbl bb next_bb.
       P func /\ lookup_block lbl func.fn_blocks = SOME bb /\
       lookup_block next_lbl func.fn_blocks = SOME next_bb /\
       can_merge_blocks func bb next_bb ==>
       P (func with fn_blocks :=
         update_succ_phi_labels next_lbl lbl
           (replace_block lbl (merge_blocks bb next_bb)
              (remove_block next_lbl func.fn_blocks))
           (bb_succs (merge_blocks bb next_bb)))) /\
    (* try_bypass preserves P *)
    (!func label_map bb succs func' lm'.
       P func /\ MEM bb func.fn_blocks /\
       try_bypass func label_map bb succs = (func', lm', T) ==> P func') ==>
    !func label_map visited wl func' lm' vis'.
      collapse_dfs func label_map visited wl = (func', lm', vis') ==>
      P func ==> P func'
Proof
  gen_tac >> strip_tac >>
  recInduct collapse_dfs_ind >> conj_tac
  >- rw[Once collapse_dfs_def]
  >> rw[] >>
  qpat_x_assum `collapse_dfs _ _ _ _ = _` mp_tac >>
  simp[Once collapse_dfs_def] >>
  IF_CASES_TAC >> fs[] >>
  TRY (disch_tac >> res_tac >> NO_TAC) >>
  Cases_on `lookup_block lbl func.fn_blocks` >> fs[] >>
  TRY (disch_tac >> res_tac >> NO_TAC) >>
  rename1 `SOME bb` >>
  Cases_on `bb_succs bb` >> fs[try_bypass_def] >>
  TRY (disch_tac >> res_tac >> NO_TAC) >>
  rename1 `h::t` >>
  Cases_on `t` >> fs[] >>
  (* single successor: merge or no-merge *)
  TRY (
    Cases_on `lookup_block h func.fn_blocks` >> fs[] >>
    TRY (disch_tac >> res_tac >> NO_TAC) >>
    rename1 `SOME next_bb` >>
    IF_CASES_TAC >> fs[] >>
    TRY (disch_tac >> res_tac >> NO_TAC) >>
    fs[LET_THM] >> disch_tac >>
    res_tac >> res_tac >> NO_TAC
  ) >>
  (* multi successor: try_bypass *)
  fs[LET_THM] >> pairarg_tac >> fs[] >>
  IF_CASES_TAC >> fs[] >> disch_tac >>
  (* bypass F: func unchanged, IH applies directly *)
  TRY (imp_res_tac simplifyCfgDefsTheory.try_bypass_F_unchanged >>
       gvs[] >> res_tac >> NO_TAC) >>
  (* bypass T *)
  imp_res_tac lookup_block_MEM >>
  SUBGOAL_THEN ``try_bypass func label_map bb (h::h'::t') = (func'',lm'',T)``
    ASSUME_TAC
  >- simp[try_bypass_def] >>
  res_tac >> res_tac
QED

(* collapse_dfs_preserves2: generalizes collapse_dfs_preserves to 2-arg predicates P lm func *)
Theorem collapse_dfs_preserves2:
  !P.
    (* merge_step preserves P *)
    (!func lbl next_lbl bb next_bb label_map.
       P label_map func /\
       lookup_block lbl func.fn_blocks = SOME bb /\
       lookup_block next_lbl func.fn_blocks = SOME next_bb /\
       can_merge_blocks func bb next_bb ==>
       P ((next_bb.bb_label, lbl) :: label_map)
         (func with fn_blocks :=
           update_succ_phi_labels next_lbl lbl
             (replace_block lbl (merge_blocks bb next_bb)
                (remove_block next_lbl func.fn_blocks))
             (bb_succs (merge_blocks bb next_bb)))) /\
    (* try_bypass preserves P *)
    (!func label_map bb succs func' lm'.
       P label_map func /\ MEM bb func.fn_blocks /\
       try_bypass func label_map bb succs = (func', lm', T) ==>
       P lm' func') ==>
    !func label_map visited wl func' lm' vis'.
      collapse_dfs func label_map visited wl = (func', lm', vis') ==>
      P label_map func ==> P lm' func'
Proof
  gen_tac >> strip_tac >>
  recInduct collapse_dfs_ind >> conj_tac
  >- rw[Once collapse_dfs_def]
  >> rw[] >>
  qpat_x_assum `collapse_dfs _ _ _ _ = _` mp_tac >>
  simp[Once collapse_dfs_def] >>
  IF_CASES_TAC >> fs[] >>
  TRY (disch_tac >> res_tac >> NO_TAC) >>
  Cases_on `lookup_block lbl func.fn_blocks` >> fs[] >>
  TRY (disch_tac >> res_tac >> NO_TAC) >>
  rename1 `SOME bb` >>
  Cases_on `bb_succs bb` >> fs[try_bypass_def] >>
  TRY (disch_tac >> res_tac >> NO_TAC) >>
  rename1 `h::t` >>
  Cases_on `t` >> fs[] >>
  (* single successor: merge or no-merge *)
  TRY (
    Cases_on `lookup_block h func.fn_blocks` >> fs[] >>
    TRY (disch_tac >> res_tac >> NO_TAC) >>
    rename1 `SOME next_bb` >>
    IF_CASES_TAC >> fs[] >>
    TRY (disch_tac >> res_tac >> NO_TAC) >>
    fs[LET_THM] >> disch_tac >>
    res_tac >> res_tac >> NO_TAC
  ) >>
  (* multi successor: try_bypass *)
  fs[LET_THM] >> pairarg_tac >> fs[] >>
  IF_CASES_TAC >> fs[] >> disch_tac >>
  (* bypass F: func and lm unchanged, IH applies directly *)
  TRY (imp_res_tac simplifyCfgDefsTheory.try_bypass_F_unchanged >>
       gvs[] >> res_tac >> NO_TAC) >>
  (* bypass T *)
  imp_res_tac lookup_block_MEM >>
  SUBGOAL_THEN ``try_bypass func label_map bb (h::h'::t') = (func'',lm'',T)``
    ASSUME_TAC
  >- simp[try_bypass_def] >>
  res_tac >> res_tac
QED

(* collapse_dfs preserves fn_inst_wf: now a corollary of collapse_dfs_preserves *)
Theorem fn_inst_wf_collapse_dfs:
  !func label_map visited wl func' lm' vis'.
    collapse_dfs func label_map visited wl = (func', lm', vis') ==>
    fn_inst_wf func ==> fn_inst_wf func'
Proof
  match_mp_tac (ISPEC ``fn_inst_wf`` collapse_dfs_preserves) >>
  rpt conj_tac
  >- (rpt strip_tac >> irule fn_inst_wf_merge_step >> metis_tac[])
  >> rpt strip_tac >> irule fn_inst_wf_try_bypass >>
     metis_tac[]
QED

(* fn_inst_wf preserved by remove_unreachable_blocks *)
Theorem fn_inst_wf_remove_unreachable:
  !func.
    fn_inst_wf func ==>
    fn_inst_wf (remove_unreachable_blocks func)
Proof
  rw[fn_inst_wf_def, remove_unreachable_blocks_def] >>
  BasicProvers.every_case_tac >> fs[] >>
  fs[listTheory.MEM_FILTER] >> res_tac
QED

(* simplify_cfg_round preserves fn_inst_wf *)
Theorem fn_inst_wf_simplify_cfg_round:
  !func.
    wf_function func /\
    fn_inst_wf func ==>
    fn_inst_wf (simplify_cfg_round func)
Proof
  rw[simplify_cfg_round_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  rw[LET_THM] >>
  pairarg_tac >> gvs[] >>
  (* Forward chain: fn_inst_wf through pipeline *)
  `fn_inst_wf (remove_unreachable_blocks func)` by
    (match_mp_tac fn_inst_wf_remove_unreachable >> simp[]) >>
  `fn_inst_wf (fix_all_phis (remove_unreachable_blocks func))` by
    (match_mp_tac fn_inst_wf_fix_all_phis >> simp[]) >>
  imp_res_tac fn_inst_wf_collapse_dfs >>
  (* Now: fn_inst_wf of collapse_dfs result is an assumption *)
  match_mp_tac fn_inst_wf_fix_all_phis >> simp[] >>
  match_mp_tac fn_inst_wf_remove_unreachable >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  match_mp_tac fn_inst_wf_subst_block_labels_fn >> simp[]
QED

(* ================================================================
   Section: wf_function preservation helpers
   ================================================================ *)

(* fix_phi_inst is identity on non-PHI instructions *)
Theorem fix_phi_inst_non_phi[local]:
  !preds inst. inst.inst_opcode <> PHI ==> fix_phi_inst preds inst = inst
Proof
  rw[fix_phi_inst_def]
QED

(* fix_phi_inst preserves inst_id *)
Theorem fix_phi_inst_id[local]:
  !preds inst. (fix_phi_inst preds inst).inst_id = inst.inst_id
Proof
  rw[fix_phi_inst_def] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* fix_phi_inst preserves opcode for non-PHI *)
Theorem fix_phi_inst_opcode_non_phi[local]:
  !preds inst. inst.inst_opcode <> PHI ==>
    (fix_phi_inst preds inst).inst_opcode = inst.inst_opcode
Proof
  rw[fix_phi_inst_def]
QED

(* LAST of FILTER for non-empty result when last element passes *)
Theorem LAST_FILTER[local]:
  !P l. l <> [] /\ P (LAST l) ==> FILTER P l <> [] /\ LAST (FILTER P l) = LAST l
Proof
  gen_tac >> Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `l` >> fs[listTheory.LAST_DEF] >>
  (* Both cases handled uniformly - no >- needed *)
  TRY (simp[listTheory.FILTER] >> NO_TAC) >>
  (* l = h'::t case: IH gives us the result for the tail *)
  res_tac >>
  simp[listTheory.FILTER] >>
  Cases_on `P h` >> simp[] >>
  simp[listTheory.LAST_DEF] >>
  Cases_on `FILTER P (h'::t)` >> fs[]
QED

(* fix_phis_in_block preserves bb_succs when block is well-formed *)
Theorem bb_succs_fix_phis_in_block[local]:
  !preds bb. bb_well_formed bb ==>
    bb_succs (fix_phis_in_block preds bb) = bb_succs bb
Proof
  rw[fix_phis_in_block_def, LET_THM, bb_succs_def] >>
  fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  (* Establish key facts about the terminator *)
  SUBGOAL_THEN ``is_terminator (LAST (h::t)).inst_opcode`` ASSUME_TAC
  >- (Cases_on `t` >> fs[listTheory.LAST_DEF]) >>
  SUBGOAL_THEN ``(LAST (h::t)).inst_opcode <> PHI`` ASSUME_TAC
  >- (strip_tac >> fs[is_terminator_def]) >>
  SUBGOAL_THEN ``LAST (MAP (fix_phi_inst preds) (h::t)) = LAST (h::t)``
    ASSUME_TAC
  >- (simp[listTheory.LAST_MAP] >> simp[fix_phi_inst_non_phi]) >>
  SUBGOAL_THEN ``(\i. i.inst_opcode <> PHI) (LAST (MAP (fix_phi_inst preds) (h::t)))``
    ASSUME_TAC >- simp[] >>
  imp_res_tac LAST_FILTER >>
  (* non_phis is non-empty, so phis ++ non_phis is non-empty *)
  SUBGOAL_THEN ``LAST (FILTER (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst preds) (h::t)) ++
    FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst preds) (h::t))) =
    LAST (h::t)`` ASSUME_TAC
  >- (simp[rich_listTheory.LAST_APPEND_NOT_NIL]) >>
  (* Now the case expression on phis ++ non_phis *)
  qabbrev_tac `phis = FILTER (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst preds) (h::t))` >>
  qabbrev_tac `nphis = FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst preds) (h::t))` >>
  Cases_on `phis ++ nphis` >> fs[]
QED

(* ===== wf_function preservation for fix_all_phis ===== *)

(* FILTER P ++ FILTER (not P) is a permutation of the original list *)
Theorem PERM_FILTER_COMPLEMENT[local]:
  !P l. PERM (FILTER P l ++ FILTER (\x. ~P x) l) l
Proof
  gen_tac >> Induct >> simp[] >>
  rpt gen_tac >>
  Cases_on `P h` >> simp[] >>
  TRY (simp[sortingTheory.PERM_CONS_IFF] >> NO_TAC) >>
  simp[sortingTheory.PERM_FUN_APPEND_CONS, sortingTheory.PERM_CONS_IFF]
QED

(* fix_phi_inst does not produce terminators from PHI instructions *)
Theorem fix_phi_inst_not_terminator[local]:
  !preds inst. inst.inst_opcode = PHI ==>
    ~is_terminator (fix_phi_inst preds inst).inst_opcode
Proof
  rw[fix_phi_inst_def, LET_THM] >>
  BasicProvers.every_case_tac >> simp[is_terminator_def]
QED

(* Key setup for fix_phis_in_block: the non-PHI filter is non-empty
   and its LAST equals the original block LAST *)
Theorem fix_phis_filter_non_phi_facts[local]:
  !preds insts.
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode ==>
    FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst preds) insts) <> [] /\
    LAST (FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst preds) insts)) =
      LAST (MAP (fix_phi_inst preds) insts)
Proof
  rpt gen_tac >> strip_tac >>
  `(LAST insts).inst_opcode <> PHI` by (strip_tac >> fs[is_terminator_def]) >>
  `MAP (fix_phi_inst preds) insts <> []` by (Cases_on `insts` >> fs[]) >>
  `LAST (MAP (fix_phi_inst preds) insts) = fix_phi_inst preds (LAST insts)` by
    simp[listTheory.LAST_MAP] >>
  `(fix_phi_inst preds (LAST insts)).inst_opcode = (LAST insts).inst_opcode` by
    simp[fix_phi_inst_opcode_non_phi] >>
  SUBGOAL_THEN ``(\i. i.inst_opcode <> PHI)
    (LAST (MAP (fix_phi_inst preds) insts))`` ASSUME_TAC
  >- simp[] >>
  imp_res_tac LAST_FILTER >>
  simp[listTheory.LAST_MAP]
QED

(* Key lemma: LAST of fix_phis_in_block instructions equals original LAST *)
Theorem LAST_fix_phis_in_block_nonempty[local]:
  !preds bb. bb_well_formed bb ==>
    (fix_phis_in_block preds bb).bb_instructions <> []
Proof
  rw[fix_phis_in_block_def, LET_THM] >>
  fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  imp_res_tac fix_phis_filter_non_phi_facts >>
  Cases_on `FILTER (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst preds) (h::t)) ++
    FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst preds) (h::t))` >>
  fs[listTheory.APPEND_eq_NIL]
QED

Theorem LAST_fix_phis_in_block[local]:
  !preds bb. bb_well_formed bb ==>
    LAST (fix_phis_in_block preds bb).bb_instructions =
      LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  `is_terminator (LAST (h::t)).inst_opcode` by
    (Cases_on `t` >> fs[listTheory.LAST_DEF]) >>
  `(LAST (h::t)).inst_opcode <> PHI` by (strip_tac >> fs[is_terminator_def]) >>
  imp_res_tac fix_phis_filter_non_phi_facts >>
  (* Establish LAST of the whole fix_phis_in_block as a chain:
     LAST(fix_phis preds bb).bb_instructions
       = LAST(phis ++ nphis)        by def
       = LAST nphis                 by LAST_APPEND_NOT_NIL
       = LAST (MAP fix_phi_inst ..) by fix_phis_filter_non_phi_facts
       = LAST (h::t)               by LAST_MAP + fix_phi_inst_non_phi *)
  SUBGOAL_THEN ``(fix_phis_in_block preds bb).bb_instructions =
    FILTER (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst preds) (h::t)) ++
    FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst preds) (h::t))``
    (fn eq => ONCE_REWRITE_TAC [eq])
  >- simp[fix_phis_in_block_def, LET_THM] >>
  simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
  simp[listTheory.LAST_MAP, fix_phi_inst_non_phi, fix_phi_inst_opcode_non_phi]
QED

(* Helper: in FILTER P l, all elements satisfy P *)
Theorem EL_FILTER_P[local]:
  !P l i. i < LENGTH (FILTER P l) ==>
    P (EL i (FILTER P l))
Proof
  rpt strip_tac >>
  imp_res_tac rich_listTheory.EL_MEM >>
  fs[listTheory.MEM_FILTER]
QED

(* Helper: elements of FILTER P l come from l *)
Theorem EL_FILTER_MEM[local]:
  !P l i. i < LENGTH (FILTER P l) ==>
    MEM (EL i (FILTER P l)) l
Proof
  rpt strip_tac >>
  imp_res_tac rich_listTheory.EL_MEM >>
  fs[listTheory.MEM_FILTER]
QED

(* Terminators only at end of MAP fix_phi_inst when original has this property *)
Theorem terminators_at_end_MAP_fix_phi_inst[local]:
  !preds insts.
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode /\
    (!i. i < LENGTH insts /\ is_terminator (EL i insts).inst_opcode ==>
         i = PRE (LENGTH insts)) ==>
    (!i. i < LENGTH (MAP (fix_phi_inst preds) insts) /\
         is_terminator (EL i (MAP (fix_phi_inst preds) insts)).inst_opcode ==>
         i = PRE (LENGTH (MAP (fix_phi_inst preds) insts)))
Proof
  rpt strip_tac >>
  fs[listTheory.LENGTH_MAP] >>
  `EL i (MAP (fix_phi_inst preds) insts) = fix_phi_inst preds (EL i insts)` by
    simp[listTheory.EL_MAP] >>
  Cases_on `(EL i insts).inst_opcode = PHI` >> (
    TRY (imp_res_tac fix_phi_inst_not_terminator >> fs[] >> NO_TAC) >>
    `(fix_phi_inst preds (EL i insts)).inst_opcode = (EL i insts).inst_opcode` by
      simp[fix_phi_inst_opcode_non_phi] >>
    fs[]
  )
QED

(* Terminators only at end for l1 ++ l2: if l1 has no terminators
   and l2 has terminators only at end *)
Theorem terminators_at_end_APPEND[local]:
  !l1 l2.
    EVERY (\x. ~is_terminator x.inst_opcode) l1 /\
    l2 <> [] /\
    (!i. i < LENGTH l2 /\ is_terminator (EL i l2).inst_opcode ==>
         i = PRE (LENGTH l2)) ==>
    (!i. i < LENGTH (l1 ++ l2) /\
         is_terminator (EL i (l1 ++ l2)).inst_opcode ==>
         i = PRE (LENGTH (l1 ++ l2)))
Proof
  rpt strip_tac >>
  Cases_on `i < LENGTH l1` >>
  TRY (
    `EL i (l1 ++ l2) = EL i l1` by simp[listTheory.EL_APPEND_EQN] >>
    imp_res_tac listTheory.EVERY_EL >>
    fs[] >> NO_TAC) >>
  `EL i (l1 ++ l2) = EL (i - LENGTH l1) l2` by
    simp[listTheory.EL_APPEND_EQN] >>
  `i - LENGTH l1 < LENGTH l2` by fs[listTheory.LENGTH_APPEND] >>
  `i - LENGTH l1 = PRE (LENGTH l2)` by (res_tac >> fs[]) >>
  fs[listTheory.LENGTH_APPEND]
QED

(* All elements of FILTER (not PHI) from FRONT of a list are non-terminators,
   given the original list has terminators only at end *)
Theorem EVERY_non_term_FILTER_non_phi[local]:
  !l.
    l <> [] /\
    (!i. i < LENGTH l /\ is_terminator (EL i l).inst_opcode ==>
         i = PRE (LENGTH l)) /\
    (LAST l).inst_opcode <> PHI ==>
    (!i. i < LENGTH (FILTER (\x. x.inst_opcode <> PHI) l) /\
         is_terminator (EL i (FILTER (\x. x.inst_opcode <> PHI) l)).inst_opcode ==>
         i = PRE (LENGTH (FILTER (\x. x.inst_opcode <> PHI) l)))
Proof
  rpt strip_tac >>
  (* Decompose l = SNOC last init *)
  `?init last'. l = SNOC last' init` by
    (Cases_on `l` using listTheory.SNOC_CASES >> fs[]) >>
  gvs[listTheory.LAST_SNOC] >>
  (* FILTER preserves SNOC when P holds for last element *)
  `FILTER (\x. x.inst_opcode <> PHI) (SNOC last' init) =
   SNOC last' (FILTER (\x. x.inst_opcode <> PHI) init)` by
    simp[rich_listTheory.FILTER_SNOC] >>
  fs[listTheory.LENGTH_SNOC] >>
  Cases_on `i < LENGTH (FILTER (\x. x.inst_opcode <> PHI) init)` >>
  TRY (
    (* Case: i is in the init part — element is non-terminator *)
    `EL i (SNOC last' (FILTER (\x. x.inst_opcode <> PHI) init)) =
     EL i (FILTER (\x. x.inst_opcode <> PHI) init)` by
      simp[listTheory.EL_SNOC] >>
    (* This element is MEM init *)
    `MEM (EL i (FILTER (\x. x.inst_opcode <> PHI) init)) init` by (
      imp_res_tac rich_listTheory.EL_MEM >>
      fs[listTheory.MEM_FILTER]) >>
    (* So it's at some position j < LENGTH init in init *)
    fs[listTheory.MEM_EL] >>
    (* In SNOC last' init, position j < LENGTH init, so EL j (SNOC last' init) = EL j init *)
    `EL n init = EL n (SNOC last' init)` by
      simp[listTheory.EL_SNOC] >>
    (* Since j < LENGTH init = PRE(LENGTH(SNOC last' init)) - 1, it's a non-terminator *)
    `n < LENGTH (SNOC last' init)` by simp[listTheory.LENGTH_SNOC] >>
    `n = PRE (LENGTH (SNOC last' init))` by (res_tac >> fs[]) >>
    fs[listTheory.LENGTH_SNOC] >> NO_TAC) >>
  (* Case: i >= LENGTH(FILTER ...) — so i = LENGTH(FILTER init part) = PRE(LENGTH filtered) *)
  simp[]
QED

(* PHIs form a prefix in phis ++ nphis when phis = FILTER PHI and nphis = FILTER ~PHI *)
Theorem phi_prefix_filter_append[local]:
  !l1 l2.
    (!i. i < LENGTH l1 ==> (EL i l1).inst_opcode = PHI) /\
    (!j. j < LENGTH l2 ==> (EL j l2).inst_opcode <> PHI) ==>
    !i j. i < j /\ j < LENGTH (l1 ++ l2) /\
          (EL j (l1 ++ l2)).inst_opcode = PHI ==>
          (EL i (l1 ++ l2)).inst_opcode = PHI
Proof
  rpt strip_tac >>
  (* j must be in l1 part; otherwise EL j has opcode <> PHI *)
  `j < LENGTH l1` by (
    CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >>
    `EL j (l1 ++ l2) = EL (j - LENGTH l1) l2` by
      simp[listTheory.EL_APPEND_EQN] >>
    `j - LENGTH l1 < LENGTH l2` by
      fs[listTheory.LENGTH_APPEND] >>
    res_tac >> fs[]) >>
  `i < LENGTH l1` by DECIDE_TAC >>
  simp[listTheory.EL_APPEND_EQN]
QED

(* bb_well_formed preserved by fix_phis_in_block *)
Theorem bb_well_formed_fix_phis_in_block[local]:
  !preds bb. bb_well_formed bb ==>
    bb_well_formed (fix_phis_in_block preds bb)
Proof
  rpt strip_tac >>
  (* Expand assumption only, keep goal as bb_well_formed *)
  qpat_x_assum `bb_well_formed bb` mp_tac >>
  simp[bb_well_formed_def] >> strip_tac >>
  (* Abbreviate to prevent FILTER expansion *)
  qabbrev_tac `insts = bb.bb_instructions` >>
  qabbrev_tac `insts' = MAP (fix_phi_inst preds) insts` >>
  qabbrev_tac `phis = FILTER (\i. i.inst_opcode = PHI) insts'` >>
  qabbrev_tac `nphis = FILTER (\i. i.inst_opcode <> PHI) insts'` >>
  (* Structural equation *)
  `(fix_phis_in_block preds bb).bb_instructions = phis ++ nphis` by
    simp[fix_phis_in_block_def, LET_THM, Abbr `phis`, Abbr `nphis`,
         Abbr `insts'`, Abbr `insts`] >>
  (* Key derived facts *)
  `is_terminator (LAST insts).inst_opcode` by (
    `insts <> []` by fs[Abbr `insts`] >>
    Cases_on `insts` >> fs[] >>
    Cases_on `t` >> fs[listTheory.LAST_DEF, Abbr `insts`]) >>
  `(LAST insts).inst_opcode <> PHI` by
    (strip_tac >> fs[is_terminator_def]) >>
  `insts <> []` by fs[Abbr `insts`] >>
  `insts' <> []` by simp[Abbr `insts'`] >>
  `nphis <> [] /\ LAST nphis = LAST insts'` by (
    simp[Abbr `nphis`, Abbr `insts'`] >>
    mp_tac (Q.SPECL [`preds`, `insts`] fix_phis_filter_non_phi_facts) >>
    simp[]) >>
  (* Now prove bb_well_formed *)
  ASM_REWRITE_TAC [bb_well_formed_def] >>
  (* Derive key facts about insts' *)
  `LAST insts' = fix_phi_inst preds (LAST insts)` by
    simp[listTheory.LAST_MAP, Abbr `insts'`] >>
  `fix_phi_inst preds (LAST insts) = LAST insts` by
    simp[fix_phi_inst_non_phi] >>
  (* terminators at end for insts' *)
  `!i. i < LENGTH insts' /\
       is_terminator (EL i insts').inst_opcode ==>
       i = PRE (LENGTH insts')` by (
    `insts' = MAP (fix_phi_inst preds) insts` by simp[Abbr `insts'`] >>
    pop_assum (fn eq => ONCE_REWRITE_TAC [eq]) >>
    match_mp_tac terminators_at_end_MAP_fix_phi_inst >> simp[]) >>
  (* terminators at end for nphis *)
  `(LAST insts').inst_opcode <> PHI` by gvs[] >>
  `!i. i < LENGTH nphis /\
       is_terminator (EL i nphis).inst_opcode ==>
       i = PRE (LENGTH nphis)` by (
    simp[Abbr `nphis`] >>
    match_mp_tac EVERY_non_term_FILTER_non_phi >> simp[]) >>
  (* phis are all non-terminator *)
  `EVERY (\x. ~is_terminator x.inst_opcode) phis` by (
    simp[listTheory.EVERY_FILTER, Abbr `phis`] >>
    simp[listTheory.EVERY_MEM, listTheory.MEM_FILTER] >> rpt strip_tac >>
    gvs[is_terminator_def]) >>
  (* Conjunct 1: non-empty *)
  conj_tac >- simp[] >>
  (* Conjunct 2: LAST is terminator *)
  conj_tac >- (
    `LAST (phis ++ nphis) = LAST nphis` by
      simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
    gvs[]) >>
  (* Conjunct 3: terminators only at end *)
  conj_tac >- (
    match_mp_tac terminators_at_end_APPEND >> simp[]) >>
  (* Conjunct 4: PHIs form a prefix *)
  match_mp_tac phi_prefix_filter_append >>
  conj_tac >- (
    rpt strip_tac >>
    `MEM (EL i phis) phis` by simp[rich_listTheory.EL_MEM] >>
    fs[Abbr `phis`, listTheory.MEM_FILTER]) >>
  rpt strip_tac >>
  `MEM (EL j nphis) nphis` by simp[rich_listTheory.EL_MEM] >>
  fs[Abbr `nphis`, listTheory.MEM_FILTER]
QED


(* ================================================================
   Section: wf_function preservation for fix_all_phis
   ================================================================ *)

(* inst_ids of fix_phis_in_block are a permutation of original inst_ids *)
Theorem inst_ids_fix_phis_in_block[local]:
  !preds bb.
    PERM (MAP (\i. i.inst_id) (fix_phis_in_block preds bb).bb_instructions)
         (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rw[fix_phis_in_block_def, LET_THM] >>
  (* Result instructions = FILTER PHI (MAP fix_phi_inst) ++ FILTER ~PHI (MAP fix_phi_inst) *)
  (* This is a permutation of MAP fix_phi_inst bb.bb_instructions *)
  SUBGOAL_THEN ``PERM
    (FILTER (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst preds) bb.bb_instructions) ++
     FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst preds) bb.bb_instructions))
    (MAP (fix_phi_inst preds) bb.bb_instructions)``
    ASSUME_TAC
  >- simp[PERM_FILTER_COMPLEMENT] >>
  (* MAP inst_id through PERM *)
  `PERM (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = PHI) (MAP (fix_phi_inst preds) bb.bb_instructions) ++
     FILTER (\i. i.inst_opcode <> PHI) (MAP (fix_phi_inst preds) bb.bb_instructions)))
    (MAP (\i. i.inst_id) (MAP (fix_phi_inst preds) bb.bb_instructions))` by
    simp[sortingTheory.PERM_MAP] >>
  (* MAP inst_id (MAP fix_phi_inst insts) = MAP inst_id insts (since fix_phi_inst preserves id) *)
  `MAP (\i. i.inst_id) (MAP (fix_phi_inst preds) bb.bb_instructions) =
   MAP (\i. i.inst_id) bb.bb_instructions` by
    simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, fix_phi_inst_id] >>
  fs[]
QED

(* Sub-lemma: fn_labels unchanged by fix_all_phis *)
Theorem fn_labels_fix_all_phis[local]:
  !func. fn_labels (fix_all_phis func) = fn_labels func
Proof
  rw[fix_all_phis_def, fn_labels_def, listTheory.MAP_MAP_o,
     combinTheory.o_DEF, fix_phis_in_block_label]
QED

(* Sub-lemma: fn_succs_closed preserved by fix_all_phis *)
Theorem fn_succs_closed_fix_all_phis[local]:
  !func. wf_function func ==> fn_succs_closed (fix_all_phis func)
Proof
  rw[fn_succs_closed_def, fix_all_phis_def] >>
  fs[listTheory.MEM_MAP] >>
  rename1 `MEM blk func.fn_blocks` >>
  `bb_well_formed blk` by (fs[wf_function_def] >> res_tac) >>
  `bb_succs (fix_phis_in_block (pred_labels func blk.bb_label) blk) =
   bb_succs blk` by simp[bb_succs_fix_phis_in_block] >>
  gvs[] >>
  fs[wf_function_def, fn_succs_closed_def] >> res_tac >>
  pop_assum mp_tac >>
  simp[fn_labels_def, listTheory.MAP_MAP_o, combinTheory.o_DEF,
       fix_phis_in_block_label]
QED

(* Sub-lemma: fn_inst_ids_distinct preserved by fix_all_phis *)
Theorem fn_inst_ids_distinct_fix_all_phis[local]:
  !func. fn_inst_ids_distinct func ==> fn_inst_ids_distinct (fix_all_phis func)
Proof
  rw[fn_inst_ids_distinct_def, fix_all_phis_def,
     listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  `!bbs. PERM (FLAT (MAP (\bb. MAP (\i. i.inst_id)
      (fix_phis_in_block (pred_labels func bb.bb_label) bb).bb_instructions) bbs))
    (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs))` by (
    Induct >> simp[] >> rpt strip_tac >>
    irule sortingTheory.PERM_CONG >> simp[] >>
    simp[inst_ids_fix_phis_in_block]) >>
  pop_assum (qspec_then `func.fn_blocks` mp_tac) >>
  strip_tac >> imp_res_tac sortingTheory.ALL_DISTINCT_PERM >> fs[]
QED

(* wf_function preserved by fix_all_phis *)
Theorem wf_fix_all_phis:
  !func. wf_function func ==> wf_function (fix_all_phis func)
Proof
  rpt strip_tac >> simp[wf_function_def] >> rpt conj_tac >- (
    (* ALL_DISTINCT fn_labels *)
    simp[fn_labels_fix_all_phis] >> fs[wf_function_def]
  ) >- (
    (* fn_has_entry *)
    fs[wf_function_def, fn_has_entry_def, fix_all_phis_def] >>
    Cases_on `func.fn_blocks` >> fs[]
  ) >- (
    (* bb_well_formed *)
    rpt strip_tac >>
    fs[fix_all_phis_def, listTheory.MEM_MAP] >>
    match_mp_tac bb_well_formed_fix_phis_in_block >>
    fs[wf_function_def] >> res_tac
  ) >- (
    (* fn_succs_closed *)
    irule fn_succs_closed_fix_all_phis >> simp[]
  ) >> (
    (* fn_inst_ids_distinct *)
    irule fn_inst_ids_distinct_fix_all_phis >> fs[wf_function_def]
  )
QED


(* ===== MEM decomposition for replace_block / remove_block ===== *)

Theorem MEM_replace_block:
  !x lbl new_bb bbs.
    MEM x (replace_block lbl new_bb bbs) ==>
    (x = new_bb /\ (?y. MEM y bbs /\ y.bb_label = lbl)) \/
    (MEM x bbs /\ x.bb_label <> lbl)
Proof
  rpt strip_tac >>
  fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  BasicProvers.every_case_tac >> fs[] >> rw[] >> metis_tac[]
QED

Theorem MEM_replace_remove:
  !b lbl new_bb nlbl bbs.
    MEM b (replace_block lbl new_bb (remove_block nlbl bbs)) ==>
    (b = new_bb /\ (?y. MEM y bbs /\ y.bb_label <> nlbl /\ y.bb_label = lbl)) \/
    (MEM b bbs /\ b.bb_label <> nlbl /\ b.bb_label <> lbl)
Proof
  rpt strip_tac >>
  fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP,
     cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER] >>
  BasicProvers.every_case_tac >> fs[] >> rw[] >> metis_tac[]
QED

Theorem MEM_replace_block_intro:
  !lbl new_bb bbs bb.
    MEM bb bbs /\ bb.bb_label <> lbl ==>
    MEM bb (replace_block lbl new_bb bbs)
Proof
  rpt strip_tac >>
  fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  qexists `bb` >> simp[]
QED

Theorem MEM_replace_block_new:
  !lbl new_bb bbs.
    (?bb. MEM bb bbs /\ bb.bb_label = lbl) ==>
    MEM new_bb (replace_block lbl new_bb bbs)
Proof
  rpt strip_tac >>
  fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  qexists `bb` >> simp[]
QED

Theorem MEM_replace_block_other:
  !x lbl new_bb bbs.
    MEM x bbs /\ x.bb_label <> lbl ==>
    MEM x (replace_block lbl new_bb bbs)
Proof
  rpt strip_tac >>
  fs[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  qexists `x` >> simp[]
QED

Theorem MEM_remove_block_intro:
  !bb lbl bbs.
    MEM bb bbs /\ bb.bb_label <> lbl ==>
    MEM bb (remove_block lbl bbs)
Proof
  rw[cfgTransformTheory.remove_block_def, listTheory.MEM_FILTER]
QED
