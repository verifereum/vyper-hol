Theory loadElimJoinPlacement
Ancestors
  loadElimDefs loadElimStaticGeneration loadElimOccurrenceCoverage
  cfgDefs venomWf list rich_list pred_set

(* Finite paths oriented from entry to consumer, using predecessor edges. *)
Definition le_pred_path_def:
  le_pred_path cfg [] = T /\
  le_pred_path cfg [x] = T /\
  le_pred_path cfg (x::y::xs) =
    (MEM x (cfg_preds_of cfg y) /\ le_pred_path cfg (y::xs))
End

Theorem le_pred_path_snoc:
  !xs x. le_pred_path cfg (SNOC x xs) <=>
    le_pred_path cfg xs /\
    (xs = [] \/ MEM (LAST xs) (cfg_preds_of cfg x))
Proof
  Induct_on `xs` >- simp[le_pred_path_def] >>
  Cases_on `xs` >> fs[le_pred_path_def, SNOC] >> metis_tac[]
QED

Theorem le_find_join_path_aux:
  !xs visited. xs <> [] /\ le_pred_path cfg xs ==>
    MEM (find_join_block cfg visited (LAST xs)) xs \/
    find_join_block cfg visited (LAST xs) IN visited \/
    (?p. cfg_preds_of cfg (HD xs) = [p])
Proof
  Induct using SNOC_INDUCT >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `xs = []`
  >- (gvs[SNOC, le_pred_path_def] >>
      simp[Once find_join_block_def] >>
      Cases_on `x IN visited` >> simp[] >>
      Cases_on `cfg_preds_of cfg x` >> simp[] >>
      Cases_on `t` >> simp[]) >>
  gvs[le_pred_path_snoc] >>
  `HD (SNOC x xs) = HD xs` by (Cases_on `xs` >> gvs[SNOC]) >>
  simp[LAST_SNOC] >>
  Cases_on `x IN visited` >- simp[Once find_join_block_def] >>
  Cases_on `?p. cfg_preds_of cfg x = [p]`
  >- (pop_assum strip_assume_tac >>
      `p = LAST xs` by gvs[] >> gvs[] >>
      `find_join_block cfg visited x =
       find_join_block cfg (x INSERT visited) (LAST xs)` by
        simp[Once find_join_block_def] >>
      asm_rewrite_tac[] >>
      first_x_assum (qspec_then `x INSERT visited` mp_tac) >>
      simp[] >> metis_tac[]) >>
  simp[Once find_join_block_def] >>
  Cases_on `cfg_preds_of cfg x` >> simp[] >>
  Cases_on `t` >> gvs[]
QED

Theorem le_find_join_path:
  xs <> [] /\ le_pred_path cfg xs /\ visited SUBSET set xs ==>
  MEM (find_join_block cfg visited (LAST xs)) xs \/
  (?p. cfg_preds_of cfg (HD xs) = [p])
Proof
  strip_tac >> drule_all le_find_join_path_aux >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem le_find_join_path_escape:
  xs <> [] /\ le_pred_path cfg xs /\
  ~MEM (find_join_block cfg {} (LAST xs)) xs ==>
  ?p. cfg_preds_of cfg (HD xs) = [p]
Proof
  strip_tac >> drule_all le_find_join_path_aux >>
  disch_then (qspec_then `{}` mp_tac) >> simp[]
QED

Theorem le_find_join_path_placement:
  xs <> [] /\ le_pred_path cfg xs /\
  (!p. cfg_preds_of cfg (HD xs) <> [p]) ==>
  MEM (find_join_block cfg {} (LAST xs)) xs
Proof
  metis_tac[le_find_join_path_escape]
QED

Theorem le_fn_path_pred_path:
  !xs. wf_function fn /\ is_fn_path fn xs ==>
    le_pred_path (cfg_analyze fn) xs
Proof
  Induct >> simp[le_pred_path_def] >>
  Cases_on `xs` >> simp[is_fn_path_def, le_pred_path_def] >>
  metis_tac[le_static_edge_pred]
QED

Theorem le_occ_prefix_pred_route:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb ==>
  le_occ_route es <> [] /\
  le_pred_path (cfg_analyze fn) (le_occ_route es) /\
  HD (le_occ_route es) = s0.vs_current_bb /\
  LAST (le_occ_route es) = s.vs_current_bb
Proof
  metis_tac[le_occ_prefix_route, le_fn_path_pred_path]
QED
