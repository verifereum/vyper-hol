(* The index must not replace the local entry from which Pop captured
   a subarray.  This protects its popped history, not all local scopes. *)
Theory bodyArraySelectCapturedMods
Ancestors
  bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods
  exprSimHypsDefs allocLimits targetOverlapAccess vyperLocalAccessFrame
  vyperSubscriptOverlap vyperInterpreter vyperState vyperAST

Theorem captured_read_local_ref[local]:
  MEM (ReadAcc (LocalRef id)) accs ==>
  MEM (LocalRef id) (nonconstant_reads mods accs)
Proof
  qid_spec_tac `accs` >> qid_spec_tac `mods` >>
  recInduct nonconstant_reads_ind >> rw[nonconstant_reads_def] >>
  rpt (CASE_TAC >> gvs[]) >> metis_tac[]
QED

Theorem captured_pop_index_local_mods[local]:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  eval_expr cx obj (es with gas_obs := gs1) = (INL (PlaceR (MemoryPlace id path)),mid) /\
  is_ArrayT (expr_type obj) /\ base_from_pop obj /\
  eval_expr cx idx (mid with gas_obs := gs2) = (res,fin) ==>
  lookup_scopes id fin.scopes = lookup_scopes id mid.scopes
Proof
  strip_tac >>
  `MEM (LocalRef id)
    (nonconstant_reads cenv.ce_modules (expr_accesses cenv.ce_modules obj))` by
    (irule captured_read_local_ref >> simp[expr_accesses_def] >>
     drule eval_expr_memory_access >> simp[]) >>
  `~MEM (WriteAcc (LocalRef id)) (accesses_expr idx)` suffices_by
    (strip_tac >> drule_all eval_expr_unwritten_local >> simp[]) >>
  strip_tac >>
  `pop_subscript_overlap cenv.ce_modules obj idx` by
    (simp[pop_subscript_overlap_def, any_written_MEM] >>
     conj_tac >- (strip_tac >> gvs[]) >>
     disj1_tac >> qexists `LocalRef id` >> simp[expr_accesses_def]) >>
  fs[expr_body_pre_mods_def, alloc_limits_expr_def]
QED
