Theory makeSsaCurrentNonDegTokenSources
Ancestors
  makeSsaCurrentTokens makeSsaCurrentCutTokens makeSsaCurrentLastSite
  venomWf venomInst list

Definition current_nondeg_token_at_def:
  (current_nondeg_token_at l (CurrentDefault v) = F) /\
  (current_nondeg_token_at l (CurrentOriginal b i j) = (b = l)) /\
  (current_nondeg_token_at l (CurrentInserted v b) = (b = l))
End

Theorem current_nondeg_token_at_unique:
  current_nondeg_token_at l t /\ current_nondeg_token_at k t ==> l = k
Proof
  Cases_on `t` >> simp[current_nondeg_token_at_def] >> metis_tac[]
QED

Theorem current_nondeg_output_token_local:
  !xs j t. current_output_token v l i j xs t = t \/
    current_nondeg_token_at l (current_output_token v l i j xs t)
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h = v` >> simp[] >>
  metis_tac[current_nondeg_token_at_def]
QED

Theorem current_nondeg_original_scan_local:
  !insts i t. current_original_scan v l i insts t = t \/
    current_nondeg_token_at l (current_original_scan v l i insts t)
Proof
  Induct >> simp[current_original_scan_def] >>
  metis_tac[current_nondeg_output_token_local]
QED

Theorem current_nondeg_block_token_local:
  current_block_token fn ins v l t = t \/
  current_nondeg_token_at l (current_block_token fn ins v l t)
Proof
  simp[current_block_token_def] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  Cases_on `ins v l` >> simp[] >>
  metis_tac[current_nondeg_original_scan_local, current_nondeg_token_at_def]
QED

Theorem current_nondeg_changing_block_reset:
  wf_function fn /\ MEM l (fn_labels fn) /\ current_changing_site fn ins v l ==>
  current_nondeg_token_at l (current_block_token fn ins v l t)
Proof
  strip_tac >>
  drule_all current_site_block_constant >>
  disch_then (qspecl_then [`t`, `CurrentInserted v l`] assume_tac) >>
  metis_tac[current_nondeg_block_token_local, current_nondeg_token_at_def]
QED

Theorem current_nondeg_chain_token_local:
  !ls t. current_chain_token fn ins v ls t = t \/
    ?l. MEM l ls /\ current_nondeg_token_at l (current_chain_token fn ins v ls t)
Proof
  Induct >> simp[current_chain_token_def] >>
  metis_tac[current_nondeg_block_token_local]
QED

Theorem current_nondeg_changing_chain_source:
  wf_function fn /\ MEM d (fn_labels fn) /\ current_changing_site fn ins v d ==>
  ?l. MEM l (d::xs) /\
      current_nondeg_token_at l (current_chain_token fn ins v (d::xs) t)
Proof
  strip_tac >> simp[current_chain_token_def] >>
  drule_all current_nondeg_changing_block_reset >> strip_tac >>
  metis_tac[current_nondeg_chain_token_local]
QED

Theorem current_nondeg_disjoint_chain_tokens:
  wf_function fn /\ MEM d (fn_labels fn) /\ current_changing_site fn ins v d /\
  DISJOINT (set (d::xs)) (set ys) /\
  (!l. MEM l (d::xs) ==> ~current_nondeg_token_at l u) ==>
  current_chain_token fn ins v (d::xs) t <> current_chain_token fn ins v ys u
Proof
  strip_tac >>
  drule_all current_nondeg_changing_chain_source >> strip_tac >>
  spose_not_then assume_tac >>
  `current_chain_token fn ins v ys u = u \/
   ?k. MEM k ys /\ current_nondeg_token_at k (current_chain_token fn ins v ys u)` by
    metis_tac[current_nondeg_chain_token_local] >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[current_nondeg_token_at_unique]
QED
