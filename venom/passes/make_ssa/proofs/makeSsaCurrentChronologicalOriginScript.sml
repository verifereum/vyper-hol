Theory makeSsaCurrentChronologicalOrigin
Ancestors makeSsaCurrentLastSite makeSsaCurrentCutTokens
  makeSsaCurrentExitTokens makeSsaCurrentTokenOwnership makeSsaCurrentTokens
  venomWf venomExecProps venomInst list rich_list

(* Chronological provenance only: no assertion about runtime values. *)
Theorem current_site_block_nondefault:
  wf_function fn /\ lookup_block l fn.fn_blocks = SOME bb /\
  current_changing_site fn ins v l ==>
  !w. current_block_token fn ins v l t <> CurrentDefault w
Proof
  strip_tac >>
  Cases_on `?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs`
  >- metis_tac[current_block_token_definition_nondefault] >>
  `EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `ins v l` by
    (gvs[current_changing_site_def] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def, optionTheory.SOME_11]) >>
  simp[current_block_token_def, current_original_scan_absent]
QED

Theorem current_chronological_last_site:
  wf_function fn /\
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) path ==>
  (EVERY (\l. ~current_changing_site fn ins v l) path /\
   current_chain_token fn ins v path t = t) \/
  ?pre h post. path = pre ++ h::post /\
    current_changing_site fn ins v h /\
    EVERY (\l. ~current_changing_site fn ins v l) post /\
    current_chain_token fn ins v path t =
      current_block_token fn ins v h (CurrentDefault v)
Proof
  strip_tac >>
  `EVERY (\l. ~current_changing_site fn ins v l) path \/
   ?pre d post. path = pre ++ d::post /\ current_changing_site fn ins v d /\
     EVERY (\l. ~current_changing_site fn ins v l) post` by
    metis_tac[current_list_last_site] >>
  pop_assum strip_assume_tac
  >- metis_tac[current_non_site_chain_token] >>
  disj2_tac >> qexistsl_tac [`pre`, `d`, `post`] >> simp[] >>
  simp[current_chain_token_append, current_chain_token_def,
    current_non_site_chain_token] >>
  irule current_site_block_constant >> simp[] >>
  gvs[EVERY_MEM] >>
  `?bb. lookup_block d fn.fn_blocks = SOME bb` by metis_tac[MEM_APPEND, MEM] >>
  simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]
QED

Theorem current_chronological_default_inverse:
  wf_function fn /\
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) path /\
  current_chain_token fn ins v path (CurrentDefault v) = CurrentDefault w ==>
  w = v /\ EVERY (\l. ~current_changing_site fn ins v l) path
Proof
  strip_tac >> drule_all current_chronological_last_site >>
  disch_then (qspecl_then [`v`, `CurrentDefault v`, `ins`] strip_assume_tac)
  >- gvs[] >>
  `?bb. lookup_block h fn.fn_blocks = SOME bb` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  metis_tac[current_site_block_nondefault]
QED

Theorem current_chronological_nondefault_origin:
  wf_function fn /\
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) path /\
  current_chain_token fn ins v path (CurrentDefault v) = token /\
  (!w. token <> CurrentDefault w) ==>
  ?pre h post. path = pre ++ h::post /\
    current_changing_site fn ins v h /\
    EVERY (\l. ~current_changing_site fn ins v l) post /\
    token = current_block_token fn ins v h (CurrentDefault v)
Proof
  strip_tac >> drule_all current_chronological_last_site >>
  disch_then (qspecl_then [`v`, `CurrentDefault v`, `ins`] strip_assume_tac) >>
  metis_tac[]
QED

Theorem current_chronological_inserted_inverse:
  wf_function fn /\
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) path /\
  current_chain_token fn ins v path (CurrentDefault v) = CurrentInserted w h ==>
  w = v /\
  ?pre post hb. path = pre ++ h::post /\ ins v h /\
    lookup_block h fn.fn_blocks = SOME hb /\
    EVERY (\i. ~MEM v i.inst_outputs) hb.bb_instructions /\
    EVERY (\l. ~current_changing_site fn ins v l) post
Proof
  strip_tac >>
  `?pre d post. path = pre ++ d::post /\
    current_changing_site fn ins v d /\
    EVERY (\l. ~current_changing_site fn ins v l) post /\
    CurrentInserted w h = current_block_token fn ins v d (CurrentDefault v)` by
    (irule current_chronological_nondefault_origin >> simp[] >> metis_tac[]) >>
  `?hb. lookup_block d fn.fn_blocks = SOME hb` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `EVERY (\i. ~MEM v i.inst_outputs) hb.bb_instructions` by
    (simp[EVERY_MEM] >> spose_not_then strip_assume_tac >>
     `?i j. current_block_token fn ins v d (CurrentDefault v) = CurrentOriginal d i j` by
       metis_tac[current_block_token_original] >> gvs[]) >>
  gvs[current_block_token_def, current_original_scan_absent] >>
  Cases_on `ins v d` >> gvs[] >> metis_tac[]
QED
