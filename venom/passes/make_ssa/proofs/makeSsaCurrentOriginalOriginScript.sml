Theory makeSsaCurrentOriginalOrigin
Ancestors makeSsaCurrentChronologicalOrigin makeSsaCurrentSingletonSelectors
  makeSsaCurrentTokenOwnership makeSsaCurrentTokens makeSsaCurrentCutTokens
  venomExecProps venomInst venomWf list rich_list

Theorem current_final_output_occurrence[local]:
  (?inst. MEM inst insts /\ MEM v inst.inst_outputs) ==>
  ?i j. i < LENGTH insts /\ j < LENGTH (EL i insts).inst_outputs /\
    EL j (EL i insts).inst_outputs = v /\
    (!k. j < k /\ k < LENGTH (EL i insts).inst_outputs ==>
      EL k (EL i insts).inst_outputs <> v) /\
    (!r. i < r /\ r < LENGTH insts ==> ~MEM v (EL r insts).inst_outputs)
Proof
  strip_tac >>
  `MEM T (MAP (\inst. MEM v inst.inst_outputs) insts)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  drule current_last_matching_slot >> strip_tac >>
  gvs[EL_MAP] >>
  drule current_last_matching_slot >> strip_tac >>
  qexistsl_tac [`j`, `j'`] >> simp[] >> metis_tac[EL_MAP]
QED

Theorem current_chronological_original_inverse:
  wf_function fn /\
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) path /\
  current_chain_token fn ins v path (CurrentDefault v) = CurrentOriginal h i j ==>
  ?pre post hb. path = pre ++ h::post /\ lookup_block h fn.fn_blocks = SOME hb /\
    i < LENGTH hb.bb_instructions /\
    j < LENGTH (EL i hb.bb_instructions).inst_outputs /\
    EL j (EL i hb.bb_instructions).inst_outputs = v /\
    (!k. j < k /\ k < LENGTH (EL i hb.bb_instructions).inst_outputs ==>
      EL k (EL i hb.bb_instructions).inst_outputs <> v) /\
    (!r. i < r /\ r < LENGTH hb.bb_instructions ==>
      ~MEM v (EL r hb.bb_instructions).inst_outputs) /\
    EVERY (\l. ~current_changing_site fn ins v l) post
Proof
  strip_tac >>
  `?pre d post. path = pre ++ d::post /\ current_changing_site fn ins v d /\
    EVERY (\l. ~current_changing_site fn ins v l) post /\
    CurrentOriginal h i j = current_block_token fn ins v d (CurrentDefault v)` by
    (irule current_chronological_nondefault_origin >> simp[] >> metis_tac[]) >>
  `?hb. lookup_block d fn.fn_blocks = SOME hb` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `?inst. MEM inst hb.bb_instructions /\ MEM v inst.inst_outputs` by
    (spose_not_then assume_tac >>
     `EVERY (\inst. ~MEM v inst.inst_outputs) hb.bb_instructions` by
       (simp[EVERY_MEM] >> metis_tac[]) >>
     gvs[current_block_token_def, current_original_scan_absent] >>
     Cases_on `ins v d` >> gvs[]) >>
  `?ii jj. ii < LENGTH hb.bb_instructions /\
    jj < LENGTH (EL ii hb.bb_instructions).inst_outputs /\
    EL jj (EL ii hb.bb_instructions).inst_outputs = v /\
    (!k. jj < k /\ k < LENGTH (EL ii hb.bb_instructions).inst_outputs ==>
      EL k (EL ii hb.bb_instructions).inst_outputs <> v) /\
    (!r. ii < r /\ r < LENGTH hb.bb_instructions ==>
      ~MEM v (EL r hb.bb_instructions).inst_outputs)` by
    (irule current_final_output_occurrence >> metis_tac[]) >>
  `!t. current_original_scan v d 0 hb.bb_instructions t =
    CurrentOriginal d ii jj` by
    (gen_tac >> irule (SRULE [] (Q.SPECL [`insts`, `0`] current_original_scan_final_slot)) >> metis_tac[]) >>
  gvs[current_block_token_def] >>
  qexistsl_tac [`pre`, `post`] >> simp[]
QED

Theorem current_chronological_original_not_unvisited:
  wf_function fn /\
  EVERY (\l. ?bb. lookup_block l fn.fn_blocks = SOME bb) path /\ ~MEM h path ==>
  current_chain_token fn ins v path (CurrentDefault v) <> CurrentOriginal h i j
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule_all current_chronological_original_inverse >> strip_tac >> gvs[]
QED
