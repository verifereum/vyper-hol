Theory makeSsaCurrentMergeSeed
Ancestors makeSsaCurrentTokenOwnership makeSsaCurrentGraphCut
  makeSsaCurrentTokens list

Theorem current_output_inserted_origin[local]:
  !xs j t. current_output_token v l i j xs t = CurrentInserted w h ==>
    t = CurrentInserted w h
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h' = v` >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem current_scan_inserted_origin[local]:
  !insts i t. current_original_scan v l i insts t = CurrentInserted w h ==>
    t = CurrentInserted w h
Proof
  Induct >> simp[current_original_scan_def] >>
  metis_tac[current_output_inserted_origin]
QED

Theorem current_block_inserted_origin[local]:
  current_block_token fn ins v l t = CurrentInserted w h ==>
    t = CurrentInserted w h \/ l = h
Proof
  simp[current_block_token_def] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  strip_tac >> drule current_scan_inserted_origin >>
  Cases_on `ins v l` >> simp[]
QED

Theorem current_chain_inserted_origin:
  !path t. current_chain_token fn ins v path t = CurrentInserted w h ==>
    t = CurrentInserted w h \/ MEM h path
Proof
  Induct >> simp[current_chain_token_def] >>
  metis_tac[current_block_inserted_origin]
QED

Theorem current_exit_inserted_origin:
  current_block_token fn ins v p
    (current_inherited_token fn ins v (REVERSE ps)) = CurrentInserted w h ==>
  MEM h (p::ps)
Proof
  strip_tac >> drule current_block_inserted_origin >>
  simp[current_inherited_token_def] >> strip_tac >> simp[] >>
  drule current_chain_inserted_origin >> simp[]
QED
