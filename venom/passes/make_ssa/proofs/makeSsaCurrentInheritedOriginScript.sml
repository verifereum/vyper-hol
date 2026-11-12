Theory makeSsaCurrentInheritedOrigin
Ancestors
  makeSsaCurrentScanOrigin makeSsaCurrentGraphCut makeSsaCurrentTokens list

Theorem current_block_token_origin[local]:
  current_block_token fn ins v l t = t \/
  (?bb j k. lookup_block l fn.fn_blocks = SOME bb /\
    j < LENGTH bb.bb_instructions /\
    k < LENGTH (EL j bb.bb_instructions).inst_outputs /\
    EL k (EL j bb.bb_instructions).inst_outputs = v /\
    current_block_token fn ins v l t = CurrentOriginal l j k) \/
  (?bb. lookup_block l fn.fn_blocks = SOME bb /\ ins v l /\
    current_block_token fn ins v l t = CurrentInserted v l)
Proof
  simp[current_block_token_def] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  qspecl_then [`bb.bb_instructions`, `0`,
    `if ins v l then CurrentInserted v l else t`]
    strip_assume_tac current_original_scan_origin
  >- (Cases_on `ins v l` >> gvs[])
  >> simp[] >> metis_tac[]
QED

Theorem current_chain_token_origin:
  !ls t. current_chain_token fn ins v ls t = t \/
  (?d bb j k. MEM d ls /\ lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH bb.bb_instructions /\
    k < LENGTH (EL j bb.bb_instructions).inst_outputs /\
    EL k (EL j bb.bb_instructions).inst_outputs = v /\
    current_chain_token fn ins v ls t = CurrentOriginal d j k) \/
  (?d bb. MEM d ls /\ lookup_block d fn.fn_blocks = SOME bb /\
    ins v d /\ current_chain_token fn ins v ls t = CurrentInserted v d)
Proof
  Induct >> simp[current_chain_token_def] >> rpt gen_tac >>
  first_x_assum (qspec_then `current_block_token fn ins v h t` strip_assume_tac)
  >- metis_tac[current_block_token_origin]
  >> metis_tac[]
QED

Theorem current_inherited_original_origin:
  current_inherited_token fn ins v (REVERSE ps) = CurrentOriginal d j k ==>
  MEM d ps /\ ?bb. lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH bb.bb_instructions /\
    k < LENGTH (EL j bb.bb_instructions).inst_outputs /\
    EL k (EL j bb.bb_instructions).inst_outputs = v
Proof
  simp[current_inherited_token_def] >> strip_tac >>
  qspecl_then [`REVERSE ps`, `CurrentDefault v`]
    strip_assume_tac current_chain_token_origin >> gvs[] >> metis_tac[]
QED

Theorem current_inherited_inserted_origin:
  current_inherited_token fn ins v (REVERSE ps) = CurrentInserted w d ==>
  w = v /\ MEM d ps /\ ins v d /\
  ?bb. lookup_block d fn.fn_blocks = SOME bb
Proof
  simp[current_inherited_token_def] >> strip_tac >>
  qspecl_then [`REVERSE ps`, `CurrentDefault v`]
    strip_assume_tac current_chain_token_origin >> gvs[] >> metis_tac[]
QED

Theorem current_inherited_original_strict_dom:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l /\
  current_inherited_token fn ins v (REVERSE ps) = CurrentOriginal d j k ==>
  strict_dominates (dom_analyze (cfg_analyze fn) fn) d l
Proof
  metis_tac[current_inherited_original_origin, current_actual_chain_membership]
QED

Theorem current_inherited_inserted_strict_dom:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l /\
  current_inherited_token fn ins v (REVERSE ps) = CurrentInserted w d ==>
  strict_dominates (dom_analyze (cfg_analyze fn) fn) d l
Proof
  metis_tac[current_inherited_inserted_origin, current_actual_chain_membership]
QED
