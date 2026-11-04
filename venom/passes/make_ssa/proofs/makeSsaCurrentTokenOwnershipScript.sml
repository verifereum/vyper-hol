Theory makeSsaCurrentTokenOwnership
Ancestors
  makeSsaCurrentTokens makeSsaCurrentPlacementCut makeSsaCurrentDefs
  venomInst venomState list arithmetic

Theorem current_output_token_present:
  !xs start t. MEM v xs ==>
    ?j. j < LENGTH xs /\ EL j xs = v /\
      current_output_token v l i start xs t = CurrentOriginal l i (start+j)
Proof
  Induct >- simp[] >> rpt gen_tac >> disch_tac >>
  simp[current_output_token_def] >> Cases_on `MEM v xs`
  >- (first_x_assum (qspecl_then [`SUC start`,
        `if h = v then CurrentOriginal l i start else t`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `SUC j` >> simp[ADD_CLAUSES]) >>
  gvs[] >> qexists_tac `0` >> simp[current_output_token_absent]
QED

Theorem current_original_scan_present:
  !insts start t. (?inst. MEM inst insts /\ MEM v inst.inst_outputs) ==>
    ?k j. k < LENGTH insts /\ j < LENGTH (EL k insts).inst_outputs /\
      EL j (EL k insts).inst_outputs = v /\
      current_original_scan v l start insts t = CurrentOriginal l (start+k) j
Proof
  Induct >- simp[] >> rpt gen_tac >> disch_tac >>
  simp[current_original_scan_def] >>
  Cases_on `?inst. MEM inst insts /\ MEM v inst.inst_outputs`
  >- (first_x_assum (qspecl_then [`SUC start`,
        `current_output_token v l start 0 h.inst_outputs t`] mp_tac) >>
      simp[] >> strip_tac >> qexistsl_tac [`SUC k`, `j`] >> simp[ADD_CLAUSES]) >>
  `EVERY (\inst. ~MEM v inst.inst_outputs) insts` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `MEM v h.inst_outputs` by metis_tac[MEM] >>
  drule current_output_token_present >>
  disch_then (qspecl_then [`l`, `start`, `0`, `t`] mp_tac) >> strip_tac >>
  qexistsl_tac [`0`, `j`] >> simp[current_original_scan_absent]
QED

Definition current_token_owns_def:
  (current_token_owns fn (CurrentDefault w) v <=> w = v) /\
  (current_token_owns fn (CurrentInserted w l) v <=> w = v) /\
  (current_token_owns fn (CurrentOriginal l i j) v <=>
    ?bb. lookup_block l fn.fn_blocks = SOME bb /\
      i < LENGTH bb.bb_instructions /\
      j < LENGTH (EL i bb.bb_instructions).inst_outputs /\
      EL j (EL i bb.bb_instructions).inst_outputs = v)
End

Theorem current_block_token_original:
  lookup_block l fn.fn_blocks = SOME bb /\
  (?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) ==>
  ?i j. i < LENGTH bb.bb_instructions /\
    j < LENGTH (EL i bb.bb_instructions).inst_outputs /\
    EL j (EL i bb.bb_instructions).inst_outputs = v /\
    current_block_token fn ins v l t = CurrentOriginal l i j
Proof
  strip_tac >> simp[current_block_token_def] >>
  metis_tac[current_original_scan_present, ADD_CLAUSES]
QED

Theorem current_block_token_owns:
  current_token_owns fn t v ==> current_token_owns fn (current_block_token fn ins v l t) v
Proof
  strip_tac >> Cases_on `lookup_block l fn.fn_blocks`
  >- simp[current_block_token_def] >>
  rename1 `lookup_block l fn.fn_blocks = SOME bb` >>
  Cases_on `?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs`
  >- (drule_all current_block_token_original >>
      disch_then (qspecl_then [`t`, `ins`] strip_assume_tac) >>
      simp[current_token_owns_def] >> metis_tac[]) >>
  `EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  simp[current_block_token_def, current_original_scan_absent] >>
  Cases_on `ins v l` >> simp[current_token_owns_def]
QED

Theorem current_chain_token_owns:
  !path t. current_token_owns fn t v ==>
    current_token_owns fn (current_chain_token fn ins v path t) v
Proof
  Induct >> simp[current_chain_token_def] >> rpt strip_tac >>
  first_x_assum irule >> irule current_block_token_owns >> simp[]
QED

Theorem current_inherited_token_owns:
  current_token_owns fn (current_inherited_token fn ins v path) v
Proof
  simp[current_inherited_token_def] >> irule current_chain_token_owns >>
  simp[current_token_owns_def]
QED

Theorem current_token_owner_unique:
  current_token_owns fn token v /\ current_token_owns fn token w ==> v = w
Proof
  Cases_on `token` >> simp[current_token_owns_def] >> metis_tac[optionTheory.SOME_11]
QED

Theorem current_block_token_definition_nondefault:
  lookup_block l fn.fn_blocks = SOME bb /\
  (?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) ==>
  (!w. current_block_token fn ins v l t <> CurrentDefault w) /\
  current_token_owns fn (current_block_token fn ins v l t) v
Proof
  strip_tac >>
  `?i j. i < LENGTH bb.bb_instructions /\
    j < LENGTH (EL i bb.bb_instructions).inst_outputs /\
    EL j (EL i bb.bb_instructions).inst_outputs = v /\
    current_block_token fn ins v l t = CurrentOriginal l i j` by
    metis_tac[current_block_token_original] >>
  simp[current_token_owns_def] >> metis_tac[]
QED

Theorem current_original_scan_repeated_provenance_probe:
  current_original_scan "x" "b" 4
    [mk_inst 0 ASSIGN [] ["x"; "x"]; mk_inst 1 ASSIGN [] ["x"]]
    (CurrentInserted "x" "b") = CurrentOriginal "b" 5 0
Proof
  EVAL_TAC
QED
