Theory makeSsaCurrentLastOutput
Ancestors
  makeSsaCurrentTokens makeSsaCurrentRuntime list arithmetic

Theorem current_output_token_last_slot:
  !outs j k t. k < LENGTH outs /\
    ~MEM (EL k outs) (DROP (SUC k) outs) ==>
    current_output_token (EL k outs) l i j outs t = CurrentOriginal l i (j + k)
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `k`
  >- (simp[current_output_token_def] >> rpt strip_tac >>
      simp[current_output_token_absent]) >>
  simp[current_output_token_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_output_token_last_position:
  MEM v outs ==>
  ?k. k < LENGTH outs /\ EL k outs = v /\ ~MEM v (DROP (SUC k) outs) /\
    current_output_token v l i 0 outs t = CurrentOriginal l i k
Proof
  strip_tac >> drule current_runtime_last_position >> strip_tac >>
  qexists_tac `k` >> simp[] >>
  mp_tac current_output_token_last_slot >>
  disch_then (qspecl_then [`outs`, `0`, `k`, `t`] mp_tac) >> simp[]
QED
