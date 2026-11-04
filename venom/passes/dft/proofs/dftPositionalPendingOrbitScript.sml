Theory dftPositionalPendingOrbit
Ancestors
  dftCofinalSegments dftPositionalPendingClosure dftPositionalPendingGas
  dftOccurrenceMachine dftPositionalRuntime dftOriginalRuntime
  dftPositionalEdit venomInst list arithmetic

Theorem dft_pending_cofinal_segments:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\ ~MEM v call.inst_outputs /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r ==>
  ?A B Z. A 0 = 0 /\ B 0 = 0 /\ Z 0 = (zs,H) /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. dft_pos_pending_aligned_phase w C D fi bi pre gas call post
      (FST (Z n)) (SND (Z n))
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r)) /\
    (!n. pending_segment_account C D w
      (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r)
      (dft_pos_pending_gas_events (FST (Z n)) ++ SND (Z n))
      (dft_pos_pending_gas_events (FST (Z (SUC n))) ++ SND (Z (SUC n))))
Proof
  strip_tac >>
  qspecl_then
    [`\z l r. dft_pos_pending_aligned_phase w C D fi bi pre gas call post (FST z) (SND z) l r`,
     `\z z' a b l r. pending_segment_account C D w a b l r
       (dft_pos_pending_gas_events (FST z) ++ SND z)
       (dft_pos_pending_gas_events (FST z') ++ SND z')`]
    (irule o SRULE []) (Q.GENL [`P`,`account`] dft_annotated_cofinal_segments) >> simp[] >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `dft_pos_pending_aligned_phase _ _ _ _ _ _ _ _ _ _ _ _ _`) dft_pending_bounded_closed >>
  simp[] >> disch_then (qspecl_then [`Dorig`,`Corig`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl [`a`,`b`,`(zs',H')`] >> simp[]
QED
