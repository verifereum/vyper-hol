Theory bodyPtrPrecompileBuiltinsPayloadNormalize
Ancestors dftCommutation venomState abiDecodeStaticProps

(* Arbitrary replacement, not just restoring the incoming memory. *)
Theorem mstore_memory_overwrite:
  (mstore a w s with vs_memory := m) = (s with vs_memory := m)
Proof
  once_rewrite_tac[mstore_with_memory] >> simp[]
QED

Theorem mstore_vars_memory_overwrite:
  (mstore a w s with <|vs_memory := m; vs_vars := v|>) =
  (s with <|vs_memory := m; vs_vars := v|>)
Proof
  once_rewrite_tac[mstore_with_memory] >> simp[]
QED

Theorem four_store_normalization_probe[local]:
  (mstore (b+96) ws (update_var z zs
    (mstore (b+64) wr (update_var y ys
      (mstore (b+32) wv (update_var x xs (mstore b wh s))))))).vs_memory =
  (mstore (b+96) ws (mstore (b+64) wr
    (mstore (b+32) wv (mstore b wh s)))).vs_memory /\
  (mstore (b+96) ws (update_var z zs
    (mstore (b+64) wr (update_var y ys
      (mstore (b+32) wv (update_var x xs (mstore b wh s))))))
    with <|vs_vars := s.vs_vars; vs_memory := m|>) =
  (s with vs_memory := m)
Proof
  pure_rewrite_tac[GSYM update_var_mstore_commute] >>
  conj_tac >- simp[update_var_def] >>
  simp[update_var_def, mstore_memory_overwrite, mstore_vars_memory_overwrite]
QED
