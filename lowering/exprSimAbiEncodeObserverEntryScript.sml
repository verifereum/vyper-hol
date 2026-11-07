Theory exprSimAbiEncodeObserverEntry
Ancestors
  exprSimAbiEncodeRelabelBoundary exprSimAbiEncodeCapacity
  exprLoweringProps loweringPosts compileEnv exprSimAbiGasBridge
  list words

Theorem abi_encode_nonword_observer_entry:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  local_ptrs_reserved ce sa ==>
  stmt_state_rel ctx func ce cx es' (s with vs_current_bb := L) /\
  local_ptrs_reserved ce (start_relabel L ids sa)
Proof
  simp[expr_post_def, abi_encode_stmt_rel_current_bb,
    abi_encode_start_relabel_resources] >> metis_tac[]
QED

Theorem abi_encode_nonword_observer_geometry:
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av ==>
  let bytes = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av in
  let m = case mid of NONE => 0 | SOME _ => 4 in
  let mw = case mid of NONE => 0 | SOME _ => 32 in
  let outsz = 32+32*word_size (abi_size_bound ce.ce_struct_fields (expr_type e)+m) in
  32+mw <= outsz /\ p <= p+32+m /\ p+32+m+LENGTH bytes <= p+outsz
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_nonword_numerical_capacity >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `mid0` >> gvs[LET_THM]
QED
