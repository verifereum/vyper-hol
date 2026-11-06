(* Allocation frontier and the full returned string region. *)
Theory bodyMemBiUint2StrBounds
Ancestors
  exprSimUint2Str exprLoweringProps venomMemDefs arithmetic

Theorem u2s_safe_result_region:
  u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s ==>
  b+n-d+sz <= s.vs_alloca_next
Proof
  strip_tac >>
  `b + (sz+n) <= s.vs_alloca_next` by
    (fs[u2s_safe_def, stmt_state_rel_def, alloca_inv_def,
        alloca_next_valid_def] >> metis_tac[]) >>
  decide_tac
QED
