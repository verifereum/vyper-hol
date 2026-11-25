(* Normal continuation adapter for a completed ABI-word child and its packed endpoint. *)
Theory bodyFullAbiEncodeWordContinuation
Ancestors
  bodyFullAbiEncodeWordFull bodyFullAbiEncodeWordPackData
  bodyFullEmptyLeafData gasOutcomeFullCompose
  bodySimFull exprSimSource exprSimHyps exprLoweringProps
  gasExemptCert vyperStorageTrace vyperStorageFootprint
  compileEnv vyperContext vyperAST venomState list

Theorem abi_encode_word_normal_continuation:
  ~t.vs_halted /\
  (!tail. N v (ee with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,func,PG)
      (t,G1,tn1) [] (OK packed,Gp,tnp) /\
    Q H res (ee with gas_obs := []) Gp tnp packed) ==>
  gas_outcome_full (DF,lo,E,ctx,func,PG) tops cx st0 (N v)
    (ee,t,G1,tn1)
    Q R
Proof
  strip_tac >> irule gas_outcome_full_pure >>
  (metis_tac[])
QED
