(* This probe concerns an intermediate load, not a source expression frame. *)
Theory bodyPtrMakeArrayCoverageProbe
Ancestors
  bodyPtrMakeArrayCopyStep bodyPtrDefs compileEnv exprLowering venomState
  venomInst finite_map vyperAST

Theorem ptr_buf_ok_missing_provenance:
  type_memory_bytes cenv (lowered_value_type cenv e) <> 0 /\
  eval_operand (Var tmp) s = SOME w /\ FLOOKUP G tmp = NONE ==>
  ~ptr_buf_ok cenv e (Var tmp) G s
Proof
  rw[ptr_buf_ok_def] >> metis_tac[]
QED

Theorem external_load_no_buffer_coverage:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  eval_operand src s = SOME a /\
  type_memory_bytes cenv (lowered_value_type cenv e) <> 0 ==>
  ~ptr_buf_ok cenv e (Var tmp)
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all external_load_output_ghost >> strip_tac >>
  irule ptr_buf_ok_missing_provenance >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem uint256_buffer_size_probe:
  type_memory_bytes cenv
    (lowered_value_type cenv (Literal (BaseT (UintT 256)) (IntL 0))) = 32
Proof
  simp[lowered_value_type_def, expr_type_def, type_memory_bytes_def]
QED
