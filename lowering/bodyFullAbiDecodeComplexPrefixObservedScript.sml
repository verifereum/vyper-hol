Theory bodyFullAbiDecodeComplexPrefixObserved
Ancestors
  bodyFullAbiDecodeComplexPrefixSlice
Libs
  bodyFullAbiDecodeComplexPrefixSyntaxLib

Theorem abi_decode_complex_prefix_observed:
  !finish.
  (^guarded_to_buf_entry) dst src opc base_op hi (DecComplex dyn infos)
    env sf ty tv live protected start finish s G tn d ==>
  (?t Gf tnf. (!H. V H ==> gas_origin_ptr_path
    (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
    (!obs. fn_has_code start finish obs ==> gas_path ctx obs s 0 (Abort Revert_abort t))) \/
  (?env' sf' tys tvs e sm sb t Gf tnf.
    infos = abi_decoder_member_infos sf' ce tys /\
    type_memory_size tv = SUM (MAP (type_memory_bytes ce) tys) /\
    emit_op ADD [src;Lit (n2w (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)))]
      start = (e,sm) /\
    compile_abi_decode_range_check src e hi sm = ((),sb) /\
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!x. not_fresh_at start x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (^empty_member_entry) dst src opc base_op hi infos env' sf' tys tvs live protected
      sb finish t Gf tnf d /\
    (!obs. fn_has_code start sb obs ==> gas_path ctx obs s 0 (OK t)) /\
    tnf.t_mem = tn.t_mem /\ t.vs_allocas = s.vs_allocas)
Proof
  BETA_TAC >> gen_tac >>
  disch_then (mp_tac o MATCH_MP
    (SPEC_ALL (BETA_RULE abi_decode_complex_prefix_observed_slice))) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu` strip_assume_tac)))
    (fn th => disj2_tac >> ACCEPT_TAC th)) >>
  disj1_tac >> qexistsl_tac [`u`, `Gu`, `tnu`] >> asm_rewrite_tac[]
QED
