Theory bodyFullAbiDecodeDecoderBase
Ancestors
  bodyFullAbiDecodePath bodyFullAllocGeneric abiDecodePtrMemberFrame
  abiDecoderSingletonSetup fragGasOriginPtr compileEnv

(* The empty member traversal has one endpoint, before the horizon is chosen.
   F carries any additional ownership/scratch frame needed by its caller. *)
Theorem abi_decode_complex_nil_joint:
  compile_abi_decode_complex_elems dst src MLOAD base_op hi [] ao vo sa =
    ((),sb) /\
  ~s.vs_halted /\
  abi_decode_ptr_window G tn s input b n /\
  ptr_covers G tn output s m /\
  (!H. V H ==>
    stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at D lo d ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn /\
    Frame H sa s G tn) ==>
  ?t G' tn'.
    sb = sa /\ t = s /\ G' = G /\ tn' = tn /\
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn') /\
    abi_decode_ptr_window G' tn' t input b n /\
    ptr_covers G' tn' output t m /\
    (!H. V H ==>
      stmt_state_rel H ctx fn ce cx es t /\
      ghost_inv_at D lo d ce cx es G' tn' t /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tn' /\
      Frame H sb t G' tn')
Proof
  simp[abi_decode_complex_nil, comp_return_def] >>
  strip_tac >> gvs[] >> conj_tac
  >- (irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  metis_tac[]
QED
