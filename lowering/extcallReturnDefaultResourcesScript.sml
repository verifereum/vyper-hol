(* Resource transport across the fresh-variable default-return control shell. *)
Theory extcallReturnDefaultResources
Ancestors
  extcallReturnDefaultRouting extcallReturnEntryBridge abiReturnPrefixTransport
  abiMalformedRecursiveInterface abiDecoderReentry exprLoweringProps
  exprSafeOperand compileEnv venomState finite_map list

Theorem return_default_ready_transport:
  abi_return_decode_ready ctx func ce cx ee a sites dstid live base_op dst
    B cap bs d n s /\ a.cs_next_var <= b.cs_next_var /\
  stmt_state_rel ctx func ce cx ee t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  (!op w. abi_decoder_operand_live a.cs_next_var op /\
     eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  abi_return_decode_ready ctx func ce cx ee b sites dstid live base_op dst
    B cap bs d n t
Proof
  strip_tac >> fs[abi_return_decode_ready_def] >>
  `local_ptrs_reserved ce b` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand base_op t = SOME (n2w B) /\
   eval_operand dst t = SOME (n2w d)` by metis_tac[] >>
  simp[abi_return_decode_ready_def] >> rpt conj_tac
  >- fs[abi_malformed_allocated_window_def]
  >- (fs[abi_malformed_destination_def] >> metis_tac[]) >>
  metis_tac[abi_decoder_operand_live_mono]
QED
