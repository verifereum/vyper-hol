Theory exprSimAbiDecodeImmutableProbe
Ancestors
  abiDecoderSiteEffect abiDecoderFrame exprSimAbiDecodeEndpointFrame
  abiDecoderVarExtend abiEncoderObserver finite_map compileEnv
  venomExecSemantics venomState valueEncodingProps valueEncoding rich_list list arithmetic

(* Both fresh and reused actual ALLOCA rows are safe.  No condition on
   unrelated allocation-map rows is needed for this one write. *)
Theorem abi_decode_actual_site_write_frame:
  inst.inst_outputs = [out] /\ exec_alloca inst s (n:bytes32) = OK t /\
  q + len <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n n /\ venomMemDefs$regions_disjoint (q,len) (b,sz)) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,w2n n) /\
  b <= dst /\ dst + LENGTH bs <= b + w2n n ==>
  mem_bytes_at q len (write_memory_with_expansion dst bs t).vs_memory =
    mem_bytes_at q len s.vs_memory
Proof
  strip_tac >>
  drule_all decode_site_protected_allocation >> strip_tac >>
  `t.vs_memory = s.vs_memory` by
    metis_tac[venomMemPropsTheory.exec_alloca_preserves_memory] >>
  `mem_bytes_at q len (write_memory_with_expansion dst bs t).vs_memory =
    mem_bytes_at q len t.vs_memory` by
    (Cases_on `len = 0` >- simp[mem_bytes_at_def] >>
     Cases_on `bs = []`
     >- (simp[write_memory_with_expansion_def, TAKE_DROP] >>
         IF_CASES_TAC >> simp[valueEncodingProofsTheory.mem_bytes_at_append_zero]) >>
     irule write_memory_mem_bytes_at_disjoint >>
     fs[venomMemDefsTheory.regions_disjoint_def] >>
     gvs[] >> `0 < LENGTH bs` by metis_tac[LENGTH_NIL, NOT_ZERO_LT_ZERO] >>
     decide_tac) >>
  simp[]
QED

(* The same endpoint memory observation survives all three transports
   used by the quantified success producer. *)
Theorem abi_decode_immutable_endpoint_transport:
  stop_view u = stop_view t /\ abi_decoder_vars_extend extras u u' /\
  mem_bytes_at q len t.vs_memory = mem_bytes_at q len s.vs_memory ==>
  mem_bytes_at q len
    (u' with <|vs_returndata := rd; vs_prev_bb := prev|>).vs_memory =
    mem_bytes_at q len s.vs_memory
Proof
  strip_tac >> drule stop_view_fields >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> simp[]
QED

(* Interface audit: abi_decoder_effect / abi_builtin_decode_effect carry a
   footprint for one contiguous scratch arena.  The actual-site outcome
   instead exports an interval overapproximation containing unused rows.
   Neither interface currently supplies actual-site destination provenance
   for every write in an observer prefix.  The missing integration fact is:
   each write range is contained in the output or in a registered ALLOCA
   row (or lies above the entry frontier), with row protection maintained
   along that prefix.  The first theorem checks the local allocation/write
   step for both reuse and freshness; the second checks same-endpoint
   observer, variable-extension and rd/prev transport.  They do not prove
   the missing whole-decoder destination invariant. *)
