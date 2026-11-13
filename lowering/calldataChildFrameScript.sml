(* Conditional physical separation for an allocating decoder child.
   The execution theorem must supply the footprint and outside-site map frame. *)
Theory calldataChildFrame
Ancestors
  valueEncodingDefs actualAllocExec abiDecoderFrame valueEncodingProps valueEncoding
  venomMemDefs venomState finite_map arithmetic list words

Theorem calldata_child_preserves_allocated_region:
  abi_decode_footprint_frame ((d,sz)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (protected_id < lo \/ hi <= protected_id) /\
  FLOOKUP s.vs_allocas protected_id = SOME (alloc_base,cap) /\
  alloc_base <= p /\ p+n <= alloc_base+cap /\
  (p+n <= d \/ d+sz <= p) /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) ==>
  FLOOKUP t.vs_allocas protected_id = SOME (alloc_base,cap) /\
  mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory /\
  t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> (
  `FLOOKUP t.vs_allocas protected_id = SOME (alloc_base,cap)` by metis_tac[] >>
  simp[] >> conj_tac
  >- (irule abi_decode_footprint_frame_slice >>
      goal_assum (drule_at Any) >>
      simp[abi_footprint_disjoint_def] >> rpt strip_tac >> gvs[] >>
      qpat_x_assum `!q len. MEM (q,len) scratch ==> _` drule >> strip_tac >>
      `id <> protected_id` by decide_tac >>
      qpat_x_assum `alloca_inv t` mp_tac >>
      pure_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def] >>
      strip_tac >>
      first_x_assum (qspecl_then
        [`protected_id`, `id`, `alloc_base`, `cap`, `d'`, `sz'`] mp_tac) >>
      impl_tac >- metis_tac[] >> decide_tac) >>
  fs[abi_decode_footprint_frame_def])
QED

(* The private counter is a whole, outside-child allocation. *)
Theorem calldata_child_preserves_counter:
  abi_decode_footprint_frame ((d,sz)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (counter_id < lo \/ hi <= counter_id) /\
  FLOOKUP s.vs_allocas counter_id = SOME (counter,32) /\
  (counter+32 <= d \/ d+sz <= counter) /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) ==>
  FLOOKUP t.vs_allocas counter_id = SOME (counter,32) /\
  mload counter t = mload counter s /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> (
  `FLOOKUP t.vs_allocas counter_id = SOME (counter,32) /\
   mem_bytes_at counter 32 t.vs_memory = mem_bytes_at counter 32 s.vs_memory /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (irule calldata_child_preserves_allocated_region >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  gvs[mem_bytes_at_def, mload_def])
QED

(* Earlier elements and the length word form a protected prefix of the
   same output allocation; only the next element is a permitted write. *)
Theorem calldata_child_preserves_output_prefix:
  abi_decode_footprint_frame
    ((dst+32+j*stride,stride)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (output_id < lo \/ hi <= output_id) /\
  FLOOKUP s.vs_allocas output_id = SOME (dst,cap) /\
  32+j*stride <= cap /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) ==>
  mem_bytes_at dst (32+j*stride) t.vs_memory =
    mem_bytes_at dst (32+j*stride) s.vs_memory
Proof
  strip_tac >> (
  irule (cj 2 calldata_child_preserves_allocated_region) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >>
  qexistsl_tac [`dst`, `cap`, `dst+32+j*stride`, `output_id`, `stride`] >>
  simp[] >> metis_tac[])
QED
