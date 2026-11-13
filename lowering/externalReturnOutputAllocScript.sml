(* Task-owned output allocation probe: the read window is an actual extent. *)
Theory externalReturnOutputAlloc
Ancestors
  externalReturnCopyAlloc externalReturnWindowDispatch exprSimAlloc
  abiEncoderWindow exprLoweringProps localPtrsProps loweringPosts
  allocaSiteResource compileEnv fragExec venomState venomInst venomMemDefs valueEncoding words

Theorem return_output_alloc_window:
  compile_alloc_buffer msz st = (buf,mid) /\ fn_has_code st mid func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ msz < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  (0 < cap ==>
    (?aid b len. aid < st.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      b <= sb /\ sb + cap <= b + len) \/
    (?name b len. local_region cenv es.scopes s name b len /\
      b <= sb /\ sb + cap <= b + len)) ==>
  ?u w.
    frag_exec ctx st mid (\z. z = s) (\z. z = u) (\r. F) /\
    stmt_state_rel ctx func cenv cx es u /\
    eval_operand src u = SOME (n2w sb) /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (w2n w,msz) /\
    w2n w + msz < dimword (:256) /\
    abi_encoder_window_input ei at av sb cap u.vs_memory /\
    (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (w2n w,msz)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at mid p)
Proof
  strip_tac >> drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `\r. F` strip_assume_tac) >>
  `0 < cap ==> sb + cap <= w2n w \/ w2n w + msz <= sb` by
    (strip_tac >> irule return_alloc_source_separation >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`cenv`, `es`, `s`, `st`, `u`] >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`u`, `w`] >>
  fs[venomMemDefsTheory.regions_disjoint_def]
QED

Theorem return_output_registered_scratch:
  stmt_state_rel ctx func cenv cx es s /\
  FLOOKUP s.vs_allocas output_id = SOME (d,msz) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_id <> output_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  len <= msz ==>
  sz = 32 /\ venomMemDefs$regions_disjoint (d,len) (b,sz)
Proof
  strip_tac >>
  `alloca_inv s /\ sz = 32` by
    (fs[stmt_state_rel_def] >>
     qpat_x_assum `!inst n base sz. _` drule_all >>
     simp[dimword_def, fcpTheory.index_bit0, fcpTheory.index_one,
          fcpTheory.finite_bit0, fcpTheory.finite_one]) >>
  `venomMemDefs$regions_disjoint (d,msz) (b,sz)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Applicability ledger for the next allocation/encoder continuation.

   Compiler call site: stmtLowering.compile_external_return_def, complex arm:
     compile_alloc_buffer msz st = (buf,mid);
     compile_abi_encode_to_buf buf.buf_operand src ei mid = (out,en);
     emit_inst RETURN [buf.buf_operand;out] [] en.
   Optional nonreentrant unlock precedes st, not the encoder.

   Checked here:
   - return_output_alloc_window executes the actual output allocation, even
     on reuse, with unchanged input memory and unchanged actual src value.
     It gives the registered output extent msz, positive-capacity source
     separation from that extent, and preservation of prior registrations.
     cap=0 has no owner or sb bound. alloc_buffer_source_frag is its producer.
   - return_output_registered_scratch obtains size32 from stmt_state_rel's
     literal-size invariant, and output/scratch separation from alloca_inv
     for a different registered scratch id. It shrinks msz to actual enc len.
   - abi_encoder_window_input_mem_agree transports equal readable bytes
     (abiEncoderWindowScript.sml:145); output allocation is stronger, keeping
     the entire memory equal, so no capacity expansion is needed.

   Premise/provider table for return_window_run after allocation:
   * input window / src eval: return_output_alloc_window.
   * dst eval / registered output: return_output_alloc_window, d=w2n w.
   * alloca_inv / alloca_room: preserved stmt_state_rel, unfold only at
     this resource boundary. Output bound follows registered_below and
     LENGTH(enc at av)<=msz. The latter remains a caller premise.
   * old src freshness / new dst freshness: counter monotonicity and the
     allocated buffer's reserved Var witness.
   * source frontier for cap>0: actual-footprint ownership/frontier fact
     supplied before allocation; preservation/monotonicity must be assembled.
   * source/output separation: checked above, shrink msz to encoded len.
   * scratch size32 / output separation: checked above once each scratch
     ALLOCA has literal32, code membership, and id<>output_id.
   * source/scratch separation for cap>0: registered owner must differ
     from each scratch site; borrowed local_region alternative uses
     local_backed disjointness. Ownerless cap0 requires neither.
   * code/distinctness: fn_has_code for arbitrary func must be split along
     st/mid/en/RETURN using compiler monotonicity; no selected-func identity.
   * PC/nonhalt: supplied by fragment entry and allocation execution, not
     by the pure resource facts in this file.

   Remaining explicit integration gaps (not certified by this probe):
   compiler-wide encoder scratch literal32 classification and id ranges;
   source owner/site distinctness or borrowed separation at the actual call
   site; enc length<=ce_max_return_size and msz<dimword package providers;
   post-allocation PC witness compatible with run_from; frame the RETURN
   buffer operand through encoder execution and compose RETURN/result_rel.

   Proposed next execution interface, not an admitted theorem:
   given the two compile equations above, admissible/window input, source
   eval/freshness, stmt_state_rel/local_ptrs_reserved, conditional actual
   ownership/frontier, encoded length<=msz<dimword, code/distinctness,
   scratch literal32 and owner/local separation facts, and entry PC,
   execute allocation then return_window_run to obtain an encoder endpoint
   with abi_encoder_window_result, dst evaluation and the encoded bytes.
   Only then append RETURN and project external_call_result_rel; counted
   composition is a separate later obligation.
*)
