(* Full scalar normalization frames.  Padding outside the runtime bytes
   copy is deliberately not asserted clean. *)
Theory extRetNormalizeEndpointPtr
Ancestors
  extRetNormalizeBytesChildPtr extRetNormalizeWordPtr
  assignTuplePtrLocalCompat typedCopyAgreement typedCopyPtr
  bodyPtrMakeArrayWordStore bodyPtrMakeArrayMloadFrame
  bodyPtrMakeArrayMemoryWord exprSimProps bodyPtrDefs
  wordLoadStorePtr fragGasSeqPtr fragGasPathPtr fragExec compileEnv
  venomState venomExecSemantics venomInst ptrDiscipline
  valueEncoding valueEncodingDefs valueEncodingProps vyperTyping
  finite_map list arithmetic

Theorem normalize_typed_bytes_endpoint_ptr:
  compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory stv v (w2n a) m) /\
  ptr_covers G tn src s (val_store_size stv v) /\
  ptr_covers G tn dst s (type_memory_size dtv) /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  n = 32 + 32 * ((len+31) DIV 32) /\
  len+31 < dimword(:256) /\ n < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory dtv v (w2n b) m) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+type_memory_size dtv) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_current_bb := s.vs_current_bb;
               vs_prev_bb := s.vs_prev_bb;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!ft fv p. val_wf ft fv /\
      (!i. p <= i /\ i < p + val_footprint ft fv ==>
        ~(w2n b <= i /\ i < w2n b+type_memory_size dtv)) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ft fv p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ft fv p m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory ce (Var src) (Var dst) dty sty =
   compile_store_bytestring (Var src) (Var dst)` by
    (irule compile_store_memory_bytestring_compat_ptr >> simp[]) >>
  `compile_store_memory_typed ce (Var dst) dty (Var src) sty =
   compile_store_memory ce (Var src) (Var dst) dty sty` by
    simp[compile_store_memory_typed_bytes] >>
  `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by metis_tac[] >>
  drule_all normalize_bytes_child_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _;
    vs_inst_idx := _|>) = s` mp_tac >>
  simp[venom_state_component_equality]
QED

(* Unequal capacities change the slot stride, not the copied runtime size. *)
Theorem normalize_unequal_string_slots_probe_ptr:
  value_has_type (BaseTV (StringT 1)) (StringV "a") /\
  value_has_type (BaseTV (StringT 33)) (StringV "a") /\
  val_store_size (BaseTV (StringT 1)) (StringV "a") = 64 /\
  val_store_size (BaseTV (StringT 33)) (StringV "a") = 64 /\
  type_memory_size (BaseTV (StringT 1)) = 64 /\
  type_memory_size (BaseTV (StringT 33)) = 96
Proof
  EVAL_TAC
QED

(* The scalar endpoint uses a common evaluated type.  This is not an
   extra restriction on a widening call: compileEnv$type_widens_to_word
   proves type_widens_to tenv sty dty /\ is_word_type dty ==> sty = dty.
   Thus both evaluate_type premises are provided by the same caller fact.
   Addresses and fixed bytes words are covered by val_in_memory_word too;
   they need not satisfy loweringSlice$word_value. *)
Theorem normalize_typed_word_endpoint_ptr:
  is_word_type sty /\ is_word_type dty /\
  evaluate_type (get_tenv cx) sty = SOME tv /\
  evaluate_type (get_tenv cx) dty = SOME tv /\ value_has_type tv v /\
  compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
  not_fresh_at sa dst /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_mem_ok cx sty v (Var src) G tn s ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_current_bb := s.vs_current_bb;
               vs_prev_bb := s.vs_prev_bb;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!ft fv p. val_wf ft fv /\
      (!i. p <= i /\ i < p + val_footprint ft fv ==>
        ~(w2n b <= i /\ i < w2n b+32)) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ft fv p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ft fv p m)
Proof
  strip_tac >> drule_all typedCopyPtrTheory.compile_store_word_code >> strip_tac >>
  `tmp <> dst` by metis_tac[] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id MLOAD [Var src] [tmp];
     mk_inst (id+1) MSTORE [Var dst; Var tmp] []]` by simp[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MLOAD [Var src] [tmp])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all memory_word_materialize_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  `get_instruction bb s1.vs_inst_idx =
    SOME (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])` by
    (qpat_x_assum `!i. _` (qspec_then `1` mp_tac) >> simp[ADD1]) >>
  `ptr_covers G1 tn1 dst s1 32 /\ lookup_var dst s1 = SOME b /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\ ~s1.vs_halted` by
    (simp[update_var_def] >> metis_tac[]) >>
  drule_all make_array_word_store_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 Gf tnf (OK sf)` >>
  `sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted` by
    simp[mstore_def, update_var_def, ADD1] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  conj_tac >- metis_tac[gas_path_ptr_then, ADD] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (drule_all exprSimPropsTheory.val_in_memory_word >>
      disch_then (fn th => rewrite_tac[th]) >>
      rpt strip_tac >> first_x_assum irule >> gvs[mstore_def, update_var_def]) >>
  conj_tac
  >- (rpt strip_tac >> `p <> tmp` by metis_tac[] >>
      qpat_x_assum `!x. x <> tmp ==> _` (qspec_then `p` mp_tac) >>
      simp[lookup_var_def, FLOOKUP_UPDATE, op_taint_def, mstore_def, update_var_def]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[mem_agree_outside_def] >> metis_tac[]) >>
  conj_tac >- simp[venom_state_component_equality, mstore_def, update_var_def] >>
  rpt strip_tac >>
  qpat_x_assum `!ty v p. val_wf ty v /\ _ ==> _` irule >>
  simp[] >> gvs[mstore_def, update_var_def]
QED

(* RECURSIVE-CONTRACT VALIDATION / PRODUCER JOIN (C2.2.4.1)

   Both endpoints export the normal-child result proposed in
   extRetNormalizeContractAuditPtr: actual sb cursor; destination robust
   value; old-register value/provenance/taint; exterior memory/taint;
   stor/trans/imm; full non-PC, non-vars, non-memory state; universal
   disjoint robust-value frame.  Neither conclusion fixes sb's block.
   Neither claims all destination capacity bytes are clean.  No ghost_inv
   is asserted: its restoration is a consumer obligation, not an endpoint
   premise hidden by these results.

   Zero-read regression uses existing proved facts, not duplicate lemmas:
   abiArgsLabelBoundary$abi_args_empty_tuple_footprint gives footprint 0,
   val_wf and val_in_memory at EVERY address in EVERY memory for TupleTV [].
   bodyPtrMakeArrayZeroWidth$literal_empty_tuple_layout gives size/stride 0
   and an identity untyped store.  Therefore R(empty,v,a,tn,s) places no
   constraint on tn or on a.  A recursive contract must not demand a
   positive source window, allocation or strict live-read bound here.
   extRetNormalizeAddressesPtr$normalize_array_addresses_execution_counted_ptr
   is the address-only interface; the coverage-enhanced version's strict
   offset < capacity premises are inappropriate for a zero slot.  These
   facts do NOT assert that every typed empty store is a no-op: the typed
   dispatcher checks cyclic metadata and can emit INVALID even on tuples.
   The general normalizer must retain its counted abort alternative.

   Root join, to be produced by C2.2.6 rather than assumed by a wrapper:
   * Source evaluated type, value typing and robust memory come from the
     expression post at post_value_type, rewritten by the equal-lowered
     post-type boundary.  ptr_mem_ok for the scalar load must be reattached
     from ptr_val_ok; R alone is insufficient.  Bytes consumes R plus the
     padded live source window, not its declared capacity window.
   * Word compatibility is compileEnv$type_widens_to_word (sty = dty).
     Bytes compatibility is the mandated assignTuplePtrLocalCompat theorem,
     used above, plus compile_store_memory_typed_bytes.  Destination value
     typing at the wider bytes bound is a separate caller typing fact.
   * compile_alloc_buffer_state_counted_ptr supplies the fresh destination
     coverage/capacity.  The root producer must also discharge fresh-vars,
     code-site distinctness, not_local_ptr and strict allocation bounds;
     pointer coverage alone supplies no concrete no-wrap bound.
   * Source/destination separation, metadata/field layout consistency,
     actual live-read bounds, and restoration of ghost_inv/allocation
     resources remain root/recursive joins.  The endpoints preserve the
     allocation/frontier/request fields and t_imm exactly, enabling those
     joins without claiming to construct the missing resources.
   * A recursive child may change blocks.  Its returned cursor feeds the
     actual loop tail; old counters and parent pointers are protected only
     when not_fresh_at its input state.  The tail intentionally changes the
     counter, so it cannot reuse an ALL-old-register frame verbatim.

   The String[1] -> String[33] probe above validates the unequal-stride
   distinction: runtime store size 64, destination capacity 96.  Retained
   taint in the last 32 bytes is legal; encoder cleanliness is a later
   semantic-prefix result, never a consequence of this normalization.
*)
