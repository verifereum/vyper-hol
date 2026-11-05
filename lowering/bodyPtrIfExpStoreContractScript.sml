Theory bodyPtrIfExpStoreContract
Ancestors
  bodyPtrDefs representationCleanPtr valueCopyBytes bodyPtrIfExpBytesPost
  context compileEnv venomExecSemantics venomState typedCopyAgreement
  stmtAbortPtr emitHelper

(* Unlike ptr_val_ok_read_covers, this boundary permits reading the
   word-padded val_store_size, not just the semantic footprint. It does
   not claim capacity for a whole type-sized buffer. *)
Theorem ptr_val_ok_store_read_covers:
  !cx ty v op G tn s tv w n.
    ptr_val_ok cx ty v op G tn s /\ ~is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\ val_footprint tv v <> 0 /\
    n <= val_store_size tv v ==>
    ?p. op = Var p /\ ptr_covers G tn p s n
Proof
  rpt strip_tac >> fs[ptr_val_ok_def, ptr_mem_ok_def] >>
  gvs[] >> simp[ptr_covers_def] >>
  qexists_tac `w` >> gvs[eval_operand_def] >> decide_tac
QED

Theorem store_memory_typed_invalid_counted:
  !D ctx fn PG cenv dst dty src sty sa sb s G tn a t.
    ~is_word_type dty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
    ~acyclic_struct_metadata cenv.ce_struct_fields /\
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    step_inst_base (mk_inst sa.cs_next_id INVALID [] []) s = Abort a t ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (Abort a t)
Proof
  rpt strip_tac >>
  `emit_void INVALID [] sa = ((),sb)` by
    metis_tac[compile_store_memory_typed_invalid] >>
  irule emit_abort_zero_path_ptr >> simp[] >>
  qexistsl_tac [`INVALID`, `[]`, `sa`, `sb`] >> gvs[emit_void_def, emit_inst_def] >>
  irule ptr_inst_ok_abort_zero >> simp[]
QED

(* BASE STORE CONTRACT AUDIT. No full store theorem is admitted here.

   The outer dispatch is contextScript.sml:835-842, distinct from the
   typed dispatch at :671-696. Reuse typedCopyAgreement's word/bytes/invalid
   equations and valueCopyBytes' bytestring source-independence theorem.

   Outer word MSTORE writes the value operand directly; it does NOT load
   it first. It is excluded by the allocating-arm guard ~is_word_type rt.
   Typed word MLOAD/MSTORE remains reachable recursively on child types;
   it is not excluded merely because the root destination is non-word.
   Outer bytes always copies runtime length, ignoring the source type.
   Outer equal-type copies type_memory_bytes rt. The differing-layout
   allocating guard alone needs a punnable reflexivity fact to exclude
   this branch; no such exclusion is claimed by this audit.
   Typed bytes requires both byte tags, then uses the same runtime copy.
   Typed INVALID precedes aggregate/fallback dispatch, after word/bytes.
   Typed fallback copies destination type_memory_bytes, regardless of
   the source's type/size. Its source coverage must be checked explicitly.

   Counted bytes contract: use the existing exact theorem
   compile_store_bytestring_robust_gas_path_ptr in BytesPost, :68-106.
   Its output is a gas_path_ptr with gas count 0 to the index-advanced
   sf, robust destination at dtv, per-byte copied/exterior taint equations,
   sc-old register/provenance preservation and robust exterior framing.
   It does not itself package ghost_inv or original-sa ghost_kept.

   Bytes premise derivation at the intended unwrap endpoint:
   - choose sty=dty=the arm annotation in BytesPost when using the outer
     bytes branch. The compiler ignores its physical src_ty tag here, so
     no robust source-layout reinterpretation is necessary for this case.
   - ptr_val_ok at that annotation supplies robust val_in_memory through
     ptr_mem_ok; typed validity/value_has_type is still needed from the
     selected-arm typing, and evaluate_type must be successful.
   - bytestring_type_value plus value_has_type identifies BytesV/StringV
     and bounds len by capacity. robust_bytestring_header then gives the
     clean length word and its machine encoding without an extra input.
   - source coverage for n=32+32*((len+31) DIV 32) comes from the checked
     ptr_val_ok_store_read_covers, val_store_size's bytes/string equations,
     and val_footprint<>0. The older read-covers theorem only promises up
     to val_footprint and is insufficient for padding. This is NOT a
     whole-type-buffer claim.
   - destination coverage is allocation coverage, transported through
     unwrap, restricted to n by runtime length<=destination capacity.
   - source/destination Var forms, defined operand values and oldness at
     the store cutoff are needed. Destination out oldness is at sc, not sa.
   - fn_has_code + current control position must supply the instruction
     prefix and block lookup. Actual precondition supplies no dalloca.
   - ghost_inv/original ghost_kept need destination disjointness from old
     allocations/live locals and the robust exterior-frame conclusion.
     Those framing consumers are not established by this diagnostic.

   Proposed fixed-copy counted robust contract (both equal-type outer and
   typed fallback; n is destination type_memory_bytes):

   compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
   lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
   n < dimword(:256) /\
   ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
   val_wf tv v /\ val_footprint tv v <= n /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory tv v (w2n a) m) /\
   ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb)
     (DROP s.vs_inst_idx bb.bb_instructions) ==>
   ?Gf tnf sf.
     gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
       (OK (sf with vs_inst_idx :=
         s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
     Gf = G /\ tnf.t_var = tn.t_var /\
     tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
     (!p. lookup_var p sf = lookup_var p s) /\
     mem_bytes_at (w2n b) n sf.vs_memory =
       mem_bytes_at (w2n a) n s.vs_memory /\
     (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
     (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
       mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
       (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
     (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
       val_in_memory tv v (w2n b) m)

   Existing compile_copy_memory_robust_frag_ptr has these resource/effect
   facts, but fixed-run execution only. Rebuild its MCOPY/no-op path with
   fragGasSeqPtr; do not assert that its execution is a counted one.
   Destination tv interpretation at source is an explicit premise here:
   at equal types it comes from the semantic annotation only if those
   types align, while fallback needs a caller-derived layout-transfer or
   reachability theorem. ptr_buf_ok only provides source lowered-size
   coverage, so n<=that size must also be proved (not added to the task).

   Typed word proposed primitive contract: emit MLOAD then MSTORE at
   source/destination covered 32-byte windows, clean source 32 bytes,
   untainted addresses and defined operands, old variables, code prefix
   and nonhalt/no-dalloca. Return a zero-gas counted path, unchanged
   machine/provenance values of old registers, unchanged stor/trans taint,
   destination word equal to source mload and clean destination 32 bytes,
   exterior memory/taint unchanged. typedCopyPtr's mload_frag_ptr and
   mload_then_mstore_ok supply primitive checks; wordCopyRobustPtr gives
   fixed-run framing. A counted composer and robust child-annotation
   encoding/cleanliness premise derivation are still required.

   INVALID exceptional contract: store_memory_typed_invalid_counted above
   preserves G/tn at the abort endpoint; step_invalid supplies a,t. There
   is no robust normal destination post. To integrate a normal source
   evaluation this branch must be excluded by actual acyclic metadata,
   or its abort must match the source exception. A raw pointer-safe abort
   alone does not satisfy expr_exit of a successful source evaluation.
*)
