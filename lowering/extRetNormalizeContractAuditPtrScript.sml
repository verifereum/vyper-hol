(* Interface audit only. No recursive normalization theorem is asserted here. *)
Theory extRetNormalizeContractAuditPtr
Ancestors
  extRetNormalizeWordPtr extRetNormalizeBytesPtr extRetNormalizeAddressesPtr
  extRetNormalizeLiveChildPtr extRetSemanticEntryPtr
  typedCopyLoopLayoutPtr typedCopyCompatibilityPtr assignBasePtrFieldsCompose
  bodyPtrBytestringBuiltinsBuffer returnMetadataPtr extRetReturnMetadataPtr

(* C1.8.3.1: RECURSIVE CHILD CONTRACT -- PROPOSAL, NOT A DEFINITION/THEOREM

   The quantifiers below are important: a child runs from arbitrary live loop
   states, not just the first iteration; retained resources are universally
   quantified, not a chosen list of source siblings. All missing implications
   are explicitly identified below. Abbreviations are documentary only:

   R(tv,v,a,tn,s) = !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
                          val_in_memory tv v a m
   W(b,n) = {j | b <= j /\ j < b+n}.
   C(sa,s) = s.vs_current_bb = sa.cs_current_bb /\
             s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted.

   Proposed normal-child interface, universally quantified over
     ce cx tenv sty dty stv dtv v src dst sa sb fn ctx D PG G tn s a b.
   Inputs:
     compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb);
     fn_has_code sa sb fn; C(sa,s); ~ctx_has_dalloca ctx;
     not_fresh_at sa src; not_fresh_at sa dst;
     get_tenv cx = tenv; evaluate_type tenv sty = SOME stv;
     evaluate_type tenv dty = SOME dtv; type_widens_to tenv sty dty;
     value_has_type stv v; value_has_type dtv v;
     type_memory_bytes ce sty = type_memory_size stv;
     type_memory_bytes ce dty = type_memory_size dtv;
     lookup_var src s = SOME (n2w a); lookup_var dst s = SOME (n2w b);
     R(stv,v,a,tn,s).
   Resources (must be produced, not inferred from widening):
     ptr_mem_ok cx sty v (Var src) G tn s;
     positive source/destination access windows have ptr_covers;
     actual positive read addresses do not wrap;
     destination capacity covers type_memory_size dtv and has a strict end;
     W(a,val_footprint stv v) disjoint W(b,type_memory_size dtv).
   Metadata:
     field-type/size consistency, ordered source/destination field agreement,
     and the relevant layout compatibility facts. These are a separate join,
     not an extra universal acyclicity assumption on the frozen theorem.

   Desired output exists Gf tnf sf:
     gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf); C(sb,sf);
     R(dtv,v,b,tnf,sf);
     !p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
          FLOOKUP Gf p = FLOOKUP G p /\
          op_taint tnf (Var p) = op_taint tn (Var p);
     !j. j NOTIN W(b,type_memory_size dtv) ==>
          mem_bytes_at j 1 sf.vs_memory = mem_bytes_at j 1 s.vs_memory /\
          (j IN tnf.t_mem <=> j IN tn.t_mem);
     tnf.t_stor = tn.t_stor; tnf.t_trans = tn.t_trans; tnf.t_imm = tn.t_imm;
     (sf with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                 vs_current_bb := s.vs_current_bb;
                 vs_prev_bb := s.vs_prev_bb;
                 vs_inst_idx := s.vs_inst_idx |>) = s;
     !ft fv p. val_wf ft fv /\ R(ft,fv,p,tn,s) /\
       W(p,val_footprint ft fv) disjoint W(b,type_memory_size dtv) ==>
       R(ft,fv,p,tnf,sf).
   In particular allocation table, frontier and requests are unchanged.
   This contract must allow sf.current_bb <> s.current_bb. It is NOT yet
   proved by the accepted endpoints. Abort (INVALID/ASSERT) is a separate
   counted exit alternative, not a normal sf with a false destination value.

   ENDPOINT-TO-CONJUNCT TABLE (current exported statements, not inferred code):
   normalize_word_robust_counted_ptr:
     counted path + actual sb cursor; destination robust primitive; exterior
     memory/taint, stor/trans; all old register operands/provenance/taint;
     universal disjoint robust values. Missing: explicit allocation/frontier/
     requests record frame and t_imm. Its source value constructor premise
     also needs word/address dispatch: it is not a generic word-value lemma.
   normalize_bytes_robust_counted_ptr:
     all those facts INCLUDING t_imm and full state frame (single block);
     exact padded-copy taint transport, not clean destination padding.
     Needs ptr_val_ok at the shifted child's source type. R alone is NOT
     ptr_val_ok: coverage and evaluated-type witnesses must be reattached.
   normalize_array_addresses_execution_counted_ptr:
     counted four arithmetic instructions, actual cursor, all memory/taint
     components and full non-var state frame; protects ctr/sr/dr provided
     none is one of so/doff/sp/dp. No child representation/coverage claim.
   normalize_array_addresses_counted_ptr:
     adds child ptr_covers, but requires i*ss < S and i*ds < T even when
     sn or dn is zero. Use the execution-only interface for zero footprint;
     no fictitious source allocation may be demanded for an empty tuple.
   No accepted child statement establishes the whole proposed interface.

   LIVE UNEQUAL-STRIDE ITERATION AND ACTUAL BACKEDGE:
   Example inner child String[1] -> String[33]: source stride ss=64,
   destination ds=96 (simp[compileEnvTheory.type_memory_bytes_def]);
   runtime string length 1 copies n=64, not ds. At i=1 a fixed two-element
   parent reads [a+64,a+128), writes [b+96,b+160), not [b+96,b+192).
   Source-parent maximum 128, destination maximum 192. Taint in the latter
   slot's last 32 bytes is permitted. No endpoint proves it clean.
   Address prefix yields sp=a+i*ss, dp=b+i*ds and preserves ctr/sr/dr.
   Source child resources come from robust child projection PLUS slot
   coverage; bytes endpoint writes its padded runtime window, retaining all
   old operands. Disjoint robust framing preserves each j>i source child and
   each j<i completed destination child. These facts advance the prefix only
   after proving child write-window containment and slot disjointness.

   For a child which itself loops, use for example elements
     ArrayT (BaseT (StringT 1)) (Fixed 2) ->
     ArrayT (BaseT (StringT 33)) (Fixed 2), strides 128 -> 192.
   compile_copy_sarray_typed_loop_layout gives si -> se for the recursive
   child. The tail is APPENDED TO se.cs_current_insts in se.cs_current_bb:
     ADD [Var ctr; Lit 1w] [fresh se.cs_next_var];
     ASSIGN [Var fresh] [ctr]; JMP [Label cond] [].
   It is not appended to si/body's block. typed_copy_loop_slice_locations
   locates exactly this back block even when se.current_bb differs from si.
   The proposed C(sb,sf) therefore matches the tail's true starting cursor;
   a same-block child contract would fail this test.
   Child old-register frame must preserve ctr, root operands, and dynamic
   length (all allocated BEFORE si); ADD then ASSIGN intentionally changes
   ctr to n2w(i+1), so the tail cannot itself promise ALL-old-var preservation.
   Require i<N and N<dimword, hence i+1<=N<dimword; clean counter yields
   clean increment. JMP reenters cond at index zero, updating prev_bb;
   compile_copy_sarray_typed_loop_no_phi and loop-test interfaces justify
   entry ghosts, not a
   same-PC record equality. Counted ADD/ASSIGN/JMP plus invariant restoration
   is MISSING; fixed-run header/ghost_run facts are not gas_path_ptr proofs.

   PREMISE -> PRODUCER / REMAINING JOIN:
   runtime source layout: ext_ret_aggregate_return_runtime_layout, from
     Return typing, call safety, expr_sim_inv (no expr_body_pre needed).
   source robust and G window: D18 ptr_val_ok at post_value_type; rewrite by
     ext_ret_aggregate_lowered_post_type, then bodyPtrDefs projections.
   child arithmetic/coverage: normalize_array_addresses* plus source stride
     = type_memory_size stv and live-child store-size containment. Strict
     no-wrap of live source offsets still needs placement/alloca evidence;
     G coverage alone does not provide concrete allocation bounds.
   fresh destination: compile_alloc_buffer_expr_counted supplies edge,
     destination ptr_covers and robust source preservation at post type.
     Its fresh_vars_wrt, fn_inst_ids_distinct and size-bound premises must
     be discharged from expr_post/compiler facts. Full ghost_inv and source
     separation/resource restoration are STILL A WRAPPER JOIN, not output
     of the four accepted child endpoints.
   metadata: source_external_frame_struct_metadata_acyclic has an additional
     supported_program premise absent from external_frame_ret_widened_ptr.
     Do NOT add that premise. ext_ret_invalid_normalize_outcome supplies the
     counted abort alternative for cyclic metadata, already sufficient for
     stmt_exit_ptr with trivial RetQ, even after successful source Return.
     Field alignment/size producers and allowed fallback pairs remain
     unproved at the recursive boundary; do not assume empty structs assignable.

   FINITE SEMANTIC CASE BOUNDARIES FOR STRATEGIST REVIEW (not new components):
   1 word primitive/address endpoints + missing non-PC state/imm frame;
   2 bytes endpoint reattachment of child ptr_val_ok and slot-sized writes;
   3 fixed-array equal-stride static bulk path (including zero-copy no-op);
   4 fixed-array slow: address prefix, recursive child, counted backedge,
     header, finite iteration, completed robust prefix;
   5 dynamic-array header/ASSERT/copy length: header clean; runtime len<=cap
     from value typing; equal-type bulk versus recursive loop at +32.
     Dynamic zero length still reads/writes header, unlike zero fixed array;
   6 tuples: equal-length paired evaluated lists, cumulative SEPARATE source
     and destination offsets. assign_base_typed_copy_fields_counted is only
     conditional composition; tuple layout projection supplies no IH;
   7 structs: metadata lookup, source field order and cumulative stored sz.
     Compiler's missing-field fallback uses (dst_fty,dst_sz); must exclude it
     for a successful layout conversion or prove that read valid separately;
   8 dispatch fallback: prove type compatibility excludes mismatched aggregate
     tags, or explicitly validate destination-sized source MCOPY;
   9 cyclic metadata INVALID: counted exit, not successful robust destination;
   10 allocation wrapper + frozen-caller producer discharge + full ghost/state
     restoration + downstream GENERAL encoder. These joins remain unresolved.

   Suggested bounded next propositions (ALL UNPROVED here):
   A. Child state frame with the exact non-PC record equality above and
      tnf.t_imm=tn.t_imm, under existing scalar compile/path premises.
   B. For every i<N and every G/tn/s satisfying the array invariant, child
      normal endpoint at se plus old ctr/root/length frame implies a counted
      ADD/ASSIGN/JMP tail to cond with ctr=n2w(i+1), exterior memory/taint
      unchanged and the invariant at i+1. Quantify se independently of si.
   C. For all i<N, disjoint child writes contained in destination slot i,
      robust source children j>i and destination children j<i imply those
      same resources after the child; add newly robust child i to prefix.
      Existing robust_val_in_memory_exterior_frame is the transport lemma;
      do not duplicate it. The new work is interval/prefix packaging.
   D. Metadata/typed-list dispatch gives child widening, evaluated sizes and
      field-source offset agreement, OR a counted abort endpoint. Never use
      destination widening capacity as a bound on source reads.

   These are requests for decomposition, not admitted helper declarations.
   Existing endpoint sources and both frozen statements are unchanged.
*)
