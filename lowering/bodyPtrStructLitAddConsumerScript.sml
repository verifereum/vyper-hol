Theory bodyPtrStructLitAddConsumer
Ancestors bodyPtrStructLitRawChild bodyPtrStructLitResourceHandoff
  exprSimPtrLiteralOps loweringPosts bodyPtrDefs freshWrites ptrSafeRun

(* Unlike ghost_kept alone, vv_post also preserves evaluation of older
   variables. ptr_covers does not mention the runtime allocation table. *)
Theorem vv_post_ghost_kept_covers:
  vv_post ctx fn ce cx e es sa sb s0 ee tv vv s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  not_fresh_at sa p /\ ptr_covers G0 tn0 p s0 N ==>
  ptr_covers G tn p s N
Proof
  simp[vv_post_def, ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem raw_child_field_add_check:
  vv_post ctx fn ce cx e es sa sb s0 ee tv vv s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  not_fresh_at sa p /\ ptr_covers G0 tn0 p s0 N /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id ADD [Var p; Lit off] [dst]) s
Proof
  strip_tac >> drule_all vv_post_ghost_kept_covers >>
  simp[ptr_covers_def] >> strip_tac >>
  irule literal_add_ptr_inst_ok >> simp[]
QED

(* Consumer ledger (actual order: child, ADD, unwrap, store):
   - raw_child_field_add_check needs no store-sized ADD access bound. ADD has
     empty memory ranges; literal_add_ptr_inst_ok asks only clean base taint
     and no dynamic allocation in ctx. ghost_kept transports that taint.
   - For successful ADD execution, clean_add_counted (FieldStore) also asks
     old base evaluation, nonhalting and instruction placement. vv_post's
     older-variable clause gives base evaluation. Nonhalting must come from
     the counted path's OK endpoint (NOT stmt_state_rel or vv_post alone).
     Code placement comes from the emitted ADD interval.
   - vv_post_ghost_kept_covers recovers whole allocation-entry coverage at the
     SAME child endpoint: vv_post supplies old pointer evaluation, ghost_kept
     supplies provenance and taint. ptr_covers needs NO allocation-table or
     memory equation. vv_post separately preserves old allocation entries.
   - PostAdd.ptr_vv_ok_fresh_add handles BOTH StackValue and LocatedValue;
     ptr_val_ok_operand_frame explicitly preserves op_prov, including NONE
     for word types. It needs the child vv operand distinct from ADD output.
     Compiler safe-value and fresh-output results must discharge that fact.
   - FreshGhost.ghost_inv_fresh_add_pc preserves live ghosts when local and
     return pointers differ from the fresh output; reservation monotonicity
     is the producer for those inequalities. Source vv_post also needs its
     corresponding fresh-update frame, not merely ptr_vv_ok preservation.
   - Unwrap StackValue and non-word LocatedValue are return-only branches.
     Memory word LocatedValue emits MLOAD: MemoryRead's
     memory_word_unwrap_continuation requires 32-byte coverage, clean loaded
     bytes and output freshness, besides vv_post/source/code premises.
     Raw ptr_vv_ok/ptr_buf_ok do NOT by themselves assert clean loaded bytes.
     Nonmemory word branches use NonmemoryRead's storage/runtime-code
     continuations, whose clean/ghost and source premises remain separate.
   - No declared field-size conversion, store or full loop is proved here.
     The compiler freshness/source-frame and clean-memory-load producers
     must be checked before integrating ADD and unwrap into a counted run. *)
