(*
 * Execution of fresh expression buffers (#636)
 *
 * An expression whose value is built in a buffer starts with an ALLOCA and
 * addresses into it with ADD ptr off.  The ADD does not wrap inside the
 * buffer, the ALLOCA is in the function, and a value stored in the buffer
 * is the expression's vv_post.  The allocation lemmas (buffer_alloc_code
 * among them) are exprSimAlloc's; they also cover reused ALLOCA entries.
 *
 * TOP-LEVEL:
 *   buffer_offset_no_wrap — w + off does not wrap inside a buffer that ends
 *     below 2 ** 256
 *   buffer_emit_add_run — emit_op ADD [ptr; Lit off] runs
 *   buffer_memory_vv_post, buffer_memory_vv_post_general — a value in the
 *     buffer, with older allocations and variables kept, is vv_post
 *)
Theory exprSimBuffer
Ancestors
  exprSimProps
  loweringPosts
  exprSimAlloc
  exprSimLiteralBuffer emitHelperProps exprLoweringProps compileEnv
  context venomInst venomState words fragExec rich_list list
  exprSimWordArgs exprSimOps



(* Unlike emit_op_ADD_correct, this exact execution boundary does not
   require all existing variables to satisfy fresh_vars_wrt. *)


Theorem buffer_memory_vv_post_general:
  !func cenv cx e es sa sb s0 es' t v tvt p w sz ctx.
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\ val_in_memory tvt v (w2n w) t.vs_memory /\
    stmt_state_rel ctx func cenv cx es' t /\
    eval_operand p.ptr_operand t = SOME w /\ p.ptr_location = LocMemory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    sa.cs_next_id < sb.cs_next_id /\ val_footprint tvt v <= sz /\
    (!n lb lsz. local_region cenv es'.scopes t n lb lsz ==>
       w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
      aid < sa.cs_next_id /\
      (!n b k. local_region cenv es.scopes s0 n b k ==>
        off+len <= b \/ b+k <= off) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory) /\
    locals_kept cenv es s0 t ==>
    vv_post ctx func cenv cx e es sa sb s0 es' (Value v)
      (LocatedValue (expr_type e) p) t
Proof
  rpt gen_tac >> strip_tac >>
  simp[vv_post_def, vv_holds_def, vv_at_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  conj_tac
  >- (disj1_tac >> qexistsl [`sa.cs_next_id`, `w2n w`, `sz`] >> simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!n lb lsz. local_region _ es'.scopes _ _ _ _ ==> _`
        drule >> decide_tac) >>
  metis_tac[]
QED

Theorem buffer_memory_vv_post:
  !func cenv cx e es sa sb s0 t v tvt p w sz ctx.
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\ val_in_memory tvt v (w2n w) t.vs_memory /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand p.ptr_operand t = SOME w /\ p.ptr_location = LocMemory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    sa.cs_next_id < sb.cs_next_id /\ val_footprint tvt v <= sz /\
    (!n lb lsz. local_region cenv es.scopes t n lb lsz ==>
       w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) /\
    (!name b len. local_region cenv es.scopes s0 name b len ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) ==>
    vv_post ctx func cenv cx e es sa sb s0 es (Value v)
      (LocatedValue (expr_type e) p) t
Proof
  rpt gen_tac >> strip_tac >>
  `locals_kept cenv es s0 t` by
    (irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` kall_tac >>
  irule buffer_memory_vv_post_general >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `aid` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!n lb lsz. local_region _ _ t _ _ _ ==> _` drule >> decide_tac
QED
