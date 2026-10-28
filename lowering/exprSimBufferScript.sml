(*
 * Execution of fresh expression buffers (#636)
 *
 * An expression whose value is built in a buffer starts with an ALLOCA and
 * addresses into it with ADD ptr off.  The ADD does not wrap inside the
 * buffer, the ALLOCA is in the function, and a value stored in the buffer
 * is the expression's vv_post.  The allocation and store code is
 * exprSimLiteralBuffer's; its lemmas also cover reused ALLOCA entries.
 *
 * TOP-LEVEL:
 *   buffer_offset_no_wrap — w + off does not wrap inside a buffer that ends
 *     below 2 ** 256
 *   buffer_emit_add_run — emit_op ADD [ptr; Lit off] runs
 *   buffer_alloc_code — compile_alloc_buffer's ALLOCA is in fn_insts
 *   buffer_memory_vv_post, buffer_memory_vv_post_general — a value in the
 *     buffer, with older allocations and variables kept, is vv_post
 *)
Theory exprSimBuffer
Ancestors
  exprSimLiteralBuffer emitHelperProps exprLoweringProps compileEnv
  context venomInst venomState words fragExec rich_list list
  exprSimWordArgs exprSimOps exprSim

Theorem buffer_offset_no_wrap:
  !w:bytes32. !off sz.
    w2n w + sz < dimword (:256) /\ off <= sz ==>
    w2n (w + n2w off) = w2n w + off
Proof
  rpt strip_tac >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (w + n2w off) = w2n w + w2n ((n2w off):bytes32)`
    suffices_by simp[] >>
  irule wordsTheory.w2n_add_2 >> simp[] >> decide_tac
QED

(* Unlike emit_op_ADD_correct, this exact execution boundary does not
   require all existing variables to satisfy fresh_vars_wrt. *)
Theorem buffer_emit_add_run:
  !sa sb ptr dst s w off.
    emit_op ADD [ptr; Lit (n2w off)] sa = (dst, sb) /\
    eval_operand ptr s = SOME w ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (update_var (STRING #"%" (toString sa.cs_next_var))
                     (w + n2w off) s)
Proof
  rpt strip_tac >> rename1 `eval_operand pop s = SOME w` >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base
     (mk_inst sa.cs_next_id ADD [pop; Lit (n2w off)]
       [STRING #"%" (toString sa.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString sa.cs_next_var))
                  (w + n2w off) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  simp[run_inst_seq_def]
QED

Theorem buffer_alloc_code:
  !size sa sb buf func.
    compile_alloc_buffer size sa = (buf, sb) /\
    fn_has_code sa sb func ==>
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w size)]
         [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  rpt strip_tac >>
  gvs[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_return_def] >>
  gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[MEM_APPEND]
QED

Theorem buffer_memory_vv_post_general:
  !func cenv cx e es sa sb s0 es' t v tvt p w sz.
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\ val_in_memory tvt v (w2n w) t.vs_memory /\
    stmt_state_rel func cenv cx es' t /\
    eval_operand p.ptr_operand t = SOME w /\ p.ptr_location = LocMemory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    sa.cs_next_id < sb.cs_next_id /\ val_footprint tvt v <= sz /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
      aid < sa.cs_next_id /\
      (!n b k. local_region cenv es.scopes s0 n b k ==>
        off+len <= b \/ b+k <= off) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory) ==>
    vv_post func cenv cx e es sa sb s0 es' (Value v)
      (LocatedValue (expr_type e) p) t
Proof
  rpt gen_tac >> strip_tac >>
  simp[vv_post_def, vv_holds_def, vv_at_def,
    vyperStateTheory.materialise_def, vyperStateTheory.return_def] >>
  conj_tac
  >- (disj1_tac >> qexistsl [`sa.cs_next_id`, `w2n w`, `sz`] >> simp[]) >>
  metis_tac[]
QED

Theorem buffer_memory_vv_post:
  !func cenv cx e es sa sb s0 t v tvt p w sz.
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\ val_in_memory tvt v (w2n w) t.vs_memory /\
    stmt_state_rel func cenv cx es t /\
    eval_operand p.ptr_operand t = SOME w /\ p.ptr_location = LocMemory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    sa.cs_next_id < sb.cs_next_id /\ val_footprint tvt v <= sz /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) ==>
    vv_post func cenv cx e es sa sb s0 es (Value v)
      (LocatedValue (expr_type e) p) t
Proof
  rpt gen_tac >> strip_tac >>
  irule buffer_memory_vv_post_general >>
  simp[] >> metis_tac[]
QED
