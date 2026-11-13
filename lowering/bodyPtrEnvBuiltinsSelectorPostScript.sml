(* Ordinary dynamic-four-byte selector post, shared by folded and runtime paths. *)
Theory bodyPtrEnvBuiltinsSelectorPost
Ancestors exprSimBuffer bodyPtrEnvBuiltinsSelectorRun exprLoweringProps
  loweringPosts context vyperValue vyperAST venomState words compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs

(* buffer_memory_vv_post with the pure frame owed only by an effect-free e. *)
Theorem buffer_memory_vv_post_cond[local]:
  !func cenv cx e es sa sb s0 t v tvt p w sz ctx.
    post_value_type cenv e = expr_type e /\
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    val_wf tvt v /\ val_in_memory tvt v (w2n w) t.vs_memory /\
    stmt_state_rel H ctx func cenv cx es t /\
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
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s0.vs_memory) /\
    (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) ==>
    vv_post H ctx func cenv cx e es sa sb s0 es (Value v)
      (LocatedValue (expr_type e) p) t
Proof
  rpt gen_tac >> strip_tac >>
  `locals_kept cenv es es s0 t` by
    (irule exprSimPropsTheory.locals_kept_regions >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` kall_tac >>
  irule buffer_memory_vv_post_general >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `aid` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!n lb lsz. local_region _ _ t _ _ _ ==> _` drule >> decide_tac
QED

Theorem selector_buffer_vv_post:
  LENGTH bs = 4 /\
  val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) b t.vs_memory /\
  stmt_state_rel H ctx fn cenv cx es t /\
  eval_operand buf.buf_operand t = SOME (n2w b) /\
  b + 64 < dimword (:256) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,64) /\
  sa.cs_next_id < sb.cs_next_id /\
  (!name off len. local_region cenv es.scopes t name off len ==>
    regions_disjoint b 64 off len) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid off len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!name off len. local_region cenv es.scopes s name off len ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (~expr_has_effect (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args) ==>
   pure_frame cenv fn es sa s t) ==>
  vv_post H ctx fn cenv cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args)
    es sa sb s es (Value (BytesV bs))
    (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf))
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  qspec_then `Builtin (BaseT (BytesT (Dynamic 4))) MethodId args`
    (fn th => irule (SRULE [expr_type_def] th))
    (buffer_memory_vv_post_cond |> Q.SPEC `fn` |> Q.SPEC `cenv` |> Q.SPEC `cx`) >>
  gvs[is_word_type_def, base_ptr_def, stmt_state_rel_inst_idx,
    lookup_var_def, local_region_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt conj_tac
  >- (qexists_tac `BaseTV (BytesT (Dynamic 4))` >>
      simp[evaluate_type_def, val_wf_def, val_footprint_def,
        base_ptr_def, eval_operand_def, lookup_var_def] >>
      conj_tac >- metis_tac[regions_disjoint_def] >>
      simp[type_slot_size_def, type_memory_size_def, dimword_def,
        vfmConstantsTheory.word_size_def]) >>
  simp[]
QED
