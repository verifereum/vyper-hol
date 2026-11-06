(* Ordinary dynamic-four-byte selector post, shared by folded and runtime paths. *)
Theory bodyPtrEnvBuiltinsSelectorPost
Ancestors exprSimBuffer bodyPtrEnvBuiltinsSelectorRun exprLoweringProps
  loweringPosts context vyperValue vyperAST venomState words compileEnv valueEncoding

Theorem selector_buffer_vv_post:
  LENGTH bs = 4 /\
  val_in_memory (BaseTV (BytesT (Dynamic 4))) (BytesV bs) b t.vs_memory /\
  stmt_state_rel ctx fn cenv cx es t /\
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
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args)
    es sa sb s es (Value (BytesV bs))
    (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf))
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  qspec_then `Builtin (BaseT (BytesT (Dynamic 4))) MethodId args`
    (fn th => irule (SRULE [expr_type_def] th))
    (buffer_memory_vv_post |> Q.SPEC `fn` |> Q.SPEC `cenv` |> Q.SPEC `cx`) >>
  gvs[is_word_type_def, base_ptr_def, stmt_state_rel_inst_idx,
    lookup_var_def, local_region_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `BaseTV (BytesT (Dynamic 4))` >>
  simp[evaluate_type_def, val_wf_def, val_footprint_def,
    base_ptr_def, eval_operand_def, lookup_var_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  simp[type_slot_size_def, type_memory_size_def, dimword_def,
    vfmConstantsTheory.word_size_def]
QED
