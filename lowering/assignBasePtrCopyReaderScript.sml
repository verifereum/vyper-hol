(* Numerical bound on the allocated root at the same counted copy endpoint. *)
Theory assignBasePtrCopyReader
Ancestors assignBasePtrCopyFrame assignBasePtrNormalizedReader exprSimAlloc
  typedMemoryCopy context compileEnv venomInst venomState exprLoweringProps
  valueEncoding bodyPtrDefs fragGasPathPtr words

Theorem assign_base_allocated_copy_reader_path_ptr:
  !dst src n sa sb fn s d a G tn D ctx PG tv v
    sz pre buf initial cx cenv es words.
    compile_alloc_buffer sz pre = (buf,sa) /\
    buf.buf_operand = Var dst /\
    stmt_state_rel ctx fn cenv cx es initial /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv pre /\ sz < dimword (:256) /\
    MEM (mk_inst pre.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString pre.cs_next_var)]) (fn_insts fn) /\
    run_inst_seq (emitted_insts pre sa) initial = OK s /\
    32*words <= sz /\ n < dimword (:256) /\
    compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s n /\
    ptr_covers G tn src s n /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a) m) ==>
    ?Gf tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      typed_copy_state_frame sa (w2n d) n s u /\
      eval_operand (Var dst) u = SOME d /\
      w2n d + 32*(words-1) < dimword (:256) /\
      (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
           val_in_memory tv v (w2n d) m)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_copy_memory_framed_robust_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `!x. Var dst = Var x ==> not_fresh_at sa x` by gvs[] >>
  drule_all typed_copy_state_frame_operand >> strip_tac >>
  `eval_operand (Var dst) u = SOME d` by gvs[eval_operand_def] >>
  `eval_operand buf.buf_operand u = SOME d` by gvs[] >>
  drule_all assign_base_ptr_normalized_reader_bound >> strip_tac >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]
QED
