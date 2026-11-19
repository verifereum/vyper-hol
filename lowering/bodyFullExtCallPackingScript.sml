Theory bodyFullExtCallPacking
Ancestors
  exprLowering compileEnv selectorDispatch byte rich_list words memoryReadProps venomMemProps calldataOverwritePtr typedCopyOriginPtrFields fragGasOriginPtrDead valueEncodingProps venomState ptrDiscipline bodyPtrDefs loweringShapeDefs fragExec ptrSafeRun

(* The request packer ends immediately before the optional code check. *)
Theorem extcall_request_buffer_layout:
  compile_external_call_kwargs ce addr vals tys mem abi mid cap minsz
    retbytes stat value gas skip hasdef def rt dt aenc adec sa = (ro,sb) ==>
  ?ba s1 s2 len s3 off sp sr u.
    compile_alloc_buffer ((if abi > cap then abi else cap) + 32) sa = (ba,s1) /\
    emit_void MSTORE [ba.buf_operand; Lit (n2w mid)] s1 = ((),s2) /\
    (if vals = [] then comp_return (Lit 4w) else
      comp_bind (compile_alloc_buffer mem) (\aa.
      comp_ignore_bind (compile_extcall_store_values ce (ZIP (vals,tys))
                         aa.buf_operand 0)
      (comp_bind (emit_op ADD [ba.buf_operand; Lit 32w]) (\dst.
       comp_bind (compile_abi_encode_to_buf dst aa.buf_operand aenc) (\alen.
       emit_op ADD [alen; Lit 4w]))))) s2 = (len,s3) /\
    emit_op ADD [ba.buf_operand; Lit 28w] s3 = (off,sp) /\
    comp_ignore_bind
      (if rt = NoneT /\ ~skip then compile_extcodesize_check addr
       else comp_return ())
      (comp_bind
        (if stat then emit_op STATICCALL
           [gas; addr; off; len; ba.buf_operand; Lit (n2w cap)]
         else emit_op CALL
           [gas; addr; value; off; len; ba.buf_operand; Lit (n2w cap)])
        (\success. comp_bind (fresh_label "extcall_fail") (\fail.
         comp_bind (fresh_label "extcall_cont") (\cont.
         comp_ignore_bind (emit_inst JNZ [success; Label cont; Label fail] [])
         (comp_ignore_bind (new_block fail)
         (comp_bind (emit_op RETURNDATASIZE []) (\rds.
          comp_bind (compile_alloc_buffer 0) (\fb.
          comp_ignore_bind (emit_void RETURNDATACOPY
                            [fb.buf_operand; Lit 0w; rds])
          (comp_ignore_bind (emit_inst REVERT [fb.buf_operand; rds] [])
                            (new_block cont)))))))))) sp = (u,sr) /\
    (if rt = NoneT then comp_return (Lit 0w)
     else if hasdef then
       comp_bind (compile_alloc_buffer retbytes) (\r.
         compile_default_return_path ce rt dt ba.buf_operand r.buf_operand
           def addr skip minsz cap adec)
     else comp_bind (compile_alloc_buffer retbytes) (\r.
       comp_bind (compile_return_value_decode minsz cap) (\hi.
       comp_ignore_bind (compile_abi_decode_to_buf r.buf_operand (Lit 0w)
                          MLOAD ba.buf_operand hi adec)
                        (comp_return r.buf_operand)))) sr = (ro,sb)
Proof
  simp[compile_external_call_kwargs_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 4 (pairarg_tac >> simp[]) >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
QED

Theorem extcall_selector_bytes:
  LENGTH bs = 4 ==> DROP 28 (word_to_bytes (calldata_method_id bs) T) = bs
Proof
  rw[listTheory.LENGTH_EQ_NUM_compute, calldata_method_id_def] >>
  irule listTheory.LIST_EQ >>
  simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  rpt strip_tac >>
  `x = 0 \/ x = 1 \/ x = 2 \/ x = 3` by decide_tac >>
  gvs[rich_listTheory.EL_DROP, word_to_bytes_def, EL_word_to_bytes_aux,
      get_byte_def, byte_index_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  rewrite_tac[GSYM word_add_n2w] >>
  simp[Once arithmeticTheory.MULT_COMM, GSYM word_mul_n2w, GSYM w2w_def] >>
  pure_rewrite_tac (map (fn e => GSYM (SRULE [] (Q.SPEC e (ISPEC ``w:bytes32`` WORD_MUL_LSL))))
                       [`24`, `16`, `8`]) >>
  blastLib.BBLAST_TAC
QED

Theorem extcall_selector_store_read:
  LENGTH bs = 4 ==>
  venomState$read_memory (baddr + 28) 4 (mstore baddr (calldata_method_id bs) s) = bs
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`baddr`, `32`, `28`, `4`,
      `mstore baddr (calldata_method_id bs) s`] read_memory_subwindow) >>
  simp[read_memory_word, mload_mstore_same, extcall_selector_bytes]
QED

Theorem extcall_selector_only_tail:
  emit_void MSTORE [Var root;Lit (calldata_method_id bs)] sa = ((),sm) /\
  emit_op ADD [Var root;Lit 28w] sm = (off,sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  LENGTH bs = 4 /\ lookup_var root s = SOME w /\
  not_fresh_at sm root /\ ptr_covers G tn root s capacity /\ 32 <= capacity /\
  w2n w + capacity < dimword (:256) /\ w2n w + capacity <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p t Gf tf.
    off = Var p /\ not_fresh_at sb p /\ ptr_covers Gf tf p t 4 /\
    lookup_var p t = SOME (n2w (w2n w + 28)) /\
    ptr_covers Gf tf root t capacity /\ lookup_var root t = SOME w /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    venomState$read_memory (w2n w + 28) 4 t = bs /\
    (!i. w2n w + 28 <= i /\ i < w2n w + 32 ==> i NOTIN tf.t_mem) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ptr_covers G tn root s 32` by (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  `eval_operand (Var root) s = SOME w /\
   eval_operand (Lit (calldata_method_id bs)) s = SOME (calldata_method_id bs) /\
   op_taint tn (Lit (calldata_method_id bs)) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` (qx_choose_then `smach` (qx_choose_then `Gm`
     (qx_choose_then `tm` strip_assume_tac)))) >>
  `lookup_var root smach = SOME w` by (fs[eval_operand_def] >> (metis_tac[eval_operand_def])) >>
  `ptr_covers Gm tm root smach capacity` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `allocas_from lo smach` by (gvs[allocas_from_def] >> metis_tac[]) >>
  `lo <= smach.vs_alloca_next /\ w2n w + 28 < dimword (:256)` by decide_tac >>
  `28 + 4 <= capacity` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp smach` by simp[] >>
  `emit_op ADD [Var root;Lit (n2w 28)] sm = (off,sb)` by simp[] >>
  drule_all (Q.SPECL [`root`, `28`, `4`, `capacity`]
      typed_copy_origin_ptr_add_path) >>
  disch_then (qspecl_then [`explicit`, `PG`, `0`, `0`] strip_assume_tac) >>
  `w2n w + 32 <= s.vs_alloca_next` by decide_tac >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK t,Gf,tnf)` by
    (gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (OK smach,Gm,tm)` by metis_tac[] >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (smach,Gm,tm) []
        (OK t,Gf,tnf)` by (irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
     metis_tac[SRULE [] (Q.SPECL [`(D,lo,explicit,ctx,fn,PG)`, `(s,G,tn)`, `[]`]
       fragGasOriginPtrTheory.gas_origin_ptr_path_append)]) >>
  `lookup_var root t = SOME w /\ FLOOKUP Gf root = FLOOKUP Gm root /\
   op_taint tnf (Var root) = op_taint tm (Var root)` by metis_tac[] >>
  `ptr_covers Gf tnf root t capacity` by
    (qpat_x_assum `ptr_covers Gm tm root smach capacity` mp_tac >>
     simp[ptr_covers_def]) >>
  `smach with vs_inst_idx := s.vs_inst_idx =
     mstore (w2n w) (calldata_method_id bs) s` by
    (`step_inst_base (mk_inst sa.cs_next_id MSTORE
         [Var root;Lit (calldata_method_id bs)] []) s =
         OK (mstore (w2n w) (calldata_method_id bs) s)` by
       (irule emitHelperPropsTheory.step_MSTORE >> simp[]) >>
     drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
     fs[exprLoweringPropsTheory.run_inst_seq_def]) >>
  `t.vs_allocas = smach.vs_allocas` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
          venom_state_component_equality]) >>
  `!x. lookup_var x smach = lookup_var x s` by
    (qpat_x_assum `smach with vs_inst_idx := _ = _`
       (mp_tac o AP_TERM ``venom_state_vs_vars``) >>
     simp[mstore_def, lookup_var_def]) >>
  `venomState$read_memory (w2n w + 28) 4 t = bs` by
    (`t.vs_memory = (mstore (w2n w) (calldata_method_id bs) s).vs_memory` by
       (qpat_x_assum `smach with vs_inst_idx := _ = _`
          (mp_tac o AP_TERM ``venom_state_vs_memory``) >> simp[]) >>
     `venomState$read_memory (w2n w + 28) 4
         (mstore (w2n w) (calldata_method_id bs) s) = bs` by
       (irule extcall_selector_store_read >> simp[]) >>
     metis_tac[read_memory_def]) >>
  qexistsl [`p`, `t`, `Gf`, `tnf`] >> simp[] >> metis_tac[]
QED
