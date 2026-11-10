Theory bodyPtrTypeBuiltinsExtract32Prepare
Ancestors
  bodyPtrTypeBuiltinsExtract32Operands bodyPtrTypeBuiltinsExtract32HeaderFrame
  exprSimExtract32Post gasSummaryComposePtr gasSummary exprLoweringProps
  compileEnv loweringStateRelDefs venomState venomMemDefs words vyperState
  bodyPtrSignedConvertSourceCompile valueEncoding valueEncodingDefs

Theorem extract32_prepare_ptr_counted:
  expr_post ctx func cenv cx src es sa sm s0 ee (BytesV bs) (Var sv) s /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  compile_bytestring_src (Var sv) sm = ((lenop,dataop),sb) /\
  not_fresh_at sm sv /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G tn s /\
  op_taint tn (Var sv) = {} /\ ghost_inv d cenv cx ee G tn s /\
  ghost_kept cenv es0 sbase G0 tn0 sbase0 G tn /\
  sbase.cs_next_var <= sm.cs_next_var /\ ~ctx_has_dalloca ctx /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) ==>
  ?u p H th len data.
    expr_post ctx func cenv cx src es sa sb s0 ee (BytesV bs) (Var sv) u /\
    eval_operand (Var sv) u = SOME (n2w p) /\
    eval_operand lenop u = SOME (n2w (LENGTH bs)) /\
    eval_operand dataop u = SOME (n2w (p+32)) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p u.vs_memory /\
    LENGTH bs < dimword (:256) /\ p+32+LENGTH bs < dimword (:256) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H th (OK u) /\
    gas_marked_exec_ptr D (ctx,func) PG (return (BytesV bs))
      (ee,s,G,tn) [] (INL (BytesV bs)) ee H th (OK u) /\
    ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) H th u /\
    ghost_inv d cenv cx ee H th u /\
    ghost_kept cenv es0 sbase G0 tn0 sbase0 H th /\
    lenop = Var len /\ dataop = Var data /\
    not_fresh_at sb sv /\ not_fresh_at sb len /\ not_fresh_at sb data /\
    op_taint th (Var sv) = {} /\ op_taint th (Var len) = {} /\
    op_prov H (Var len) = NONE /\
    (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers H th data u n)
Proof
  strip_tac >> drule_all extract32_source_post_view >> strip_tac >>
  drule_all extract32_prepare_site >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `!j. j < LENGTH (emitted_insts sm sb) ==>
    get_instruction bb (s.vs_inst_idx+j) = SOME (EL j (emitted_insts sm sb))` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at sm p` by (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all extract32_source_prefix_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all compile_bytestring_src_shape_fresh >> strip_tac >>
  gvs[] >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by metis_tac[] >>
  `eval_operand (Var sv) t = eval_operand (Var sv) s` by simp[eval_operand_def] >>
  `expr_post ctx func cenv cx src es sa sb s0 ee (BytesV bs) (Var sv) t` by
    (irule extract32_prepare_post_readonly >> metis_tac[]) >>
  `p < dimword(:256)` by decide_tac >>
  `mload (w2n (n2w p:bytes32)) s = n2w (LENGTH bs)` by
    gvs[w2n_n2w, mload_def, mem_word_at_def, mem_bytes_at_def] >>
  qexistsl_tac [`t`,`p`,`H`,`th`] >>
  simp[eval_operand_def, word_add_n2w, gas_marked_exec_ptr_def,
       return_def] >> conj_tac
  >- gvs[w2n_n2w] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED
