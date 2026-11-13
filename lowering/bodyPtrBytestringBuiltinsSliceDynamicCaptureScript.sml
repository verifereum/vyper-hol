(* Pointer-aware boundary for the ordinary dynamic Slice source capture. *)
Theory bodyPtrBytestringBuiltinsSliceDynamicCapture
Ancestors
  exprSimSliceDynamicAdapter bodyPtrBytestringBuiltinsSource
  bodyPtrBopHashFootprint bodyPtrDefs exprSimPtrProps
  exprSimSource exprSimHypsDefs exprLoweringProps compileEnv
  appendStorageGhostPtr fragGasPathPtr exprOperandVar loweringPosts
  bodyPtrSignedConvertSourceFixed bodyPtrSignedConvertSourceFrame fragGasSeqPtr
  valueEncodingProps valueEncodingDefs exprSimProps venomInst venomState
  rawLogPtrDynamic logAbiPrefixPtr bodyPtrPrecompileBuiltinsEndpoints
  bodyPtrSignedConvertSourceCompile stmtReasonLitFragMemory ptrDiscipline
  assignTuplePtrCopyEndpoint

Theorem slice_dynamic_capture_ptr:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx src es sa sm s0 ee v src_op t /\
  expr_type src = BaseT bt /\ is_bytestring_type (BaseT bt) /\
  lower_value compile_expr cenv (BaseT bt) src sa = (src_op,sm) /\
  compile_bytestring_src src_op sm = ((len_op,data),sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sc func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv src) v src_op G tn t /\
  ptr_buf_ok cenv src src_op G t /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) ==>
  !D PG. ?cap bs (p:bytes32) u G' tn' pvar.
    ((bt = BytesT (Dynamic cap) /\ v = BytesV bs) \/
     (?str. bt = StringT cap /\ v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    expr_sim_inv cenv cx env ee /\
    run_inst_seq (emitted_insts sm sc) t = OK u /\
    w2n p + 32 < dimword (:256) /\
    w2n p + 32 + LENGTH bs < dimword (:256) /\
    evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
    32 + LENGTH bs <= val_footprint (BaseTV bt) v /\
    let u' = u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sm sc) in
      u'.vs_inst_idx = LENGTH sc.cs_current_insts /\
      u'.vs_current_bb = sc.cs_current_bb /\
      stmt_state_rel ctx func cenv cx ee u' /\
      eval_operand len_op u' = SOME (n2w (LENGTH bs)) /\
      eval_operand data u' = SOME (n2w (w2n p + 32)) /\
      eval_operand src_op u' = SOME p /\
      expr_val_at cenv cx (BaseT bt) sa sc ee v src_op u' /\
      mem_bytes_at (w2n p + 32) (LENGTH bs) u'.vs_memory = bs /\
      (!e sd ee' v' op' r.
        expr_post ctx func cenv cx e ee sc sd u' ee' v' op' r ==>
        mem_bytes_at (w2n p + 32) (LENGTH bs) r.vs_memory = bs) /\
      (!env' sd se e1 e2 ee1 ee2 v1 v2 op1 op2 r1 r2.
        expr_sim_inv cenv cx env' ee1 /\
        local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd.cs_next_id /\
        MAP FDOM ee.scopes = MAP FDOM ee1.scopes /\
        (!z. src_op = Var z ==> not_fresh_at sc z) /\
        (!l. src_op <> Label l) /\
        expr_post ctx func cenv cx e1 ee sc sd u' ee1 v1 op1 r1 /\
        expr_post ctx func cenv cx e2 ee1 sd se r1 ee2 v2 op2 r2 ==>
        mem_bytes_at (w2n p + 32) (LENGTH bs) r2.vs_memory = bs) /\
      (!tops source Q R.
        gas_outcome F tops (ctx,func) source (ee,u') Q R ==>
        gas_outcome F tops (ctx,func) source (ee,t) Q R) /\
      gas_path_ptr D 0 ctx func PG G tn t 0 G' tn' (OK u') /\
      ghost_inv d cenv cx ee G' tn' u' /\
      ptr_covers G' tn' pvar u' (LENGTH bs) /\ data = Var pvar /\
      op_prov G' len_op = NONE /\ op_taint tn' len_op = {} /\
      (!x. not_fresh_at sm x ==>
        lookup_var x u' = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
        op_taint tn' (Var x) = op_taint tn (Var x)) /\
      ghost_kept cenv ee sm G tn t G' tn'
Proof
  strip_tac >> rpt gen_tac >>
  `post_value_type cenv src = BaseT bt` by metis_tac[post_value_type_bytestring] >>
  drule_all slice_source_dynamic_capture_entry >> strip_tac >>
  `~is_word_type (BaseT bt)` by
    (fs[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `ptr_mem_ok cx (BaseT bt) v src_op G tn t` by gvs[ptr_val_ok_def] >>
  `?w. eval_operand src_op t = SOME w` by
    (fs[expr_post_def, expr_val_at_def] >> metis_tac[]) >>
  `?x b sz. src_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + val_store_size (BaseTV bt) v <= b+sz` by
    (`val_footprint (BaseTV bt) v <> 0` by decide_tac >>
     drule_all ptr_mem_ok_bounds >> simp[]) >>
  `(!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
   mem_word_at (w2n w) t.vs_memory = n2w (LENGTH bs)` by
    (gvs[] >> FIRST
      [drule ptr_mem_ok_bytes_clean >>
       disch_then (qspecl_then [`w`, `BaseTV (BytesT (Dynamic cap))`] mp_tac) >>
       simp[] >> strip_tac >> drule ptr_mem_ok_bytes_length >>
       disch_then (qspecl_then [`w`, `BaseTV (BytesT (Dynamic cap))`] mp_tac) >> simp[],
       drule_all ptr_mem_ok_string_clean >> strip_tac >>
       drule_all ptr_mem_ok_string_length >> simp[]]) >>
  `ptr_covers G tn x t (32+LENGTH bs)` by
    (gvs[ptr_covers_def, ptr_val_ok_def, eval_operand_def, val_store_size_def,
         val_footprint_def] >>
     qmatch_goalsub_abbrev_tac `L + _ <= _` >>
     qspec_then `L` mp_tac le_word_size_mul >> decide_tac) >>
  `not_fresh_at sm x` by metis_tac[compile_lower_value_var] >>
  gvs[] >>
  `lookup_var x t = SOME w /\ 32 <= LENGTH bs + 32` by
    gvs[eval_operand_def] >>
  drule_at (Pat `run_inst_seq _ _ = _`) compile_bytestring_src_fixed_frame >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  simp[] >>
  disch_then drule >>
  disch_then (qspecl_then [`D`,`func`,`PG`]
    (qx_choose_then `l` (qx_choose_then `dp`
      (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))))) >>
  `w = p` by (gvs[eval_operand_def] >> metis_tac[]) >>
  gvs[] >>
  `!z. not_fresh_at sm z ==>
    lookup_var z u = lookup_var z t /\ FLOOKUP H z = FLOOKUP G z /\
    op_taint th (Var z) = op_taint tn (Var z)` by metis_tac[] >>
  `ghost_inv d cenv cx ee H th u` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sm`,`t`,`tn`] >>
     simp[] >> metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
  `ghost_kept cenv ee sm G tn t H th` by
    (simp[ghost_kept_def] >> metis_tac[]) >>
  drule_all compile_bytestring_src_shape_fresh >> strip_tac >> gvs[] >>
  rename1 `eval_operand (Var dp) u = SOME (p + 32w)` >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sc) t
    (DRESTRICT G (COMPL {l}) |+ (dp,(b,sz)))
    (tn with t_var := tn.t_var |+ (l,{}) |+ (dp,{}))` by
    (simp[] >> irule bytes_mload_add_inst_seq_ptr >>
     simp[listTheory.ALL_DISTINCT] >> conj_tac >- gvs[ptr_covers_def] >>
     qexistsl_tac [`w2n p`,`w2n (mload (w2n p) t)`] >>
     gvs[ptr_covers_def, eval_operand_def] >> decide_tac) >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sm sc) t H th` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]) >>
  `H = DRESTRICT G (COMPL {l}) |+ (dp,(b,sz)) /\
   th = tn with t_var := tn.t_var |+ (l,{}) |+ (dp,{})` by
    (irule inst_seq_ptr_endpoint_unique >>
     metis_tac[]) >>
  `!n. ptr_covers G tn x t (32+n) /\ w2n p+32 < dimword(:256) ==>
    ptr_covers H th dp u n` by
    (rpt strip_tac >>
     `w2n (p + 32w) = w2n p + 32` by
       simp[wordsTheory.w2n_add_2] >>
     gvs[ptr_covers_def, eval_operand_def, op_taint_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> decide_tac) >>
  `sc.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sc` by
    (drule compile_bytestring_src_parts >> strip_tac >>
     imp_res_tac emitted_insts_emit_op_local >> gvs[]) >>
  drule_all fn_has_code_code >> strip_tac >>
  `gas_path_ptr D 0 ctx func PG G tn t 0 H th
    (OK (u with vs_inst_idx := LENGTH sm.cs_current_insts + 2))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_ptr >>
     simp[mk_inst_def, is_terminator_def] >>
     disch_then irule >>
     gvs[mk_inst_def]) >>
  qexistsl_tac [`H`,`th`] >>
  simp[ghost_inv_inst_idx, lookup_var_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[lookup_var_def] >> metis_tac[]
QED
