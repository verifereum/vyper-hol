(* Provenance of a staged initializer, for the typed assignment suffix. *)
Theory bodyIntCallFamStmtMutationAssignInit
Ancestors
  bodyIntCallFamStmtMutationCopyInit bodyIntCallWindowPosts localPtrsProps
  loweringHalt exprSimAlloc exprLoweringProps valueEncodingTyping
  compileEnv venomInst bodyIntCallJointContract exprSimProps
  bodyIntCallFamStmtMutationStaging placeMemoryCopyEffect freshWrites venomState stmtSimAugAssignPlaceMemory

Theorem intcall_staged_initializer_value:
  intcall_expr_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s es sb t /\
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sb) /\
  fn_has_code sa sm fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ ~is_word_type ty /\
  val_wf tv v /\ type_memory_size tv <= n /\
  eval_operand buf.buf_operand t = SOME w /\
  val_in_memory tv v (w2n w) t.vs_memory /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) ==>
  expr_val_rel fp.jc_cx ty v buf.buf_operand t /\
  expr_val_at ce fp.jc_cx ty sa sb es v buf.buf_operand t
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `sm.cs_next_id <= sb.cs_next_id` by
    metis_tac[ci_mono_compile_copy_memory, ci_mono_def, pairTheory.SND] >>
  `not_local_ptr ce es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (fs[intcall_expr_res_def, local_ptrs_reserved_def, not_local_ptr_def] >>
     metis_tac[]) >>
  `!name b k. local_region ce es.scopes t name b k ==>
     regions_disjoint (w2n w) n b k` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     qexistsl [`ce`,`fp.jc_func`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
         [STRING #"%" (toString sa.cs_next_var)]`,
       `name`,`STRING #"%" (toString sa.cs_next_var)`,`es.scopes`,`t`] >>
     fs[intcall_expr_cont_def,intcall_expr_res_def,stmt_state_rel_def,
        state_rel_def,mk_inst_def] >>
     metis_tac[buffer_alloc_code, mk_inst_def]) >>
  conj_tac >- simp[loweringPostsTheory.expr_val_rel_def] >>
  irule (cj 1 allocated_value_location) >>
  qexistsl [`sa.cs_next_id`,`w2n w`,`n`,`tv`,`w`] >>
  simp[] >> fs[regions_disjoint_def] >>
  conj_tac >- metis_tac[] >>
  drule val_footprint_le >> decide_tac
QED

Theorem intcall_staged_initializer_store:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer (type_memory_size stv) sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src (type_memory_size stv) sm = ((),sn) /\
  compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
  fn_has_code sn sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ (!lbl. src <> Label lbl) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  ~is_word_type sty /\ evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  type_widens_to (get_tenv fp.jc_cx) sty dty /\
  value_has_type stv v /\ value_has_type dtv v /\
  type_memory_size stv < dimword (:256) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  eval_operand dst s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\ inst.inst_id < sa.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  fp.jc_lo <= b /\ b <= w2n dw /\
  w2n dw + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes s name a n ==>
     a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es sa s es sn t /\
    typed_copy_effect fp.jc_ctx fp.jc_func sn sb t u
      (w2n dw) (type_memory_size dtv) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    intcall_expr_res fp ce env es sb u
Proof
  strip_tac >>
  `val_wf stv v` by metis_tac[value_has_type_val_wf] >>
  drule_all (intcall_staging_initialize |>
    Q.INST [`n` |-> `type_memory_size stv`, `tv` |-> `stv`] |> SRULE []) >>
  strip_tac >>
  `expr_val_rel fp.jc_cx sty v buf.buf_operand t /\
   expr_val_at ce fp.jc_cx sty sa sn es v buf.buf_operand t` by
    (irule intcall_staged_initializer_value >> simp[] >> metis_tac[]) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sn.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
      ci_mono_compile_store_memory,ci_mono_def,pairTheory.SND,
      arithmeticTheory.LESS_EQ_TRANS] >>
  `t.vs_labels = s.vs_labels` by metis_tac[aug_place_marked_path_labels] >>
  `eval_operand dst t = SOME dw` by
    (Cases_on `dst` >> fs[intcall_expr_cont_def,eval_operand_def] >> metis_tac[]) >>
  `!name a n. local_region ce es.scopes t name a n ==>
     a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a` by
    (rpt strip_tac >>
     `local_region ce es.scopes s name a n` by
       (irule local_region_frame >> conj_tac
        >- (qexists `fp.jc_func` >>
            fs[intcall_expr_res_def,stmt_state_rel_def,state_rel_def]) >>
        qexistsl [`sa`,`es.scopes`,`t`] >>
        fs[intcall_expr_res_def,intcall_expr_cont_def]) >> metis_tac[]) >>
  `?u. typed_copy_effect fp.jc_ctx fp.jc_func sn sb t u
       (w2n dw) (type_memory_size dtv) /\
       val_in_memory dtv v (w2n dw) u.vs_memory /\
       intcall_expr_res fp ce env es sb u` by
    (`!x. dst = Var x ==> not_fresh_at sn x` by
       metis_tac[not_fresh_at_mono] >>
     `FLOOKUP t.vs_allocas inst.inst_id = SOME (b,k)` by
       (fs[intcall_expr_cont_def] >> metis_tac[]) >>
     fs[intcall_expr_cont_def] >>
     qpat_assum `buf.buf_operand = _` (fn th => fs[th]) >>
     irule intcall_initializer_store_landing >> simp[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >> simp[]) >>
  qexistsl [`t`,`u`] >> simp[]
QED
