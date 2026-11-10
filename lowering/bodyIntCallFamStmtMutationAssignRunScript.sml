(* Assignment of an aggregate initializer to an inactive buffer. *)
Theory bodyIntCallFamStmtMutationAssignRun
Ancestors
  bodyIntCallFamStmtMutationAssignInit stmtLowering compileEnv fragGasMode fragExec
  exprLoweringProps placeMemoryCopyEffect venomState loweringHalt freshWrites
  bodyIntCallJointContract bodyIntCallFamStmtMutationCopyInit

Theorem intcall_aggregate_initializer_run:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_res fp ce env es sa s /\
  compile_assign_value ce dst LocMemory src F loc dty sty info bytes sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ (!lbl. src <> Label lbl) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  expr_val_rel fp.jc_cx sty v src s /\
  expr_val_at ce fp.jc_cx sty si sa es v src s /\
  si.cs_next_id <= sa.cs_next_id /\
  ~is_word_type sty /\ evaluate_type (get_tenv fp.jc_cx) sty = SOME stv /\
  evaluate_type (get_tenv fp.jc_cx) dty = SOME dtv /\
  type_widens_to (get_tenv fp.jc_cx) sty dty /\
  value_has_type stv v /\ value_has_type dtv v /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_size stv < dimword (:256) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  eval_operand dst s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\ inst.inst_id < si.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  fp.jc_lo <= b /\ b <= w2n dw /\
  w2n dw + type_memory_size dtv <= b+k /\ b+k < dimword (:256) /\
  (!name a n. local_region ce es.scopes s name a n ==>
     a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    intcall_expr_res fp ce env es sb u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x wd. not_fresh_at sa x /\ lookup_var x s = SOME wd ==>
       lookup_var x u = SOME wd) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def] >>
  Cases_on `loc = SOME LocMemory`
  >- (simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >>
      rename1 `compile_alloc_buffer (type_memory_size stv) sa = (buf,sm)` >>
      rename1 `compile_copy_memory buf.buf_operand src (type_memory_size stv) sm = (ret,sn)` >>
      Cases_on `ret` >>
      `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb` by
        metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
          ci_mono_compile_store_memory,ci_mono_def,pairTheory.SND] >>
      `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
       fn_has_code sn sb fp.jc_func` by
        metis_tac[fn_has_code_split,cs_extends_trans] >>
      `inst.inst_id < sa.cs_next_id` by decide_tac >>
      drule_all intcall_staged_initializer_store >> strip_tac >>
      qexists `u` >>
      fs[intcall_expr_cont_def,typed_copy_effect_def,
         venom_state_component_equality] >>
      conj_tac
      >- (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
          qexists `t` >> simp[]) >>
      `sa.cs_next_var <= sn.cs_next_var` by
        metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
          ci_mono_def,pairTheory.SND,arithmeticTheory.LESS_EQ_TRANS] >>
      metis_tac[not_fresh_at_mono]) >>
  simp[] >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_compile_store_memory,ci_mono_def,pairTheory.SND] >>
  drule_all intcall_initializer_store_landing >> strip_tac >>
  qexists `u` >> fs[typed_copy_effect_def,venom_state_component_equality]
QED
