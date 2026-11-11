(* Bytes assignment stages at the physical source capacity, not the
   semantic post capacity or the destination capacity. *)
Theory bodyIntCallFamStmtMutationBytesAssign
Ancestors
  bodyIntCallFamStmtMutationBytesInit bodyIntCallFamStmtMutationStaging
  bodyIntCallJointContract exprLoweringProps valueCopyBytes valueEncodingTyping
  placeMemoryCopyEffect freshWrites compileEnv venomState venomInst fragGasMode
  stmtSimAugAssignPlaceMemory localPtrsProps loweringHalt stmtLowering exprSimProps fragExec

Theorem intcall_bytes_staged_store:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer (type_memory_bytes ce physical) sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src (type_memory_bytes ce physical) sm = ((),sn) /\
  compile_store_memory ce buf.buf_operand dst dty physical sn = ((),sb) /\
  is_bytestring_type dty /\ is_bytestring_type a /\ is_bytestring_type physical /\
  evaluate_type tenv a = SOME av /\ evaluate_type tenv dty = SOME dv /\
  evaluate_type tenv physical = SOME pv /\
  value_has_type av v /\ value_has_type dv v /\ value_has_type pv v /\
  val_in_memory av v (w2n sw) s.vs_memory /\
  type_memory_bytes ce a = type_memory_size av /\
  type_memory_bytes ce physical = type_memory_size pv /\
  type_memory_size pv + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ (!lbl. src <> Label lbl) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
  fn_has_code sn sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  fp.jc_lo <= b /\ b <= w2n dw /\ w2n dw + type_memory_size dv <= b+k /\
  (!name p n. local_region ce es.scopes s name p n ==>
     regions_disjoint b k p n) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es sa s es sn t /\
    val_in_memory dv v (w2n dw) u.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func sn sb t u (w2n dw) (type_memory_size dv) /\
    intcall_expr_res fp ce env es sb u
Proof
  strip_tac >>
  `val_in_memory pv v (w2n sw) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_wf pv v` by metis_tac[value_has_type_val_wf] >>
  `type_memory_size pv < dimword (:256)` by decide_tac >>
  fs[] >>
  drule_all (intcall_staging_initialize |>
    Q.INST [`n` |-> `type_memory_size pv`, `tv` |-> `pv`] |> SRULE []) >>
  strip_tac >> suspend "store"
QED

Resume intcall_bytes_staged_store[store]:
  `sa.cs_next_var <= sn.cs_next_var` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
      ci_mono_def,pairTheory.SND,arithmeticTheory.LESS_EQ_TRANS] >>
  `t.vs_labels = s.vs_labels` by metis_tac[aug_place_marked_path_labels] >>
  `eval_operand dst t = SOME dw` by
    (Cases_on `dst` >> fs[intcall_expr_cont_def,eval_operand_def] >> metis_tac[]) >>
  `!x. dst = Var x ==> not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME (b,k)` by
    (fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `!name p n. local_region ce es.scopes t name p n ==>
     regions_disjoint b k p n` by
    (map_every qx_gen_tac [`name`,`addr`,`n`] >> strip_tac >>
     `local_region ce es.scopes s name addr n` by
       (irule local_region_frame >> conj_tac
        >- (qexists `fp.jc_func` >>
            fs[intcall_expr_res_def,stmt_state_rel_def,state_rel_def]) >>
        qexistsl [`sa`,`es.scopes`,`t`] >>
        fs[intcall_expr_res_def,intcall_expr_cont_def]) >> metis_tac[]) >>
  suspend "apply_store"
QED

Resume intcall_bytes_staged_store[apply_store]:
  `intcall_expr_res fp ce env es sn t /\ ~t.vs_halted /\
   t.vs_current_bb = sn.cs_current_bb /\
   t.vs_inst_idx = LENGTH sn.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sn x` by simp[] >>
  `?u. val_in_memory dv v (w2n dw) u.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func sn sb t u (w2n dw) (type_memory_size dv) /\
    intcall_expr_res fp ce env es sb u` by
    (irule intcall_bytes_initializer_store >> simp[] >>
     metis_tac[]) >>
  qexistsl [`t`,`u`] >> simp[]
QED

Finalise intcall_bytes_staged_store

Theorem intcall_bytes_initializer_run:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_assign_value ce dst LocMemory src F loc dty physical info bytes sa = ((),sb) /\
  is_bytestring_type dty /\ is_bytestring_type a /\ is_bytestring_type physical /\
  evaluate_type tenv a = SOME av /\ evaluate_type tenv dty = SOME dv /\
  evaluate_type tenv physical = SOME pv /\
  value_has_type av v /\ value_has_type dv v /\ value_has_type pv v /\
  val_in_memory av v (w2n sw) s.vs_memory /\
  type_memory_bytes ce a = type_memory_size av /\
  type_memory_bytes ce physical = type_memory_size pv /\
  type_memory_size av + 64 < dimword (:256) /\
  type_memory_size pv + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ (!lbl. src <> Label lbl) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  fp.jc_lo <= b /\ b <= w2n dw /\ w2n dw + type_memory_size dv <= b+k /\
  (!name p n. local_region ce es.scopes s name p n ==>
     regions_disjoint b k p n) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    val_in_memory dv v (w2n dw) u.vs_memory /\
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
      rename1 `compile_alloc_buffer (type_memory_size pv) sa = (buf,sm)` >>
      rename1 `compile_copy_memory buf.buf_operand src (type_memory_size pv) sm = (ret,sn)` >>
      Cases_on `ret` >>
      `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb` by
        metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
          ci_mono_compile_store_memory,ci_mono_def,pairTheory.SND] >>
      `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
       fn_has_code sn sb fp.jc_func` by
        metis_tac[fn_has_code_split,cs_extends_trans] >>
      suspend "staged") >>
  simp[] >> strip_tac >> suspend "direct"
QED

Resume intcall_bytes_initializer_run[staged]:
  `?t u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es sa s es sn t /\
    val_in_memory dv v (w2n dw) u.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func sn sb t u (w2n dw) (type_memory_size dv) /\
    intcall_expr_res fp ce env es sb u` by
    (irule intcall_bytes_staged_store >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists `u` >>
  fs[intcall_expr_cont_def,typed_copy_effect_def,venom_state_component_equality] >>
  conj_tac
  >- (irule (gas_marked_path_then |>
        Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
      qexists `t` >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
      ci_mono_def,pairTheory.SND,arithmeticTheory.LESS_EQ_TRANS] >>
  metis_tac[not_fresh_at_mono]
QED

Resume intcall_bytes_initializer_run[direct]:
  `?u. val_in_memory dv v (w2n dw) u.vs_memory /\
    typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u (w2n dw) (type_memory_size dv) /\
    intcall_expr_res fp ce env es sb u` by
    (irule intcall_bytes_initializer_store >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexists `u` >>
  fs[typed_copy_effect_def,venom_state_component_equality]
QED

Finalise intcall_bytes_initializer_run
