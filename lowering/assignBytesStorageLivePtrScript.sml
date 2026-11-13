(* Actual live bytestring copy; the semantic landing is cnt-parametric. *)
Theory assignBytesStorageLivePtr
Ancestors
  storeSlotsPtrBytesCount storeSlotsPtrWordCopy assignBasePtrStorageLoop
  assignStorageExecFramePtr assignStorageBlockFramePtr stmtLoweringMono exprLoweringProps exprOperandVar
  typedMemoryCopy stmtLowering context compileEnv emitHelper emitHelperProps
  loweringStateRelDefs fragExec fragGasPathPtr stateFrame venomState
  ptrDiscipline arithmetic words finite_map list
Libs monadsyntax

Theorem bytes_storage_live_code[local]:
  is_bytestring_type dty /\ is_bytestring_type sty ==>
  compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    (Var root) F loc dty sty capacity =
  do cnt <- compile_bytestring_word_count (Var root);
     compile_word_copy_loop_op (Var root) dst cnt LocMemory
       (if tr then LocTransient else LocStorage) F;
     return () od
Proof
  strip_tac >>
  `is_abi_dynamic cenv.ce_struct_fields dty` by
    (Cases_on `dty` >> gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
     Cases_on `b` >> gvs[is_bytestring_type_def, is_abi_dynamic_def] >>
     Cases_on `b'` >> gvs[is_bytestring_type_def, is_abi_dynamic_def]) >>
  Cases_on `tr` >>
  simp[FUN_EQ_THM, compile_assign_value_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  simp[Once compile_store_slots_def,comp_bind_def,comp_return_def,
    comp_ignore_bind_def]
QED

Theorem bytes_count_operand_ready[local]:
  compile_bytestring_word_count src sa = (cnt,sm) ==>
  ci_mono sa sm /\ ?out. cnt = Var out /\ not_fresh_at sm out
Proof
  simp[compile_bytestring_word_count_def, comp_bind_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac typed_copy_emit_op_mono >>
  conj_tac
  >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  qpat_x_assum `emit_op SHR _ _ = _` mp_tac >>
  simp[emit_op_def,comp_bind_def,comp_ignore_bind_def,fresh_var_def,
    emit_def,emit_inst_def,fresh_id_def,comp_return_def] >>
  strip_tac >> gvs[not_fresh_at_def,ASCIInumbersTheory.toString_inj]
QED

Theorem bytes_storage_live_compile_cuts[local]:
  is_bytestring_type dty /\ is_bytestring_type sty /\
  compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    (Var root) F loc dty sty dst_capacity sa = (z,sb) ==>
  ?out sm result.
    compile_bytestring_word_count (Var root) sa=(Var out,sm) /\
    compile_word_copy_loop_op (Var root) dst (Var out) LocMemory
      (if tr then LocTransient else LocStorage) F sm=(result,sb) /\
    ci_mono sa sm /\ ci_mono sm sb /\ not_fresh_at sm out
Proof
  strip_tac >>
  `compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    (Var root) F loc dty sty dst_capacity =
    do cnt <- compile_bytestring_word_count (Var root);
       compile_word_copy_loop_op (Var root) dst cnt LocMemory
         (if tr then LocTransient else LocStorage) F;
       return () od` by (irule bytes_storage_live_code >> simp[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >>
  simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_word_count (Var root) sa=(cnt,sm)` >>
  drule bytes_count_operand_ready >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  metis_tac[ci_mono_compile_word_copy_loop_op,pairTheory.SND]
QED

Theorem bytes_storage_live_copy_counted_ptr:
  compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    (Var root) F loc dty sty dst_capacity sa = (z,sb) /\
  is_bytestring_type dty /\ is_bytestring_type sty /\
  copied = (len+63) DIV 32 /\ 0<copied /\ copied<dimword (:256) /\
  32 <= read_capacity /\ 32*copied <= read_capacity /\ len+63<dimword (:256) /\
  w2n a+32*(copied-1)<dimword (:256) /\
  fn_has_code sa sb func /\ not_fresh_at sa root /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn root s read_capacity /\ lookup_var root s = SOME a /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    mem_word_at (w2n a) m = n2w len) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
    execution_frame u = execution_frame
      (store_copy_prefix (if tr then LocTransient else LocStorage) a k s copied) /\
    assign_base_store_frame (if tr then LocTransient else LocStorage)
      a k s tn copied u tf /\
    store_slots_ptr_frame tr a k s tn (GENLIST I copied) u tf /\
    ptr_covers Gf tf root u read_capacity /\ lookup_var root u = SOME a /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all bytes_storage_live_compile_cuts >>
  disch_then (qx_choosel_then [`out`,`sm`,`result`] strip_assume_tac) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  mp_tac (Q.INST [`fn` |-> `func`,`sb` |-> `sm`,
    `capacity` |-> `read_capacity`]
    (SPEC_ALL store_slots_bytestring_count_counted)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `s1.vs_labels=s.vs_labels /\ s1.vs_call_ctx=s.vs_call_ctx` by
    (qpat_x_assum `execution_frame s1 = _` mp_tac >>
     simp[execution_frame_def]) >>
  `eval_operand dst s1=eval_operand dst s /\
   op_prov g1 dst=op_prov G dst /\ op_taint t1 dst=op_taint tn dst` by
    (irule store_slots_operand_transport >> simp[] >> metis_tac[]) >>
  `eval_operand dst s1=SOME k /\ op_taint t1 dst={}` by asm_rewrite_tac[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (qpat_assum `ci_mono sa sm` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[compiler_ci_mono_not_fresh]) >>
  `!x. dst=Var x \/ Var out=Var x ==> not_fresh_at sm x` by
    (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` mp_tac >>
     qpat_assum `!x. dst=Var x ==> not_fresh_at sa x` mp_tac >>
     qpat_assum `not_fresh_at sm out` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `not_fresh_at sm root` by simp[] >>
  `!x. dst=Var x \/ out=x ==> not_fresh_at sm x` by
    (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `lookup_var root s1 = SOME a /\ ~s1.vs_call_ctx.cc_static` by
    (asm_rewrite_tac[] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`tr`,`root`,`dst`,`Var out`,`copied`,`sm`,`result`,
    `sb`,`func`,`s1`,`g1`,`t1`,`ctx`,`D`,`PG`,`a`,`k`,`read_capacity`]
    store_slots_word_copy_op_prefix_counted) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[eval_operand_def,op_prov_def])) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf`
    (qx_choose_then `u` strip_assume_tac))) >>
  `execution_frame (store_copy_prefix
      (if tr then LocTransient else LocStorage) a k s1 copied) =
   execution_frame (store_copy_prefix
      (if tr then LocTransient else LocStorage) a k s copied)` by
    (irule store_copy_prefix_execution_frame >> first_assum ACCEPT_TAC) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
    a k s tn 0 s1 t1` by
    (qpat_assum `execution_frame s1 = _` mp_tac >>
     simp[execution_frame_def,assign_base_store_frame_def,
       assign_base_store_prefix_zero,assign_base_store_taint_prefix_def]) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
    a k s tn copied u tf` by
    (qpat_assum `assign_base_store_frame _ _ _ _ _ copied u tf` mp_tac >>
     qpat_assum `assign_base_store_frame _ _ _ _ _ 0 s1 t1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     mp_tac (Q.INST [`loc` |-> `if tr then LocTransient else LocStorage`,
       `b` |-> `a`,`s0` |-> `s`,`tn0` |-> `tn`,`i` |-> `0`,
       `s` |-> `s1`,`tn` |-> `t1`,`j` |-> `copied`]
       (SPEC_ALL assign_base_store_frame_block)) >>
     simp[ADD_CLAUSES,WORD_MULT_CLAUSES,WORD_ADD_0]) >>
  `store_slots_ptr_frame tr a k s tn (GENLIST I copied) u tf` by
    (irule store_slots_word_copy_frame >> asm_rewrite_tac[] >> metis_tac[]) >>
  qexistsl_tac [`gf`,`tf`,`u`] >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`,`m` |-> `0`]
        gas_path_ptr_then)) >> goal_assum (drule_at Any) >> simp[]) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `not_fresh_at sm x` by simp[] >>
  metis_tac[]
QED
