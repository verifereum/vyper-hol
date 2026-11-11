(* Counted direct memory return at the actual store endpoint. *)
Theory internalReturnMemorySuffixPtr
Ancestors internalReturnStorePtr internalReturnCountedPtr stmtLowering
  typedMemoryCopy compileEnv fragGasPathPtr

Theorem internal_return_memory_suffix_path_ptr:
  compile_internal_return_from_env ce ty sty (Var src) (Var rpc) sa = ((),sb) /\
  ce.ce_return_buf = SOME (PtrVar (Var dst) cap) /\ ce.ce_returns_count = 0 /\
  ~is_word_type ty /\ (ty = sty \/ is_bytestring_type ty) /\
  n = (if is_bytestring_type ty then 32 + 32 * word_size len
       else type_memory_bytes ce ty) /\ n < dimword (:256) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  (is_bytestring_type ty ==>
    mload (w2n a) s = n2w len /\ ptr_covers G tn src s 32 /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)) /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) /\
  stor_taint_ok cx tn s /\ not_fresh_at sa rpc /\
  lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} ==>
  ?H tm t.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (IntRet <| iret_values := []; iret_adopt_fmp := NONE |> t) /\
    typed_copy_state_frame sa (w2n d) n s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory tv v (w2n d) m) /\
    stor_taint_ok cx tm t /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, compile_internal_return_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory ce (Var src) (Var dst) ty sty sa = (uval,sm)` >>
  Cases_on `uval` >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_store_memory,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND,
      fragExecTheory.cs_extends_emit_inst] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all internal_return_store_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK t)` >>
  `lookup_var rpc t = SOME pc /\ op_taint tm (Var rpc) = {}` by metis_tac[] >>
  `gas_path_ptr D 0 ctx func PG H tm t 0 H tm
    (IntRet <| iret_values := []; iret_adopt_fmp := NONE |> t)` by
    (irule emit_ret_values_path_ptr >> simp[ptrDisciplineTheory.allocas_from_def] >>
     qexistsl_tac [`[]`, `pc`, `rpc`, `sm`, `sb`] >>
     simp[venomStateTheory.eval_operands_def]) >>
  qexistsl_tac [`H`, `tm`, `t`] >> simp[] >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0] >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
  simp[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality] >>
  strip_tac >> gvs[bodyPtrDefsTheory.stor_taint_ok_def]
QED
