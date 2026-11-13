(*
 * Widened compound internal return at the store endpoint, with the ghost:
 * the pointer twin of stmtSimReturnWiden's
 * compile_internal_return_memory_widen_frag (compound branch).  The source
 * value, robust under tainted memory, is copied by
 * compile_store_memory_typed into the caller's return buffer, which must
 * not overlap the source; then RET.
 *
 * TOP-LEVEL:
 *   internal_return_memory_widen_suffix_path_ptr -- the store and RET after
 *     the lock release
 *   compile_internal_return_memory_widen_ptr
 *)
Theory internalReturnWidenPtr
Ancestors internalReturnStorePtr internalReturnCountedPtr
  internalReturnMemorySuffixPtr internalReturnUnlockSuffixPtr
  internalReturnUnlockPtr aggregateStorePtr stmtLowering typedMemoryCopy
  compileEnv fragGasPathPtr stmtSimReturn venomState bodyPtrDefs loweringStateRelDefs

Theorem internal_return_memory_widen_suffix_path_ptr:
  compile_internal_return_from_env ce ty sty (Var src) (Var rpc) sa0 = ((),sb) /\
  compile_return_unlock ce sa0 = ((),sa) /\
  ce.ce_return_buf = SOME (PtrVar (Var dst) cap) /\ ce.ce_returns_count = 0 /\
  sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
  type_widens_to tenv sty ty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv ty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields.
     FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname, fty, sz). !tv.
       evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_memory_bytes ce ty = type_memory_size dtv /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
  w2n a + type_memory_size stv < dimword (:256) /\
  w2n d + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n a) (type_memory_size stv) (w2n d)
    (type_memory_size dtv) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  ptr_covers G tn dst s (type_memory_size dtv) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) /\
  stor_taint_ok cx tn s /\ not_fresh_at sa rpc /\
  lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} ==>
  ?H tm t.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (IntRet <| iret_values := []; iret_adopt_fmp := NONE |> t) /\
    typed_copy_state_frame sa (w2n d) (type_memory_size dtv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n d) m) /\
    stor_taint_ok cx tm t /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [compile_internal_return_from_env_def,
       compile_internal_return_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory ce (Var src) (Var dst) ty sty sa = (uval,sm)` >>
  Cases_on `uval` >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_store_memory,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND,
      fragExecTheory.cs_extends_emit_inst] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  mp_tac (Q.SPECL [`ce`,`tenv`,`ctx`,`D`,`PG`,`ty`,`sty`,`dtv`,`stv`,`v`]
    compile_store_memory_aggregate_counted_ptr) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`sa`,`sm`,`dst`,`Var src`,`d`,`a`,`func`,`G`,`tn`,`s`]
    mp_tac) >>
  impl_tac
  >- (gvs[bodyPtrDefsTheory.ptr_covers_def,
          loweringStateRelDefsTheory.regions_disjoint_def,
          venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  disch_then (qx_choosel_then [`H`,`tm`,`t`] strip_assume_tac) >>
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

Theorem compile_internal_return_memory_widen_ptr:
  compile_internal_return_from_env ce ty sty (Var src) (Var rpc) sa = ((),sb) /\
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  ce.ce_return_buf = SOME (PtrVar (Var dst) cap) /\ ce.ce_returns_count = 0 /\
  sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
  type_widens_to tenv sty ty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv ty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields.
     FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname, fty, sz). !tv.
       evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_memory_bytes ce ty = type_memory_size dtv /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~s.vs_call_ctx.cc_static /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
  w2n a + type_memory_size stv < dimword (:256) /\
  w2n d + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n a) (type_memory_size stv) (w2n d)
    (type_memory_size dtv) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  ptr_covers G tn dst s (type_memory_size dtv) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) /\
  stor_taint_ok cx tn s /\ not_fresh_at sa rpc /\
  lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} ==>
  ?H tm t i.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (return_unlock_state ce t with vs_inst_idx := i)) /\
    typed_copy_state_frame sa (w2n d) (type_memory_size dtv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n d) m) /\
    stor_taint_ok cx tm (return_unlock_state ce t with vs_inst_idx := i) /\
    tm.t_stor = tn.t_stor /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qspecl_then [`ce`, `ty`, `sty`, `Var src`, `Var rpc`, `sa`, `sb`, `func`,
    `ctx`, `s`, `cx`, `tn`, `D`, `PG`, `G`] mp_tac return_unlock_start >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[]) >> strip_tac >>
  qabbrev_tac `u = s with <| vs_transient := tr; vs_inst_idx := i0 |>` >>
  `!x. lookup_var x u = lookup_var x s` by simp[Abbr `u`, lookup_var_def] >>
  `!x k. ptr_covers G tu x u k <=> ptr_covers G tn x s k` by
    asm_simp_tac (srw_ss()) [ptr_covers_def] >>
  `~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
   u.vs_inst_idx = LENGTH su.cs_current_insts /\
   u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx` by
    simp[Abbr `u`] >>
  qspecl_then [`ce`, `ty`, `sty`, `src`, `rpc`, `sa`, `sb`, `su`, `dst`,
    `cap`, `tenv`, `stv`, `dtv`, `v`, `func`, `u`, `ctx`, `a`, `d`, `G`, `tu`,
    `cx`, `pc`, `D`, `PG`] mp_tac
    (Q.GENL [`ce`, `ty`, `sty`, `src`, `rpc`, `sa0`, `sb`, `sa`, `dst`,
      `cap`, `tenv`, `stv`, `dtv`, `v`, `func`, `s`, `ctx`, `a`, `d`, `G`,
      `tn`, `cx`, `pc`, `D`, `PG`] internal_return_memory_widen_suffix_path_ptr) >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
        (asm_simp_tac (srw_ss()) [] >> NO_TAC)]) >>
  strip_tac >>
  rename1 `gas_path_ptr D 0 ctx func PG G tu u 0 H tm (IntRet _ f)` >>
  `f.vs_transient = tr /\ f.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ u f` mp_tac >>
     simp[Abbr `u`, typed_copy_state_frame_def,
          venom_state_component_equality]) >>
  `?i. f with vs_inst_idx := i0 =
       return_unlock_state ce
         (f with <| vs_transient := s.vs_transient; vs_inst_idx := i |>)` by
    (mp_tac (Q.SPECL [`ce`, `f with vs_inst_idx := i0`, `s`]
       (Q.GENL [`ce`, `t`, `t0`] return_unlock_state_from_final)) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >> simp[Abbr `u`]) >>
     simp[]) >>
  qexistsl_tac [`H`, `tm`,
    `f with <| vs_transient := s.vs_transient; vs_inst_idx := i |>`,
    `f.vs_inst_idx`] >>
  `return_unlock_state ce
     (f with <| vs_transient := s.vs_transient; vs_inst_idx := i |>) with
     vs_inst_idx := f.vs_inst_idx = f` by
    (pop_assum (SUBST1_TAC o SYM) >> simp[venom_state_component_equality]) >>
  pop_assum SUBST1_TAC >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0] >>
  rpt conj_tac >>
  FIRST [
    (fs[Abbr `u`] >> NO_TAC),
    (qpat_x_assum `typed_copy_state_frame _ _ _ u f` mp_tac >>
     simp[Abbr `u`, typed_copy_state_frame_def,
          venom_state_component_equality, lookup_var_def] >>
     rpt strip_tac >> res_tac >> fs[lookup_var_def] >> NO_TAC),
    (rpt strip_tac >> res_tac >> fs[Abbr `u`, lookup_var_def] >> NO_TAC)]
QED
