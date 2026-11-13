(*
 * An internal return's whole code, lock release then the stack or memory
 * suffix, from the state before the release.  The return's state is the
 * release of a state framed like the pre-release state, the form intret_q
 * asks for.
 *
 * TOP-LEVEL:
 *   internal_return_stack_unlock_path_ptr  -- release, then a stack return
 *   internal_return_memory_unlock_path_ptr -- release, then a memory return
 *)
Theory internalReturnUnlockSuffixPtr
Ancestors
  internalReturnUnlockPtr internalReturnStackSuffixPtr
  internalReturnMemorySuffixPtr stmtLoweringMono stmtLowering stmtSimReturn
  compileEnv exprLoweringProps fragExec fragGasPathPtr bodyPtrDefs
  ptrDiscipline venomState typedMemoryCopy stateFrame loweringStateRelDefs

(* Helper: the release's code, then the rest of the return. *)
Theorem return_unlock_split[local]:
  compile_internal_return_from_env ce ty sty op rpc sa = ((),sb) /\
  compile_return_unlock ce sa = ((),su) /\
  (!off sz. ce.ce_return_buf <> SOME (MemLoc off sz)) /\
  fn_has_code sa sb func ==>
  fn_has_code sa su func /\ fn_has_code su sb func
Proof
  strip_tac >>
  `ci_mono sa su` by
    (qspecl_then [`ce`, `sa`] mp_tac ci_mono_compile_return_unlock >>
     simp[]) >>
  `?ets rb. compile_internal_return ce (SOME op) rpc ce.ce_returns_count
      ty sty ets rb su = ((),sb)` by
    (qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_internal_return_from_env_def, comp_ignore_bind_def,
          comp_bind_def] >>
     Cases_on `ce.ce_return_buf` >>
     TRY (rename1 `ce.ce_return_buf = SOME loc` >> Cases_on `loc`) >>
     gvs[comp_return_def] >> metis_tac[]) >>
  `ci_mono su sb` by
    metis_tac[cj 1 ci_mono_return_helpers, pairTheory.SND] >>
  metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def]
QED

(* Helper: the release state, the facts the suffix needs at it. *)
Theorem return_unlock_start:
  !ce ty sty op rpc sa sb func ctx s cx tn D PG G.
  compile_internal_return_from_env ce ty sty op rpc sa = ((),sb) /\
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  (!off sz. ce.ce_return_buf <> SOME (MemLoc off sz)) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ stor_taint_ok cx tn s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?su tu tr i0.
    compile_return_unlock ce sa = ((),su) /\ fn_has_code su sb func /\
    return_unlock_state ce s =
      s with <| vs_transient := tr; vs_inst_idx := i0 |> /\
    i0 = LENGTH su.cs_current_insts /\ su.cs_current_bb = sa.cs_current_bb /\
    (!x. not_fresh_at sa x ==> not_fresh_at su x) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tu
      (OK (s with <| vs_transient := tr; vs_inst_idx := i0 |>)) /\
    stor_taint_ok cx tu (s with <| vs_transient := tr; vs_inst_idx := i0 |>) /\
    tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\ tu.t_imm = tn.t_imm /\
    (!op. op_taint tu op = op_taint tn op)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_return_unlock ce sa` >> rename1 `_ = (uu,su)` >>
  Cases_on `uu` >>
  `fn_has_code sa su func /\ fn_has_code su sb func` by
    metis_tac[return_unlock_split] >>
  drule_all compile_return_unlock_code_idx >> strip_tac >>
  `?tu. gas_path_ptr D 0 ctx func PG G tn s 0 G tu
          (OK (return_unlock_state ce s)) /\
        stor_taint_ok cx tu (return_unlock_state ce s) /\
        tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\ tu.t_imm = tn.t_imm /\
        (!p. op_taint tu (Var p) = op_taint tn (Var p))` by
    (irule return_unlock_path_ptr >> simp[] >> metis_tac[]) >>
  `?tr i0. return_unlock_state ce s =
             s with <| vs_transient := tr; vs_inst_idx := i0 |>` by
    metis_tac[return_unlock_state_shape] >>
  qexistsl_tac [`su`, `tu`, `tr`, `i0`] >>
  rpt conj_tac >>
  FIRST [
    first_assum ACCEPT_TAC,
    (qpat_x_assum `(return_unlock_state ce s).vs_inst_idx = _` mp_tac >>
     asm_simp_tac (srw_ss()) [] >> NO_TAC),
    (Cases >> fs[op_taint_def] >> NO_TAC),
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[] >> NO_TAC),
    metis_tac[]]
QED

Theorem internal_return_stack_unlock_path_ptr:
  compile_internal_return_from_env ce ty sty op (Var rpc) sa = ((),sb) /\
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  (!off sz. ce.ce_return_buf <> SOME (MemLoc off sz)) /\
  0 < ce.ce_returns_count /\
  ets = (case ty of TupleT ts => ts | StructT ns =>
    MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string ns))
    | _ => []) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ stor_taint_ok cx tn s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa rpc /\ lookup_var rpc s = SOME pc /\
  op_taint tn (Var rpc) = {} /\
  (ets = [] ==> eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  (ets <> [] ==> op = Var src /\ not_fresh_at sa src /\
    lookup_var src s = SOME bw /\
    (!i. i < LENGTH ets ==>
      ptr_covers G tn src s
        (SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32) /\
      w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32 <= dimword (:256) /\
      (!j. w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) <= j /\
        j < w2n bw + SUM (MAP (type_memory_bytes ce) (TAKE i ets)) + 32 ==>
        j NOTIN tn.t_mem))) ==>
  ?t H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (IntRet <| iret_values := (if ets = [] then [w]
        else tuple_words ce bw ets 0 s.vs_memory); iret_adopt_fmp := NONE |>
        (return_unlock_state ce t)) /\
    stor_taint_ok cx tm (return_unlock_state ce t) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ets = _`
    (fn th => assume_tac
      (EQ_MP (SYM (SPEC (concl th) markerTheory.Abbrev_def)) th)) >>
  qspecl_then [`ce`, `ty`, `sty`, `op`, `Var rpc`, `sa`, `sb`, `func`, `ctx`,
    `s`, `cx`, `tn`, `D`, `PG`, `G`] mp_tac return_unlock_start >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[]) >> strip_tac >>
  qabbrev_tac `u = s with <| vs_transient := tr; vs_inst_idx := i0 |>` >>
  `!x. lookup_var x u = lookup_var x s` by simp[Abbr `u`, lookup_var_def] >>
  `!o'. eval_operand o' u = eval_operand o' s` by
    (Cases >> simp[Abbr `u`, eval_operand_def, lookup_var_def]) >>
  `!x n. ptr_covers G tu x u n <=> ptr_covers G tn x s n` by
    asm_simp_tac (srw_ss()) [ptr_covers_def] >>
  `~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
   u.vs_inst_idx = LENGTH su.cs_current_insts /\
   u.vs_memory = s.vs_memory` by simp[Abbr `u`] >>
  qspecl_then [`ce`, `ty`, `sty`, `op`, `rpc`, `sa`, `sb`, `su`, `ets`,
    `func`, `ctx`, `u`, `pc`, `tu`, `w`, `src`, `bw`, `G`, `D`, `PG`] mp_tac
    (Q.GENL [`ce`, `ty`, `sty`, `op`, `rpc`, `sa0`, `sb`, `sa`, `ets`,
      `func`, `ctx`, `s`, `pc`, `tn`, `w`, `src`, `bw`, `G`, `D`, `PG`]
      internal_return_stack_suffix_path_ptr) >>
  impl_tac
  >- (rpt conj_tac >>
      TRY (FIRST [first_assum ACCEPT_TAC,
        first_assum (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def]),
        (asm_simp_tac (srw_ss()) [] >> NO_TAC),
        (strip_tac >> qpat_x_assum `_ = [] ==> _` drule >> strip_tac >>
         asm_simp_tac (srw_ss()) [] >> NO_TAC)]) >>
      strip_tac >> qpat_x_assum `_ <> [] ==> _` drule >> strip_tac >>
      metis_tac[]) >>
  strip_tac >>
  rename1 `gas_path_ptr D 0 ctx func PG G tu u 0 H tm (IntRet _ f)` >>
  `?i. f = return_unlock_state ce
             (f with <| vs_transient := s.vs_transient; vs_inst_idx := i |>)` by
    (mp_tac (Q.SPECL [`ce`, `f`, `s`]
       (Q.GENL [`ce`, `t`, `t0`] return_unlock_state_from_final)) >>
     impl_tac
     >- (rpt conj_tac >>
         FIRST [first_assum ACCEPT_TAC, (fs[Abbr `u`] >> NO_TAC)]) >>
     disch_then ACCEPT_TAC) >>
  qexistsl_tac [`f with <| vs_transient := s.vs_transient; vs_inst_idx := i |>`,
    `H`, `tm`] >>
  pop_assum (SUBST1_TAC o SYM) >>
  `f.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `state_frame f = _` mp_tac >>
     simp[Abbr `u`, state_frame_def, venom_state_component_equality]) >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0] >>
  rpt conj_tac >>
  FIRST [
    (fs[Abbr `u`] >> NO_TAC),
    (qpat_x_assum `stor_taint_ok cx tu u` mp_tac >>
     fs[Abbr `u`, stor_taint_ok_cx_dead, stor_taint_ok_at_def] >> NO_TAC),
    (qpat_x_assum `state_frame f = _` mp_tac >>
     simp[Abbr `u`, state_frame_def, venom_state_component_equality] >> NO_TAC),
    (rpt strip_tac >> res_tac >> fs[Abbr `u`, lookup_var_def] >> NO_TAC)]
QED

Theorem internal_return_memory_unlock_path_ptr:
  compile_internal_return_from_env ce ty sty (Var src) (Var rpc) sa = ((),sb) /\
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  ce.ce_return_buf = SOME (PtrVar (Var dst) cap) /\ ce.ce_returns_count = 0 /\
  ~is_word_type ty /\ (ty = sty \/ is_bytestring_type ty) /\
  n = (if is_bytestring_type ty then 32 + 32 * word_size len
       else type_memory_bytes ce ty) /\ n < dimword (:256) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~s.vs_call_ctx.cc_static /\
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
      (IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (return_unlock_state ce t)) /\
    typed_copy_state_frame sa (w2n d) n s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory tv v (w2n d) m) /\
    stor_taint_ok cx tm (return_unlock_state ce t) /\
    tm.t_stor = tn.t_stor /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `n = _`
    (fn th => assume_tac
      (EQ_MP (SYM (SPEC (concl th) markerTheory.Abbrev_def)) th)) >>
  qspecl_then [`ce`, `ty`, `sty`, `Var src`, `Var rpc`, `sa`, `sb`, `func`,
    `ctx`, `s`, `cx`, `tn`, `D`, `PG`, `G`] mp_tac return_unlock_start >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[]) >> strip_tac >>
  qabbrev_tac `u = s with <| vs_transient := tr; vs_inst_idx := i0 |>` >>
  `!x. lookup_var x u = lookup_var x s` by simp[Abbr `u`, lookup_var_def] >>
  `!k. mload k u = mload k s` by simp[Abbr `u`, mload_def] >>
  `!x k. ptr_covers G tu x u k <=> ptr_covers G tn x s k` by
    asm_simp_tac (srw_ss()) [ptr_covers_def] >>
  `~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
   u.vs_inst_idx = LENGTH su.cs_current_insts /\
   u.vs_memory = s.vs_memory` by simp[Abbr `u`] >>
  qspecl_then [`ce`, `ty`, `sty`, `src`, `rpc`, `sa`, `sb`, `su`, `dst`,
    `cap`, `n`, `len`, `func`, `u`, `ctx`, `a`, `d`, `G`, `tu`, `tv`, `v`,
    `cx`, `pc`, `D`, `PG`] mp_tac
    (Q.GENL [`ce`, `ty`, `sty`, `src`, `rpc`, `sa0`, `sb`, `sa`, `dst`,
      `cap`, `n`, `len`, `func`, `s`, `ctx`, `a`, `d`, `G`, `tn`, `tv`, `v`,
      `cx`, `pc`, `D`, `PG`] internal_return_memory_suffix_path_ptr) >>
  impl_tac
  >- (rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
        first_assum (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def]),
        (asm_simp_tac (srw_ss()) [] >> NO_TAC)]) >>
  strip_tac >>
  rename1 `gas_path_ptr D 0 ctx func PG G tu u 0 H tm (IntRet _ f)` >>
  `f.vs_transient = tr /\ f.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ u f` mp_tac >>
     simp[Abbr `u`, typed_copy_state_frame_def,
          venom_state_component_equality]) >>
  `?i. f = return_unlock_state ce
             (f with <| vs_transient := s.vs_transient; vs_inst_idx := i |>)` by
    (mp_tac (Q.SPECL [`ce`, `f`, `s`]
       (Q.GENL [`ce`, `t`, `t0`] return_unlock_state_from_final)) >>
     impl_tac
     >- (rpt conj_tac >>
         FIRST [first_assum ACCEPT_TAC, (fs[Abbr `u`] >> NO_TAC)]) >>
     disch_then ACCEPT_TAC) >>
  qexistsl_tac [`H`, `tm`,
    `f with <| vs_transient := s.vs_transient; vs_inst_idx := i |>`] >>
  pop_assum (SUBST1_TAC o SYM) >>
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

Theorem internal_return_none_unlock_path_ptr:
  compile_return_unlock ce sa = ((),su) /\
  emit_inst RET [Var rpc] [] su = ((),sb) /\
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ stor_taint_ok cx tn s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} ==>
  ?tm. gas_path_ptr D 0 ctx func PG G tn s 0 G tm
         (IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
           (return_unlock_state ce s)) /\
       stor_taint_ok cx tm (return_unlock_state ce s)
Proof
  strip_tac >>
  `ci_mono sa su` by
    (qspecl_then [`ce`, `sa`] mp_tac ci_mono_compile_return_unlock >>
     simp[]) >>
  `cs_extends su sb` by metis_tac[fragExecTheory.cs_extends_emit_inst] >>
  `fn_has_code sa su func /\ fn_has_code su sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def] >>
  drule_all compile_return_unlock_code_idx >> strip_tac >>
  `?tu. gas_path_ptr D 0 ctx func PG G tn s 0 G tu
          (OK (return_unlock_state ce s)) /\
        stor_taint_ok cx tu (return_unlock_state ce s) /\
        tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\ tu.t_imm = tn.t_imm /\
        (!p. op_taint tu (Var p) = op_taint tn (Var p))` by
    (irule return_unlock_path_ptr >> simp[] >> metis_tac[]) >>
  `?tr i0. return_unlock_state ce s =
             s with <| vs_transient := tr; vs_inst_idx := i0 |>` by
    metis_tac[return_unlock_state_shape] >>
  `gas_path_ptr D 0 ctx func PG G tu (return_unlock_state ce s) 0 G tu
     (IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
       (return_unlock_state ce s))` by
    (irule internalReturnCountedPtrTheory.emit_ret_values_path_ptr >>
     rpt conj_tac >> TRY (qexistsl_tac [`[]`, `pc`, `rpc`, `su`, `sb`]) >>
     gvs[ptrDisciplineTheory.allocas_from_def, eval_operands_def,
         lookup_var_def]) >>
  qexists_tac `tu` >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0]
QED

(* intret_q's witness is the state before the release. *)
Theorem intret_q_unlock_intro:
  LENGTH ir.iret_values = cenv.ce_returns_count /\
  result_rel func ret_tv cenv cx (INR (ReturnException v), es) (IntRet ir s) ==>
  intret_q func cenv cx ret_tv v es (IntRet ir (return_unlock_state cenv s))
Proof
  rw[intret_q_def] >> qexistsl_tac [`s`, `(return_unlock_state cenv s).vs_inst_idx`] >>
  simp[venom_state_component_equality]
QED

(* The same at any instruction index: RET may sit at the start of a block
   that a looping copy opened after the release. *)
Theorem intret_q_unlock_idx_intro:
  LENGTH ir.iret_values = cenv.ce_returns_count /\
  result_rel func ret_tv cenv cx (INR (ReturnException v), es) (IntRet ir s) ==>
  intret_q func cenv cx ret_tv v es
    (IntRet ir (return_unlock_state cenv s with vs_inst_idx := i))
Proof
  rw[intret_q_def] >> metis_tac[]
QED
