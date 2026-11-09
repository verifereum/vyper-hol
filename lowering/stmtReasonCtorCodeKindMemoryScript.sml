(* The revert encoder's run from a string reason compiled to a pointer into
   the immutables (reason_code_vv) inside a constructor: as at runtime
   (stmtReasonCodeKindMemory), but unwrap_value copies the message out of
   the immutables' memory region, which lies clear of every allocation, so
   the encoder's head leaves it alone. *)
Theory stmtReasonCtorCodeKindMemory
Ancestors
  stmtReasonCodeKindMemory exprSimMemUnwrap
  stmtReasonMemory stmtReasonLitFragMemory
  stmtSimReasonExpr stmtSimReason exprReasonOperand exprOperandVar
  exprSimUnwrapProps exprSimCopy exprSimStorageCopy bodyImmutableCopyMemory
  immutableCopyExecution valueEncodingProps valueEncodingProofs
  stmtSimDefs exprLoweringProps loweringPosts fragGasPathMem fragGasMode
  fragExec fragExecMem instMemFrontier freshWrites venomMemDefs venomInstProps
  exprLowering stmtLowering emitHelper emitHelperProps compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs vfmConstants vyperValue vyperInterpreter
  venomExecSemantics venomState venomInst context
  words list rich_list finite_map arithmetic
Libs
  monadsyntax

(* A window's prefix is the shorter window. *)
Theorem mem_bytes_at_take[local]:
  !off k n mem. k <= n ==> TAKE k (mem_bytes_at off n mem) = mem_bytes_at off k mem
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[LENGTH_TAKE] >> rpt strip_tac >>
  `x < n` by decide_tac >>
  simp[EL_TAKE, EL_mem_bytes_at]
QED

(* The constructor's word copy snapshots memory: the buffer's first word is
   the source's first word, whatever else memory held. *)
Theorem ctor_copy_first_word[local]:
  !a d m s u.
    0 < m /\ w2n a + 32 * m < dimword (:256) /\ d + 32 * m < dimword (:256) /\
    (d + 32 * m <= w2n a \/ w2n a + 32 * m <= d) /\
    mem_word_at (w2n a) s.vs_memory = mem_word_at (w2n a) u.vs_memory ==>
    mem_word_at d (immutable_transfers F T a (n2w d) m 0 s).vs_memory =
    mem_word_at d (immutable_transfers F T a (n2w d) m 0 u).vs_memory
Proof
  rpt strip_tac >>
  `!z. (immutable_transfers F T a (n2w d) m 0 z).vs_memory =
       (mcopy d (w2n a) (32 * m) z).vs_memory` by
    (gen_tac >>
     qspecl_then [`m`, `w2n a`, `d`, `0`, `z`] mp_tac
       (Q.INST [`store` |-> `F`, `ctor` |-> `T`]
          immutable_memory_transfers_snapshot) >>
     simp[n2w_w2n]) >>
  `mem_bytes_at (w2n a) 32 s.vs_memory = mem_bytes_at (w2n a) 32 u.vs_memory` by
    metis_tac[mload_eq_mem_bytes_at_eq, mem_word_at_eq_mload] >>
  qpat_x_assum `!z. _` (fn th => rewrite_tac[th]) >>
  `32 <= 32 * m` by decide_tac >>
  `!z. mem_word_at d (mcopy d (w2n a) (32 * m) z).vs_memory =
       word_of_bytes T (0w:bytes32) (mem_bytes_at (w2n a) 32 z.vs_memory)` by
    (gen_tac >>
     `mem_bytes_at d 32 (mcopy d (w2n a) (32 * m) z).vs_memory =
      mem_bytes_at (w2n a) 32 z.vs_memory` by
       metis_tac[mem_bytes_at_take, mcopy_mem_bytes_at_same] >>
     pop_assum (SUBST1_TAC o GSYM) >>
     simp[mem_word_at_def, mem_bytes_at_def]) >>
  asm_rewrite_tac[]
QED

Theorem reason_ctor_code_revert_path_mem:
  !ctx func cenv cx se es sa vv sm sb s0 ee tv t str n.
    reason_code_vv vv /\ cenv.ce_is_ctor /\
    expr_type se = BaseT (StringT n) /\
    type_memory_bytes cenv (BaseT (StringT n)) < 2 ** 64 /\
    compile_expr cenv (expr_type se) se sa = (vv, sm) /\
    compile_revert_with_reason cenv vv (expr_type se)
      (type_memory_bytes cenv (expr_type se)) sm = ((), sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    vv_post ctx func cenv cx se es sa sm s0 ee tv vv t /\
    read_result cx tv ee = (INL (StringV str), ee) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func t 0 (Abort Revert_abort u)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_type se = _` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  `?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
          p.ptr_location = LocCode` by fs[reason_code_vv_def] >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qspecl_then [`cenv`, `BaseT (StringT n)`, `se`, `sa`,
                  `LocatedValue ty p`, `sm`] mp_tac
       (CONJUNCT1 compiler_compile_var) >>
     simp[vv_operand_def]) >>
  `vv_post ctx func cenv cx se es sa sm s0 ee (Value (StringV str))
     (LocatedValue ty p) t` by metis_tac[vv_post_read_result] >>
  `ty = BaseT (StringT n)` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ (Value _) _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def, post_value_type_bytestring,
          is_bytestring_type_def]) >>
  qpat_x_assum `ty = _` SUBST_ALL_TAC >>
  `?a. eval_operand p.ptr_operand t = SOME a /\
       immutable_holds cenv cx (BaseT (StringT n)) (Value (StringV str))
         a ee t` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ (Value _) _ _` mp_tac >>
     asm_simp_tac (srw_ss()) [vv_post_def, vv_holds_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  qabbrev_tac `k = (n + 31) DIV 32` >>
  qabbrev_tac `Z = 32 + k * 32` >>
  `type_memory_bytes cenv (BaseT (StringT n)) = Z` by
    simp[Abbr `Z`, Abbr `k`, type_memory_bytes_def] >>
  `Z < 2 ** 64` by metis_tac[] >>
  `(Z + 31) DIV 32 = k + 1` by
    (simp[Abbr `Z`] >>
     `32 + k * 32 + 31 = (k + 1) * 32 + 31` by decide_tac >>
     pop_assum SUBST1_TAC >> simp[ADD_DIV_ADD_DIV]) >>
  `n < 2 ** 64` by
    (`(n + 31) MOD 32 < 32 /\
      n + 31 = (n + 31) DIV 32 * 32 + (n + 31) MOD 32` by
       metis_tac[DIVISION, DECIDE ``0n < 32``] >>
     qpat_x_assum `Z < _` mp_tac >> simp[Abbr `Z`, Abbr `k`] >>
     decide_tac) >>
  `k <= n + 31` by simp[Abbr `k`, DIV_LESS_EQ] >>
  `evaluate_type (get_tenv cx) (BaseT (StringT n)) =
     SOME (BaseTV (StringT n))` by
    (simp[evaluate_type_def, type_slot_size_def, word_size_def] >>
     fs[dimword_def, Abbr `k`]) >>
  `type_memory_size (BaseTV (StringT n)) = Z` by
    simp[type_memory_size_def, word_size_def, Abbr `Z`, Abbr `k`] >>
  `type_slot_size (BaseTV (StringT n)) = k + 1` by
    simp[type_slot_size_def, word_size_def, Abbr `k`] >>
  `val_wf (BaseTV (StringT n)) (StringV str) /\ w2n a + Z < dimword (:256)` by
    metis_tac[immutable_holds_bounds] >>
  `LENGTH str + 32 <= Z` by fs[val_wf_def] >>
  `w2n a + Z <= t.vs_alloca_next` by
    metis_tac[ctor_immutable_frontier] >>
  (* the immutable lies clear of every allocation *)
  `!i0 M outs b m. MEM (mk_inst i0 ALLOCA [Lit (n2w M)] outs) (fn_insts func) /\
       FLOOKUP t.vs_allocas i0 = SOME (b, m) ==>
       w2n a + Z <= b \/ b + m <= w2n a` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`uu` |-> `t`]
       (Q.INST [`es` |-> `ee`, `t` |-> `BaseT (StringT n)`,
                `v` |-> `StringV str`, `tv` |-> `BaseTV (StringT n)`,
                `inst` |-> `mk_inst i0 ALLOCA [Lit (n2w M)] outs`,
                `dst` |-> `b`, `sz` |-> `m`]
          immutable_holds_alloca_disjoint)) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[mk_inst_def]) >>
     asm_rewrite_tac[regions_disjoint_def]) >>
  drule compile_revert_reason_shape >>
  disch_then (qx_choosel_then [`op`, `sn`] strip_assume_tac) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) code_unwrap_shape >>
  simp[] >> strip_tac >>
  qabbrev_tac `id0 = sm.cs_next_id` >> qabbrev_tac `v0 = sm.cs_next_var` >>
  qabbrev_tac `out = STRING #"%" (toString (v0 + 3))` >>
  qabbrev_tac `allocI = mk_inst (id0 + 4) ALLOCA [Lit (n2w Z)] [out]` >>
  qabbrev_tac `mid = sm with <|cs_next_var := v0 + 4; cs_next_id := id0 + 5;
      cs_current_insts :=
        sm.cs_current_insts ++ reason_head id0 v0 Z ++ [allocI]|>` >>
  drule code_ctor_copy_insts >> strip_tac >>
  rename1 `sn.cs_current_insts = mid.cs_current_insts ++ cis` >>
  `ci_mono mid sn` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `mid.cs_next_var = v0 + 4 /\ mid.cs_next_id = id0 + 5 /\
   mid.cs_current_bb = sm.cs_current_bb` by simp[Abbr `mid`] >>
  `v0 + 4 <= sn.cs_next_var /\ id0 + 5 <= sn.cs_next_id` by
    (fs[ci_mono_def] >> metis_tac[]) >>
  qabbrev_tac `j = sn.cs_next_id` >> qabbrev_tac `u0 = sn.cs_next_var` >>
  qabbrev_tac `tcode = reason_tail j u0 v0 op` >>
  qabbrev_tac `ecode = reason_head id0 v0 Z ++ [allocI] ++ cis ++ tcode` >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ ecode` by
    (qpat_x_assum `sb = _` SUBST1_TAC >>
     fs[same_blocks_def, Abbr `ecode`, Abbr `tcode`, Abbr `mid`]) >>
  qspecl_then [`sm`, `sb`, `func`, `ecode`] mp_tac fn_has_code_code >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `64 + Z < dimword (:256) /\ Z < dimword (:256)` by
    (qpat_x_assum `Z < 2 ** 64` mp_tac >> simp[dimword_def]) >>
  `alloca_room ctx func t /\ alloca_next_valid t /\
   allocas_non_overlapping t` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `MEM (mk_inst id0 ALLOCA [Lit (n2w (64 + Z))] ["%" ++ toString v0])
       (fn_insts func) /\
   MEM (mk_inst (id0 + 3) ALLOCA [Lit (n2w Z)] ["%" ++ toString (v0 + 2)])
       (fn_insts func) /\
   MEM allocI (fn_insts func) /\
   MEM (mk_inst (j + 5) ALLOCA [Lit 32w] ["%" ++ toString (u0 + 4)])
       (fn_insts func)` by
    (rpt conj_tac >>
     qpat_assum `!i. MEM i ecode ==> MEM i (fn_insts func)` irule >>
     simp[Abbr `ecode`, Abbr `tcode`, reason_head_def, reason_tail_def]) >>
  (* the encoder's head *)
  qspecl_then [`ctx`, `func`, `id0`, `v0`, `Z`, `t`] mp_tac
    reason_head_run_mem >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0`,
            `64 + Z`, `["%" ++ toString v0]`] mp_tac state_rel_site_size >>
          simp[]) >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0 + 3`,
        `Z`, `["%" ++ toString (v0 + 2)]`] mp_tac state_rel_site_size >>
      simp[]) >>
  disch_then (qx_choosel_then [`B`, `TP`] strip_assume_tac) >>
  (* the buffer's ALLOCA *)
  `id0 + 4 <> id0 /\ id0 + 4 <> id0 + 3` by decide_tac >>
  `FLOOKUP s1.vs_allocas (id0 + 4) = FLOOKUP t.vs_allocas (id0 + 4)` by
    metis_tac[] >>
  qspecl_then [`ctx`, `func`, `id0 + 4`, `Z`, `out`, `s1`] mp_tac
    alloca_step_props >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- fs[Abbr `allocI`] >>
      rpt gen_tac >> strip_tac >>
      `FLOOKUP t.vs_allocas (id0 + 4) = SOME (b, m)` by metis_tac[] >>
      `m = Z` by
        (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0 + 4`,
           `Z`, `[out]`] mp_tac state_rel_site_size >>
         impl_tac >- fs[Abbr `allocI`] >>
         disch_then drule >> simp[]) >>
      `b + m <= t.vs_alloca_next` by metis_tac[alloca_next_valid_def] >>
      decide_tac) >>
  disch_then (qx_choosel_then [`bw`, `A`, `N`] strip_assume_tac) >>
  qabbrev_tac `s2 = update_var out (n2w bw)
                      (s1 with <| vs_allocas := A; vs_alloca_next := N |>)` >>
  `N < dimword (:256)` by
    (drule alloca_room_next_lt >> simp_tac (srw_ss()) []) >>
  `step_inst_base allocI s1 = OK s2` by
    (simp[Abbr `allocI`, Abbr `s2`] >> first_assum ACCEPT_TAC) >>
  `run_inst_seq (reason_head id0 v0 Z ++ [allocI]) t = OK s2` by
    (drule run_inst_seq_append >> simp[run_inst_seq_def]) >>
  `s2.vs_data_section = t.vs_data_section /\ s2.vs_labels = t.vs_labels` by
    (drule run_inst_seq_data_section >>
     simp[reason_head_def, Abbr `allocI`, mk_inst_def, is_terminator_def]) >>
  `s2.vs_alloca_next = N /\ s2.vs_allocas = A` by
    simp[Abbr `s2`, update_var_def] >>
  `!x. lookup_var x s2 = if x = out then SOME (n2w bw) else lookup_var x s1` by
    simp[Abbr `s2`, lookup_var_update_var, lookup_var_def] >>
  `"%" ++ toString v0 <> out /\ "%" ++ toString (v0 + 1) <> out /\
   "%" ++ toString (v0 + 2) <> out` by
    simp_tac (srw_ss() ++ ARITH_ss) [Abbr `out`, ASCIInumbersTheory.toString_11] >>
  `!x. p.ptr_operand = Var x ==>
       !k. x <> STRING #"%" (toString (v0 + k))` by
    (rpt strip_tac >> res_tac >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `v0 + k` mp_tac) >> simp[Abbr `v0`]) >>
  `eval_operand p.ptr_operand s2 = SOME a` by
    (Cases_on `p.ptr_operand` >> fs[eval_operand_def] >>
     rename1 `Var x` >>
     `x <> "%" ++ toString v0 /\ x <> "%" ++ toString (v0 + 1) /\
      x <> "%" ++ toString (v0 + 2) /\ x <> out` by
       (qpat_x_assum `!k. x <> _` (fn th =>
          MAP_EVERY (fn n => assume_tac (SPEC n th))
            [``0n``, ``1n``, ``2n``, ``3n``]) >>
        fs[Abbr `out`]) >>
     simp[] >>
     qpat_x_assum `!x. x <> _ /\ x <> _ /\ x <> _ ==> lookup_var x s1 = _`
       (qspec_then `x` mp_tac) >>
     fs[]) >>
  (* the immutables' base, untouched since t *)
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >>
     metis_tac[local_ptrs_reserved_imm_base, cj 1 compile_expr_grows]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region s2 = SOME 0w /\ copy_old_operand mid region` by
    (gen_tac >> strip_tac >>
     `immutable_base_zero cenv t` by fs[stmt_state_rel_def] >>
     `eval_operand region t = SOME 0w` by fs[immutable_base_zero_def] >>
     `!x. region = Var x ==> not_fresh_at sm x` by
       (rpt strip_tac >> first_x_assum irule >> fs[]) >>
     conj_tac
     >- (Cases_on `region` >> fs[eval_operand_def] >>
         rename1 `Var x` >>
         `not_fresh_at sm x` by fs[] >>
         `x <> "%" ++ toString v0 /\ x <> "%" ++ toString (v0 + 1) /\
          x <> "%" ++ toString (v0 + 2) /\ x <> out` by
           (qpat_x_assum `not_fresh_at sm x`
              (mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
            disch_then (fn th =>
              MAP_EVERY (fn n => assume_tac (SPEC n th))
                [``v0:num``, ``v0 + 1``, ``v0 + 2``, ``v0 + 3``]) >>
            fs[Abbr `out`, Abbr `v0`]) >>
         simp[] >>
         qpat_x_assum `!x. x <> _ /\ x <> _ /\ x <> _ ==> lookup_var x s1 = _`
           (qspec_then `x` mp_tac) >>
         fs[]) >>
     simp[copy_old_operand_def] >> rpt strip_tac >>
     irule not_fresh_at_mono >> qexists `sm` >> simp[Abbr `v0`] >> fs[]) >>
  (* the immutable copy into the buffer *)
  `bw + Z < dimword (:256) /\ bw < dimword (:256)` by decide_tac >>
  `regions_disjoint (w2n a) Z bw Z` by
    (rewrite_tac[regions_disjoint_def] >> Cases_on `FLOOKUP t.vs_allocas (id0 + 4)`
     >- (`bw = s1.vs_alloca_next` by metis_tac[] >> decide_tac) >>
     PairCases_on `x` >>
     `bw = x0` by metis_tac[pairTheory.FST] >>
     `x1 = Z` by
       (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0 + 4`,
          `Z`, `[out]`] mp_tac state_rel_site_size >>
        impl_tac >- fs[Abbr `allocI`] >>
        disch_then drule >> simp[]) >>
     qpat_assum `!i0 M outs b m. _`
       (qspecl_then [`id0 + 4`, `Z`, `[out]`, `x0`, `x1`] mp_tac) >>
     impl_tac >- fs[Abbr `allocI`] >>
     decide_tac) >>
  `regions_disjoint (w2n a) 32 B 32` by
    (rewrite_tac[regions_disjoint_def] >> Cases_on `FLOOKUP t.vs_allocas id0`
     >- (`B = t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
     PairCases_on `x` >>
     `B = x0` by metis_tac[pairTheory.FST] >>
     `x1 = 64 + Z` by
       (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0`,
          `64 + Z`, `["%" ++ toString v0]`] mp_tac state_rel_site_size >>
        impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
        disch_then drule >> simp[]) >>
     qpat_assum `!i0 M outs b m. _`
       (qspecl_then [`id0`, `64 + Z`, `["%" ++ toString v0]`, `x0`, `x1`]
          mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     decide_tac) >>
  `mem_word_at (w2n a) s2.vs_memory = mem_word_at (w2n a) t.vs_memory` by
    (`s2.vs_memory = s1.vs_memory` by simp[Abbr `s2`, update_var_def] >>
     pop_assum SUBST1_TAC >> rewrite_tac[mem_word_at_eq_mload] >>
     metis_tac[regions_disjoint_def]) >>
  `w2n (n2w bw : bytes32) = bw` by simp[w2n_n2w] >>
  `32 * (k + 1) = Z` by simp[Abbr `Z`] >>
  `eval_operand (Var out) s2 = SOME (n2w bw)` by simp[eval_operand_def] >>
  `not_fresh_at mid out /\ not_fresh_at mid ("%" ++ toString v0) /\
   not_fresh_at mid ("%" ++ toString (v0 + 1)) /\
   not_fresh_at mid ("%" ++ toString (v0 + 2))` by
    (simp[not_fresh_at_def, Abbr `out`, ASCIInumbersTheory.toString_11] >>
     rpt strip_tac >> decide_tac) >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid (Var out)` by
    (simp[copy_old_operand_def] >> rpt strip_tac >>
     irule not_fresh_at_mono >> qexists `sm` >> simp[Abbr `v0`]) >>
  `emitted_insts mid sn = cis` by simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    body_ctor_copy_mem_ok >>
  disch_then (qspecl_then [`s2`, `a`, `n2w bw`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> simp[] >> decide_tac) >>
  strip_tac >> pop_assum mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)
    copy_ctor_run >>
  disch_then (qspecl_then [`s2`, `a`, `n2w bw`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `s3` strip_assume_tac) >>
  `run_inst_seq cis s2 = OK s3 /\ copy_static s3 = copy_static s2 /\
   (!x. not_fresh_at mid x ==> lookup_var x s3 = lookup_var x s2)` by
    (qpat_x_assum `copy_runtime_frame _ _ _ _` mp_tac >>
     asm_rewrite_tac[copy_runtime_frame_def] >> simp[]) >>
  `s3.vs_allocas = A /\ s3.vs_alloca_next = N /\
   s3.vs_data_section = t.vs_data_section` by
    (drule copy_static_fields >> simp[]) >>
  (* the copied length word *)
  `mem_word_at bw s3.vs_memory = n2w (STRLEN str)` by
    (mp_tac (Q.INST [`uu` |-> `t`, `zz` |-> `t with vs_memory :=
                  (immutable_transfers F T a (n2w bw) (k + 1) 0 t).vs_memory`]
       (Q.INST [`es` |-> `ee`, `t` |-> `BaseT (StringT n)`,
                `v` |-> `StringV str`, `tv` |-> `BaseTV (StringT n)`,
                `w` |-> `n2w bw`]
          copy_ctor_contents)) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         fs[regions_disjoint_def] >> decide_tac) >>
     simp[val_in_memory_def] >> strip_tac >>
     qspecl_then [`a`, `bw`, `k + 1`, `s2`, `t`] mp_tac ctor_copy_first_word >>
     impl_tac >- (asm_rewrite_tac[] >> fs[regions_disjoint_def] >> decide_tac) >>
     strip_tac >> fs[]) >>
  `mload bw s3 = n2w (STRLEN str)` by metis_tac[mem_word_at_eq_mload] >>
  (* the encoder's tail *)
  `(STRLEN str + 31) DIV 32 <= k` by
    (irule round_le_of_le_mult >> fs[Abbr `Z`]) >>
  `alloca_room ctx func s3` by
    (irule room_by_fields >>
     qexists `s1 with <| vs_allocas := A; vs_alloca_next := N |>` >>
     simp[]) >>
  `j + 5 <> id0 /\ j + 5 <> id0 + 3 /\ j + 5 <> id0 + 4` by decide_tac >>
  `FLOOKUP s3.vs_allocas (j + 5) = FLOOKUP t.vs_allocas (j + 5)` by
    metis_tac[] >>
  `v0 + 2 < u0` by decide_tac >>
  `!x. Var out = Var x ==> !k. x <> "%" ++ toString (u0 + k)` by
    (simp[Abbr `out`, ASCIInumbersTheory.toString_11] >> decide_tac) >>
  `eval_operand (Var out) s3 = SOME (n2w bw)` by
    (simp[eval_operand_def] >>
     `lookup_var out s3 = lookup_var out s2` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     fs[]) >>
  `lookup_var ("%" ++ toString v0) s3 = SOME (n2w B) /\
   lookup_var ("%" ++ toString (v0 + 1)) s3 = SOME (n2w (B + 32)) /\
   lookup_var ("%" ++ toString (v0 + 2)) s3 = SOME (n2w TP)` by
    (`lookup_var ("%" ++ toString v0) s3 =
        lookup_var ("%" ++ toString v0) s2 /\
      lookup_var ("%" ++ toString (v0 + 1)) s3 =
        lookup_var ("%" ++ toString (v0 + 1)) s2 /\
      lookup_var ("%" ++ toString (v0 + 2)) s3 =
        lookup_var ("%" ++ toString (v0 + 2)) s2` by
       (rpt conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[] >> fs[]) >>
  `32 + ((STRLEN str + 31) DIV 32) * 32 <= Z` by
    (simp[Abbr `Z`] >> decide_tac) >>
  `bw + 32 + ((STRLEN str + 31) DIV 32) * 32 <= s3.vs_alloca_next` by
    (asm_rewrite_tac[] >> decide_tac) >>
  `B + 64 + Z <= s3.vs_alloca_next /\ TP + Z <= s3.vs_alloca_next /\
   s3.vs_alloca_next < dimword (:256)` by
    (asm_rewrite_tac[] >> decide_tac) >>
  `FLOOKUP s3.vs_allocas (j + 5) = NONE ==>
   s3.vs_alloca_next + 32 < dimword (:256)` by
    (strip_tac >>
     qspecl_then [`func`, `s3`,
       `mk_inst (j + 5) ALLOCA [Lit 32w] ["%" ++ toString (u0 + 4)]`,
       `32w`, `ctx`] mp_tac alloca_room_fresh >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         TRY (simp_tac (srw_ss()) [mk_inst_def] >> NO_TAC) >>
         qpat_x_assum `FLOOKUP s3.vs_allocas _ = NONE` mp_tac >>
         simp_tac (srw_ss()) [mk_inst_def, FLOOKUP_DEF]) >>
     disch_then (mp_tac o CONJUNCT1) >> simp[dimword_def]) >>
  `!z m. FLOOKUP s3.vs_allocas (j + 5) = SOME (z, m) ==>
         z + 32 <= s3.vs_alloca_next /\ (z + 32 <= TP \/ TP + 32 <= z)` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP t.vs_allocas (j + 5) = SOME (z, m)` by metis_tac[] >>
     `m = 32` by
       (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `j + 5`, `32`,
          `["%" ++ toString (u0 + 4)]`] mp_tac state_rel_site_size >>
        impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
        disch_then drule >> simp[]) >>
     `z + m <= t.vs_alloca_next` by metis_tac[alloca_next_valid_def] >>
     `z + 32 <= TP \/ TP + 32 <= z` by
       (Cases_on `FLOOKUP t.vs_allocas (id0 + 3)`
        >- (`t.vs_alloca_next <= TP` by metis_tac[] >> decide_tac) >>
        `TP = FST x` by metis_tac[] >> PairCases_on `x` >>
        `x1 = Z` by
          (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0 + 3`,
             `Z`, `["%" ++ toString (v0 + 2)]`] mp_tac state_rel_site_size >>
           impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
           disch_then drule >> simp[]) >>
        qpat_x_assum `allocas_non_overlapping t`
          (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
        disch_then (qspecl_then [`j + 5`, `id0 + 3`, `z`, `m`, `x0`, `x1`]
          mp_tac) >>
        asm_rewrite_tac[] >> fs[] >> decide_tac) >>
     asm_rewrite_tac[] >> decide_tac) >>
  qspecl_then [`j`, `u0`, `v0`, `Var out`, `s3`, `bw`, `STRLEN str`, `Z`,
               `B`, `TP`] mp_tac reason_tail_run_mem >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `t'` assume_tac)) >>
  `run_inst_seq_mem_ok tcode s3 /\ run_inst_seq tcode s3 = Abort Revert_abort t'` by
    fs[Abbr `tcode`] >>
  (* the whole encoder *)
  `ecode = reason_head id0 v0 Z ++ (allocI :: (cis ++ tcode))` by
    simp[Abbr `ecode`] >>
  `run_inst_seq_mem_ok (cis ++ tcode) s2` by
    (irule run_inst_seq_mem_ok_append >> asm_rewrite_tac[] >>
     rpt strip_tac >> fs[]) >>
  `run_inst_seq_mem_ok (allocI :: (cis ++ tcode)) s1` by
    (rewrite_tac[run_inst_seq_mem_ok_def] >> asm_rewrite_tac[] >>
     simp[] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[Abbr `allocI`, mk_inst_def]) >>
     simp[Abbr `allocI`, dload_mk_inst_other]) >>
  `run_inst_seq_mem_ok ecode t` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
     asm_rewrite_tac[] >> rpt strip_tac >> fs[]) >>
  `run_inst_seq ecode t = Abort Revert_abort t'` by
    (`run_inst_seq (cis ++ tcode) s2 = Abort Revert_abort t'` by
       metis_tac[run_inst_seq_append] >>
     `run_inst_seq (allocI :: (cis ++ tcode)) s1 = Abort Revert_abort t'` by
       (asm_rewrite_tac[run_inst_seq_def] >> simp[]) >>
     asm_rewrite_tac[] >> metis_tac[run_inst_seq_append]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              (is_terminator i.inst_opcode ==> i.inst_opcode = REVERT)) ecode` by
    (simp[EVERY_MEM] >> gen_tac >>
     qpat_x_assum `ecode = _` (fn th => rewrite_tac[th]) >>
     simp[Abbr `tcode`, MEM_APPEND] >> strip_tac
     >- (mp_tac (cj 1 (Q.SPECL [`id0`, `v0`, `Z`, `j`, `u0`, `Var out`]
           reason_encoder_ops)) >>
         simp[EVERY_MEM] >> disch_then drule >> simp[])
     >- simp[Abbr `allocI`, mk_inst_def, is_terminator_def]
     >- (qpat_x_assum `EVERY _ cis` mp_tac >> simp[EVERY_MEM] >>
         disch_then drule >> strip_tac >> asm_rewrite_tac[] >>
         simp[is_terminator_def]) >>
     mp_tac (cj 2 (Q.SPECL [`id0`, `v0`, `Z`, `j`, `u0`, `Var out`]
       reason_encoder_ops)) >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  qspecl_then [`ecode`, `t`, `t'`, `Revert_abort`, `ctx`, `func`, `bb`] mp_tac
    run_inst_seq_revert_path_mem >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qpat_assum `t.vs_current_bb = _` SUBST1_TAC >>
          first_assum ACCEPT_TAC) >>
      qpat_assum `t.vs_inst_idx = _` SUBST1_TAC >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  qexists_tac `t' with vs_inst_idx := j'` >>
  pop_assum mp_tac >> simp_tac (srw_ss()) [gas_marked_path_def]
QED
