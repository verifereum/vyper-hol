(* The revert encoder's run from a string reason compiled to a pointer into
   storage or transient storage (reason_storage_vv): unwrap_value copies
   the message's words into a buffer of its own between the encoder's head
   and tail, with one SLOAD or TLOAD and an MSTORE, or a word-copy loop.
   The encoder reads the copied length word, which the storage encoding of
   the string bounds by its declared length. *)
Theory stmtReasonStorageKindMemory
Ancestors
  stmtReasonMemory stmtReasonLitFragMemory
  stmtSimReasonStorage stmtSimReasonExpr stmtSimReason exprReasonOperand
  exprOperandVar exprSimUnwrapProps exprSimCopy exprSimStorageCopy
  storageCopyGasPath storageDecodeMemory vyperTypeStatePreservation
  vyperTypeValues valueEncodingTyping vyperStorageBackend
  valueEncodingProps valueEncodingProofs
  stmtSimDefs exprLoweringProps loweringPosts fragGasPathMem fragGasMode
  fragGasSeqMem fragExec fragExecMem instMemFrontier freshWrites venomMemDefs
  venomInstProps exprLowering stmtLowering emitHelper emitHelperProps
  compileEnv valueEncoding vfmConstants vyperValue vyperInterpreter
  venomExecSemantics venomState venomInst context
  words list rich_list finite_map arithmetic
Libs
  monadsyntax

(* The encoder's head and the buffer's ALLOCA write no storage. *)
Theorem step_keeps_storage[local]:
  !i s s'.
    MEM i.inst_opcode [ALLOCA; MSTORE; ADD] /\ step_inst_base i s = OK s' ==>
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs, exec_pure2_def,
    exec_write2_def, exec_alloca_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[update_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem run_seq_keeps_storage[local]:
  !code s t.
    run_inst_seq code s = OK t /\
    EVERY (\i. MEM i.inst_opcode [ALLOCA; MSTORE; ADD]) code ==>
    contract_storage t = contract_storage s /\
    contract_transient t = contract_transient s
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> rpt strip_tac >>
  rename1 `step_inst_base h s = OK u` >>
  `u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx` by
    (irule step_keeps_storage >> qexists_tac `h` >> simp[]) >>
  first_x_assum (qspecl_then [`u`, `t`] mp_tac) >> simp[] >>
  simp[contract_storage_def, contract_transient_def]
QED

(* What copy_buffer_storage_contents says of a copy that starts from a
   state other than u with the same storage: the copied words are those of
   a memory holding the value.  That memory is u's with the copied bytes
   written over the buffer, which copies from u itself. *)
Theorem storage_copy_words_hold[local]:
  !ctx func cenv cx es u t v a tr tv b s z.
    stmt_state_rel ctx func cenv cx es u /\
    storage_holds cx tr t (Value v) a es u /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    contract_storage s = contract_storage u /\
    contract_transient s = contract_transient u /\
    copy_prefix (if tr then LocTransient else LocStorage)
      a b (type_slot_size tv) s (type_slot_size tv) z ==>
    val_wf tv v /\
    ?m. val_in_memory tv v b m /\
        !i. i < type_slot_size tv ==>
            mem_word_at (b + 32 * i) m = mem_word_at (b + 32 * i) z.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `loc = if tr then LocTransient else LocStorage` >>
  qabbrev_tac `n = type_slot_size tv` >>
  qabbrev_tac `bs = mem_bytes_at b (32 * n) z.vs_memory` >>
  qabbrev_tac `z' = write_memory_with_expansion b bs u` >>
  `LENGTH bs = 32 * n` by simp[Abbr `bs`] >>
  `mem_bytes_at b (32 * n) z'.vs_memory = mem_bytes_at b (32 * n) z.vs_memory` by
    (qpat_x_assum `LENGTH bs = _` (SUBST1_TAC o SYM) >>
     simp[Abbr `z'`, write_memory_mem_bytes_at_same] >> simp[Abbr `bs`]) >>
  `!i. i < n ==>
       mem_word_at (b + 32 * i) z'.vs_memory =
       mem_word_at (b + 32 * i) z.vs_memory` by
    (rpt strip_tac >>
     drule (cj 2 mem_bytes_at_agree_window) >>
     disch_then (qspec_then `b + 32 * i` mp_tac) >> simp[]) >>
  `copy_prefix loc a b n u n z'` by
    (simp[copy_prefix_def] >> rpt conj_tac
     >- simp[Abbr `z'`, copy_static_def, write_memory_with_expansion_def,
             LET_THM]
     >- (rpt strip_tac >> res_tac >> asm_rewrite_tac[] >>
         drule_all copy_prefix_word >> strip_tac >> asm_rewrite_tac[] >>
         Cases_on `tr` >>
         fs[Abbr `loc`, copy_runtime_word_def, sload_def, tload_def]) >>
     rpt strip_tac >> simp[Abbr `z'`] >>
     irule write_memory_mem_bytes_at_disjoint >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `u`, `t`, `v`, `a`, `tr`,
               `tv`, `b`, `z'`] mp_tac copy_buffer_storage_contents >>
  impl_tac >- fs[Abbr `loc`, Abbr `n`] >>
  strip_tac >> simp[] >>
  qexists_tac `z'.vs_memory` >> fs[Abbr `n`]
QED

(* unwrap_value of a pointer to a string in storage or transient storage:
   a buffer of the type's size, then the copy into it. *)
Theorem storage_unwrap_shape[local]:
  !cenv ty p st op st' M wc.
    ~is_word_type ty /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    unwrap_value cenv (LocatedValue ty p) st = (op, st') /\
    type_memory_bytes cenv ty = M /\ (M + 31) DIV 32 = wc ==>
    op = Var ("%" ++ toString st.cs_next_var) /\
    ?r. (if wc = 1 then
           do v <- emit_op (if p.ptr_location = LocStorage then SLOAD
                            else TLOAD) [p.ptr_operand];
              emit_void MSTORE [op; v] od
         else do compile_word_copy_loop p.ptr_operand op wc
                   p.ptr_location LocMemory F;
                 return () od)
        (st with <| cs_next_id := st.cs_next_id + 1;
                    cs_next_var := st.cs_next_var + 1;
                    cs_current_insts := st.cs_current_insts ++
                      [mk_inst st.cs_next_id ALLOCA
                         [Lit (n2w M)]
                         ["%" ++ toString st.cs_next_var]] |>) = (r, st')
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  `p.ptr_location <> LocMemory` by (strip_tac >> fs[]) >>
  simp[unwrap_value_def] >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes cenv ty) ((type_memory_bytes cenv ty + 31) DIV 32)
     cenv.ce_is_ctor cenv.ce_imm_alloca =
   do buf <- compile_alloc_buffer (type_memory_bytes cenv ty);
      (if (type_memory_bytes cenv ty + 31) DIV 32 = 1 then
         do v <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                   [p.ptr_operand];
            emit_void MSTORE [buf.buf_operand; v] od
       else do compile_word_copy_loop p.ptr_operand buf.buf_operand
                 ((type_memory_bytes cenv ty + 31) DIV 32) p.ptr_location
                 LocMemory F;
               return () od);
      return buf.buf_operand
   od` by (irule ensure_storage_memory_layout >> fs[]) >>
  Cases_on `p.ptr_location` >> fs[] >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[]
QED

Theorem storage_suffix_mono[local]:
  !loc opc src dst n sa r sb.
    (if n = 1 then
       do v <- emit_op opc [src];
          emit_void MSTORE [dst; v] od
     else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
      sa = (r, sb) ==>
    ci_mono sa sb
Proof
  rpt gen_tac >> Cases_on `n = 1` >> simp[]
  >- (simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_var_def, fresh_id_def, emit_def,
           emit_inst_def] >>
      strip_tac >> gvs[ci_mono_def, cs_extends_def] >>
      rewrite_tac[GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]) >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qspecl_then [`src`, `dst`, `n`, `loc`, `LocMemory`, `F`, `sa`] mp_tac
    ci_mono_compile_word_copy_loop >>
  simp[]
QED

(* One storage word into the buffer, memory-safe below the frontier. *)
Theorem storage_word_path_mem[local]:
  !ctx func loc src dst sa u sb s a b.
    (loc = LocStorage \/ loc = LocTransient) /\
    do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
       emit_void MSTORE [dst; v] od sa = (u,sb) /\
    fn_has_code sa sb func /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
    b + 32 < 2**256 /\ b + 32 <= s.vs_alloca_next /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?z. gas_path_mem ctx func s 0 (OK z) /\ copy_prefix loc a b 1 s 1 z /\
        (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
        z.vs_current_bb = sb.cs_current_bb /\
        z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule storage_copy_word_layout >> strip_tac >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = copy_runtime_word loc s a` >>
  `step_inst_base (mk_inst sa.cs_next_id
    (if loc = LocStorage then SLOAD else TLOAD) [src] [v]) s =
    OK (update_var v w s)` by
    (gvs[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
         Abbr `w`, copy_runtime_word_def]) >>
  `eval_operand dst (update_var v w s) = SOME (n2w b)` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var] >>
     metis_tac[]) >>
  `w2n (n2w b : bytes32) = b` by
    (gvs[w2n_n2w, dimword_def] >> decide_tac) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) MSTORE [dst; Var v] [])
    (update_var v w s) = OK (mstore b w (update_var v w s))` by
    (qpat_assum `w2n (n2w b : bytes32) = b`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule step_MSTORE >> simp[eval_operand_def, lookup_var_update_var]) >>
  qpat_x_assum `isPREFIX _ _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  rename1 `sb.cs_current_insts = sa.cs_current_insts ++ l` >>
  `l = [mk_inst sa.cs_next_id (if loc = LocStorage then SLOAD else TLOAD)
          [src] [v];
        mk_inst (sa.cs_next_id + 1) MSTORE [dst; Var v] []]` by
    fs[emitted_insts_def, DROP_LENGTH_APPEND, Abbr `v`] >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qspecl_then [`sa`, `sb`, `func`, `l`] mp_tac fn_has_code_code >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `run_inst_seq l s = OK (mstore b w (update_var v w s))` by
    asm_simp_tac (srw_ss()) [run_inst_seq_def] >>
  `run_inst_seq_mem_ok l s` by
    (`~MEM (if loc = LocStorage then SLOAD else TLOAD)
        [MLOAD; ILOAD; MCOPY; DRET; RETURN; REVERT; SHA3; LOG; CALL;
         STATICCALL; DELEGATECALL; CREATE; CREATE2; MSTORE; MSTORE8; ISTORE;
         CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY; EXTCODECOPY] /\
      (if loc = LocStorage then SLOAD else TLOAD) <> DLOAD /\
      (if loc = LocStorage then SLOAD else TLOAD) <> DLOADBYTES` by rw[] >>
     asm_simp_tac (srw_ss()) [run_inst_seq_mem_ok_def, dload_mk_inst_other,
       below_frontier_MSTORE, eval_operand_def, lookup_var_update_var] >>
     conj_tac
     >- (irule below_frontier_no_ranges >> rw[mk_inst_def]) >>
     simp[update_var_def]) >>
  qspecl_then [`l`, `s`, `mstore b w (update_var v w s)`, `ctx`, `func`, `bb`]
    mp_tac run_inst_seq_gas_path_mem >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qpat_assum `s.vs_current_bb = _` SUBST1_TAC >>
                   first_assum ACCEPT_TAC) >>
      conj_tac >- (qpat_assum `s.vs_inst_idx = _` SUBST1_TAC >>
                   first_assum ACCEPT_TAC) >>
      conj_tac
      >- (qpat_x_assum `l = _` SUBST1_TAC >>
          rw[mk_inst_def, is_terminator_def]) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) l) = 0` by
    (qpat_x_assum `l = _` SUBST1_TAC >> rw[mk_inst_def]) >>
  asm_rewrite_tac[] >> strip_tac >>
  qexists_tac `mstore b w (update_var v w s) with
                 vs_inst_idx := s.vs_inst_idx + LENGTH l` >>
  conj_tac >- (pop_assum mp_tac >> simp[]) >>
  rpt conj_tac
  >- (`copy_prefix loc a b 1 s (0+1)
        (mstore (b+32*0) (copy_runtime_word loc s (a+n2w 0))
          (update_var v w s))` by
        (irule copy_prefix_extend >>
         simp[copy_prefix_update_var, copy_prefix_zero]) >>
      gvs[Abbr `w`, WORD_ADD_0, copy_prefix_idx])
  >- (simp[update_var_def, mstore_def, write_memory_with_expansion_def,
           lookup_var_def] >>
      rpt strip_tac >> simp[FLOOKUP_UPDATE] >> metis_tac[])
  >- fs[update_var_def, mstore_def, write_memory_with_expansion_def]
  >- fs[]
QED

(* The copy after the buffer's ALLOCA, either kind, memory-safe. *)
Theorem storage_suffix_path_mem[local]:
  !ctx func loc opc src dst n sa r sb s a b.
    (loc = LocStorage \/ loc = LocTransient) /\
    opc = (if loc = LocStorage then SLOAD else TLOAD) /\
    (if n = 1 then
       do v <- emit_op opc [src];
          emit_void MSTORE [dst; v] od
     else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
      sa = (r, sb) /\
    fn_has_code sa sb func /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
    n < 2**256 /\ b + 32 * n < 2**256 /\ b + 32 * n <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?z. gas_path_mem ctx func s 0 (OK z) /\ copy_prefix loc a b n s n z /\
        (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
        z.vs_current_bb = sb.cs_current_bb /\
        z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `opc = _` SUBST_ALL_TAC >>
  Cases_on `n = 1`
  >- (qpat_x_assum `n = 1` SUBST_ALL_TAC >>
      qspecl_then [`ctx`, `func`, `loc`, `src`, `dst`, `sa`, `r`, `sb`, `s`,
                   `a`, `b`] mp_tac storage_word_path_mem >>
      impl_tac >- (fs[] >> metis_tac[]) >> simp[]) >>
  fs[] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  mp_tac (storageCopyGasPathTheory.compile_storage_copy_content_capacity_path
    |> Q.SPEC `T`
    |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
    |> Q.SPEC `(ctx,func)`) >>
  simp[gas_marked_path_def] >>
  disch_then (drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`s`, `a`, `b`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
                FIRST [first_assum ACCEPT_TAC, decide_tac, simp[]])) >>
  strip_tac >> qexists_tac `t` >> simp[]
QED

Theorem reason_storage_revert_path_mem:
  !ctx func cenv cx se es sa vv sm sb s0 ee tv t str n.
    reason_storage_vv vv /\
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
  (* one goal for both locations: keep the disjunction whole *)
  qpat_assum `reason_storage_vv vv`
    (qx_choosel_then [`ty`, `p`]
       (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 assume_tac assume_tac))
     o REWRITE_RULE [reason_storage_vv_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qspecl_then [`cenv`, `BaseT (StringT n)`, `se`, `sa`,
                  `LocatedValue ty p`, `sm`] mp_tac
       (CONJUNCT1 compiler_compile_var) >>
     simp[vv_operand_def]) >>
  `vv_post ctx func cenv cx se es sa sm s0 ee (Value (StringV str))
     (LocatedValue ty p) t` by metis_tac[vv_post_read_result] >>
  `ty = BaseT (StringT n)` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ (Value _) _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def]) >>
  qpat_x_assum `ty = _` SUBST_ALL_TAC >>
  qabbrev_tac `tr = (p.ptr_location = LocTransient)` >>
  `(if tr then LocTransient else LocStorage) = p.ptr_location` by
    (qunabbrev_tac `tr` >> Cases_on `p.ptr_location` >> fs[]) >>
  `?a. eval_operand p.ptr_operand t = SOME a /\
       storage_holds cx tr (BaseT (StringT n)) (Value (StringV str)) a ee t` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ (Value _) _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def] >> strip_tac >>
     qexists_tac `w` >> qunabbrev_tac `tr` >>
     Cases_on `p.ptr_location` >> fs[]) >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  qabbrev_tac `k = (n + 31) DIV 32` >>
  qabbrev_tac `Z = 32 + k * 32` >>
  `type_memory_bytes cenv (BaseT (StringT n)) = Z` by
    simp[Abbr `Z`, Abbr `k`, type_memory_bytes_def] >>
  `Z < 2 ** 64` by metis_tac[] >>
  qabbrev_tac `wc = (Z + 31) DIV 32` >>
  `wc = k + 1` by
    (simp[Abbr `wc`, Abbr `Z`] >>
     `32 + k * 32 + 31 = (k + 1) * 32 + 31` by decide_tac >>
     pop_assum SUBST1_TAC >> simp[ADD_DIV_ADD_DIV]) >>
  `32 * wc = Z /\ wc < 2 ** 256 /\ 0 < wc` by
    (qpat_x_assum `wc = _` SUBST1_TAC >>
     qpat_x_assum `Z < _` mp_tac >> simp[Abbr `Z`]) >>
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
  `type_slot_size (BaseTV (StringT n)) = wc` by
    (qpat_x_assum `wc = _` SUBST1_TAC >>
     simp[type_slot_size_def, word_size_def, Abbr `k`]) >>
  qpat_x_assum `wc = _` kall_tac >>
  drule compile_revert_reason_shape >>
  disch_then (qx_choosel_then [`op`, `sn`] strip_assume_tac) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) storage_unwrap_shape >>
  disch_then (qspecl_then [`Z`, `wc`] mp_tac) >>
  impl_tac >- simp[Abbr `wc`] >>
  simp[] >> strip_tac >>
  qabbrev_tac `id0 = sm.cs_next_id` >> qabbrev_tac `v0 = sm.cs_next_var` >>
  qabbrev_tac `out = STRING #"%" (toString (v0 + 3))` >>
  qabbrev_tac `allocI = mk_inst (id0 + 4) ALLOCA [Lit (n2w Z)] [out]` >>
  qabbrev_tac `mid = sm with <|cs_next_var := v0 + 4; cs_next_id := id0 + 5;
      cs_current_insts :=
        sm.cs_current_insts ++ reason_head id0 v0 Z ++ [allocI]|>` >>
  `ci_mono mid sn` by (drule storage_suffix_mono >> simp[]) >>
  `mid.cs_next_var = v0 + 4 /\ mid.cs_next_id = id0 + 5 /\
   mid.cs_current_bb = sm.cs_current_bb` by simp[Abbr `mid`] >>
  `v0 + 4 <= sn.cs_next_var /\ id0 + 5 <= sn.cs_next_id` by
    (fs[ci_mono_def] >> metis_tac[]) >>
  qabbrev_tac `j = sn.cs_next_id` >> qabbrev_tac `u0 = sn.cs_next_var` >>
  qabbrev_tac `tcode = reason_tail j u0 v0 op` >>
  qabbrev_tac `hcode = reason_head id0 v0 Z ++ [allocI]` >>
  `sb.cs_current_bb = sn.cs_current_bb /\
   sb.cs_current_insts = sn.cs_current_insts ++ tcode` by
    (qpat_x_assum `sb = _` SUBST1_TAC >> simp[Abbr `tcode`]) >>
  `cs_extends sm mid` by
    (simp[Abbr `mid`, cs_extends_def] >>
     rewrite_tac[GSYM APPEND_ASSOC, IS_PREFIX_APPEND3]) >>
  `cs_extends sn sb` by
    (qpat_x_assum `sb = _` SUBST1_TAC >>
     simp[cs_extends_def, IS_PREFIX_APPEND3]) >>
  `cs_extends mid sn` by fs[ci_mono_def] >>
  qspecl_then [`sm`, `sn`, `sb`, `func`] mp_tac fn_has_code_split >>
  impl_tac >- metis_tac[cs_extends_trans] >> strip_tac >>
  qspecl_then [`sm`, `mid`, `sn`, `func`] mp_tac fn_has_code_split >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`sm`, `mid`, `func`, `hcode`] mp_tac fn_has_code_code >>
  impl_tac >- simp[Abbr `mid`, Abbr `hcode`] >>
  strip_tac >> rename1 `lookup_block sm.cs_current_bb _ = SOME bb` >>
  qspecl_then [`sn`, `sb`, `func`, `tcode`] mp_tac fn_has_code_code >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rename1 `lookup_block sn.cs_current_bb _ = SOME bb2` >>
  `64 + Z < dimword (:256) /\ Z < dimword (:256)` by
    (qpat_x_assum `Z < 2 ** 64` mp_tac >> simp[dimword_def]) >>
  `alloca_room ctx func t /\ alloca_next_valid t /\
   allocas_non_overlapping t` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `MEM (mk_inst id0 ALLOCA [Lit (n2w (64 + Z))] ["%" ++ toString v0])
       (fn_insts func) /\
   MEM (mk_inst (id0 + 3) ALLOCA [Lit (n2w Z)] ["%" ++ toString (v0 + 2)])
       (fn_insts func) /\
   MEM allocI (fn_insts func)` by
    (rpt conj_tac >>
     qpat_assum `!i. MEM i hcode ==> MEM i (fn_insts func)` irule >>
     simp[Abbr `hcode`, reason_head_def]) >>
  `MEM (mk_inst (j + 6) ALLOCA [Lit 32w] ["%" ++ toString (u0 + 5)])
       (fn_insts func)` by
    (qpat_assum `!i. MEM i tcode ==> MEM i (fn_insts func)` irule >>
     simp[Abbr `tcode`, reason_tail_def]) >>
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
  `run_inst_seq hcode t = OK s2` by
    (simp[Abbr `hcode`] >> drule run_inst_seq_append >>
     simp[run_inst_seq_def]) >>
  `s2.vs_labels = t.vs_labels` by
    (qspecl_then [`hcode`, `t`, `s2`] mp_tac run_inst_seq_data_section >>
     simp[Abbr `hcode`, Abbr `allocI`, reason_head_def, mk_inst_def,
          is_terminator_def]) >>
  `contract_storage s2 = contract_storage t /\
   contract_transient s2 = contract_transient t` by
    (irule run_seq_keeps_storage >> qexists_tac `hcode` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[Abbr `hcode`, Abbr `allocI`, reason_head_def, mk_inst_def]) >>
  `s2.vs_alloca_next = N /\ s2.vs_allocas = A /\ ~s2.vs_halted` by
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
     rename1 `p.ptr_operand = Var x` >>
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
  (* the head and the ALLOCA as one gas path *)
  `run_inst_seq_mem_ok [allocI] s1` by
    (simp[run_inst_seq_mem_ok_def] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[Abbr `allocI`, mk_inst_def]) >>
     simp[Abbr `allocI`, dload_mk_inst_other]) >>
  `run_inst_seq_mem_ok hcode t` by
    (simp[Abbr `hcode`] >> irule run_inst_seq_mem_ok_append >>
     rpt strip_tac >> fs[]) >>
  qspecl_then [`hcode`, `t`, `s2`, `ctx`, `func`, `bb`] mp_tac
    run_inst_seq_gas_path_mem >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qpat_assum `t.vs_current_bb = _` SUBST1_TAC >>
                   first_assum ACCEPT_TAC) >>
      conj_tac >- (qpat_assum `t.vs_inst_idx = _` SUBST1_TAC >>
                   first_assum ACCEPT_TAC) >>
      conj_tac
      >- simp[Abbr `hcode`, Abbr `allocI`, reason_head_def, mk_inst_def,
              is_terminator_def] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) hcode) = 0` by
    simp[Abbr `hcode`, Abbr `allocI`, reason_head_def, mk_inst_def] >>
  `t.vs_inst_idx + LENGTH hcode = LENGTH mid.cs_current_insts` by
    simp[Abbr `mid`, Abbr `hcode`] >>
  qabbrev_tac `s2i = s2 with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  disch_then (fn th => `gas_path_mem ctx func t 0 (OK s2i)` by
    (mp_tac th >>
     qpat_assum `LENGTH (FILTER _ _) = 0` (fn th => rewrite_tac[th]) >>
     qpat_assum `t.vs_inst_idx + _ = _` (fn th => rewrite_tac[th]) >>
     simp[Abbr `s2i`])) >>
  `!x. lookup_var x s2i = lookup_var x s2` by
    (qunabbrev_tac `s2i` >> simp_tac (srw_ss()) [lookup_var_def]) >>
  `!o'. eval_operand o' s2i = eval_operand o' s2` by
    (qunabbrev_tac `s2i` >> Cases >>
     simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  `!s i. contract_storage (s with vs_inst_idx := i) = contract_storage s /\
         contract_transient (s with vs_inst_idx := i) = contract_transient s` by
    simp[contract_storage_def, contract_transient_def] >>
  `contract_storage s2i = contract_storage t /\
   contract_transient s2i = contract_transient t` by
    simp[Abbr `s2i`] >>
  `~s2i.vs_halted /\ s2i.vs_alloca_next = N /\ s2i.vs_allocas = A /\
   s2i.vs_current_bb = mid.cs_current_bb /\
   s2i.vs_inst_idx = LENGTH mid.cs_current_insts` by
    (simp[Abbr `s2i`] >> simp[Abbr `s2`, update_var_def]) >>
  (* the storage copy into the buffer *)
  `bw + Z < dimword (:256) /\ bw < dimword (:256)` by decide_tac >>
  `w2n (n2w bw : bytes32) = bw` by simp[w2n_n2w] >>
  `not_fresh_at mid out /\ not_fresh_at mid ("%" ++ toString v0) /\
   not_fresh_at mid ("%" ++ toString (v0 + 1)) /\
   not_fresh_at mid ("%" ++ toString (v0 + 2))` by
    (simp[not_fresh_at_def, Abbr `out`, ASCIInumbersTheory.toString_11] >>
     rpt strip_tac >> decide_tac) >>
  `!x. p.ptr_operand = Var x \/ op = Var x ==> not_fresh_at mid x` by
    (rpt strip_tac >> fs[] >>
     irule not_fresh_at_mono >> qexists `sm` >> simp[Abbr `v0`]) >>
  `eval_operand p.ptr_operand s2i = SOME a /\
   eval_operand (Var out) s2i = SOME (n2w bw) /\
   eval_operand op s2i = SOME (n2w bw)` by
    simp[eval_operand_def] >>
  `bw + 32 * wc < 2 ** 256 /\ bw + 32 * wc <= s2i.vs_alloca_next` by
    (asm_rewrite_tac[] >> fs[dimword_def]) >>
  drule_at (Pat `(if _ then _ else _) _ = _`) storage_suffix_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `s2i`, `a`, `bw`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, fs[]]) >>
  disch_then (qx_choose_then `z` strip_assume_tac) >>
  `copy_static z = copy_static s2i` by fs[copy_prefix_def] >>
  `z.vs_allocas = A /\ z.vs_alloca_next = N /\ ~z.vs_halted` by
    (drule copy_static_fields >> simp[]) >>
  (* the copied length word *)
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `BaseT (StringT n)`,
    `StringV str`, `a`, `tr`, `BaseTV (StringT n)`, `bw`, `s2i`, `z`] mp_tac
    storage_copy_words_hold >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC >>
      qpat_assum `(if tr then _ else _) = _` SUBST1_TAC >>
      qpat_assum `type_slot_size _ = _` SUBST1_TAC >> fs[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `mm` strip_assume_tac)) >>
  `LENGTH str + 32 <= Z` by fs[val_wf_def] >>
  `mem_word_at bw mm = n2w (STRLEN str)` by fs[val_in_memory_def] >>
  `mem_word_at bw z.vs_memory = n2w (STRLEN str)` by
    (qpat_x_assum `!i. i < type_slot_size _ ==> _` (qspec_then `0` mp_tac) >>
     simp[]) >>
  `mload bw z = n2w (STRLEN str)` by metis_tac[mem_word_at_eq_mload] >>
  (* the encoder's tail *)
  `(STRLEN str + 31) DIV 32 <= k` by
    (irule round_le_of_le_mult >> fs[Abbr `Z`]) >>
  `alloca_room ctx func z` by
    (irule room_by_fields >>
     qexists `s1 with <| vs_allocas := A; vs_alloca_next := N |>` >>
     simp[]) >>
  `j + 6 <> id0 /\ j + 6 <> id0 + 3 /\ j + 6 <> id0 + 4` by decide_tac >>
  `FLOOKUP z.vs_allocas (j + 6) = FLOOKUP t.vs_allocas (j + 6)` by
    metis_tac[] >>
  `v0 + 2 < u0` by decide_tac >>
  `!x. Var out = Var x ==> !k. x <> "%" ++ toString (u0 + k)` by
    (simp[Abbr `out`, ASCIInumbersTheory.toString_11] >> decide_tac) >>
  `eval_operand (Var out) z = SOME (n2w bw)` by
    (simp[eval_operand_def] >>
     `lookup_var out z = lookup_var out s2i` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     fs[]) >>
  `lookup_var ("%" ++ toString v0) z = SOME (n2w B) /\
   lookup_var ("%" ++ toString (v0 + 1)) z = SOME (n2w (B + 32)) /\
   lookup_var ("%" ++ toString (v0 + 2)) z = SOME (n2w TP)` by
    (`lookup_var ("%" ++ toString v0) z =
        lookup_var ("%" ++ toString v0) s2i /\
      lookup_var ("%" ++ toString (v0 + 1)) z =
        lookup_var ("%" ++ toString (v0 + 1)) s2i /\
      lookup_var ("%" ++ toString (v0 + 2)) z =
        lookup_var ("%" ++ toString (v0 + 2)) s2i` by
       (rpt conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[] >> fs[]) >>
  `32 + ((STRLEN str + 31) DIV 32) * 32 <= Z` by
    (simp[Abbr `Z`] >> decide_tac) >>
  `bw + 32 + ((STRLEN str + 31) DIV 32) * 32 <= z.vs_alloca_next` by
    (asm_rewrite_tac[] >> decide_tac) >>
  `B + 64 + Z <= z.vs_alloca_next /\ TP + Z <= z.vs_alloca_next /\
   z.vs_alloca_next < dimword (:256)` by
    (asm_rewrite_tac[] >> decide_tac) >>
  `FLOOKUP z.vs_allocas (j + 6) = NONE ==>
   z.vs_alloca_next + 32 < dimword (:256)` by
    (strip_tac >>
     qspecl_then [`func`, `z`,
       `mk_inst (j + 6) ALLOCA [Lit 32w] ["%" ++ toString (u0 + 5)]`,
       `32w`, `ctx`] mp_tac alloca_room_fresh >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         TRY (simp_tac (srw_ss()) [mk_inst_def] >> NO_TAC) >>
         qpat_x_assum `FLOOKUP z.vs_allocas _ = NONE` mp_tac >>
         simp_tac (srw_ss()) [mk_inst_def, FLOOKUP_DEF]) >>
     disch_then (mp_tac o CONJUNCT1) >> simp[dimword_def]) >>
  `!z' m. FLOOKUP z.vs_allocas (j + 6) = SOME (z', m) ==>
          z' + 32 <= z.vs_alloca_next /\ (z' + 32 <= TP \/ TP + 32 <= z')` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP t.vs_allocas (j + 6) = SOME (z', m)` by metis_tac[] >>
     `m = 32` by
       (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `j + 6`, `32`,
          `["%" ++ toString (u0 + 5)]`] mp_tac state_rel_site_size >>
        impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
        disch_then drule >> simp[]) >>
     `z' + m <= t.vs_alloca_next` by metis_tac[alloca_next_valid_def] >>
     `z' + 32 <= TP \/ TP + 32 <= z'` by
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
        disch_then (qspecl_then [`j + 6`, `id0 + 3`, `z'`, `m`, `x0`, `x1`]
          mp_tac) >>
        asm_rewrite_tac[] >> fs[] >> decide_tac) >>
     asm_rewrite_tac[] >> decide_tac) >>
  qspecl_then [`j`, `u0`, `v0`, `Var out`, `z`, `bw`, `STRLEN str`, `Z`,
               `B`, `TP`] mp_tac reason_tail_run_mem >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `t'` assume_tac)) >>
  `run_inst_seq_mem_ok tcode z /\
   run_inst_seq tcode z = Abort Revert_abort t'` by
    fs[Abbr `tcode`] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              (is_terminator i.inst_opcode ==> i.inst_opcode = REVERT)) tcode` by
    (mp_tac (cj 2 (Q.SPECL [`id0`, `v0`, `Z`, `j`, `u0`, `Var out`]
       reason_encoder_ops)) >> simp[Abbr `tcode`]) >>
  qspecl_then [`tcode`, `z`, `t'`, `Revert_abort`, `ctx`, `func`, `bb2`]
    mp_tac run_inst_seq_revert_path_mem >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qpat_assum `z.vs_current_bb = _` SUBST1_TAC >>
                   first_assum ACCEPT_TAC) >>
      conj_tac >- (qpat_assum `z.vs_inst_idx = _` SUBST1_TAC >>
                   first_assum ACCEPT_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `j'` (assume_tac o
    SIMP_RULE (srw_ss()) [gas_marked_path_def])) >>
  qexists_tac `t' with vs_inst_idx := j'` >>
  qpat_x_assum `gas_path_mem _ _ s2i _ _` (fn th1 =>
    qpat_x_assum `gas_path_mem _ _ z _ _` (fn th2 =>
      assume_tac (MATCH_MP gas_path_mem_then (CONJ th1 th2)))) >>
  qpat_x_assum `gas_path_mem _ _ t _ _` (fn th1 =>
    qpat_x_assum `gas_path_mem _ _ s2i _ _` (fn th2 =>
      assume_tac (MATCH_MP gas_path_mem_then (CONJ th1 th2)))) >>
  fs[]
QED
