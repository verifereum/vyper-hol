(* The revert encoder's run from a string reason compiled to a memory
   pointer (reason_vv_ok): the encoder reads the message where vv_post puts
   it, in one of the reason's own allocas or a local's region, so apart
   from the encoder's sites.  The message's rounded footprint below the
   frontier is a premise. *)
Theory stmtReasonMemKindMemory
Ancestors
  stmtReasonVvMemory stmtReasonLitFragMemory stmtReasonMemory
  stmtSimReasonExpr stmtSimReason exprOperandVar localPtrsProps
  stmtSimDefs exprLoweringProps loweringPosts fragGasPathMem fragGasMode
  fragExec instMemFrontier venomMemDefs exprLowering stmtLowering
  emitHelper compileEnv valueEncoding vfmConstants vyperValue
  vyperInterpreter venomExecSemantics venomState venomInst context
  words list rich_list finite_map arithmetic
Libs
  monadsyntax

Theorem unwrap_value_reason_vv_mem[local]:
  !cenv vv op st. reason_vv vv = SOME op ==> unwrap_value cenv vv st = (op, st)
Proof
  Cases_on `vv` >>
  simp[reason_vv_def, unwrap_value_def, comp_return_def] >>
  rw[] >> simp[comp_return_def]
QED

(* Where vv_post puts a string reason's message. *)
Theorem reason_vv_message_at:
  reason_vv vv = SOME op /\
  expr_type se = BaseT (StringT n) /\ n < 2 ** 64 /\
  vv_post ctx func cenv cx se es sa sm s0 ee tv vv t /\
  read_result cx tv ee = (INL (StringV str), ee) ==>
  ?w. eval_operand op t = SOME w /\
      mem_word_at (w2n w) t.vs_memory = n2w (LENGTH str) /\
      LENGTH str + 32 <= type_memory_size (BaseTV (StringT n)) /\
      ((?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
                   sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\
                   b <= w2n w /\ w2n w + (32 + LENGTH str) <= b + sz) \/
       (?nm b sz. local_region cenv ee.scopes t nm b sz /\
                  b <= w2n w /\ w2n w + (32 + LENGTH str) <= b + sz))
Proof
  strip_tac >>
  `(n + 31) DIV 32 <= n + 31` by simp[DIV_LESS_EQ] >>
  `evaluate_type (get_tenv cx) (BaseT (StringT n)) =
     SOME (BaseTV (StringT n))` by
    (simp[evaluate_type_def, type_slot_size_def, word_size_def] >>
     fs[dimword_def]) >>
  `~is_word_type (BaseT (StringT n))` by simp[is_word_type_def] >>
  `post_value_type cenv se = BaseT (StringT n)` by
    simp[post_value_type_bytestring, is_bytestring_type_def] >>
  Cases_on `vv` >> fs[reason_vv_def] >> rpt BasicProvers.VAR_EQ_TAC >>
  fs[vv_post_def, vv_holds_def, vv_at_def, expr_val_rel_def,
     expr_val_at_def] >>
  gvs[val_in_memory_def, LET_THM, val_wf_def, val_footprint_def] >>
  metis_tac[]
QED

(* The memory-pointer kind's revert: the encoder from the reason's post. *)
Theorem reason_mem_revert_path_mem:
  !ctx func cenv cx se es sa vv sm sb s0 ee tv t str n.
    reason_vv_ok vv /\ expr_type se = BaseT (StringT n) /\
    type_memory_bytes cenv (BaseT (StringT n)) < 2 ** 64 /\
    compile_expr cenv (expr_type se) se sa = (vv, sm) /\
    compile_revert_with_reason cenv vv (expr_type se)
      (type_memory_bytes cenv (expr_type se)) sm = ((), sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    vv_post ctx func cenv cx se es sa sm s0 ee tv vv t /\
    read_result cx tv ee = (INL (StringV str), ee) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!w. eval_operand (vv_operand vv) t = SOME w ==>
         w2n w + 32 + ((LENGTH str + 31) DIV 32) * 32 <= t.vs_alloca_next) ==>
    ?u. gas_path_mem ctx func t 0 (Abort Revert_abort u)
Proof
  rpt gen_tac >> strip_tac >>
  `?op. reason_vv vv = SOME op /\ !l. op <> Label l` by fs[reason_vv_ok_def] >>
  `vv_operand vv = op` by
    (Cases_on `vv` >> fs[reason_vv_def, vv_operand_def] >> gvs[AllCaseEqs()]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[cj 1 compile_expr_grows] >>
  qabbrev_tac `Z = 32 + ((n + 31) DIV 32) * 32` >>
  `type_memory_bytes cenv (expr_type se) = Z` by
    simp[Abbr `Z`, type_memory_bytes_def] >>
  qpat_x_assum `type_memory_bytes _ (expr_type _) = _` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `Z < 2 ** 64` by fs[type_memory_bytes_def, Abbr `Z`] >>
  `32 <= Z` by simp[Abbr `Z`] >>
  `n < 2 ** 64` by
    (`(n + 31) MOD 32 < 32 /\
      n + 31 = (n + 31) DIV 32 * 32 + (n + 31) MOD 32` by
       metis_tac[DIVISION, DECIDE ``0n < 32``] >>
     qpat_x_assum `Z < _` mp_tac >> qunabbrev_tac `Z` >> decide_tac) >>
  drule_all reason_vv_message_at >>
  disch_then (qx_choose_then `w` (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  drule compile_revert_reason_shape >>
  disch_then (qx_choosel_then [`op'`, `sn`] strip_assume_tac) >>
  drule unwrap_value_reason_vv_mem >>
  disch_then (qspecl_then [`cenv`, `sm with <|cs_next_id := sm.cs_next_id + 4;
      cs_next_var := sm.cs_next_var + 3;
      cs_current_insts := sm.cs_current_insts ++
        reason_head sm.cs_next_id sm.cs_next_var Z|>`] assume_tac) >>
  `op' = op /\ sn = sm with <|cs_next_id := sm.cs_next_id + 4;
      cs_next_var := sm.cs_next_var + 3;
      cs_current_insts := sm.cs_current_insts ++
        reason_head sm.cs_next_id sm.cs_next_var Z|>` by fs[] >>
  qpat_x_assum `op' = op` SUBST_ALL_TAC >>
  qpat_x_assum `sn = _` SUBST_ALL_TAC >>
  qpat_x_assum `sb = _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qabbrev_tac `id0 = sm.cs_next_id` >> qabbrev_tac `v0 = sm.cs_next_var` >>
  qabbrev_tac `ecode = reason_head id0 v0 Z ++
                       reason_tail (id0 + 4) (v0 + 3) v0 op` >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ ecode` by
    (qpat_x_assum `sb = _` SUBST1_TAC >> simp[Abbr `ecode`]) >>
  qspecl_then [`sm`, `sb`, `func`, `ecode`] mp_tac fn_has_code_code >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `64 + Z < dimword (:256) /\ Z < dimword (:256)` by
    (qpat_x_assum `Z < 2 ** 64` mp_tac >> simp[dimword_def]) >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  `alloca_room ctx func t /\ alloca_next_valid t /\
   allocas_non_overlapping t` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `MEM (mk_inst id0 ALLOCA [Lit (n2w (64 + Z))] ["%" ++ toString v0])
       (fn_insts func) /\
   MEM (mk_inst (id0 + 3) ALLOCA [Lit (n2w Z)] ["%" ++ toString (v0 + 2)])
       (fn_insts func) /\
   MEM (mk_inst (id0 + 4 + 5) ALLOCA [Lit 32w] ["%" ++ toString (v0 + 3 + 4)])
       (fn_insts func)` by
    (rpt conj_tac >>
     qpat_assum `!i. MEM i ecode ==> MEM i (fn_insts func)` irule >>
     simp[Abbr `ecode`, reason_head_def, reason_tail_def]) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `(LENGTH str + 31) DIV 32 <= (n + 31) DIV 32` by
    (irule round_le_of_le_mult >>
     fs[type_memory_size_def, word_size_def]) >>
  (* the message is apart from a held Error buffer *)
  `!x. FLOOKUP t.vs_allocas id0 = SOME x ==>
       w2n w + 32 <= FST x \/ FST x + 32 <= w2n w` by
    (gen_tac >> strip_tac >> PairCases_on `x` >>
     `x1 = 64 + Z` by
       (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0`, `64 + Z`,
                     `["%" ++ toString v0]`] mp_tac state_rel_site_size >>
        impl_tac >- simp[] >> disch_then drule >> simp[]) >>
     fs[]
     >- (`aid <> id0` by simp[Abbr `id0`] >>
         qpat_x_assum `allocas_non_overlapping t`
           (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
         disch_then (qspecl_then [`aid`, `id0`, `b`, `sz`, `x0`, `64 + Z`]
           mp_tac) >>
         simp[]) >>
     qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
     simp[local_region_def] >> strip_tac >>
     `local_ptrs_rel func cenv ee.scopes t` by
       fs[stmt_state_rel_def, state_rel_def] >>
     pop_assum (mp_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     disch_then (drule_all o CONJUNCT1) >> strip_tac >> gvs[] >>
     qpat_x_assum `local_backed _ _ _ _ _` mp_tac >>
     simp[local_backed_def] >> strip_tac
     >- (Cases_on `inst.inst_id = id0`
         >- (`inst = mk_inst id0 ALLOCA [Lit (n2w (64 + Z))]
                       ["%" ++ toString v0]` by
               (irule fn_inst_ids_distinct_inj >>
                conj_tac >- simp[mk_inst_def] >>
                qexists_tac `func` >> fs[mk_inst_def]) >>
             `not_fresh_at sa p` by
               (qpat_assum `local_ptrs_reserved _ _` mp_tac >>
                rewrite_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
             fs[mk_inst_def, not_fresh_at_def] >>
             first_x_assum (qspec_then `v0` mp_tac) >> simp[Abbr `v0`]) >>
         qpat_x_assum `allocas_non_overlapping t`
           (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
         disch_then (qspecl_then [`inst.inst_id`, `id0`, `w2n w'`, `sz`, `x0`,
           `64 + Z`] mp_tac) >>
         simp[]) >>
     first_x_assum drule >> simp[regions_disjoint_def]) >>
  qspecl_then [`ctx`, `func`, `id0`, `v0`, `op`, `t`, `w2n w`,
               `LENGTH str`, `Z`] mp_tac reason_encoder_run_mem >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (gen_tac >> strip_tac >> conj_tac
          >- (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0`,
                `64 + Z`, `["%" ++ toString v0]`] mp_tac state_rel_site_size >>
              impl_tac >- simp[] >> disch_then drule >> simp[]) >>
          metis_tac[])
      >- (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0 + 3`,
            `Z`, `["%" ++ toString (v0 + 2)]`] mp_tac state_rel_site_size >>
          impl_tac >- simp[] >> simp[])
      >- (gen_tac >> strip_tac >>
          `SND x = 32` by
            (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0 + 4 + 5`,
               `32`, `["%" ++ toString (v0 + 3 + 4)]`] mp_tac
               state_rel_site_size >>
             impl_tac >- simp[] >> disch_then drule >> simp[]) >>
          simp[] >> gen_tac >> strip_tac >>
          `SND y = Z` by
            (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee`, `t`, `id0 + 3`,
                          `Z`, `["%" ++ toString (v0 + 2)]`] mp_tac
               state_rel_site_size >>
             impl_tac >- simp[] >> disch_then drule >> simp[]) >>
          PairCases_on `x` >> PairCases_on `y` >> fs[] >>
          qpat_x_assum `allocas_non_overlapping t`
            (mp_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
          disch_then (qspecl_then [`id0 + 4 + 5`, `id0 + 3`, `x0`, `32`,
                                   `y0`, `Z`] mp_tac) >>
          simp[])
      >- (rpt strip_tac >> fs[not_fresh_at_def] >>
          first_x_assum (qspec_then `v0 + k` mp_tac) >> simp[Abbr `v0`])
      >- first_assum ACCEPT_TAC
      >- simp[]
      >- fs[mload_def, mem_word_at_def]
      >- (qunabbrev_tac `Z` >> decide_tac) >>
      first_x_assum (qspec_then `w` mp_tac) >> simp[]) >>
  strip_tac >>
  qspecl_then [`ecode`, `t`, `t'`, `Revert_abort`, `ctx`, `func`, `bb`] mp_tac
    run_inst_seq_revert_path_mem >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qpat_assum `t.vs_current_bb = _` SUBST1_TAC >>
          first_assum ACCEPT_TAC)
      >- (qpat_assum `t.vs_inst_idx = _` SUBST1_TAC >>
          first_assum ACCEPT_TAC)
      >- simp[Abbr `ecode`, EVERY_APPEND, reason_encoder_ops]
      >- simp[Abbr `ecode`] >>
      simp[Abbr `ecode`]) >>
  strip_tac >>
  qexists_tac `t' with vs_inst_idx := j` >>
  pop_assum mp_tac >> simp_tac (srw_ss()) [gas_marked_path_def]
QED
