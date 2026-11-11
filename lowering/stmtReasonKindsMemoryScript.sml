(* The memory-safe revert path of a raise's or assert's non-literal reason,
   whatever its compiled value: a memory or stack value
   (stmtReasonMemKindMemory), a storage or transient pointer
   (stmtReasonStorageKindMemory), or a pointer into code
   (stmtReasonCodeKindMemory, and stmtReasonCtorCodeKindMemory in a
   constructor).  bodySimStmtCases's reason_covered and
   supported_reason_code tell them apart. *)
Theory stmtReasonKindsMemory
Ancestors
  stmtReasonMemKindMemory stmtReasonStorageKindMemory stmtReasonCodeKindMemory
  stmtReasonCtorCodeKindMemory
  bodySimStmtCases bodySim exprSimHyps allocLimits supportedStmts
  exprSimMemDefs exprSimProps stmtSimReason stmtSimReasonExpr context
  valueEncoding vfmConstants vyperValue
  vyperTypeSystem vyperAST compileEnv words arithmetic

(* A supported reason that is not a string literal has a string type. *)
Theorem supported_reason_string_type:
  !tops e.
    supported_string_reason tops e /\
    (!ml str. e <> Literal (BaseT (StringT ml)) (StringL str)) /\
    well_typed_expr env e ==>
    ?n. expr_type e = BaseT (StringT n)
Proof
  rpt strip_tac >>
  Cases_on `?t str. e = Literal t (StringL str)`
  >- (gvs[well_typed_expr_def, expr_type_def] >>
      Cases_on `t` >> gvs[well_typed_literal_def] >>
      rename1 `BaseT b` >> Cases_on `b` >> gvs[well_typed_literal_def]) >>
  `case expr_type e of BaseT (StringT _) => T | _ => F` by
    (Cases_on `e` >> fs[supported_string_reason_def] >>
     rename1 `Literal _ lit` >> Cases_on `lit` >>
     fs[supported_string_reason_def]) >>
  Cases_on `expr_type e` >> fs[] >>
  rename1 `BaseT b` >> Cases_on `b` >> fs[]
QED

Theorem reason_revert_path_mem:
  !tops ctx func cenv cx env es0 se es sa vv sm sb s0 ee tv t str.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
    supported_string_reason tops se /\ well_typed_expr env se /\
    alloc_limits_expr cenv se /\
    (!ml str. se <> Literal (BaseT (StringT ml)) (StringL str)) /\
    compile_expr cenv (expr_type se) se sa = (vv, sm) /\
    compile_revert_with_reason cenv vv (expr_type se)
      (type_memory_bytes cenv (expr_type se)) sm = ((), sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    vv_post ctx func cenv cx se es sa sm s0 ee tv vv t /\
    vv_store_bound cx (expr_type se) (lowered_value_type cenv se) ee tv vv t /\
    read_result cx tv ee = (INL (StringV str), ee) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func t 0 (Abort Revert_abort u)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all supported_reason_string_type >> strip_tac >>
  `type_memory_bytes cenv (BaseT (StringT n)) < 2 ** 64` by
    (drule alloc_limits_expr_type_alloc_ok >>
     simp[type_alloc_ok_def, is_word_type_def]) >>
  Cases_on `reason_covered cenv se`
  >- (qpat_x_assum `reason_covered _ _`
        (DISJ_CASES_TAC o REWRITE_RULE [reason_covered_def])
      >- (`reason_vv_ok vv` by metis_tac[] >>
          (* footprint: the value's store bound *)
          `!w. eval_operand (vv_operand vv) t = SOME w ==>
               w2n w + 32 + ((LENGTH str + 31) DIV 32) * 32 <=
               t.vs_alloca_next` by
            (rpt strip_tac >>
             `(n + 31) DIV 32 * 32 + 32 < 2 ** 64` by
               (qpat_x_assum `type_memory_bytes _ _ < _` mp_tac >>
                simp[type_memory_bytes_def]) >>
             `n < 2 ** 64` by
               (`(n + 31) MOD 32 < 32 /\
                 n + 31 = (n + 31) DIV 32 * 32 + (n + 31) MOD 32` by
                  metis_tac[DIVISION, DECIDE ``0n < 32``] >>
                decide_tac) >>
             `evaluate_type (get_tenv cx) (BaseT (StringT n)) =
                SOME (BaseTV (StringT n))` by
               (simp[evaluate_type_def, type_slot_size_def, word_size_def] >>
                fs[dimword_def]) >>
             Q.SUBGOAL_THEN
               `?vt. (?p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory /\
                        p.ptr_operand = vv_operand vv) \/
                   ((?t'. vv = StackValue t' (vv_operand vv)) /\
                    ~is_word_type (expr_type se))`
               (qx_choose_then `vt` assume_tac)
             >- (qpat_x_assum `reason_vv_ok vv` mp_tac >>
                qpat_x_assum `expr_type se = _` (fn th => rewrite_tac[th]) >>
                Cases_on `vv` >>
                simp[reason_vv_ok_def, reason_vv_def, vv_operand_def,
                     is_word_type_def]) >>
             qpat_x_assum `vv_store_bound _ _ _ _ _ _ _`
               (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_store_bound_def]) >>
             disch_then (qspecl_then [`vt`, `vv_operand vv`, `StringV str`,
               `BaseTV (StringT n)`, `w`] mp_tac) >>
             impl_tac
             >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                 qpat_x_assum `expr_type se = _` (fn th => rewrite_tac[th]) >>
                 first_assum ACCEPT_TAC) >>
             simp[val_store_size_def, word_size_def]) >>
          drule_all reason_mem_revert_path_mem >> disch_then ACCEPT_TAC) >>
      `reason_storage_vv vv` by metis_tac[] >>
      drule_all reason_storage_revert_path_mem >> disch_then ACCEPT_TAC) >>
  `reason_code_vv vv` by metis_tac[supported_reason_code] >>
  Cases_on `cenv.ce_is_ctor`
  >- (drule_all reason_ctor_code_revert_path_mem >> disch_then ACCEPT_TAC) >>
  drule_all reason_code_revert_path_mem >> disch_then ACCEPT_TAC
QED
