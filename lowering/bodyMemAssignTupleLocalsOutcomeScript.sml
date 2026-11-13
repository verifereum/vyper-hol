(* Normal suffix and counted statement composition for tuple locals. *)
Theory bodyMemAssignTupleLocalsOutcome
Ancestors
  bodyMemAssignTupleLocalsPrefix bodyMemAssignTupleLocalsStores stmtSimForced
  tupleAssignMemory tupleAssignPrefix tupleTypedLoad tupleStageProps
  tupleLocalStoreProps tupleMemoryFrame tupleMemoryLayout
  stmtSimAssignTuple stmtSimDeclMem stmtSimDeclStore stmtSimDefs exprSimDefs
  exprSimProps exprLoweringProps localPtrsProps compileEnv loweringPosts
  fragGasMode fragGasPath fragGasPathMem fragExec freshWrites
  list rich_list finite_map valueEncoding valueEncodingProps vyperTyping
  vyperTypeABI vyperInterpreter vyperState venomState venomInst vyperValue
  stmtLowering emitHelperProps exprLowering valueCopyBytes stmtSimReturn
  stmtSimForced exprSimMemDefs gasOutcome gasSummary gasSummaryCompose
  gasExemptCert bodyMemoryDefs bodyDeclMemoryCore gasContext vyperExprNoControl
  vyperLookup exprOperandVar stmtSimProps stmtSimDeclCompose gasOracleReplay
  gasStorage vyperStorageTrace vyperStorageFootprint exprSimWordArgs
Libs
  monadsyntax

(* S1 assign_tuple_locals_memory_suffix_path, with allocation history and
   the memory frontier carried by the staging/load/store interfaces. *)
Theorem assign_tuple_locals_memory_suffix_path_mem:
  !H ctx func cx cenv ids es1 es' tys tvs vs sa su sl ss sf op staged elems sv flag d.
    ids <> [] /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (!i. i < LENGTH ids ==> ?p sz vt.
      FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type (EL i ids) = SOME vt /\
      if is_word_type (EL i tys) then is_word_type vt else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
          type_memory_bytes cenv vt = type_memory_size vtv /\
          0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256)) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    (!i entry. i < LENGTH ids /\ lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
      if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
      else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type (EL i vs)) /\
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es1 = (INL (),es') /\
    expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv /\
    expr_val_at cenv cx (TupleT tys) sa su es1 (ArrayV (TupleV vs)) op sv /\
    (!x. op = Var x ==> not_fresh_at su x) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) elems ss = ((),sf) /\
    su.cs_next_var <= sl.cs_next_var /\ sl.cs_next_var <= ss.cs_next_var /\
    cs_extends su sl /\ cs_extends sl ss /\ cs_extends ss sf /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
    stmt_state_rel H ctx func cenv cx es1 sv /\ alloca_history func sv /\
    return_buf_frame d cenv su sv /\ ~sv.vs_halted /\
    sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
    ~block_is_terminated sf /\
    ?t. stmt_state_rel H ctx func cenv cx es' t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x sv) /\
      (!aid b. FLOOKUP sv.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      alloca_history func t /\ sv.vs_alloca_next <= t.vs_alloca_next /\
      gas_marked_path T ctx func sv 0 (OK t) /\
      t.vs_accounts = sv.vs_accounts /\ t.vs_transient = sv.vs_transient /\
      t.vs_requests = sv.vs_requests /\ t.vs_call_ctx = sv.vs_call_ctx
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `values_have_types tvs vs` by gvs[value_has_type_def] >>
  drule assign_tuple_target_list_length >> strip_tac >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `LENGTH ids = LENGTH vs /\ LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, values_have_types_length, LENGTH_MAP] >>
  suspend "code"
QED

Resume assign_tuple_locals_memory_suffix_path_mem[code]:
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    (irule tuple_element_sizes >> reverse conj_tac
     >- (qexists `get_tenv cx` >> first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tuple_memory_size_positive >> qexistsl_tac [`get_tenv cx`, `tys`] >>
     simp[SF CONJ_ss] >> rpt gen_tac >> strip_tac >>
     Cases_on `is_word_type (EL i tys)` >- simp[] >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> metis_tac[]) >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    (irule type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `?sw. eval_operand op sv = SOME sw` by metis_tac[expr_val_rel_def] >>
  drule_all optional_tuple_stage_path_mem >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w. _`
    (qx_choosel_then [`st`, `w`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?b sz. _`
    (qx_choosel_then [`b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists `su` >> simp[]) >>
  `w2n w + type_memory_size_list tvs < dimword (:256)` by
    (drule_all tuple_container_bound >> decide_tac) >>
  drule_all compile_tuple_load_all_typed_path_mem >> strip_tac >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  suspend "store"
QED

Resume assign_tuple_locals_memory_suffix_path_mem[store]:
  `LENGTH ids = LENGTH tys /\ LENGTH elems = LENGTH vs` by decide_tac >>
  `!i. i < LENGTH ids ==> ?v. eval_operand (EL i elems) t = SOME v /\
     if is_word_type (EL i tys) then
       v = typed_val_to_w256 (EL i tvs) (EL i vs)
     else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. i < LENGTH ids ==> ?p dsz vt.
     FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) dsz) /\
     cenv.ce_var_type (EL i ids) = SOME vt /\
     (is_word_type vt = is_word_type (EL i tys)) /\
     (~is_word_type (EL i tys) ==>
       (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
       type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
       ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
         type_memory_bytes cenv vt = type_memory_size vtv /\
         0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256))` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> ?p sz vt. _` (qspec_then `i` mp_tac) >>
     simp[] >> POP_ASSUM_LIST (K all_tac) >>
     disch_then (qx_choosel_then [`p`, `sz`, `vt`]
       (map_every assume_tac o CONJUNCTS)) >>
     qexistsl_tac [`p`, `sz`, `vt`] >>
     Cases_on `is_word_type (EL i tys)` >> gvs[] >>
     metis_tac[is_bytestring_word_type]) >>
  suspend "store_ready"
QED

Resume assign_tuple_locals_memory_suffix_path_mem[store_ready]:
  `!i. i < LENGTH tys ==>
     evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
     (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)` by
    (rpt gen_tac >> strip_tac >>
     `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by
       (qpat_assum `LIST_REL (\t tv. evaluate_type _ t = SOME tv) _ _`
          (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
        disch_then (qspec_then `i` mp_tac o CONJUNCT2) >> simp[]) >>
     simp[] >> strip_tac >> drule_all word_type_sizes >>
     disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]) >>
  `tuple_in_memory vs tvs (w2n w) t.vs_memory /\
   w2n w + type_memory_size_list tvs <= t.vs_alloca_next` by simp[] >>
  SUBGOAL_THEN
    ``(?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
      (?name. local_region cenv es1.scopes t name b sz)`` assume_tac
  >- (simp[] >> metis_tac[]) >>
  drule_all tuple_store_mixed_locals_path_mem >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t. stmt_state_rel H ctx _ _ _ es' _ /\ _`
    (qx_choose_then `sfv` (map_every assume_tac o CONJUNCTS)) >>
  suspend "compose"
QED

Resume assign_tuple_locals_memory_suffix_path_mem[compose]:
  conj_tac >- (first_x_assum irule >> simp[]) >>
  qexists `sfv` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sl x /\ not_fresh_at ss x` by
        metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  `gas_marked_path T ctx func sv 0 (OK st) /\
   gas_marked_path T ctx func st 0 (OK t)` by simp[gas_marked_path_def] >>
  `gas_marked_path T ctx func sv (0 + 0) (OK t)` by
    (irule gas_marked_path_then >> qexists `st` >> simp[]) >>
  fs[] >>
  `gas_marked_path T ctx func sv (0 + 0) (OK sfv)` by
    (irule gas_marked_path_then >> qexists `t` >> simp[]) >> fs[]
QED

Finalise assign_tuple_locals_memory_suffix_path_mem

(* Source boundary from S1 stmtSimAssignTuple, absent in the overlay. *)
Theorem eval_assign_tuple_action[local]:
  eval_stmt cx (Assign (TupleTarget gs) e) =
  bind (bind (eval_expr cx e) (read_result cx))
    (assign_tuple_targets cx (TupleTarget gs))
Proof
  simp[Once evaluate_def, FUN_EQ_THM, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[bind_def]
QED

(* S1 stmtSimAssignTuple gas-frame source boundaries. *)
Theorem assign_tuple_target_local_gas[local]:
  assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (res, ee) ==>
  !tail. assign_tuple_targets cx (BaseTarget (NameTarget id)) v
    (es with gas_obs := tail) = (res, ee with gas_obs := tail)
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def,
       get_place_def, write_place_def, lift_option_type_def, lift_sum_def,
       replace_memory_entry_def, evaluate_subscripts_def,
       assign_subscripts_def, set_scopes_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope id es.scopes` >>
  gvs[return_def, raise_def] >> PairCases_on `x` >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      set_scopes_def, AllCaseEqs()]
QED

Theorem assign_tuple_target_list_locals_gas[local]:
  !ids cx vs es res ee.
  assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es =
    (res, ee) ==>
  !tail. assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs
    (es with gas_obs := tail) = (res, ee with gas_obs := tail)
Proof
  Induct >> Cases_on `vs` >> rpt gen_tac >> strip_tac >> gen_tac >>
  gvs[Once evaluate_def, return_def, raise_def] >>
  simp[Once evaluate_def, return_def, raise_def] >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs()] >>
  drule assign_tuple_target_local_gas >>
  disch_then (qspec_then `tail` assume_tac) >>
  simp[] >> metis_tac[]
QED

Theorem assign_tuple_locals_gas[local]:
  assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))
    v es = (res, ee) ==>
  !tail. assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))
    v (es with gas_obs := tail) = (res, ee with gas_obs := tail)
Proof
  Cases_on `v` >> simp[evaluate_def, raise_def] >>
  Cases_on `a` >> simp[raise_def] >>
  metis_tac[assign_tuple_target_list_locals_gas]
QED

(* S1 compile_assign_tuple_locals_memory_stmt_frag, using the memory
   expression outcome and the counted, memory-checked suffix above. *)
Theorem compile_assign_tuple_locals_memory_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty ids e es tys tvs.
    ids <> [] /\
    expr_type e = TupleT tys /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
     type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH ids ==>
       ?p sz vt.
         FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         if is_word_type (EL i tys) then is_word_type vt
         else
           (vt = EL i tys \/
            is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
           type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
           ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
                 type_memory_bytes cenv vt = type_memory_size vtv /\
                 0 < type_memory_size vtv /\
                 type_memory_size vtv + 64 < dimword (:256)) /\
    (!gs v es1. (do result <- eval_expr cx e; read_result cx result od)
               (es with gas_obs := gs) = (INL v, es1) ==>
               value_has_type (TupleTV tvs) v) /\
    (!gs vs es1 i entry.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL (ArrayV (TupleV vs)), es1) /\
       i < LENGTH ids /\
       lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
       if is_word_type (EL i tys) then
         store_lays_out (EL i tvs) entry.type (EL i vs)
       else
         ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
              evaluate_type (get_tenv cx) vt = SOME entry.type /\
              value_has_type entry.type (EL i vs)) /\
    expr_sim_mem ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (eval_stmt cx
         (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `!i. i < LENGTH ids /\ i < LENGTH tys ==> ?p sz vt.
     FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
     cenv.ce_var_type (EL i ids) = SOME vt /\
     (is_word_type vt = is_word_type (EL i tys)) /\
     (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> qexistsl [`p`, `sz`, `vt`] >>
     Cases_on `is_word_type (EL i tys)` >> gvs[] >>
     metis_tac[is_bytestring_word_type]) >>
  drule_all assign_tuple_locals_memory_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by
    (irule (cj 1 fn_has_code_split) >> simp[] >> qexists `sb` >> simp[] >>
     metis_tac[cs_extends_trans]) >>
  RULE_ASSUM_TAC (REWRITE_RULE [eval_assign_tuple_action]) >>
  drule forced_then_admissible >> strip_tac >>
  pure_rewrite_tac[eval_assign_tuple_action] >>
  irule forced_then_outcome >>
  qexists_tac `\H v ee t.
    expr_post H ctx func cenv cx e es sa su s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = su.cs_current_bb /\
    t.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> simp[vyperStorageTraceTheory.evaluate_storage_trace_frame])
  >~ [`expr_exit (INR _) _`]
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])
  >~ [`gas_outcome _ _ _ _ _ _ _ _ _`]
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`st0`, `sa`, `su`, `op`, `s0`] mp_tac) >>
      simp[]) >>
  suspend "cont"
QED

Resume compile_assign_tuple_locals_memory_stmt_frag_mem[cont]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `valid_horizon cx st0 H1 ee.storage_trace` >>
  qpat_x_assum `?gs. _` (qx_choose_then `gs` assume_tac) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `value_has_type (TupleTV tvs) v` by
    (qpat_x_assum `!gs v es1. _ ==> value_has_type (TupleTV _) _`
       (qspecl_then [`gs`, `v`, `ee`] irule) >> first_assum ACCEPT_TAC) >>
  Cases_on `assign_tuple_targets cx
    (TupleTarget (MAP (BaseTarget o NameTarget) ids)) v ee` >>
  rename1 `_ = (res, ee')` >>
  `bind (bind (eval_expr cx e) (read_result cx))
     (assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids)))
     (es with gas_obs := gs) = (res, ee')` by
    (pure_once_rewrite_tac[bind_def] >> BETA_TAC >> simp[]) >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  `res = INL ()` by
    (drule assign_tuple_locals_ok >> disch_then irule >> gvs[stmt_res_ok_def]) >>
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  `!x. op = Var x ==> not_fresh_at su x` by
    metis_tac[compile_lower_value_var] >>
  `ee'.accounts = ee.accounts /\ ee'.tStorage = ee.tStorage` by
    (qpat_assum `assign_tuple_targets _ _ _ _ = _`
       (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
     drule tupleLocalStorePropsTheory.assign_tuple_target_list_locals_backends >> strip_tac >> simp[]) >>
  `!tail. assign_tuple_targets cx
     (TupleTarget (MAP (BaseTarget o NameTarget) ids))
     (ArrayV (TupleV vs)) (ee with gas_obs := tail) =
     (INL (), ee' with gas_obs := tail)` by
    (drule assign_tuple_locals_gas >> simp[]) >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee t /\
       storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==>
                      expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     rewrite_tac[expr_post_def] >> strip_tac >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==>
                   expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H1` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  rewrite_tac[expr_post_def] >> strip_tac >>
  suspend "suffix"
QED

Resume compile_assign_tuple_locals_memory_stmt_frag_mem[suffix]:
  `!i entry. i < LENGTH ids /\ lookup_scopes (EL i ids) ee.scopes = SOME entry ==>
     if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
     else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
       evaluate_type (get_tenv cx) vt = SOME entry.type /\
       value_has_type entry.type (EL i vs)` by
    (rpt strip_tac >> qpat_x_assum `!gs vs es1 i entry. _` irule >>
     conj_tac >- simp[] >> qexistsl [`ee`, `gs`] >> simp[]) >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `return_buf_frame d cenv su t` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`, `s0`, `sa`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  `post_value_type cenv e = expr_type e` by
    (`lowered_value_type cenv e = expr_type e` by simp[] >>
     pop_assum mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
     Cases_on `e` >> gvs[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     gvs[post_value_type_def, vyperASTTheory.expr_type_def]) >>
  `expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op t /\
   expr_val_at cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op t` by
    (qpat_x_assum `expr_type e = _` SUBST_ALL_TAC >> gvs[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ?u. stmt_state_rel H ctx func cenv cx ee' u /\
           u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
           u.vs_requests = t.vs_requests /\ u.vs_call_ctx = t.vs_call_ctx` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee t` by metis_tac[] >>
     drule_all (Q.SPEC `H` (CONV_RULE (DEPTH_CONV ETA_CONV)
                  assign_tuple_locals_memory_suffix_path_mem)) >>
     strip_tac >> qexists_tac `t'` >> simp[]) >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
               assign_tuple_locals_memory_suffix_path_mem) >>
  strip_tac >>
  suspend "post"
QED

Resume compile_assign_tuple_locals_memory_stmt_frag_mem[post]:
  qexistsl [`INL ()`, `ee' with gas_obs := []`, `OK t'`] >>
  rpt conj_tac
  >- simp[]
  >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexists_tac `t'` >> conj_tac >- REFL_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (irule vyperStorageFootprintTheory.valid_horizon_frame >>
     qexistsl [`assign_tuple_targets cx
                  (TupleTarget (MAP (BaseTarget o NameTarget) ids))
                  (ArrayV (TupleV vs))`, `INL ()`, `ee'`] >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?u. stmt_state_rel H ctx func cenv cx ee' u /\
       u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
       u.vs_requests = t.vs_requests /\ u.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[] >>
  `stmt_state_rel H ctx func cenv cx ee' t'` by
    (mp_tac (Q.INST [`H0` |-> `H1`, `u` |-> `t'`, `s` |-> `u`, `es` |-> `ee'`]
               exprLoweringPropsTheory.stmt_state_rel_fields_transport) >>
     impl_tac >- (rpt conj_tac >> simp[]) >> simp[]) >>
  `storage_well_formed_on cx (ee' with gas_obs := []) (FST H)` by
    (`storage_well_formed_on cx ee (FST H)` by metis_tac[] >>
     `(ee' with gas_obs := []).accounts = ee.accounts /\
      (ee' with gas_obs := []).tStorage = ee.tStorage` by simp[] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  `sa.cs_next_var <= sb.cs_next_var` by decide_tac >>
  `return_buf_frame d cenv sb t'` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`, `s0`, `sa`] >> simp[] >>
     conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at su x` by metis_tac[not_fresh_at_mono] >> metis_tac[])
     >> decide_tac) >>
  BETA_TAC >> qexists_tac `cenv` >> rpt conj_tac
  >- simp[stmt_lands_def]
  >- simp[]
  >- simp[]
  >- simp[cenv_top_ext_refl]
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >>
      `not_fresh_at su x` by metis_tac[not_fresh_at_mono] >> metis_tac[])
  >- metis_tac[]
  >- first_assum ACCEPT_TAC
  >- simp[]
  >- decide_tac
QED

Finalise compile_assign_tuple_locals_memory_stmt_frag_mem
