(* Counted composition of tuple staging, loads, and mixed stores. *)
Theory bodyMemAssignTupleTargetsSuffix
Ancestors
  bodyMemAssignTupleTargetsLoad bodyMemAssignTupleTargetsStore
  bodyMemAssignTupleTargetsGas
  tupleAssignPrefix stmtSimAssignTupleTargets tupleStageProps tupleMemoryLayout
  exprSimDefs exprSimProps exprLoweringProps stmtSimProps stmtSimDefs
  valueEncoding valueEncodingProps vyperTyping vyperInterpreter vyperState
  compileEnv loweringSlice fragExec freshWrites list rich_list finite_map
  fragGasPathMem bodyMemoryDefs tupleTargetStoreProps stmtSimReturn
  tupleAssignParts stmtLowering exprLowering vyperTypeABI vyperValue
  loweringPosts stmtSimAssignTuple tupleTypedLoad vyperTypeDefaults exprOperandVar
Libs
  monadsyntax

Theorem tuple_assignment_prefix_path_mem:
  !ctx func cenv cx es1 tys tvs vs sa su sl ss op staged elems sv flag d.
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    0 < type_memory_size_list tvs /\
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
    cs_extends su sl /\ cs_extends sl ss /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
    stmt_state_rel ctx func cenv cx es1 sv /\ alloca_history func sv /\
    return_buf_frame d cenv su sv /\ ~sv.vs_halted /\
    sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems /\
    local_ptrs_reserved cenv ss /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    ?t (w:256 word) b sz. stmt_state_rel ctx func cenv cx es1 t /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\
      t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      tuple_in_memory vs tvs (w2n w) t.vs_memory /\ b <= w2n w /\
      w2n w + type_memory_size_list tvs <= b + sz /\
      b + sz <= t.vs_alloca_next /\
      ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
       (?name. local_region cenv es1.scopes t name b sz)) /\
      w2n w + type_memory_size_list tvs < dimword (:256) /\
      (!i. i < LENGTH tys ==> ?v. eval_operand (EL i elems) t = SOME v /\
        if is_word_type (EL i tys) then
          v = typed_val_to_w256 (EL i tvs) (EL i vs)
        else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))) /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x sv) /\
      (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      alloca_history func t /\ return_buf_frame d cenv ss t /\
      sv.vs_alloca_next <= t.vs_alloca_next /\
      gas_path_mem ctx func sv 0 (OK t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    (irule evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT tys) = _` mp_tac >>
     simp_tac (srw_ss()) [evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    (irule type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `?sw. eval_operand op sv = SOME sw` by metis_tac[expr_val_rel_def] >>
  drule_all optional_tuple_stage_path_mem >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w. _`
    (qx_choosel_then [`st`, `w`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?b sz. _`
    (qx_choosel_then [`b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [GSYM optional_tuple_stage_code]) >>
  drule tuple_stage_grows >> strip_tac >>
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `su` >> simp[]) >>
  `w2n w + type_memory_size_list tvs < dimword (:256)` by
    (drule_all tuple_container_bound >> decide_tac) >>
  `w2n w + type_memory_size_list tvs <= st.vs_alloca_next` by decide_tac >>
  drule_all compile_tuple_load_all_typed_path_mem >> strip_tac >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at ss x) elems` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  asm_rewrite_tac[] >> qexistsl_tac [`t`, `w`, `b`, `sz`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sl x` by
        (irule not_fresh_at_mono >> qexists_tac `su` >> fs[cs_extends_def]) >>
      simp[]) >>
  `gas_path_mem ctx func sv (0 + 0) (OK t)` by
    (irule gas_path_mem_then >> qexists_tac `st` >> simp[]) >> gvs[]
QED

Theorem assign_tuple_targets_suffix_mem:
  !ctx func cx lctx cenv gs e es ee v tys tvs sa su sl ss sf op staged elems sv s0 flag d.
    expr_post ctx func cenv cx e es sa su s0 ee v op sv /\
    sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts /\ ~sv.vs_halted /\
    alloca_history func sv /\ return_buf_frame d cenv su sv /\
    ee.gas_obs = [] /\ value_has_type (TupleTV tvs) v /\
    gs <> [] /\ LENGTH gs = LENGTH tys /\ expr_type e = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
      tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs)
        (EL i (case v of ArrayV (TupleV vs) => vs | _ => []))) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT tys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT tys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    (flag ==> type_memory_size_list tvs < dimword (:256)) /\
    compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
    compile_tuple_store_all cenv tys gs elems ss = ((),sf) /\
    cs_extends sa su /\ sa.cs_next_var <= su.cs_next_var /\
    cs_extends su sl /\ cs_extends sl ss /\
    su.cs_next_var <= sl.cs_next_var /\ sl.cs_next_var <= ss.cs_next_var /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
    ?ee' t'.
      (!tail. assign_tuple_targets cx (TupleTarget gs) v (ee with gas_obs := tail) =
        (INL (), ee' with gas_obs := tail)) /\
      gas_path_mem ctx func sv 0 (OK t') /\
      alloca_history func t' /\ return_buf_frame d cenv sf t' /\
      sv.vs_alloca_next <= t'.vs_alloca_next /\
      stmt_post ctx func cx lctx cenv cenv sa sf s0 (INL ())
        (ee' with gas_obs := []) t'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    (gvs[evaluate_type_def, AllCaseEqs()] >>
     metis_tac[LIST_REL_LENGTH, values_have_types_length]) >>
  `LIST_REL (tuple_source_target cx ee.scopes) gs tvs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule tuple_target_aligned_source >>
     qexistsl_tac [`cenv`, `EL n tys`, `EL n vs`] >> simp[]) >>
  `LIST_REL value_has_type tvs vs` by simp[GSYM values_have_types_LIST_REL] >>
  `~cx.txn.is_static` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
  drule_all assign_tuple_targets_safe >> strip_tac >>
  rename1 `assign_tuple_targets _ _ _ ee = (INL (),ee')` >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  suspend "prefix"
QED

Resume assign_tuple_targets_suffix_mem[prefix]:
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    0 < type_memory_size (EL i tvs)` by
    (gen_tac >> disch_tac >> irule tuple_target_aligned_sizes >>
     qexists_tac `EL i gs` >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    simp[LIST_REL_EL_EQN] >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) tys tvs` by
    simp[LIST_REL_EL_EQN] >>
  `tys <> []` by (Cases_on `tys` >> gvs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tuple_memory_size_positive >> qexistsl_tac [`get_tenv cx`, `tys`] >>
     simp[] >> rpt strip_tac >>
     disj2_tac >> qexistsl_tac [`EL i tys`, `EL i tvs`] >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at su x` by
    metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv su` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[cs_extends_def]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op sv` by metis_tac[] >>
  `expr_val_at cenv cx (TupleT tys) sa su ee (ArrayV (TupleV vs)) op sv` by metis_tac[] >>
  drule_all tuple_assignment_prefix_path_mem >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t w b sz. _`
    (qx_choosel_then [`t`, `w`, `b`, `sz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "stores"
QED

(* Built once here rather than inside the proof below. *)
val tuple_store_targets_path_mem_T =
  SIMP_RULE (srw_ss()) [] (Q.SPECL [`gs`, `T`] tuple_store_targets_path_mem);

Resume assign_tuple_targets_suffix_mem[stores]:
  `!i. i < LENGTH gs ==> ?v. eval_operand (EL i elems) t = SOME v /\
    if is_word_type (EL i tys) then
      v = typed_val_to_w256 (EL i tvs) (EL i vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE i tvs))` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)` by
    (gen_tac >> disch_tac >> simp[] >> strip_tac >>
     `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by simp[] >>
     drule_all word_type_sizes >>
     disch_then (qspec_then `cenv` strip_assume_tac) >> simp[]) >>
  `LENGTH elems = LENGTH vs` by decide_tac >>
  `!i. i < LENGTH gs ==>
    tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
    tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)` by
    (rpt strip_tac >> simp[]) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(if flag then _ else _) su = _` kall_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `expr_val_rel _ (expr_type e) _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ (expr_type e) _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_val_rel _ (TupleT tys) _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ (TupleT tys) _ _ _ _ _ _` kall_tac >>
  drule_all tuple_store_targets_path_mem_T >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?t. stmt_state_rel ctx _ _ _ ee' _ /\ _`
    (qx_choose_then `sfv` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`ee'`, `sfv`] >> conj_tac
  >- (drule_all assign_tuple_target_list_gas_obs >>
      simp[Once evaluate_def]) >>
  conj_tac
  >- (drule_all gas_path_mem_then >> simp[]) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  suspend "frame"
QED

Resume assign_tuple_targets_suffix_mem[frame]:
  rpt strip_tac >>
  `not_fresh_at su x` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sl x` by
    (irule not_fresh_at_mono >> qexists_tac `su` >> simp[]) >>
  `not_fresh_at ss x` by
    (irule not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
  simp[]
QED

Finalise assign_tuple_targets_suffix_mem
