(* Flag-parametric bridge from the expression endpoint to the suffix head. *)
Theory tuplePlaceFlagPrefix
Ancestors
  tuplePlaceHead tupleAssignParts abiCallerTupleLayout
Libs monadsyntax

Theorem flag_optional_stage_path[local]:
  !ctx func cenv cx es flag tys ltys ltvs vs sa su sl staged op s sw.
    (if flag then
       do buf <- compile_alloc_buffer (type_memory_size_list ltvs);
          emit_void MCOPY [buf.buf_operand; op; Lit (n2w (type_memory_size_list ltvs))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    tuple_in_memory vs ltvs (w2n sw) s.vs_memory /\ tuple_val_wf vs ltvs /\
    w2n sw + type_memory_size_list ltvs < dimword (:256) /\
    tuple_place_snapshot cenv cx es sa.cs_next_id su.cs_next_id tys ltys ltvs sw s /\
    sa.cs_next_id <= su.cs_next_id /\
    fn_has_code su sl func /\ local_ptrs_reserved cenv su /\
    (!x. op = Var x ==> not_fresh_at su x) /\ eval_operand op s = SOME sw /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
    s.vs_inst_idx = LENGTH su.cs_current_insts ==>
    ?t w. eval_operand staged t = SOME w /\
      tuple_in_memory vs ltvs (w2n w) t.vs_memory /\
      w2n w + type_memory_size_list ltvs < dimword (:256) /\
      tuple_place_snapshot cenv cx es sa.cs_next_id sl.cs_next_id tys ltys ltvs w t /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sl x) /\
      ~t.vs_halted /\ t.vs_current_bb = sl.cs_current_bb /\
      t.vs_inst_idx = LENGTH sl.cs_current_insts /\
      gas_marked_path F ctx func s 0 (OK t) /\
      alloca_frame cenv es su s cenv es t
Proof
  rpt gen_tac >> strip_tac >> Cases_on `flag`
  >- (gvs[] >>
      `val_in_memory (TupleTV ltvs) (ArrayV (TupleV vs)) (w2n sw) s.vs_memory /\
       val_wf (TupleTV ltvs) (ArrayV (TupleV vs)) /\
       val_footprint (TupleTV ltvs) (ArrayV (TupleV vs)) <= type_memory_size_list ltvs` by
        simp[valueEncodingDefsTheory.val_in_memory_def, valueEncodingDefsTheory.val_wf_def,
          loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
      `type_memory_size_list ltvs < dimword (:256)` by decide_tac >>
      drule_all tuplePlaceStageTheory.tuple_place_stage_snapshot_path >>
      disch_then (qspecl_then [`tys`, `ltys`]
        (qx_choosel_then [`t`, `w`] strip_assume_tac)) >>
      `w2n w + type_memory_size_list ltvs < dimword (:256)` by
        (irule tupleTypedLoadTheory.tuple_container_bound >>
         goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
         disj1_tac >> qexists `su.cs_next_id` >> simp[]) >>
      qexistsl [`t`, `w`] >> gvs[valueEncodingDefsTheory.val_in_memory_def]) >>
  gvs[compileEnvTheory.comp_return_def] >> qexistsl [`s`, `sw`] >> simp[] >>
  simp[fragGasModeTheory.gas_marked_path_def, cj 1 fragGasPathTheory.gas_path_rules,
    stmtSimDefsTheory.alloca_frame_def] >> metis_tac[]
QED

Theorem flag_assignment_prefix_head[local]:
  !ctx func cenv cx es es1 tys ltys ltvs vs sa su sl ss op staged elems sv s0 e flag.
    expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\
    value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
    evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
    expr_post ctx func cenv cx e es sa su s0 es1 (ArrayV (TupleV vs)) op sv /\
    (!x. op = Var x ==> not_fresh_at su x) /\ sa.cs_next_id <= su.cs_next_id /\
    (if flag /\ EXISTS (\t. ~is_word_type t) ltys /\
        0 < type_memory_size_list ltvs then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT ltys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT ltys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    compile_tuple_load_all cenv staged ltys 0 sl = (elems,ss) /\
    cs_extends sl ss /\ fn_has_code su sl func /\ fn_has_code sl ss func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
    ~sv.vs_halted /\ sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
    ?t w. tuple_place_head ctx func cenv cx es1 sa.cs_next_id ss
      tys ltys ltvs vs elems w 0 t /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x sv) /\
      (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      gas_marked_path F ctx func sv 0 (OK t) /\
      alloca_frame cenv es1 su sv cenv es1 t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuplePlaceRhsCertTheory.tuple_place_rhs_certificate >> strip_tac >>
  `values_have_types ltvs vs` by gvs[vyperTypingTheory.value_has_type_def] >>
  `LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv) ltys ltvs` by
    (irule vyperTypeABITheory.evaluate_types_LIST_REL >>
     qpat_assum `evaluate_type _ (TupleT ltys) = _` mp_tac >>
     simp_tac (srw_ss()) [vyperValueTheory.evaluate_type_def, LET_THM, AllCaseEqs()] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `type_memory_bytes cenv (TupleT ltys) = type_memory_size_list ltvs` by
    (irule tupleStagePropsTheory.type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `w2n w + type_memory_size_list ltvs < dimword (:256)` by
    (Cases_on `type_memory_size_list ltvs = 0`
     >- simp[wordsTheory.w2n_lt] >>
     `0 < type_memory_size_list ltvs` by decide_tac >>
     drule_all tupleStagePropsTheory.expr_tuple_memory_owned >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_x_assum `?b sz. _` (qx_choosel_then [`b`, `sz`]
       (map_every assume_tac o CONJUNCTS)) >>
     drule_all tupleTypedLoadTheory.tuple_container_bound >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `if guard then _ else _` >>
  `cs_extends su sl /\ su.cs_next_var <= sl.cs_next_var` by
    (irule stmtSimAssignTupleTheory.tuple_stage_grows >>
     qexistsl [`guard`, `op`, `staged`, `type_memory_size_list ltvs`] >>
     Cases_on `guard` >>
     gvs[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def]) >>
  `local_ptrs_reserved cenv sl` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists `su` >> simp[]) >>
  fs[] >> drule flag_optional_stage_path >>
  disch_then (drule_at (Pat `tuple_place_snapshot _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspec_then `vs` mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`st`, `sw`] strip_assume_tac) >>
  drule tuplePlaceLoadTheory.tuple_place_load_snapshot_path >>
  disch_then (drule_at (Pat `tuple_place_snapshot _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`vs`, `get_tenv cx`] mp_tac) >>
  simp[] >> strip_tac >>
  `alloca_frame cenv es1 su sv cenv es1 t` by
    (fs[stmtSimDefsTheory.alloca_frame_def] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!aid off sz. _` (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  qexistsl [`t`, `sw`] >> simp[] >>
  conj_tac
  >- (irule tuple_place_head_intro >> simp[] >>
      gvs[listTheory.LIST_REL_EL_EQN]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sl x` by gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> simp[]) >>
  `gas_marked_path F ctx func sv (0 + 0) (OK t)` suffices_by simp[] >>
  irule fragGasModeTheory.gas_marked_path_then >> qexists `st` >> simp[]
QED

Theorem tuple_place_compiler_flag_prefix_head:
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\
  value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
  expr_post ctx func cenv cx e es sa su s0 es1 (ArrayV (TupleV vs)) op sv /\
  (!x. op = Var x ==> not_fresh_at su x) /\ sa.cs_next_id <= su.cs_next_id /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  compile_tuple_unpack cenv (TupleT ltys) flag gs op su = ((),sf) /\
  fn_has_code su sf func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
  ~sv.vs_halted /\ sv.vs_current_bb = su.cs_current_bb /\
  sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?staged sl elems ss t w.
    (if flag /\ EXISTS (\t. ~is_word_type t) ltys /\
        0 < type_memory_size_list ltvs then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT ltys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT ltys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    compile_tuple_load_all cenv staged ltys 0 sl = (elems,ss) /\
    compile_tuple_store_all cenv ltys gs elems ss = ((),sf) /\
    cs_extends su sl /\ cs_extends sl ss /\ cs_extends ss sf /\
    fn_has_code su sl func /\ fn_has_code sl ss func /\ fn_has_code ss sf func /\
    tuple_place_head ctx func cenv cx es1 sa.cs_next_id ss
      tys ltys ltvs vs elems w 0 t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x sv) /\
    (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    gas_marked_path F ctx func sv 0 (OK t) /\
    alloca_frame cenv es1 su sv cenv es1 t
Proof
  strip_tac >>
  `SUM (MAP (type_memory_bytes cenv) ltys) = type_memory_size_list ltvs` by
    (irule abiCallerTupleLayoutTheory.abi_caller_memory_size_list >> simp[]) >>
  `~(flag /\ EXISTS (\t. ~is_word_type t) ltys /\
     0 < type_memory_size_list ltvs /\ ~cenv.ce_target CapMcopy)` by metis_tac[] >>
  qpat_x_assum `compile_tuple_unpack _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [stmtLoweringTheory.compile_tuple_unpack_def,
    LET_THM, GSYM CONJ_ASSOC, arithmeticTheory.GREATER_DEF,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def,
    GSYM compileEnvTheory.type_memory_bytes_def] >>
  qmatch_goalsub_abbrev_tac `(if guard then stage else comp_return op) su` >>
  Cases_on `(if guard then stage else comp_return op) su` >>
  rename1 `_ = (staged,sl)` >> simp[] >>
  Cases_on `compile_tuple_load_all cenv staged ltys 0 sl` >>
  rename1 `compile_tuple_load_all _ _ _ _ _ = (elems,ss)` >>
  simp[] >> strip_tac >> qunabbrev_tac `stage` >>
  drule (SRULE [compileEnvTheory.comp_ignore_bind_def]
    stmtSimAssignTupleTheory.tuple_stage_grows) >> strip_tac >>
  drule stmtSimReturnTheory.compile_tuple_load_all_grows >> strip_tac >>
  drule tuple_target_stores_growth >> strip_tac >>
  `cs_extends sl sf` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code su sl func /\ fn_has_code sl sf func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code sl ss func /\ fn_has_code ss sf func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `type_memory_bytes cenv (TupleT ltys) = type_memory_size_list ltvs` by
    (simp[compileEnvTheory.type_memory_bytes_def] >> metis_tac[]) >>
  `(if guard then
      do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT ltys));
         emit_void MCOPY [buf.buf_operand; op;
           Lit (n2w (type_memory_bytes cenv (TupleT ltys)))];
         comp_return buf.buf_operand od
    else comp_return op) su = (staged,sl)` by
    (Cases_on `guard` >>
     gvs[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
     pairarg_tac >> gvs[compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def]) >>
  gnvs[compileEnvTheory.comp_ignore_bind_def] >>
  irule flag_assignment_prefix_head >> simp[] >> goal_assum (drule_at Any) >>
  simp[Abbr `guard`, compileEnvTheory.comp_ignore_bind_def] >> metis_tac[]
QED
