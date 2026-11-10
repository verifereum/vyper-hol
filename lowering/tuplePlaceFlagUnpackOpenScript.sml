(* Nonempty actual-flag unpack with success-only compiler openness. *)
Theory tuplePlaceFlagUnpackOpen
Ancestors
  tuplePlaceFlagPrefix tuplePlaceSuffixOpen tuplePlaceRootReady tuplePlaceOpen
  stmtSimDeclCompose exprSimMemDefs vyperInterpreter tuplePlaceHead

Theorem tuple_place_flag_unpack_outcome_open:
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\ gs <> [] /\
  value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
  expr_post ctx func cenv cx e es sa su s0 ee (ArrayV (TupleV vs)) op sv /\
  (!x. op = Var x ==> not_fresh_at su x) /\ sa.cs_next_id <= su.cs_next_id /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  compile_tuple_unpack cenv (TupleT ltys) flag gs op su = ((),sf) /\
  fn_has_code su sf func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
  ~sv.vs_halted /\ sv.vs_current_bb = su.cs_current_bb /\
  sv.vs_inst_idx = LENGTH su.cs_current_insts /\
  expr_sim_inv cenv cx env ee /\
  LIST_REL (\g t. well_typed_atarget env g t) gs tys /\
  EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target_pure tops bt /\
    target_case F ctx func cenv cx bt /\ ~immutable_root cx bt /\
    target_indices_pre cenv cx env bt /\ call_evaluation_safe cx (int_calls_target bt)) gs /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  type_alloc_ok cenv (TupleT tys) /\ acyclic_struct_metadata cenv.ce_struct_fields ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs))) (ee,sv)
    (\res ff t. res = INL () /\ expr_sim_inv cenv cx env ff /\ ~block_is_terminated sf /\
      stmt_state_rel ctx func cenv cx ff t /\ ~t.vs_halted /\
      t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x v. not_fresh_at su x /\ lookup_var x sv = SOME v ==> lookup_var x t = SOME v) /\
      (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      alloca_frame cenv ee su sv cenv ff t)
    (\res ff r. expr_exit res r)
Proof
  strip_tac >>
  drule_all tuple_place_compiler_flag_prefix_head >> strip_tac >>
  `ltys <> []` by
    (imp_res_tac vyperTypeArgFitsTheory.arg_types_fit_LENGTH >>
     fs[listTheory.LIST_REL_EL_EQN] >> Cases_on `ltys` >> fs[]) >>
  `~block_is_terminated ss` by
    (irule tuple_place_load_open_probe >> goal_assum (drule_at Any) >> simp[]) >>
  `su.cs_next_var <= sl.cs_next_var` by
    (irule (cj 2 stmtSimAssignTupleTheory.tuple_stage_grows) >>
     qexistsl [`flag /\ EXISTS (\t. ~is_word_type t) ltys /\
        0 < type_memory_size_list ltvs`, `op`, `staged`,
       `type_memory_bytes cenv (TupleT ltys)`] >>
     qpat_x_assum `(if _ then _ else _) su = (staged,sl)` mp_tac >>
     Cases_on `flag /\ EXISTS (\t. ~is_word_type t) ltys /\
       0 < type_memory_size_list ltvs` >>
     simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_ignore_bind_def] >> pairarg_tac >>
     simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def]) >>
  `sl.cs_next_var <= ss.cs_next_var` by
    metis_tac[stmtSimReturnTheory.compile_tuple_load_all_grows] >>
  `gas_outcome F (cx_tops cx) (ctx,func)
     (assign_tuple_target_list cx gs vs) (ee,t)
     (\res ff q. res = INL () /\ expr_sim_inv cenv cx env ff /\ ~block_is_terminated sf /\
       tuple_place_head ctx func cenv cx ff sa.cs_next_id sf
         tys ltys ltvs vs elems w (LENGTH tys) q /\
       (!x v. not_fresh_at ss x /\ lookup_var x t = SOME v ==> lookup_var x q = SOME v) /\
       (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
         FLOOKUP q.vs_allocas aid = SOME entry) /\
       alloca_frame cenv ee ss t cenv ff q)
     (\res ff r. expr_exit res r)` by
    (irule (SRULE [] (DISCH_ALL (Q.SPEC `0` (UNDISCH (SPEC_ALL tuple_place_suffix_run_open))))) >>
     simp[] >> metis_tac[]) >>
  simp[Once evaluate_def] >>
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `sl.cs_next_id <= ss.cs_next_id` by
    (mp_tac (cj 4 stmtLoweringMonoTheory.ci_mono_list_helpers) >>
     disch_then (qspecl_then [`cenv`, `staged`, `ltys`, `0`, `sl`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `su.cs_next_id <= sl.cs_next_id` by
    (qpat_x_assum `(if _ then _ else _) su = (staged,sl)` mp_tac >>
     IF_CASES_TAC >> simp[compileEnvTheory.comp_return_def] >>
     simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def] >>
     pairarg_tac >> simp[compileEnvTheory.comp_return_def] >>
     pairarg_tac >> simp[compileEnvTheory.comp_return_def] >> strip_tac >>
     imp_res_tac pairTheory.SND >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
       exprLoweringPropsTheory.ci_mono_emit_void, exprLoweringPropsTheory.ci_mono_def,
       pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]) >>
  fs[tuple_place_head_def] >>
  reverse conj_tac
  >- (irule stmtSimDefsTheory.alloca_frame_trans >>
      qexistsl [`cenv`, `ee`, `t`, `ss`] >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  `not_fresh_at ss x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  metis_tac[]
QED
