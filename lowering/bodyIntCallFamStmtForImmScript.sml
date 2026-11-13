(* Immutable-array case of the internal-call For producer: iteration over a
   main-module immutable array (TopLevelName), through the generic counted
   loop of bodyIntCallFamStmtForArrayGen. *)
Theory bodyIntCallFamStmtForImm
Ancestors
  bodyIntCallFamStmtForImmEntry bodyIntCallFamStmtForImmCopy
  bodyIntCallFamStmtForArrayGen bodyIntCallJointContract
  bodyIntCallJointStmtSeq bodyIntCallJointStmtBoundary
  whitelistForIterImmLoop whitelistForIterImmSource whitelistForIterImmFrame
  whitelistForIterImmCopy whitelistForIterImmFrag whitelistForIterDynFrag
  bodyStorageMetadata exprSimTopLevelProps exprSimHyps
  stmtSimProps stmtSimDefs bodySim exprSimHypsDefs vyperTyping
  vyperTypeSystem vyperTypeValues vyperTypeInvariants vyperBareGlobalName
  bodySimDeclCases bodyExprPreFacts stmtLoweringMono stmtLowering
  stmtSimForArray stmtSimForArrayLoop stmtForArrayMemorySupport stmtSimDeclCompose
  exprSimSubscriptMap supportedStmts supportedStmtTraverse
  valueEncodingProps valueEncodingTyping exprLoweringProps localPtrsProps
  loweringPosts loweringStateRelDefs compileEnv fragExec allocLimits
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperAST
  venomState venomInst finite_map list arithmetic

(* The For statement runs its loop on the iterator's values when they fit
   the bound. *)
Theorem intcall_imm_eval_for_source[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs <= n /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
    (INL vs, es with gas_obs := gs)) ==>
  !gs. eval_stmt cx (For id et it n stmts) (es with gas_obs := gs) =
    eval_for cx tv id stmts vs (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  simp[Once evaluate_def, lift_option_type_def, bind_def, return_def,
       ignore_bind_def, check_def, compatible_bound_def, assert_def]
QED

(* The immutable array's header and elements, read at any state where the
   array is still the one the loop started from. *)
Theorem intcall_imm_source_holds[local]:
  expr_sim_inv ce cx env ei /\
  FLOOKUP env.bare_globals (ce.ce_module,name) = SOME (ArrayT fty bd) /\
  lookup_immutable cx ei ce.ce_module name = SOME (ArrayTV tv bd,ArrayV av) /\
  evaluate_type (get_tenv cx) fty = SOME tv /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  vs = array_elements (ArrayTV tv bd) av ==>
  (!cap. bd = Dynamic cap ==>
     immutable_holds ce cx (ArrayT fty (Dynamic cap)) (Value (ArrayV av))
       (n2w off) ei t /\
     value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
     LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
  (!k. k < LENGTH vs ==>
     immutable_holds ce cx fty (Value (EL k vs))
       (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                       k * type_memory_size tv)) ei t)
Proof
  strip_tac >>
  drule_all immutable_array_source_ready >> strip_tac >>
  gvs[lookup_immutable_def] >>
  `immutable_holds ce cx (ArrayT fty bd) (Value (ArrayV av)) (n2w off) ei t` by
    (simp[immutable_holds_def, read_result_def, return_def] >>
     qexistsl_tac [`name`, `off`, `ArrayTV tv bd`, `ArrayV av`, `0`] >>
     simp[sub_layout_def]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      Cases_on `av` >> gvs[value_has_type_def, array_elements_def, array_length_def]) >>
  rpt strip_tac >> once_rewrite_tac[ADD_COMM] >>
  irule (cj 1 immutable_iter_element_ready) >> simp[] >>
  qexistsl_tac [`av`, `Value (ArrayV av)`] >>
  simp[read_result_def, return_def] >>
  metis_tac[value_has_type_val_wf]
QED

(* Names of the form %n are fresh exactly from n on. *)
Theorem intcall_imm_var_name_fresh[local]:
  not_fresh_at st (STRING #"%" (toString n)) <=> n < st.cs_next_var
Proof
  simp[not_fresh_at_def] >> eq_tac >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

(* The loop's fresh names, all allocated from st1's next variable on,
   against the names older than the statement and against each other. *)
Theorem intcall_imm_names[local]:
  p = STRING #"%" (toString st1.cs_next_var) /\
  idx = STRING #"%" (toString (st1.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st1.cs_next_var + if dyn then 4 else 2)) /\
  ov = STRING #"%" (toString (st1.cs_next_var + if dyn then 5 else 3)) /\
  ep = STRING #"%" (toString (st1.cs_next_var + if dyn then 7 else 4)) /\
  nv = STRING #"%" (toString m) /\
  sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
  sa.cs_next_var <= sb0.cs_next_var /\ sb0.cs_next_var <= m /\
  st.cs_next_var <= st1.cs_next_var /\ local_ptrs_reserved ce st1 /\
  (!x. not_fresh_at st x ==> not_fresh_at st1 x) /\
  (!x. lvo = Var x ==> not_fresh_at st1 x) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at st x) ==>
  (!scs. not_local_ptr ce scs p /\ not_local_ptr ce scs idx /\
     not_local_ptr ce scs (STRING #"%" (toString (st1.cs_next_var + 2))) /\
     not_local_ptr ce scs (STRING #"%" (toString (st1.cs_next_var + 3)))) /\
  (!scs. not_local_ptr ce scs idx /\ not_local_ptr ce scs dv /\
     not_local_ptr ce scs nv) /\
  (!scs. not_local_ptr ce scs ov /\
     not_local_ptr ce scs (STRING #"%" (toString (st1.cs_next_var + 6))) /\
     not_local_ptr ce scs ep) /\
  (!op. reserved op ==> op <> Var idx /\ op <> Var dv /\ op <> Var nv) /\
  (!x. not_fresh_at st x ==>
     not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv) /\
  (!x. x = p \/ lvo = Var x \/ Lit (n2w off) = Var x ==>
     not_fresh_at sb0 x /\ x <> idx /\ x <> dv /\ x <> nv) /\
  (!x. lvo = Var x ==>
     ~MEM x [p; idx; STRING #"%" (toString (st1.cs_next_var + 2));
             STRING #"%" (toString (st1.cs_next_var + 3))]) /\
  (!x. not_fresh_at st x ==>
     ~MEM x [p; idx; STRING #"%" (toString (st1.cs_next_var + 2));
             STRING #"%" (toString (st1.cs_next_var + 3))]) /\
  (!x. not_fresh_at st x \/ x = idx \/ x = p \/ lvo = Var x ==>
     not_fresh_at sa x /\ x <> ov /\
     x <> STRING #"%" (toString (st1.cs_next_var + 6)) /\ x <> ep) /\
  ALL_DISTINCT [idx; dv; nv; p] /\
  ALL_DISTINCT [p; idx; STRING #"%" (toString (st1.cs_next_var + 2));
                STRING #"%" (toString (st1.cs_next_var + 3))] /\
  p <> ov /\ p <> STRING #"%" (toString (st1.cs_next_var + 6)) /\ p <> ep /\
  ov <> STRING #"%" (toString (st1.cs_next_var + 6)) /\
  not_fresh_at sa ep /\ not_fresh_at sb0 idx
Proof
  strip_tac >>
  `st1.cs_next_var + 5 <= sa.cs_next_var` by (Cases_on `dyn` >> fs[]) >>
  `!x. not_fresh_at st1 x ==> not_fresh_at sa x /\ not_fresh_at sb0 x` by
    (qpat_x_assum `st1.cs_next_var + 5 <= sa.cs_next_var` mp_tac >>
     qpat_x_assum `sa.cs_next_var <= sb0.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> rw[not_fresh_at_def]) >>
  `!k. st1.cs_next_var <= k ==> ~reserved (Var (STRING #"%" (toString k)))` by
    (rpt strip_tac >>
     `not_fresh_at st1 (STRING #"%" (toString k))` by metis_tac[] >>
     pop_assum mp_tac >> rewrite_tac[not_fresh_at_def] >>
     disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  `!k scs. st1.cs_next_var <= k ==>
     not_local_ptr ce scs (STRING #"%" (toString k))` by
    metis_tac[local_ptrs_reserved_fresh] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  Cases_on `dyn` >> fs[] >> rpt conj_tac >> rpt strip_tac >>
  gvs[intcall_imm_var_name_fresh]
QED

(* One round's body entry: the element copy, from the loop invariant at
   the body label to the declared body's joint resources. *)
Theorem intcall_imm_copy_round[local]:
  compile_iter_elem_copy ce (Var ep) (Var p) (type_memory_size tv) LocCode F
    fty fty sa = ((),sb0) /\
  sa.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w (type_memory_size tv))] [ov]] ++
    (if dyn then [mk_inst j4 ADD [Lit 32w; Var ov] [tot]] else []) ++
    [mk_inst j5 ADD [Lit (n2w off); Var (if dyn then tot else ov)] [ep]] /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
  fn_has_code sa sb0 fp.jc_func /\ sb0.cs_current_bb = bod /\
  0 < type_memory_size tv /\ type_memory_bytes ce fty = type_memory_size tv /\
  type_memory_bytes ce fty < 2 ** 64 /\
  type_memory_bytes ce fty < dimword (:256) /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tv /\
  intcall_frame_ok fp /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  local_ptrs_reserved ce sd /\ sd'.cs_next_var <= sa.cs_next_var /\
  sa.cs_next_var <= sb0.cs_next_var /\ sc.cs_next_var <= sb0.cs_next_var /\
  (!scs. not_local_ptr ce scs ov /\ not_local_ptr ce scs tot /\
         not_local_ptr ce scs ep) /\
  p = STRING #"%" (toString sd.cs_next_var) /\
  p <> ov /\ p <> tot /\ p <> ep /\ ov <> tot /\ not_fresh_at sa ep /\
  ainst = mk_inst aid ALLOCA [Lit (n2w (type_memory_bytes ce fty))] [p] /\
  MEM ainst (fn_insts fp.jc_func) /\ fn_inst_ids_distinct fp.jc_func /\
  (!ei t k. P ei /\ intcall_joint_res fp ce env ei sc t /\ k < LENGTH vs ==>
     immutable_holds ce fp.jc_cx fty (Value (EL k vs))
       (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) ei t) /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs)) /\
  (!x. not_fresh_at sc x \/ x = idx \/ x = p \/ lvo = Var x ==>
       not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) ==>
  !k es next. k < LENGTH vs /\
    array_loop_inv fp.jc_ctx fp.jc_func ce fp.jc_cx P vs id idx
      (Lit (n2w off)) (n2w off) p dst (type_memory_bytes ce fty) ainst bod sc
      k es next /\
    intcall_joint_res fp ce env es sc next ==>
    ?s2. gas_marked_path F fp.jc_ctx fp.jc_func next 0 (OK s2) /\
      intcall_joint_res fp bc (extend_local env id fty F)
        (es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tv;
                            value := EL k vs; popped := []|>)) :: es.scopes)
        sb0 s2 /\
      s2.vs_current_bb = sb0.cs_current_bb /\
      s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s2.vs_halted /\
      (!x. not_fresh_at sc x \/ x = idx \/ x = p \/ lvo = Var x \/
           Lit (n2w off) = Var x ==> lookup_var x s2 = lookup_var x next) /\
      (!aid b. FLOOKUP next.vs_allocas aid = SOME b ==>
               FLOOKUP s2.vs_allocas aid = SOME b) /\
      next.vs_alloca_next <= s2.vs_alloca_next
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `w2n dst + type_memory_bytes ce fty < dimword (:256)` by
    metis_tac[immutable_entry_allocation_bound] >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved bc sd'` by metis_tac[declare_local_reserved] >>
  `local_ptrs_reserved bc sa /\ local_ptrs_reserved bc sb0` by
    (conj_tac >> irule local_ptrs_reserved_next_var >>
     qexists_tac `sd'` >> gvs[]) >>
  `bc.ce_imm_alloca = ce.ce_imm_alloca` by
    (qpat_x_assum `bc with <|ce_vars := _; ce_var_type := _;
        ce_dynarray_capacity := _|> = ce`
       (mp_tac o Q.AP_TERM `\c. c.ce_imm_alloca`) >> simp[]) >>
  `!scs. not_local_ptr ce scs p` by
    (gen_tac >> qpat_x_assum `p = _` SUBST1_TAC >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sd` >> simp[]) >>
  `?bb. lookup_block sb0.cs_current_bb fp.jc_func.fn_blocks = SOME bb /\
     isPREFIX sb0.cs_current_insts bb.bb_instructions` by
    (qpat_x_assum `fn_has_code sa sb0 _` mp_tac >>
     rewrite_tac[fn_has_code_def] >> metis_tac[]) >>
  qhdtm_x_assum `array_loop_inv` mp_tac >>
  simp[array_loop_inv_def] >> strip_tac >>
  `immutable_holds ce fp.jc_cx fty (Value (EL k vs))
     (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) es next` by
    metis_tac[] >>
  `!x. not_fresh_at sc x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep` by
    metis_tac[] >>
  `value_has_type tv (EL k vs) /\ next.vs_current_bb = sb0.cs_current_bb` by
    metis_tac[] >>
  mp_tac (Q.INST [`stride` |-> `type_memory_size tv`, `tyv` |-> `tv`,
    `v` |-> `EL k vs`, `sz` |-> `type_memory_bytes ce fty`, `s` |-> `next`]
    intcall_imm_copy_entry) >>
  impl_tac >- suspend "premises" >>
  strip_tac >> qexists_tac `s2` >> asm_rewrite_tac[] >>
  conj_tac >- simp[] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED
Resume intcall_imm_copy_round[premises]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[mk_inst_def]
QED
Finalise intcall_imm_copy_round

Theorem intcall_stmts_producer_for_immutable_array:
  intcall_stmts_producer fp stmts ==>
  intcall_stmts_producer fp [For id fty (Array (TopLevelName ty nid)) bound stmts]
Proof
  strip_tac >> simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  map_every qx_gen_tac [`bindings`, `ce`, `ce'`, `env`, `env'`, `lctx`, `es`,
    `st`, `st'`, `s`] >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es /\ ce_locals_declared ce env /\
   local_ptrs_reserved ce st` by
    fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `supported_stmt fp.jc_tops bindings
     (For id fty (Array (TopLevelName ty nid)) bound stmts) /\
   type_stmt env fp.jc_ret_ty
     (For id fty (Array (TopLevelName ty nid)) bound stmts) = SOME env'` by
    gvs[supported_stmts_list, type_stmt_def, AllCaseEqs()] >>
  `supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
   ce.ce_alloca_locals /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) fp.jc_tops))` by
    fs[body_inv_def] >>
  `supported_iterator fp.jc_tops fty (Array (TopLevelName ty nid)) bound /\
   supported_stmts fp.jc_tops bindings stmts /\
   ~supported_stmts_expr_exists expr_internal_call_root stmts` by
    fs[supported_stmt_def, supported_iterator_def] >>
  `?bd. ty = ArrayT fty bd /\ bound_length bd <= bound /\
     IS_SOME (supported_immutable_type fp.jc_tops nid)` by
    (Cases_on `ty` >> gvs[supported_iterator_def]) >>
  gvs[] >>
  `assignable_type env.type_defs fty /\
   well_typed_expr env (TopLevelName (ArrayT fty bd) nid) /\
   id NOTIN FDOM env.var_types /\
   iterator_unmodified (Array (TopLevelName (ArrayT fty bd) nid)) stmts /\
   ?env_b. type_stmts (extend_local env id fty F) fp.jc_ret_ty stmts = SOME env_b` by
    gvs[type_stmt_def, well_typed_iterator_def, optionTheory.IS_SOME_EXISTS,
        AllCaseEqs()] >>
  `env' = env` by gvs[type_stmt_def, AllCaseEqs()] >>
  PairCases_on `nid` >> gvs[optionTheory.IS_SOME_EXISTS] >>
  drule_all supported_immutable_type_find_NONE >> strip_tac >> gvs[] >>
  rename1 `TopLevelName _ (NONE,name)` >>
  `FLOOKUP env.bare_globals (NONE,name) = SOME (ArrayT fty bd)` by
    (irule toplevel_find_NONE_bare_global >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all immutable_array_source_ready >> strip_tac >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  rename1 `evaluate_type (get_tenv fp.jc_cx) fty = SOME tv` >>
  suspend "facts"
QED

Resume intcall_stmts_producer_for_immutable_array[facts]:
  `FLOOKUP ce.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _` drule >>
     simp[FLOOKUP_DEF]) >>
  qmatch_asmsub_abbrev_tac `INL (MAP Value vs)` >>
  `LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
   (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T)` by
    suspend "bounds" >>
  `!k. k < LENGTH vs ==> value_has_type tv (EL k vs)` by suspend "typed" >>
  `type_memory_bytes ce fty < 2 ** 64` by
    fs[stmts_exprs_ok_thm, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
       alloc_limits_stmt_def, compileVyperTheory.stmt_valued_return_def] >>
  `type_memory_bytes ce fty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `elem_size_in_location ce LocCode fty = type_memory_size tv` by
    simp[elem_size_in_location_def, is_slot_addressed_def] >>
  `0 < type_memory_size tv` by
    metis_tac[immutable_array_element_size_positive] >>
  `type_memory_bytes ce fty + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `32 <= type_memory_bytes ce fty` by
    (`assignable_type (get_tenv fp.jc_cx) fty` by metis_tac[] >>
     drule_all assignable_type_slot_size_pos >>
     simp[type_memory_size_slots]) >>
  `!gs. eval_stmt fp.jc_cx
     (For id fty (Array (TopLevelName (ArrayT fty bd) (NONE,name))) bound stmts)
     (es with gas_obs := gs) =
   eval_for fp.jc_cx tv id stmts (MAP Value vs) (es with gas_obs := gs)` by
    (irule intcall_imm_eval_for_source >> simp[]) >>
  `gas_admissible (eval_for fp.jc_cx tv id stmts (MAP Value vs)) (stmt_res_ok lctx) es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gasContextTheory.gas_admissible_def] >> metis_tac[]) >>
  suspend "compile"
QED

Resume intcall_stmts_producer_for_immutable_array[bounds]:
  `bound_length bd < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def] >>
     rpt strip_tac >> Cases_on `bd` >> fs[type_slot_size_def, bound_length_def] >>
     `n <= n * type_slot_size tv` by
       (irule LESS_EQ_TRANS >> qexists_tac `n * 1` >> simp[]) >> decide_tac) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, array_elements_def, bound_length_def, Abbr `vs`]
QED

Resume intcall_stmts_producer_for_immutable_array[typed]:
  gen_tac >> strip_tac >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, Abbr `vs`]
  >- (irule (cj 1 fixed_array_elements_typed) >> simp[value_has_type_def] >>
      metis_tac[]) >>
  gvs[array_elements_def, all_have_type_EVERY, EVERY_EL]
QED

Resume intcall_stmts_producer_for_immutable_array[compile]:
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt ce lctx _ _ st = (_,sf)` >>
  `!c lc sa sb. compile_stmts c lc
     (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sa = ((),sb) ==>
     cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[compile_stmt_cs_mono, cs_mono_def] >>
  `!c lc sa sb. compile_stmts c lc
     (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sa = ((),sb) ==>
     cs_extends sa sb` by metis_tac[] >>
  drule_all compile_for_immutable_entry_code_normalized >> strip_tac >>
  suspend "entry"
QED

Resume intcall_stmts_producer_for_immutable_array[entry]:
  drule_all immutable_optional_load_ready >> strip_tac >>
  `cs_extends st1 sf` by
    (irule cs_extends_trans >> qexists_tac `sa` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule cs_extends_trans >> qexists_tac `sb0` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule cs_extends_trans >> qexists_tac `sb1` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule cs_extends_trans >> qexists_tac `sj` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `fn_has_code st st1 fp.jc_func` by
    (irule (cj 1 fn_has_code_split) >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sf` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (qpat_x_assum `!c lc sa sb. _ ==> _ /\ _` drule >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `sb0.cs_next_var <= sj.cs_next_var` by
    (qpat_x_assum `sj.cs_next_var = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `st.cs_next_var <= sf.cs_next_var` by
    (qpat_x_assum `compile_stmt _ _ _ _ st = _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[compile_stmt_cs_mono, cs_mono_def]) >>
  `!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at st x` by
    (qpat_x_assum `intcall_joint_res _ _ _ _ st s` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`m` |-> `sj.cs_next_var`, `reserved` |-> `fp.jc_reserved`]
    intcall_imm_names) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  suspend "facts2"
QED

Resume intcall_stmts_producer_for_immutable_array[facts2]:
  qpat_x_assum `elem_size_in_location ce LocCode fty = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `toto = Var (if dyn then STRING #"%" (toString (st1.cs_next_var + 6)) else ov)` by
    (qpat_x_assum `toto = _` mp_tac >> qpat_x_assum `ov = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `dyn` >> simp[]) >>
  qpat_x_assum `toto = Var (if _ then _ else _)` SUBST_ALL_TAC >>
  `0 < type_memory_size tv /\ type_memory_bytes ce fty < 2 ** 64 /\
   type_memory_bytes ce fty < dimword (:256) /\
   32 <= type_memory_bytes ce fty` by
    (qpat_x_assum `type_memory_bytes ce fty = _` SUBST1_TAC >>
     qpat_x_assum `32 <= type_memory_size tv` mp_tac >>
     qpat_x_assum `type_memory_size tv + 64 < _` mp_tac >>
     qpat_x_assum `type_memory_size tv < _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `LENGTH vs < dimword (:256)` by
    (qpat_x_assum `LENGTH vs <= bound_length bd` mp_tac >>
     qpat_x_assum `bound_length bd < dimword (:256)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `(st1 with cs_next_var := st1.cs_next_var + 1).cs_next_var <= sa.cs_next_var /\
   st.cs_next_var <= sb0.cs_next_var /\
   st1.cs_next_var <= sb1.cs_next_var` by
    (qpat_x_assum `sa.cs_next_var = _` mp_tac >>
     qpat_x_assum `sa.cs_next_var <= sb0.cs_next_var` mp_tac >>
     qpat_x_assum `sb0.cs_next_var <= sb1.cs_next_var` mp_tac >>
     qpat_x_assum `st.cs_next_var <= st1.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> rw[]) >>
  `local_ptrs_reserved ce sb1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st1` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `MEM (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce fty))] [p])
     (fn_insts fp.jc_func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _` (irule_at Any) >> simp[]) >>
  `!l. Lit (n2w off) <> Label l` by simp[] >>
  `~block_is_terminated sb1 ==>
     sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
     sj.cs_current_insts = sb1.cs_current_insts ++
       [mk_inst sb1.cs_next_id JMP [Label incr] []] /\
     fn_has_code sb1 sj fp.jc_func` by
    (strip_tac >> qpat_x_assum `~block_is_terminated sb1 ==> _` drule >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?ce_b. stmts_env bc (InLoop exit incr)
      (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0 =
      (ce_b,sb1)` by
    (qpat_x_assum `compile_stmts bc _ _ _ sb0 = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[compile_stmts_env] >>
     Cases_on `stmts_env bc (InLoop exit incr)
       (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sb0` >>
     simp[]) >>
  `same_frame ce bc` by
    (irule declare_local_same_frame >>
     qhdtm_assum `declare_local` (irule_at Any) >> simp[]) >>
  `body_inv fp.jc_tops fp.jc_ctx bc fp.jc_cx` by
    (qpat_x_assum `same_frame ce bc` mp_tac >>
     qpat_x_assum `body_inv _ _ ce _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[bodyExprPreFactsTheory.body_inv_same_frame]) >>
  `call_evaluation_safe fp.jc_cx (int_calls_stmts stmts)` by
    (qpat_x_assum `intcall_frame_ok _` mp_tac >>
     qpat_x_assum `calls_follow_call_graph _ _ (int_calls_stmts _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[intcall_frame_ok_def,
          vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
     rpt strip_tac >>
     qexists_tac `fp.jc_edges` >> gvs[]) >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
     occurs_abi_decode_target target fp.jc_tops` by
    (qpat_x_assum `!target. supported_stmts_expr_exists _ [_] ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def]) >>
  `stmts_exprs_ok bc stmts` by
    (irule bodyExprPreFactsTheory.for_declare_stmts_exprs_ok >>
     qhdtm_assum `declare_local` (irule_at Any) >>
     qpat_assum `stmt_exprs_ok ce _`
       (irule_at Any o MATCH_MP bodySimDeclCasesTheory.body_for_exprs_ok) >>
     first_assum ACCEPT_TAC) >>
  `IS_SOME (type_stmts ((extend_local env id fty F) with
     bare_global_assignable := FEMPTY) fp.jc_ret_ty stmts)` by
    (qpat_x_assum `type_stmts (env with bare_global_assignable := FEMPTY) _ _ = _`
       mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[type_stmt_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[extend_local_def, optionTheory.IS_SOME_EXISTS]) >>
  suspend "source"
QED

Resume intcall_stmts_producer_for_immutable_array[source]:
  `lookup_immutable fp.jc_cx es NONE name = SOME (ArrayTV tv bd,ArrayV av)` by
    (qpat_x_assum `ALOOKUP es.immutables _ = _` mp_tac >>
     qpat_x_assum `FLOOKUP (get_source_immutables _ _) _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperBareGlobalNameTheory.lookup_immutable_def]) >>
  `!ei t. expr_sim_inv ce fp.jc_cx env ei /\
     lookup_immutable fp.jc_cx ei NONE name = SOME (ArrayTV tv bd,ArrayV av) ==>
     (dyn ==>
        immutable_holds ce fp.jc_cx (ArrayT fty (Dynamic (bound_length bd)))
          (Value (ArrayV av)) (n2w off) ei t /\
        value_has_type (ArrayTV tv (Dynamic (bound_length bd))) (ArrayV av) /\
        LENGTH vs = array_length (ArrayTV tv (Dynamic (bound_length bd))) av) /\
     (!k. k < LENGTH vs ==>
        immutable_holds ce fp.jc_cx fty (Value (EL k vs))
          (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv))
          ei t)` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`cx` |-> `fp.jc_cx`] intcall_imm_source_holds) >>
     impl_tac
     >- (qpat_x_assum `ce.ce_module = NONE` (fn th => rewrite_tac [th]) >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qpat_assum `Abbrev _`
           (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])) >>
     qpat_x_assum `dyn <=> _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `bd` >> simp[bound_length_def]) >>
  `!ei t k. lookup_immutable fp.jc_cx ei NONE name = SOME (ArrayTV tv bd,ArrayV av) /\
     intcall_joint_res fp ce env ei st t /\ k < LENGTH vs ==>
     immutable_holds ce fp.jc_cx fty (Value (EL k vs))
       (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) ei t` by
    (rpt strip_tac >>
     `expr_sim_inv ce fp.jc_cx env ei` by
       (qpat_x_assum `intcall_joint_res _ _ _ ei _ _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[intcall_joint_res_def, intcall_expr_res_def]) >>
     qpat_x_assum `!ei t. expr_sim_inv _ _ _ ei /\ _ ==> _`
       (qspecl_then [`ei`, `t`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (irule o CONJUNCT2) >> first_assum ACCEPT_TAC) >>
  `dyn ==>
     immutable_holds ce fp.jc_cx (ArrayT fty (Dynamic (bound_length bd)))
       (Value (ArrayV av)) (n2w off) es s /\
     evaluate_type (get_tenv fp.jc_cx) fty = SOME tv /\
     value_has_type (ArrayTV tv (Dynamic (bound_length bd))) (ArrayV av) /\
     LENGTH vs = array_length (ArrayTV tv (Dynamic (bound_length bd))) av` by
    (strip_tac >>
     qpat_x_assum `!ei t. expr_sim_inv _ _ _ ei /\ _ ==> _`
       (qspecl_then [`es`, `s`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT1) >>
     qpat_x_assum `dyn` (fn th => rewrite_tac [th]) >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~dyn ==> LENGTH vs = bound_length bd` by
    (qpat_x_assum `dyn <=> _` mp_tac >>
     qpat_x_assum `bound_CASE bd _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bd` >> simp[bound_length_def]) >>
  `env_context_consistent (extend_local env id fty F) fp.jc_cx` by
    (qpat_x_assum `expr_sim_inv ce fp.jc_cx env es` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
          extend_local_def] >> metis_tac[]) >>
  `FLOOKUP (extend_local env id fty F).bare_globals (NONE,name) =
     SOME (ArrayT fty bd)` by
    (qpat_x_assum `FLOOKUP env.bare_globals _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[extend_local_def]) >>
  `!k ei gs res ee. k < LENGTH vs /\
     lookup_immutable fp.jc_cx ei NONE name = SOME (ArrayTV tv bd,ArrayV av) /\
     lookup_scopes id ei.scopes = NONE /\
     eval_stmts fp.jc_cx stmts
       ((ei with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tv;
                            value := EL k vs; popped := []|>)) :: ei.scopes)
        with gas_obs := gs) = (res,ee) /\
     ee.scopes <> [] ==>
     lookup_immutable fp.jc_cx (ee with scopes := TL ee.scopes) NONE name =
       SOME (ArrayTV tv bd,ArrayV av)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
     qpat_x_assum `lookup_immutable _ ei _ _ = _` mp_tac >>
     qpat_x_assum `env_context_consistent (extend_local _ _ _ _) _` mp_tac >>
     qpat_x_assum `FLOOKUP (extend_local _ _ _ _).bare_globals _ = _` mp_tac >>
     qpat_x_assum `type_stmts (extend_local env id fty F) _ _ = _` mp_tac >>
     qpat_x_assum `iterator_unmodified _ _` mp_tac >>
     qpat_x_assum `~supported_stmts_expr_exists expr_internal_call_root _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule_all immutable_array_body_observation >>
     fs[vyperBareGlobalNameTheory.lookup_immutable_def]) >>
  suspend "start"
QED

Resume intcall_stmts_producer_for_immutable_array[start]:
  mp_tac (BETA_RULE (Q.INST [`et` |-> `fty`, `cap` |-> `bound_length bd`,
    `sz` |-> `type_memory_bytes ce fty`, `aid` |-> `st1.cs_next_id`,
    `ainst` |->
      `mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce fty))] [p]`,
    `lbl` |-> `st1.cs_current_bb`, `j` |-> `st1.cs_next_id + 1`,
    `e1` |-> `st1.cs_next_id + 2`, `e2` |-> `st1.cs_next_id + 3`,
    `e3` |-> `st1.cs_next_id + 4`, `e4` |-> `st1.cs_next_id + 5`,
    `e5` |-> `h - 3`,
    `g` |-> `STRING #"%" (toString (st1.cs_next_var + 2))`,
    `vld` |-> `STRING #"%" (toString (st1.cs_next_var + 3))`,
    `P` |-> `\ei. lookup_immutable fp.jc_cx ei NONE name = SOME (ArrayTV tv bd,ArrayV av)`] (INST_TYPE [alpha |-> ``:value``] intcall_imm_loop_start))) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      REFL_TAC) >>
  strip_tac >>
  mp_tac (Q.INST [`j3` |-> `h`, `j4` |-> `h + 1`,
    `j5` |-> `h + if dyn then 2 else 1`,
    `tot` |-> `STRING #"%" (toString (st1.cs_next_var + 6))`,
    `sd` |-> `st1`, `sd'` |-> `st1 with cs_next_var := st1.cs_next_var + 1`,
    `sc` |-> `st`, `aid` |-> `st1.cs_next_id`,
    `ainst` |->
      `mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce fty))] [p]`,
    `P` |-> `\ei. lookup_immutable fp.jc_cx ei NONE name = SOME (ArrayTV tv bd,ArrayV av)`] intcall_imm_copy_round) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      REFL_TAC) >>
  strip_tac >>
  suspend "loop"
QED

Resume intcall_stmts_producer_for_immutable_array[loop]:
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] (Q.INST [
    `saved` |-> `Lit (n2w off)`, `arrbase` |-> `n2w off`,
    `sz` |-> `type_memory_bytes ce fty`,
    `aa` |->
      `mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce fty))] [p]`,
    `sc` |-> `st`, `origin` |-> `s`, `j1` |-> `h - 2`, `j2` |-> `h - 1`,
    `i1` |-> `sj.cs_next_id`, `i2` |-> `sj.cs_next_id + 1`,
    `i3` |-> `sj.cs_next_id + 2`,
    `sd` |-> `st1`, `sd'` |-> `st1 with cs_next_var := st1.cs_next_var + 1`,
    `tyv` |-> `tv`, `P` |-> `\ei. lookup_immutable fp.jc_cx ei NONE name = SOME (ArrayTV tv bd,ArrayV av)`] intcall_array_gen_loop))) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      REFL_TAC) >>
  disch_then (qspecl_then [`0`, `es`, `cc`] mp_tac) >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rewrite_tac [DROP_0, ZERO_LESS_EQ] >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  suspend "finish"
QED

Resume intcall_stmts_producer_for_immutable_array[finish]:
  qmatch_goalsub_abbrev_tac `gas_outcome F _ _ _ _ QQ RR` >>
  `LENGTH (MAP Value vs) <= bound` by
    (qpat_x_assum `LENGTH vs <= bound_length bd` mp_tac >>
     qpat_x_assum `bound_length bd <= bound` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  mp_tac (Q.INST [`cx` |-> `fp.jc_cx`,
    `it` |-> `Array (TopLevelName (ArrayT fty bd) (NONE,name))`,
    `vsx` |-> `MAP Value vs`, `n` |-> `bound`, `et` |-> `fty`,
    `tops` |-> `cx_tops fp.jc_cx`, `ctx` |-> `fp.jc_ctx`,
    `func` |-> `fp.jc_func`, `Q` |-> `QQ`, `R` |-> `RR`]
    (Q.INST [`vs` |-> `vsx`] for_source_prefix_bounded)) >>
  impl_tac >- suspend "prefix" >>
  disch_then ACCEPT_TAC
QED

Resume intcall_stmts_producer_for_immutable_array[prefix]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule gas_outcome_zero_prefix >> qexists_tac `cc` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule gas_outcome_start_gas_obs >>
  irule gas_outcome_conseq >>
  qhdtm_x_assum `gas_outcome` (irule_at Any o REWRITE_RULE [DROP_0]) >>
  conj_tac >- simp[Abbr `RR`, PULL_EXISTS] >>
  (rpt gen_tac >> CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >>
      qunabbrev_tac `QQ` >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
      qexistsl_tac [`ce`, `env`] >>
      `intcall_joint_res fp ce env ee sf t` by
        (irule intcall_joint_res_next_var >> qexists_tac `st` >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      simp[stmt_lands_def, block_is_terminated_def, cenv_top_ext_refl])
QED

Finalise intcall_stmts_producer_for_immutable_array
