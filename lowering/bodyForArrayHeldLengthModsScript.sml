(* Reached value and local-memory Array captures and their length slice. *)
Theory bodyForArrayHeldLengthMods
Ancestors
  bodyForArrayRouteMods bodyCopyAtomicRhsTypeMods bodyFullForArray
  reasonEndpointResourcesPtr bodyPtrIfExpAllocSource bodyPtrBopHashFootprint
  bodyPtrBopInMemoryContents exprPtrUnwrapFacts emitHelperProps
  vyperTypeArgFits valueEncodingProps exprBodyPreProps vyperTypeEvalCaseProofs
  vyperTypeExprSoundness vyperAST vyperState vyperTypeSystem vyperTyping
  vyperTypeValues compileEnv loweringPosts bodyFullPostsMods bodyPtrDefs context
  exprSimDefs exprLowering valueEncoding venomState venomExecSemantics words
  bodyFullTargetArrayLoad exprLoweringProps fragGasOriginPtr emitHelper ptrDiscipline
  exprSimCopy vyperValue vyperValueOperation
Libs
  monadsyntax

Theorem held_array_post_shape[local]:
  expr_body_pre_mods mods c cx env e es /\ expr_type e = ArrayT elem bd /\
  eval_expr cx e es = (INL raw,em) /\
  read_result cx raw em = (INL (ArrayV av),em) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) ==>
  ?pe pb pet. post_value_type c e = ArrayT pe pb /\
    evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV pet pb) /\
    (case bd of Fixed k => pb = Fixed k | Dynamic k => ?j. pb = Dynamic j /\ j <= k)
Proof
  strip_tac >> Cases_on `?ty key args drv. e = Call ty (IntCall key) args drv`
  >- (gvs[expr_type_def] >>
      drule_then assume_tac expr_body_pre_mods_inv >>
      drule_then assume_tac expr_body_pre_mods_well_typed >>
      drule_then assume_tac expr_sim_inv_mods_env >>
      drule_then assume_tac env_consistent_type_defs_get_tenv >>
      rename1 `well_typed_expr env (Call _ (IntCall key) args drv)` >>
      `bind (eval_expr cx (Call (ArrayT elem bd) (IntCall key) args drv))
        (read_result cx) es = (INL (ArrayV av),em)` by simp[bind_def] >>
      drule_all_then assume_tac (REWRITE_RULE [ETA_THM] copy_intcall_read_lowered_mods) >>
      PairCases_on `key` >>
      qpat_x_assum `well_typed_expr _ _` mp_tac >>
      simp[Once well_typed_expr_def] >> strip_tac >>
      drule_all_then assume_tac expr_sim_inv_mods_return_type >>
      gvs[lowered_value_type_def,is_word_type_def,is_bytestring_type_def,value_runtime_typed_def] >>
      qpat_x_assum `type_widens_to _ _ (ArrayT elem bd)` mp_tac >>
      rename1 `evaluate_type _ sg.ret_ty = SOME _` >>
      Cases_on `sg.ret_ty` >> simp[type_widens_to_def,arg_type_fits_def] >>
      rename1 `evaluate_type _ (ArrayT pe pb) = SOME _` >>
      Cases_on `pb` >> Cases_on `bd` >>
      simp[arg_type_fits_def] >> strip_tac >>
      drule_then strip_assume_tac evaluate_type_ArrayT_cases >> gvs[]) >>
  `post_value_type c e = ArrayT elem bd` by
    (qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >>
     irule post_value_type_not_int_call >>
     qpat_x_assum `~(?ty key args drv. _)` mp_tac >> simp[]) >>
  qpat_assum `expr_type e = _` (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  Cases_on `bd` >> gvs[]
QED

Theorem held_array_mem_ptr[local]:
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  ~is_word_type (post_value_type c e) /\
  vv_post_mods H ctx func c cx e es sa sb s0 em raw vv s /\
  ptr_vv_ok cx (post_value_type c e) raw vv em G tn s /\
  read_result cx raw em = (INL v,em) ==>
  ?a. eval_operand (vv_operand vv) s = SOME a /\
    op_taint tn (vv_operand vv) = {} /\
    ptr_mem_ok cx (post_value_type c e) v (vv_operand vv) G tn s
Proof
  strip_tac >> qhdtm_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  Cases_on `vv` >>
  gvs[vv_location_def,vv_operand_def,vv_holds_mods_def,vv_holds_def,
      ptr_vv_ok_def,ptr_val_ok_def,expr_val_rel_def]
QED

(* The filled header, not the compile-time capacity, supplies the load. *)
Theorem held_array_dyn_observation[local]:
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV pet (Dynamic j)) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  ptr_mem_ok cx ty (ArrayV (DynArrayV xs)) op G tn s /\
  w2n a + type_memory_size (ArrayTV pet (Dynamic j)) <= s.vs_alloca_next ==>
  mload (w2n a) s = n2w (LENGTH xs) /\
  (?p. op = Var p /\ ptr_covers G tn p s 32) /\
  mem_word_taint tn.t_mem (w2n a) = {} /\ w2n a + 32 <= s.vs_alloca_next
Proof
  strip_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV pet (Dynamic j)) (ArrayV (DynArrayV xs)) (w2n a) m` by
    (qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
       (qspecl_then [`ArrayTV pet (Dynamic j)`,`a`] mp_tac o
        REWRITE_RULE [ptr_mem_ok_def]) >> simp[]) >>
  conj_tac >-
    (`val_in_memory (ArrayTV pet (Dynamic j)) (ArrayV (DynArrayV xs))
       (w2n a) s.vs_memory` by
       (first_x_assum irule >> simp[mem_agree_outside_def]) >>
     fs[valueEncodingPropsTheory.val_in_memory_dynarray,
        valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  conj_tac >-
    (irule ptr_mem_ok_read_covers >>
     simp[] >> qexistsl [`cx`,`ty`,`ArrayTV pet (Dynamic j)`,`ArrayV (DynArrayV xs)`] >>
     simp[val_footprint_def,exprSimPropsTheory.val_store_size_def,type_memory_size_def]) >>
  conj_tac >- (drule_then ACCEPT_TAC dynarray_memory_header_clean) >>
  fs[type_memory_size_def]
QED

Theorem held_array_length_run[local]:
  (case bd of Fixed k => comp_return (Lit (n2w k))
    | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocMemory op) sa =
    (len_op,sb) /\
  (case bd of Fixed k => k = LENGTH vs | Dynamic _ =>
    eval_operand op s = SOME a /\ mload (w2n a) s = n2w (LENGTH vs) /\
    (?p. op = Var p /\ ptr_covers G tn p s 32) /\
    mem_word_taint tn.t_mem (w2n a) = {} /\ w2n a + 32 <= s.vs_alloca_next) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?z Gz tz. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
                (s,G,tn) [] (OK z,Gz,tz)) /\
    eval_operand len_op z = SOME (n2w (LENGTH vs)) /\
    op_taint tz len_op = {} /\ op_prov Gz len_op = NONE /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ array_length_frame sa s G tn z Gz tz
Proof
  Cases_on `bd` >> simp[] >> strip_tac
  >- (gvs[comp_return_def] >> qexistsl [`s`,`G`,`tn`] >>
      simp[array_length_frame_def,eval_operand_def,op_taint_def,op_prov_def,
           venom_state_component_equality] >>
      gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u` by
    (qpat_assum `compile_ptr_load _ _ _ _ _ = _`
       (mp_tac o REWRITE_RULE [compile_ptr_load_def]) >>
     disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_x_assum `op = Var p` SUBST_ALL_TAC >>
     drule_then (fn th => simp[run_inst_seq_def,th]) step_MLOAD) >>
  `?p. op = Var p /\ ptr_covers G tn p s 32` by (qexists_tac `p` >> simp[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`)
    (SIMP_RULE (srw_ss()) [] (for_nonslot_array_length_checked |>
      Q.INST [`dynamic` |-> `T`, `loc` |-> `LocMemory`])) >>
  disch_then (drule_at (Pat `compile_ptr_load _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `mload _ _ = _`)) >>
  simp[] >> strip_tac >>
  `p' = p` by fs[] >> gvs[] >>
  first_x_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >> simp[] >>
  strip_tac >>
  qexistsl [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`G'`,`tn'`] >> simp[]
QED

Theorem held_array_extent[local]:
  vv_post_mods H ctx func c cx e es sa sb s0 em raw vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  post_value_type c e = ArrayT pe pb /\
  evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV pet pb) /\
  read_result cx raw em = (INL (ArrayV av),em) /\
  eval_operand (vv_operand vv) s = SOME a ==>
  val_wf (ArrayTV pet pb) (ArrayV av) /\
  (0 < type_memory_size (ArrayTV pet pb) ==>
     w2n a + type_memory_size (ArrayTV pet pb) <= s.vs_alloca_next /\
     ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sb.cs_next_id /\
         b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz) \/
      (?name b sz. local_region c em.scopes s name b sz /\
         b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz)))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory` by
    (Cases_on `vv` >> gvs[vv_location_def]) >>
  qhdtm_x_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `val_footprint (ArrayTV pet pb) (ArrayV av) = type_memory_size (ArrayTV pet pb)` by
    simp[val_footprint_def] >>
  `~is_word_type (post_value_type c e)` by simp[is_word_type_def] >>
  drule_all_then strip_assume_tac vv_at_memory_footprint >>
  simp[] >> strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `w2n a + type_memory_size (ArrayTV pet pb) - 1` mp_tac) >>
      decide_tac) >>
  Cases_on `vv` >> gvs[vv_location_def,vv_operand_def,vv_at_def]
  >- (drule expr_val_at_region_prefix >>
      disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
      disch_then (qspec_then `type_memory_size (ArrayTV pet pb)` mp_tac) >> simp[])
  >- (disj1_tac >> qexistsl [`aid`,`b`,`sz`] >> simp[]) >>
  disj2_tac >> qexistsl [`n`,`b`,`sz`] >> simp[]
QED

Theorem held_array_base_frame[local]:
  array_length_frame sa s G tn z Gz tz /\ copy_old_operand sa op /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  ptr_mem_ok cx ty v op G tn s ==>
  eval_operand op z = SOME a /\ op_taint tz op = {} /\
  op_prov Gz op = op_prov G op /\ ptr_mem_ok cx ty v op Gz tz z /\
  z.vs_alloca_next = s.vs_alloca_next /\ z.vs_allocas = s.vs_allocas /\
  z.vs_memory = s.vs_memory
Proof
  simp[array_length_frame_def,copy_old_operand_def] >> strip_tac >>
  `z.vs_alloca_next = s.vs_alloca_next /\ z.vs_allocas = s.vs_allocas /\
   z.vs_memory = s.vs_memory /\ z.vs_labels = s.vs_labels` by
    (qpat_assum `_ with vs_vars := _ = s` (once_rewrite_tac o single o SYM) >> simp[]) >>
  Cases_on `op` >> gvs[eval_operand_def,op_taint_def,op_prov_def,ptr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> simp[]
QED

(* A nonzero-size owned buffer lies in an expression-age allocation, not a
   live local. The distinct held-place route can use the local alternative
   of held_array_extent instead. *)
Theorem held_array_owned_row[local]:
  vv_own c cx ty sa sb em raw vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME (ArrayTV pet pb) /\
  read_result cx raw em = (INL (ArrayV av),em) /\
  eval_operand (vv_operand vv) s = SOME a /\
  0 < type_memory_size (ArrayTV pet pb) ==>
  ?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  Cases_on `vv` >>
  gvs[vv_location_def,vv_operand_def,vv_own_def,expr_val_own_def,val_footprint_def] >>
  qexistsl [`aid`,`b`,`sz`] >> simp[]
QED

(* The only source evaluation here is the already reached raw expression.
   In particular, the source list and the physical memory descriptor may be
   chosen before the downstream callback quantifies over valid horizons. *)
Theorem for_array_held_length_ready_mods:
  expr_body_pre_mods mods c cx env e es /\ expr_type e = ArrayT elem bd /\
  eval_expr cx e es = (INL raw,em) /\ bound_length bd <= n /\
  vv_post_mods H ctx func c cx e es sa sb s0 em raw vv s /\
  ptr_vv_ok cx (post_value_type c e) raw vv em G tn s /\
  (!v. raw = Value v /\ ~is_word_type (post_value_type c e) /\
       ~is_bytestring_type (post_value_type c e) ==>
       vv_own c cx (post_value_type c e) sa sb em raw vv s) /\
  ((?v. raw = Value v) \/ (?name path. raw = PlaceR (MemoryPlace name path))) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  compile_expr c (expr_type e) e sa = (vv,sb) /\ local_ptrs_reserved c sa /\
  (case bd of Fixed k => comp_return (Lit (n2w k))
    | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocMemory (vv_operand vv)) sb =
    (len_op,sc) /\ fn_has_code sb sc func /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?et av vs pe pb pet a z Gz tz.
    evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
    read_result cx raw em = (INL (ArrayV av),em) /\
    value_has_type (ArrayTV et bd) (ArrayV av) /\
    eval_iterator cx (Array e) es = (INL vs,em) /\
    vs = MAP Value (array_elements (ArrayTV et bd) av) /\
    compatible_bound (Dynamic n) (LENGTH vs) /\
    (!tail. array_iterator_results cx (expr_type e) raw (em with gas_obs := tail) =
       (INL vs,em with gas_obs := tail)) /\
    post_value_type c e = ArrayT pe pb /\
    evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV pet pb) /\
    val_wf (ArrayTV pet pb) (ArrayV av) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    eval_operand len_op z = SOME (n2w (LENGTH vs)) /\
    op_taint tz len_op = {} /\ op_prov Gz len_op = NONE /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    array_length_frame sb s G tn z Gz tz /\
    eval_operand (vv_operand vv) z = SOME a /\ op_taint tz (vv_operand vv) = {} /\
    op_prov Gz (vv_operand vv) = op_prov G (vv_operand vv) /\
    ptr_mem_ok cx (post_value_type c e) (ArrayV av) (vv_operand vv) Gz tz z /\
    z.vs_alloca_next = s.vs_alloca_next /\ z.vs_allocas = s.vs_allocas /\
    z.vs_memory = s.vs_memory /\
    (raw = Value (ArrayV av) /\ 0 < type_memory_size (ArrayTV pet pb) ==>
       ?aid b sz. FLOOKUP z.vs_allocas aid = SOME (b,sz) /\
         sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
         b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz) /\
    (0 < type_memory_size (ArrayTV pet pb) ==>
       w2n a + type_memory_size (ArrayTV pet pb) <= z.vs_alloca_next /\
       ((?aid b sz. FLOOKUP z.vs_allocas aid = SOME (b,sz) /\ aid < sb.cs_next_id /\
           b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz) \/
        (?name b sz. local_region c em.scopes s name b sz /\
           b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz)))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `!tr slot et bd. raw <> PlaceR (StoragePlace tr slot (ArrayTV et bd))` by
    (qpat_x_assum `(?v. raw = Value v) \/ _` strip_assume_tac >> simp[]) >>
  drule_all_then strip_assume_tac for_array_nonslot_vv_capture_mods >>
  drule_all_then assume_tac for_array_nonslot_result_replay_mods >>
  drule_all_then strip_assume_tac held_array_post_shape >>
  `~is_word_type (post_value_type c e)` by simp[is_word_type_def] >>
  drule_all_then strip_assume_tac held_array_mem_ptr >>
  drule_all_then strip_assume_tac held_array_extent >>
  `copy_old_operand sb (vv_operand vv)` by
    (drule_all_then ACCEPT_TAC compile_expr_old_operand) >>
  `(case bd of Fixed k => k = LENGTH vs | Dynamic _ =>
    eval_operand (vv_operand vv) s = SOME a /\ mload (w2n a) s = n2w (LENGTH vs) /\
    (?p. vv_operand vv = Var p /\ ptr_covers G tn p s 32) /\
    mem_word_taint tn.t_mem (w2n a) = {} /\ w2n a + 32 <= s.vs_alloca_next)` by
    (Cases_on `bd` >> simp[NoAsms]
     >- (qpat_assum `compatible_bound (Fixed _) _`
           (ACCEPT_TAC o REWRITE_RULE [compatible_bound_def])) >>
     `?xs. av = DynArrayV xs` by
       (qpat_x_assum `value_has_type (ArrayTV et _) _` mp_tac >>
        Cases_on `av` >> simp[value_has_type_def]) >>
     qpat_x_assum `av = DynArrayV _` SUBST_ALL_TAC >>
     qpat_x_assum `case Dynamic _ of Fixed _ => _ | Dynamic _ => _`
       (qx_choose_then `j` (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) o
        SIMP_RULE (srw_ss()) []) >>
     qpat_x_assum `vs = MAP _ _` SUBST_ALL_TAC >>
     `w2n a + type_memory_size (ArrayTV pet (Dynamic j)) <= s.vs_alloca_next` by
       (qpat_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[type_memory_size_def]) >>
     drule_all held_array_dyn_observation >> simp[array_elements_def]) >>
  drule_all held_array_length_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all_then strip_assume_tac held_array_base_frame >>
  qexistsl [`et`,`av`,`vs`,`pe`,`pb`,`pet`,`a`,`z`,`Gz`,`tz`] >> simp[] >>
  conj_tac
  >- (strip_tac >>
      `~is_bytestring_type (post_value_type c e)` by simp[is_bytestring_type_def] >>
      `vv_own c cx (post_value_type c e) sa sb em raw vv s` by
        (qpat_assum `!v. raw = Value v /\ _ ==> _`
           (qspec_then `ArrayV av` mp_tac) >> simp[]) >>
      drule_all held_array_owned_row >> simp[]) >>
  qpat_x_assum `0 < type_memory_size _ ==> _` mp_tac >> simp[]
QED

(* Installing the loop header can grow memory, and may clean taint. Only
   the actual selected array window, not the entire memory, is framed. *)
Theorem for_array_held_payload_frame_mods:
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV pet pb) /\
  val_wf (ArrayTV pet pb) (ArrayV av) /\
  ptr_mem_ok cx ty (ArrayV av) op G tn z /\
  eval_operand op z = SOME a /\ eval_operand op t = SOME a /\
  op_prov G' op = op_prov G op /\
  mem_bytes_at (w2n a) (type_memory_size (ArrayTV pet pb)) t.vs_memory =
    mem_bytes_at (w2n a) (type_memory_size (ArrayTV pet pb)) z.vs_memory /\
  (!i. w2n a <= i /\ i < w2n a + type_memory_size (ArrayTV pet pb) /\
       i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  ptr_mem_ok cx ty (ArrayV av) op G' tn' t
Proof
  strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _`
    (qspecl_then [`ArrayTV pet pb`,`a`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
  simp[] >> strip_tac >> simp[ptr_mem_ok_def] >>
  conj_tac
  >- (rpt strip_tac >> irule logValueFramePtrTheory.robust_val_in_memory_footprint_frame >>
      simp[val_footprint_def] >>
      qexistsl [`z.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tn'.t_mem`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  Cases_on `op` >> fs[op_prov_def]
QED
