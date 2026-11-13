(* Counted semantic sequencing for mapping subscripts. *)
Theory bodyMappingOutcomeMemory
Ancestors
  mappingSubscriptCode mappingSubscriptSemantics exprSimSubscriptMap
  bodyMemMapBase bodyMemoryPreds
  exprSimMemDefs exprSimMapMemDefs exprSimMapKey exprSimSubscriptArraySource
  exprSimWordArgs exprSimProps exprBopSimProps stmtSimProps exprOperandVar
  fragGasMode fragGasPath gasSummary

Theorem mapping_index_sim_mem[local]:
  (!s res t. eval_expr cx obj s = (INL res,t) ==>
     body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  gas_marked_exec T (ctx,func) (eval_expr cx obj)
    (es,s0) marks (INL tv) mid (OK t) ==>
  expr_sim_mem ctx func cenv cx (expr_type idx) idx (mid with gas_obs := [])
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  drule_all mapping_subscript_marked_index_pre >> strip_tac >>
  `body_expr_mem_ok cx idx` by metis_tac[] >>
  qpat_x_assum `body_expr_mem_ok cx idx`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
  disch_then (qspecl_then
    [`tops`, `ctx`, `func`, `cenv`, `env`, `expr_type idx`,
     `mid with gas_obs := []`] mp_tac) >> simp[]
QED

Theorem compile_mapping_subscript_outcome_mem_given_tail:
  (!ctx func cenv cx idx em sm sn s1 en kv key t kt tv hashed sp base_op slot sb base_slot.
    expr_post ctx func cenv cx idx em sm sn s1 en kv key t /\
    expr_type idx = kt /\ hashmap_key_type kt /\
    evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn
     else (key,sn)) = (hashed,sp) /\
    compile_mapping_subscript base_op hashed sp = (slot,sb) /\
    (!x. key = Var x ==> not_fresh_at sn x) /\
    (!x. base_op = Var x ==> not_fresh_at sm x) /\ (!l. base_op <> Label l) /\
    eval_operand base_op s1 = SOME base_slot /\
    fn_inst_ids_distinct func /\ fn_has_code sp sb func /\ fn_has_code sn sb func /\
    stmt_state_rel ctx func cenv cx em s1 /\ local_ptrs_reserved cenv sm /\
    MAP FDOM em.scopes = MAP FDOM en.scopes /\
    sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    expr_store_bound cx (expr_type idx) kv key t /\ alloca_history func t ==>
    ?u. gas_marked_path T ctx func t 0 (OK u) /\
      eval_operand slot u = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
      stmt_state_rel ctx func cenv cx en u /\ wb_frame cenv em en sm s1 u /\
      (~expr_has_effect idx ==> pure_frame cenv func em sm s1 u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next) /\
  body_expr_mem_ok cx obj /\
  (!s tv t. eval_expr cx obj s = (INL tv,t) ==> body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) A es /\
  (!ex. A (INR ex) ==> expr_map_res_ok (INR ex)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    (\res ee t. ?tr base_slot kv tv tp p.
       res = INL tv /\
       storage_mapping_region cx tr base_slot (HashMapT kt vt) /\
       select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
         (ValueSubscript kv) ee = (INL tv,ee) /\
       expr_type idx = kt /\ hashmap_key_type kt /\
       (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\
                 value_has_type key_ty kv) /\
       expr_sim_inv cenv cx env ee /\ vv = LocatedValue tp p /\
       p.ptr_location = slot_loc tr /\
       eval_operand p.ptr_operand t =
         SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
       stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv es ee sa s0 t /\
       (~expr_has_effect (Subscript ann obj idx) ==>
          pure_frame cenv func es sa s0 t) /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail")
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 assume_tac
          (CONJUNCTS_THEN2 assume_tac strip_assume_tac))))) >>
  drule_all mapping_subscript_code_parts >> strip_tac >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_map_subscript_base, expr_map_pre_subscript_base] >>
  drule exprOperandVarTheory.compile_lower_value_var >> simp[] >> disch_tac >>
  qpat_assum `compile_expr _ _ obj _ = _`
    (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
  simp[] >> disch_tac >>
  `type_place_expr env obj = SOME (HashMapT kt vt)` by
    (drule_all expr_map_pre_checked_type >> simp[]) >>
  qpat_assum `type_place_expr _ obj = _`
    (strip_assume_tac o Q.SPECL [`cenv`, `idx`, `cx`] o
     MATCH_MP map_base_no_overlap) >>
  drule_all compile_mapping_operand_not_label >> disch_tac >>
  `gas_admissible (eval_expr cx obj) expr_map_res_ok es` by
    (irule subscript_result_base_admissible >>
     qexistsl_tac [`A`, `ann`, `idx`] >> simp[]) >>
  `expr_map_sim_mem ctx func cenv cx ty obj es` by
    (drule_all body_expr_mem_ok_map >> simp[]) >>
  qpat_x_assum `expr_map_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_map_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `bvv`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  disch_then (mp_then Any irule gas_outcome_bind_result_exec) >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt gen_tac >> Cases_on `res` >> simp[] >> rpt strip_tac >> simp[]) >>
      rpt gen_tac >> simp[] >> rpt strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  fs[IgnAsm `expr_body_pre _ _ _ _ _ \/ expr_map_pre _ _ _ _ _`] >>
  suspend "index_bind"
QED

Resume compile_mapping_subscript_outcome_mem_given_tail[index_bind]:
  markerLib.RESUME_TAC >> (
  rename1 `v = HashMapRef tr base_slot bkt bvt` >>
  qpat_x_assum `v = HashMapRef _ _ _ _` SUBST_ALL_TAC >>
  `wb_frame cenv es (mid with gas_obs := []) sa s0 t` by
    (pure_rewrite_tac[loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `bkt = kt /\ bvt = vt /\
   expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
   (?s u. eval_expr cx obj s = (INL (HashMapRef tr base_slot bkt bvt),u)) /\
   gas_admissible (bind (eval_expr cx idx) (read_result cx))
      expr_res_ok (mid with gas_obs := [])` by
    (irule mapping_subscript_marked_base_preparation >> simp[] >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type idx) idx (mid with gas_obs := [])` by
    (irule mapping_index_sim_mem >> simp[] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_mem_def] >>
  disch_then (qspecl_then [`sm`, `sn`, `key`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ (start,t)` >>
  irule forced_then_outcome_exec >>
  conj_tac >- metis_tac[stmtSimPropsTheory.expr_exit_INR_type] >>
  qexists_tac `\kv ee u. expr_post ctx func cenv cx idx
    (mid with gas_obs := []) sm sn t ee kv key u /\
    expr_store_bound cx (expr_type idx) kv key u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next` >>
  reverse conj_tac >- (simp[Abbr `start`] >> first_assum ACCEPT_TAC) >>
  simp[Abbr `start`] >>
  map_every qx_gen_tac [`imarks`, `kv`, `fin`, `it`] >> strip_tac >>
  suspend "success")
QED

Resume compile_mapping_subscript_outcome_mem_given_tail[success]:
  markerLib.RESUME_TAC >> (
  `expr_sim_inv cenv cx env (fin with gas_obs := []) /\
   expr_type idx = kt /\ hashmap_key_type kt /\
   (?key_ty. evaluate_type (get_tenv cx) kt = SOME key_ty /\
             value_has_type key_ty kv) /\
   MAP FDOM es.scopes = MAP FDOM mid.scopes /\
   MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (irule mapping_subscript_marked_success >> simp[] >> metis_tac[]) >>
  `?selected. !tail.
     select_result cx (expr_type obj) (HashMapRef tr base_slot kt vt)
       (ValueSubscript kv) (fin with gas_obs := tail) =
     (INL selected,fin with gas_obs := tail)` by
    (irule mapping_subscript_selection_success >>
     qexistsl_tac [`ann`, `cenv`, `env`, `es`, `idx`] >> simp[]) >>
  `~it.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `eval_operand (vv_operand bvv) t = SOME base_slot` by
    gvs[contextTheory.vv_operand_def] >>
  `?out. gas_marked_path T ctx func it 0 (OK out) /\
     eval_operand slot out = SOME (hashmap_slot base_slot (encode_hashmap_key kt kv)) /\
     stmt_state_rel ctx func cenv cx (fin with gas_obs := []) out /\
     wb_frame cenv (mid with gas_obs := []) (fin with gas_obs := []) sm t out /\
     (~expr_has_effect idx ==>
        pure_frame cenv func (mid with gas_obs := []) sm t out) /\
     out.vs_current_bb = sb.cs_current_bb /\
     out.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func out /\ it.vs_alloca_next <= out.vs_alloca_next` by
    (asm "tail" drule >> disch_then irule >> simp[] >>
     qexists `vv_operand bvv` >> simp[]) >>
  suspend "finish")
QED

Resume compile_mapping_subscript_outcome_mem_given_tail[finish]:
  markerLib.RESUME_TAC >> (
  `wb_frame cenv es (fin with gas_obs := []) sa s0 out /\
   (~expr_has_effect (Subscript ann obj idx) ==>
      pure_frame cenv func es sa s0 out)` by
    (irule mapping_subscript_frames >>
     conj_tac >- simp[] >>
     conj_tac >- (qexistsl [`ctx`, `cx`] >> simp[]) >>
     qexistsl [`mid with gas_obs := []`, `sm`, `t`] >> simp[]) >>
  `storage_mapping_region cx tr base_slot (HashMapT kt vt)` by
    (qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >> simp[]) >>
  qexistsl_tac [`INL selected`, `fin with gas_obs := []`, `OK out`] >>
  simp[] >> qexistsl_tac [`tr`, `base_slot`, `kv`] >>
  simp[contextTheory.mk_ptr_def, contextTheory.vv_location_def] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ (fin with gas_obs := []) out` mp_tac >>
  simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs])
QED

Finalise compile_mapping_subscript_outcome_mem_given_tail
