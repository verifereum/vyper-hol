(*
 * The pointer twin of S1's compile_subscript_map_map_case
 * (exprSimSubscriptMap): a subscript of a mapping whose value is a mapping
 * (m[a] for m : HashMap[K, HashMap[...]]) names a mapping too.  The base's
 * expr_map_sim_ptr gives the operand holding its slot, the key is lowered
 * after it, and compile_mapping_subscript's SHA3 over the two in a fresh
 * 64-byte buffer is hashmap_slot slot (encode_hashmap_key kt kv), the slot
 * of the inner mapping (select_result_hashmap_nested,
 * storage_mapping_region_step).
 *
 * TOP-LEVEL:
 *   subscript_map_map_ptr
 *)
Theory bodyPtrSubscriptMapMap
Ancestors
  bodyPtrSubscriptSeamMapConsumer bodyPtrSubscriptMapDefs bodyPtrPreds gasSummaryComposePtr
  bodyPtrDefs bodySim exprSimMapDefs exprSimSubscriptMap exprSimHypsDefs
  vyperStoragePlaceProvenance exprLowering vyperInterpreter vyperState vyperContext vyperAST

(* mapping_marked_index_ready_ptr for a subscript naming a mapping: the
   index's precondition, its admissibility, and the base's key and value
   types, from expr_map_pre in place of expr_body_pre. *)
Theorem mapping_marked_index_ready_map_ptr:
  expr_map_pre cenv cx env (Subscript ann obj idx) es /\
  place_type cenv obj = MapPT kt vt /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_map_res_ok es /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx obj)
    (es,s0,G0,tn0) marks (INL (HashMapRef tr slot bkt bvt)) mid G tn (OK t) ==>
  expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
  (?s u. eval_expr cx obj s = (INL (HashMapRef tr slot bkt bvt),u)) /\
  bkt = kt /\ bvt = vt /\ ~t.vs_halted /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,fn) (eval_expr cx obj) (es,s0) marks
     (INL (HashMapRef tr slot bkt bvt)) mid (OK t)` by
    (irule gas_marked_exec_ptr_exec >> goal_assum (drule_at Any)) >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := []) /\
   ?s u. eval_expr cx obj s = (INL (HashMapRef tr slot bkt bvt),u)` by
    (irule exprSimSubscriptMapTheory.mapping_subscript_marked_index_pre >> metis_tac[]) >>
  `expr_map_pre cenv cx env obj es` by
    metis_tac[exprSimSubscriptMapTheory.expr_map_pre_subscript_base] >>
  drule_all exprSimSubscriptMapTheory.expr_map_pre_checked_type >> strip_tac >>
  drule bodyPtrHashBuiltinsSuffixTheory.hash_marked_ptr_normal >> strip_tac >>
  `bkt = kt /\ bvt = vt` by
    (qpat_assum `eval_expr _ _ (_ with gas_obs := _) = _`
       (mp_then Any mp_tac exprSimSubscriptMapTheory.expr_map_pre_eval_result) >>
     disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum (qspec_then `HashMapT kt vt` mp_tac) >>
     simp[vyperTypeInvariantsTheory.eval_result_typed_def]) >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
     (mid with gas_obs := [])` by
    (`~subscript_reads_base cx obj idx` by
       metis_tac[exprSimSubscriptMapTheory.map_base_no_overlap] >>
     irule exprSimSubscriptMapTheory.subscript_map_index_admissible >>
     metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

(* The pointer twin of S1's compile_subscript_map_map_case, from the same
   pieces as compile_mapping_subscript_outcome_ptr
   (bodyPtrSubscriptSeamMapConsumer), its value-leaf twin: the base's
   expr_map_sim_ptr, the key's expr_sim_ptr from body_expr_ptr_ok cx e2,
   array_index_outcome_post_compose_ptr, and mapping_index_tail_ptr
   (bodyPtrSubscriptSeamMapTail) for the hash; the selection is
   select_result_hashmap_nested, and storage_mapping_region_step the region
   of the inner mapping. *)
Theorem subscript_map_map_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_inv tops ctx cenv cx /\
    expr_map_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_map_sim_ptr d ctx PG func cenv cx ty e1 es ==>
    expr_map_sim_ptr d ctx PG func cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_map_pre cenv cx env e1 es` by
    metis_tac[exprSimSubscriptMapTheory.expr_map_pre_subscript_base] >>
  `?kt vt. type_place_expr env e1 = SOME (HashMapT kt vt)` by
    fs[expr_map_pre_def] >>
  `place_map_tables_agree_on_defined cenv env` by
    fs[expr_map_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def] >>
  `place_type cenv e1 = MapPT kt vt` by
    (drule_all placeTypingPropsTheory.place_type_checked_place_on_defined >>
     simp[exprLoweringTheory.value_type_place_def]) >>
  `?ikt ivt. vt = HashMapT ikt ivt` by
    (qpat_x_assum `expr_map_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_map_pre_def, Once vyperTypeSystemTheory.well_typed_expr_def] >>
     Cases_on `vt` >>
     simp[vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  gvs[] >>
  `~copies_subscript_base cenv e1 e2 /\ ~subscript_reads_base cx e1 e2` by
    metis_tac[exprSimSubscriptMapTheory.map_base_no_overlap] >>
  rewrite_tac[expr_map_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all exprSimMapKeyTheory.compile_expr_mapping_subscript_parts >>
  strip_tac >> rename1 `compile_mapping_subscript _ hashed sp = (outop,sb)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp` by
    (irule bodyPtrSubscriptSeamMapTailTheory.mapping_key_encoding_extends >>
     goal_assum (drule_at Any)) >>
  `cs_extends sp sb` by
    (mp_tac (Q.SPECL [`vv_operand bvv`, `hashed`, `sp`]
       exprLoweringPropsTheory.ci_mono_compile_mapping_subscript) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `cs_extends sn sb /\ cs_extends sm sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
              arithmeticTheory.LESS_EQ_TRANS] >>
  `gas_admissible (eval_expr cx e1) expr_map_res_ok es` by
    metis_tac[exprSimSubscriptMapTheory.subscript_map_base_admissible] >>
  qpat_x_assum `expr_map_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_map_sim_ptr_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th => rewrite_tac[
    MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  disch_then (mp_then Any irule
    bodyPtrSubscriptSeamMapComposeTheory.gas_outcome_result_cases_ptr) >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt gen_tac >> simp[] >> rpt strip_tac >> simp[]) >>
      rpt gen_tac >> simp[] >> rpt strip_tac >>
      Cases_on `res` >> gvs[]) >>
  map_every qx_gen_tac [`left`, `bres`, `mid`, `G1`, `tn1`, `t`] >>
  strip_tac >> suspend "base_success"
QED
Resume subscript_map_map_ptr[base_success]:
  qpat_x_assum `(\res ee G tn t. _) _ _ _ _ _` mp_tac >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `gas_marked_exec_ptr _ _ _ (eval_expr _ e1) _ _
             (INL (HashMapRef btr bslot bkt bvt)) _ _ _ _` >>
  drule_all mapping_marked_index_ready_map_ptr >> strip_tac >> gvs[] >>
  `body_expr_ptr_ok cx e2` by metis_tac[] >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e2) e2 (mid with gas_obs := [])` by
    (qpat_x_assum `body_expr_ptr_ok _ _` mp_tac >>
     rewrite_tac[body_expr_ptr_ok_def] >> strip_tac >>
     first_x_assum (irule o cj 1) >> simp[] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.expr_sim_ptr_def] >>
  disch_then (qspecl_then [`sm`, `sn`, `key`, `t`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- simp[]) >>
  `!(res : value + exception) r. expr_exit res r <=>
     ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r` by
    (Cases >> simp[stmtSimPropsTheory.expr_exit_INR_type]) >>
  asm_rewrite_tac[] >>
  disch_then (mp_then Any mp_tac
    (Q.INST [`R` |-> `\res ee gt r. expr_exit res r`]
      bodyPtrSubscriptMarkedComposeTheory.array_index_outcome_post_compose_ptr
      |> BETA_RULE)) >>
  disch_then ho_match_mp_tac >> goal_assum (drule_at Any) >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  map_every qx_gen_tac [`imarks`, `fin`, `kv`, `Gi`, `tni`, `it`] >>
  strip_tac >> suspend "selection"
QED
Resume subscript_map_map_ptr[selection]:
  qpat_x_assum `(\res ee G' tn' t'. _) _ _ _ _ _` mp_tac >>
  simp[] >> strip_tac >>
  `wb_frame cenv es (mid with gas_obs := []) sa s0 t` by
    (simp[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
  `!z. p.ptr_operand = Var z ==> not_fresh_at sm z` by
    (qpat_assum `compile_expr _ _ e1 _ = _`
       (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.vv_operand_def]) >>
  `!l. p.ptr_operand <> Label l` by
    (drule_all exprSimMapKeyTheory.compile_mapping_operand_not_label >>
     simp[contextTheory.vv_operand_def]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  gvs[contextTheory.vv_operand_def, contextTheory.vv_location_def] >>
  `gas_marked_exec F (ctx,func) (eval_expr cx e1) (es,s0) left
     (INL (HashMapRef btr bslot bkt (HashMapT ikt ivt))) mid (OK t)` by
    (irule gas_marked_exec_ptr_exec >> goal_assum (drule_at Any)) >>
  `gas_marked_exec F (ctx,func) (bind (eval_expr cx e2) (read_result cx))
     (mid with gas_obs := [],t) imarks (INL kv) fin (OK it)` by
    (irule gas_marked_exec_ptr_exec >> goal_assum (drule_at Any)) >>
  `expr_sim_inv cenv cx env (fin with gas_obs := []) /\
   expr_type e2 = bkt /\ hashmap_key_type bkt /\
   (?key_ty. evaluate_type (get_tenv cx) bkt = SOME key_ty /\ value_has_type key_ty kv) /\
   MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (irule exprSimSubscriptMapTheory.mapping_subscript_marked_success >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `~it.vs_halted` by metis_tac[bodyPtrHashBuiltinsSuffixTheory.hash_marked_ptr_normal] >>
  `local_ptrs_rel func cenv es.scopes s0 /\
   local_ptrs_rel func cenv (mid with gas_obs := []).scopes t` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def, loweringPostsTheory.expr_post_def] >>
  `eval_operand p.ptr_operand it = SOME bslot /\ op_taint tni p.ptr_operand = {}` by
    (qpat_assum `ghost_kept _ _ sm _ _ _ _ _`
       (mp_then Any mp_tac bodyPtrSubscriptSeamMapInterfaceTheory.mapping_slot_index_frame) >>
     disch_then irule >> simp[] >> gvs[loweringPostsTheory.expr_post_def]) >>
  `!z. p.ptr_operand = Var z ==> not_fresh_at sn z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  gvs[] >> drule_all bodyPtrSubscriptSeamMapTailTheory.mapping_index_tail_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`]
    (qx_choosel_then [`uf`, `Gu`, `tnu`] strip_assume_tac)) >>
  `wb_frame cenv (mid with gas_obs := []) (fin with gas_obs := []) sm t it` by
    (gvs[loweringPostsTheory.expr_post_def, loweringPostsTheory.wb_frame_def] >>
     metis_tac[]) >>
  `wb_frame cenv (mid with gas_obs := []) (fin with gas_obs := []) sm t uf` by
    (qspecl_then [`func`, `cenv`, `cx`, `mid with gas_obs := []`, `t`, `sm`,
                  `fin with gas_obs := []`, `fin with gas_obs := []`, `sn`, `it`, `uf`,
                  `ctx`] mp_tac exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
  `wb_frame cenv es (fin with gas_obs := []) sa s0 uf` by
    (qspecl_then [`func`, `cenv`, `cx`, `es`, `s0`, `sa`, `mid with gas_obs := []`,
                  `fin with gas_obs := []`, `sm`, `t`, `uf`, `ctx`]
       mp_tac exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
  `ghost_kept cenv (mid with gas_obs := []) sm G1 tn1 t Gu tnu` by
    (irule bodyPtrHashBuiltinsGhostComposeTheory.hash_expr_post_ghost_kept_compose >>
     first_assum (irule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `ghost_kept cenv es sa G0 tn0 s0 Gu tnu` by
    (irule bodyPtrEnvBuiltinsGhostComposeTheory.ghost_kept_locals_trans >>
     first_assum (irule_at (Pat `ghost_kept _ _ sa _ _ _ _ _`)) >>
     qexists `func` >> simp[] >>
     gvs[loweringPostsTheory.wb_frame_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `storage_mapping_region cx btr
     (hashmap_slot bslot (encode_hashmap_key (expr_type e2) kv)) (HashMapT ikt ivt)` by
    metis_tac[storage_mapping_region_step] >>
  `~expr_has_effect (Subscript ann e1 e2) ==> pure_frame cenv func es sa s0 uf` by
    (rewrite_tac[loweringPostsTheory.expr_has_effect_thm, DE_MORGAN_THM] >>
     strip_tac >>
     `pure_frame cenv func es sa s0 t` by
       (qpat_x_assum `~expr_has_effect e1 ==> _` mp_tac >> simp[]) >>
     `pure_frame cenv func (mid with gas_obs := []) sm t it` by
       (qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _`
          (mp_then Any mp_tac exprSimWordArgsTheory.expr_post_pure_frame) >>
        disch_then irule >> first_assum ACCEPT_TAC) >>
     `pure_frame cenv func (mid with gas_obs := []) sm t uf` by
       (match_mp_tac exprSimPropsTheory.pure_frame_trans >>
        qexistsl_tac [`fin with gas_obs := []`, `sn`, `it`] >>
        fs[loweringPostsTheory.wb_frame_def]) >>
     match_mp_tac exprSimPropsTheory.pure_frame_trans >>
     qexistsl_tac [`mid with gas_obs := []`, `sm`, `t`] >>
     fs[loweringPostsTheory.wb_frame_def]) >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl [`INL (HashMapRef btr (hashmap_slot bslot (encode_hashmap_key (expr_type e2) kv))
                ikt ivt)`, `fin`, `Gu`, `tnu`, `OK uf`] >>
  conj_tac
  >- simp[gas_marked_exec_ptr_def, vyperHashMapStorageTheory.select_result_hashmap_nested] >>
  disj1_tac >> qexists `uf` >>
  gvs[contextTheory.mk_ptr_def, loweringPostsTheory.wb_frame_def] >>
  metis_tac[]
QED
Finalise subscript_map_map_ptr
