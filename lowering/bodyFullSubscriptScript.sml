(* Dispatch the joint subscript judgment, leaving only the unframed array
   case as a premise. Each branch supplies the VV judgment at one endpoint. *)
Theory bodyFullSubscript
Ancestors
  bodyFullShadowBodyInv
  bodyFullSubscriptMapBase bodyFullSubscriptMap bodyFullSubscriptTuple
  bodyFullSubscriptArrayCode bodyFullSubscriptArrayMemory
  bodyFullOfVV bodyFullPreds bodySimFull bodySimExprCases
  exprSimPlaces exprSimTuple exprSimSubscriptMap exprSimSource exprSimHyps
  exprSimHypsDefs exprSimMapDefs placeTypingProps exprLowering
  loweringPosts compileEnv vyperInterpreter vyperTypeSystem vyperState vyperAST
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

val _ = Parse.hide "body";

Theorem subscript_ih_not_read[local]:
  !mods exps cx e1 e2.
    (!s'' res t s3 res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==> body_expr_full_ok_mods mods exps cx e2) /\
    ~subscript_reads_base cx e1 e2 ==>
    !s0 r0 t0. eval_expr cx e1 s0 = (INL r0,t0) ==> body_expr_full_ok_mods mods exps cx e2
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`s0`,`r0`,`t0`,`t0`,`r0`,`t0`] mp_tac) >>
  simp[vyperStateTheory.return_def]
QED

Theorem subscript_value_base_type:
  !mods.
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  place_type cenv obj = ValPT bt ==>
  bt = expr_type obj
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Subscript ann obj idx)` by
    fs[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
  simp[Once vyperTypeSystemTheory.well_typed_expr_def] >>
  rpt strip_tac
  >- (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
      simp[expr_sim_inv_def] >> strip_tac >>
      drule_all place_type_well_typed_on_defined >> simp[]) >>
  `place_map_tables_agree_on_defined cenv env` by fs[expr_sim_inv_def] >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  Cases_on `vt` >> gvs[value_type_place_def] >>
  drule type_place_expr_annotation >> simp[]
QED

Theorem subscript_expr_full_ok_from_place_base:
  !mods exps cx v8 e1 e2.
    (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et bd.
       (!s'' res t s3 res' t'.
          eval_expr cx e1 s'' = (INL res,t) /\
          (if subscript_reads_base cx e1 e2 then
             bind (read_result cx res) (\v. return (Value v))
           else return res) s3 = (INL res',t') ==>
          body_expr_full_ok_mods mods exps cx e2) /\
       body_expr_full_ok_mods mods exps cx e1 /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
       body_const_cells_agree mods cx env es /\
       expr_body_pre_mods mods cenv cx env (Subscript v8 e1 e2) es /\
       expr_type e1 = ArrayT et bd /\
       place_type cenv e1 = ValPT (ArrayT et bd) /\
       post_value_type cenv e1 = expr_type e1 /\
       ~((!t r t'. eval_expr cx e2 t = (INL r,t') ==>
                   t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
         ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
         (!s tr slot vt t.
            eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
         ((~cenv.ce_is_ctor /\
           !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) \/
          ((?n. bd = Fixed n) /\
           (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
           !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory))) ==>
       expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx ty (Subscript v8 e1 e2) es) /\
    (!s'' res t s3 res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_full_ok_mods mods exps cx e2) /\
    body_expr_full_ok_mods mods exps cx e1 ==>
    body_expr_full_ok_mods mods exps cx (Subscript v8 e1 e2)
Proof
  rpt gen_tac >> strip_tac >> once_rewrite_tac[body_expr_full_ok_def] >>
  reverse conj_tac >- (conj_tac >- simp[] >> suspend "mapping_result") >>
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac expr_body_pre_subscript_base_type >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Subscript v8 e1 e2) es`
    suffices_by (strip_tac >> simp[] >> suspend "value") >>
  Cases_on `place_type cenv e1` >- suspend "mapping_base" >>
  drule_all subscript_value_base_type >> strip_tac >> gvs[] >>
  drule_all subscript_base_array_or_tuple >> strip_tac >> gvs[]
  >- suspend "array" >>
  irule subscript_tuple_vv_sim_full >> simp[] >>
  drule_all tuple_pre_base >> strip_tac >>
  qpat_assum `body_expr_full_ok cx e1`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  metis_tac[]
QED

Resume subscript_expr_full_ok_from_place_base[mapping_result]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_then assume_tac expr_map_pre_subscript_base >>
  `~subscript_reads_base cx e1 e2` by
    (gvs[expr_map_pre_def] >> metis_tac[map_base_no_overlap]) >>
  `!s0 r0 t0. eval_expr cx e1 s0 = (INL r0,t0) ==> body_expr_full_ok cx e2` by
    metis_tac[subscript_ih_not_read] >>
  irule subscript_map_map_full >> metis_tac[body_expr_full_ok_map]
QED

Resume subscript_expr_full_ok_from_place_base[value]:
  irule expr_sim_full_of_vv >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists `x` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Subscript v8 e1 e2) (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >> metis_tac[]
QED

Resume subscript_expr_full_ok_from_place_base[mapping_base]:
  rename1 `place_type cenv e1 = MapPT kt vt` >>
  drule_all_then assume_tac expr_body_pre_map_subscript_base >>
  drule_all expr_map_pre_checked_type >> strip_tac >>
  `~subscript_reads_base cx e1 e2` by metis_tac[map_base_no_overlap] >>
  `!s0 r0 t0. eval_expr cx e1 s0 = (INL r0,t0) ==> body_expr_full_ok cx e2` by
    metis_tac[subscript_ih_not_read] >>
  irule subscript_map_full >> metis_tac[body_expr_full_ok_map]
QED

Resume subscript_expr_full_ok_from_place_base[array]:
  Cases_on `(!t r t'. eval_expr cx e2 t = (INL r,t') ==>
                       t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
            ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
            (!s tr slot vt t.
               eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
            ((~cenv.ce_is_ctor /\
              !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) \/
             ((?n. bd = Fixed n) /\
              (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
              !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory))`
  >- ((qpat_x_assum `(!t r t'. _) /\ _` strip_assume_tac >>
       `!s0 r0 t0. eval_expr cx e1 s0 = (INL r0,t0) ==> body_expr_full_ok cx e2` by
         metis_tac[subscript_ih_not_read])
      >- (irule subscript_array_framed_code_full >> metis_tac[]) >>
      irule subscript_array_framed_memory_full >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise subscript_expr_full_ok_from_place_base
