(* Tuple unpacking consumes the values from one RHS read. The staged store
   traversal is independent of how a particular destination is implemented. *)
Theory bodyTupleWriteRouteMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodySim supportedStmts
  tupleTargetStoreRun tupleTargetStoreProps stmtSimAssignTuple
  fragGasOriginPtr fragGasOrigin fragGasMode gasSummary gasSummaryCompose
  vyperInterpreter vyperState venomState
  stmtLowering compileEnv finite_map list

Theorem tuple_assign_read_targets_mods:
  (!s pv t s1 v t1.
     eval_expr cx e s = (INL pv,t) /\ read_result cx pv s1 = (INL v,t1) ==>
     body_tuple_target_full_ok_mods mods exps cx (TupleTarget gs) v) /\
  bind (eval_expr cx e) (read_result cx) es = (INL (ArrayV (TupleV vs)),mid) ==>
  body_tuple_targets_full_ok_mods mods exps cx gs vs /\
  !res out. eval_stmt cx (Assign (TupleTarget gs) e) es = (res,out) <=>
            assign_tuple_target_list cx gs vs mid = (res,out)
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `bind _ _ _ = _` mp_tac >>
      simp[bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `body_tuple_target_full_ok_mods mods exps cx (TupleTarget gs)
         (ArrayV (TupleV vs))` by metis_tac[] >>
      fs[body_tuple_target_full_ok_mods_def]) >>
  simp[eval_assign_tuple_action, bind_def, Once evaluate_def]
QED

(* Routing uses the active type environment and active tops. The nested
   immutable test uses the actual root, including a qualified owner. *)
Theorem tuple_assign_route_mods:
  (!t. MEM (BaseTarget t) gs /\ immutable_root cx t /\
       ~(?nsid. t = TopLevelNameTarget nsid) ==> P) /\
  (~EXISTS (\g. ?t. g = BaseTarget t /\ immutable_root cx t /\
                   ~(?nsid. t = TopLevelNameTarget nsid)) gs /\
   lowered_value_type cenv e <> expr_type e ==> P) /\
  (!ids. lowered_value_type cenv e = expr_type e /\
         gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
         EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids ==> P) /\
  (lowered_value_type cenv e = expr_type e /\
   EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                       FLOOKUP env.var_types id = SOME ty /\
                       0 < type_memory_bytes cenv ty) \/
              (?nsid dty. g = BaseTarget (TopLevelNameTarget nsid) /\
                          supported_scalar_target tops nsid /\
                          type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
                          is_word_type dty) \/
              (?nsid fld fty.
                g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                supported_storage_field_write tops nsid fld /\
                type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
                  SOME (Type fty) /\ is_word_type fty)) gs ==> P) /\
  (lowered_value_type cenv e = expr_type e /\
   (!ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] ==>
          ~EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) /\
   ~EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid dty. g = BaseTarget (TopLevelNameTarget nsid) /\
                           supported_scalar_target tops nsid /\
                           type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
                           is_word_type dty) \/
               (?nsid fld fty.
                 g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                 supported_storage_field_write tops nsid fld /\
                 type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
                   SOME (Type fty) /\ is_word_type fty)) gs ==> P) ==> P
Proof
  strip_tac >>
  Cases_on `EXISTS (\g. ?t. g = BaseTarget t /\ immutable_root cx t /\
                          ~(?nsid. t = TopLevelNameTarget nsid)) gs`
  >- (fs[EXISTS_MEM] >> metis_tac[]) >>
  Cases_on `lowered_value_type cenv e = expr_type e` >> fs[Excl "NOT_EVERY"] >>
  Cases_on `?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids`
  >- (qpat_assum `!ids. _ ==> P` (qspec_then `ids` mp_tac) >> simp[]) >>
  `!ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] ==>
         ~EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids` by
    metis_tac[] >>
  qpat_x_assum `(_ /\ ~EVERY _ gs) ==> P` mp_tac >>
  qpat_x_assum `(EVERY _ gs) ==> P` mp_tac >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

(* The source-to-machine relation at the reached boundary. The baseline
   for old allocations stays fixed through the traversal. *)
Definition tuple_store_frame_mods_def[nocompute]:
  tuple_store_frame_mods H ctx func cenv cx start code es s <=>
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    ~s.vs_halted /\ s.vs_current_bb = code.cs_current_bb /\
    s.vs_inst_idx = LENGTH code.cs_current_insts /\
    (!aid b. FLOOKUP start.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b)
End

(* Ready relates the still-staged operands to the remaining source values;
   ExitPost supplies the linked terminal post for a failed place. Each caller
   supplies the head implementation for the selected typed write route. *)
Theorem tuple_store_staged_path_mods:
  !bts tys vs ops st sf es s G tn.
  compile_tuple_store_all cenv tys (MAP BaseTarget bts) ops st = ((),sf) /\
  LENGTH bts = LENGTH tys /\ LENGTH bts = LENGTH vs /\ LENGTH bts = LENGTH ops /\
  body_tuple_targets_full_ok_mods mods exps cx (MAP BaseTarget bts) vs /\
  tuple_store_frame_mods H ctx func cenv cx start st es s /\
  Ready bts tys vs ops st es s G tn /\
  (!bt rest ty tys v vs op ops a b es s G tn.
    compile_tuple_store_all cenv [ty] [BaseTarget bt] [op] a = ((),b) /\
    body_base_target_full_ok_mods mods exps cx bt /\
    tuple_store_frame_mods H ctx func cenv cx start a es s /\
    Ready (bt::rest) (ty::tys) (v::vs) (op::ops) a es s G tn ==>
    ?left res mid r G1 tn1.
      (!tail. assign_tuple_targets cx (BaseTarget bt) v
         (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
         (res,mid with gas_obs := tail)) /\
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) left (r,G1,tn1) /\
      ((res = INL () /\ ?t. r = OK t /\
          tuple_store_frame_mods H ctx func cenv cx start b mid t /\
          Ready rest tys vs ops b mid t G1 tn1) \/
       (?exc. res = INR exc /\ ExitPost exc mid r G1 tn1))) ==>
  ?marks res out r Gf tnf.
    (!tail. assign_tuple_target_list cx (MAP BaseTarget bts) vs
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (res,out with gas_obs := tail)) /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) marks (r,Gf,tnf) /\
    ((res = INL () /\ ?t. r = OK t /\
         tuple_store_frame_mods H ctx func cenv cx start sf out t /\
         Ready [] [] [] [] sf out t Gf tnf) \/
     (?exc. res = INR exc /\ ExitPost exc out r Gf tnf))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      `tys = [] /\ vs = [] /\ ops = []` by fs[LENGTH_NIL] >>
      gvs[compile_tuple_store_all_def, comp_return_def] >>
      qexistsl_tac [`[]`,`INL ()`,`es`,`OK s`,`G`,`tn`] >>
      simp[Once evaluate_def, return_def, gas_explicit_def] >>
      fs[tuple_store_frame_mods_def, gas_origin_ptr_path_rules]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tys` >> fs[] >> Cases_on `vs` >> fs[] >> Cases_on `ops` >> fs[] >>
  rename1 `compile_tuple_store_all _ (ty::tys) (BaseTarget bt::_) (op::ops) a = _` >>
  rename1 `Ready (bt::bts) (ty::tys) (v::vs) (op::ops) a es s G tn` >>
  drule tuple_store_base_cons >> strip_tac >>
  qpat_x_assum `body_tuple_targets_full_ok_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_tuple_target_full_ok_mods_def]) >>
  qpat_assum `!bt rest ty tys v vs op ops a b es s G tn. _`
    (drule_all_then strip_assume_tac) >>
  gvs[]
  >- (`body_tuple_targets_full_ok_mods mods exps cx (MAP BaseTarget bts) vs` by
        (qpat_assum `!tail. assign_tuple_targets _ _ _ _ = _`
           (qspec_then `[]` assume_tac) >>
         qpat_x_assum `( ?s t. assign_tuple_targets _ _ _ s = _) ==> _` irule >>
         metis_tac[]) >>
      qpat_x_assum `!tys vs ops st sf es s G tn.
        compile_tuple_store_all _ _ (MAP BaseTarget _) _ _ = _ /\ _ ==> _` drule >>
      disch_then (drule_at (Pat `Ready _ _ _ _ _ _ _ _ _`)) >>
      impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
      disch_then (qx_choosel_then [`marks`,`res`,`out`,`r`,`Gf`,`tnf`]
        (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
      `gas_path ctx func s (LENGTH left) (OK t)` by
        (irule gas_marked_path_exec >> qexists_tac `T` >>
         irule gas_origin_path_erase >> qexists_tac `explicit` >>
         qpat_assum `gas_origin_ptr_path _ (s,G,tn) left (OK t,_,_)`
           (mp_then Any strip_assume_tac gas_origin_ptr_path_projections) >>
         first_assum ACCEPT_TAC) >>
      qexistsl_tac [`left ++ marks`,`res`,`out`,`r`,`Gf`,`tnf`] >>
      conj_tac
      >- (drule gas_explicit_append_path >> disch_then (qspec_then `marks` SUBST1_TAC) >>
          gen_tac >> pure_once_rewrite_tac[assign_tuple_target_list_cons] >>
          pure_rewrite_tac[GSYM APPEND_ASSOC] >>
          qexistsl_tac [`INL ()`, `mid with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail`] >>
          simp[]) >>
      conj_tac >- (irule gas_origin_ptr_path_append >> metis_tac[]) >>
      simp[]) >>
  qexistsl_tac [`left`,`INR exc`,`mid`,`r`,`G1`,`tn1`] >> simp[] >>
  gen_tac >> simp[Once assign_tuple_target_list_cons] >> metis_tac[]
QED

Theorem tuple_assign_flat_targets_mods:
  supported_stmt tops bindings (Assign (TupleTarget gs) e) ==>
  ?bts. gs = MAP BaseTarget bts /\ EVERY (supported_target tops bindings) bts
Proof
  simp[Once supported_stmt_def, supported_assignment_def] >>
  strip_tac >>
  qpat_x_assum `supported_expr _ _` kall_tac >>
  pop_assum mp_tac >> Induct_on `gs` >> simp[] >>
  Cases_on `h` >> simp[] >> metis_tac[MAP, EVERY_DEF]
QED
