Theory bodyPtrSubscriptRootExecution
Ancestors
  bodyPtrSubscriptMappingInterface targetPlaceSim exprLowering
  vyperInterpreter vyperState fragGasPathPtr bodyPtrDefs
  exprLoweringProps exprSimProps loweringPosts context ptrDiscipline venomState
  vyperTypeEnv vyperPlaceResultTyping compileEnv exprSimHypsDefs

(* The source computation is independent of the observation tail.  This
   equation supplies execution, unlike admissibility-domain weakening. *)
Theorem mapping_root_source:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (HashMapVarDecl tr kt vt, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot ==>
  eval_expr cx (TopLevelName ann (src,id)) es =
    (INL (HashMapRef tr (n2w slot) kt vt), es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def,
       lift_option_type_def, return_def]
QED

Theorem mapping_root_counted:
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (HashMapVarDecl tr kt vt, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  ~s0.vs_halted /\
  Q (INL (HashMapRef tr (n2w slot) kt vt))
    (es with gas_obs := []) G0 tn0 s0 ==>
  gas_outcome_ptr D all_tops (ctx,func) PG
    (eval_expr cx (TopLevelName ann (src,id))) (es,s0,G0,tn0) Q R
Proof
  rpt strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (HashMapRef tr (n2w slot) kt vt)`, `es`,
                `G0`, `tn0`, `OK s0`] >>
  simp[mapping_root_source, gas_path_ptr_rules]
QED

Theorem mapping_root_compile:
  FLOOKUP cenv.ce_module_vars nsid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) ==>
  compile_expr cenv ty (TopLevelName ann nsid) sa =
    (LocatedValue (expr_type (TopLevelName ann nsid))
       (mk_ptr (Lit slot) (slot_loc tr)), sa)
Proof
  Cases_on `tr` >> simp[Once compile_expr_def, slot_loc_def]
QED

Theorem mapping_root_environment:
  expr_sim_inv cenv cx env es /\
  type_place_expr env (TopLevelName ann (src,id)) = SOME (HashMapT kt vt) /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
  ?tops tr id_str slot.
    get_module_code cx src = SOME tops /\
    find_var_decl_by_name id tops = SOME (HashMapVarDecl tr kt vt,id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    FLOOKUP cenv.ce_module_vars (src,id) =
      SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  rpt strip_tac >>
  drule type_place_expr_global_lookup >> strip_tac >>
  `env_consistent env cx es` by gvs[expr_sim_inv_def] >>
  drule_all env_consistent_toplevel_hashmap_static >>
  strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout cx tr src id_str = SOME slot` >>
  Cases_on `tr` >>
  gvs[storage_vars_rel_def, transient_vars_rel_def, var_decl_transient_def] >>
  metis_tac[]
QED

(* The remaining widened body preconditions are unnecessary for this
   zero-instruction case; this theorem assumes only their typing/invariant
   fields and the initial execution frame. *)
Theorem mapping_root_execution:
  expr_sim_inv cenv cx env es /\
  type_place_expr env (TopLevelName ann (src,id)) = SOME (HashMapT kt vt) /\
  compile_expr cenv ty (TopLevelName ann (src,id)) sa = (vv,sb) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (TopLevelName ann (src,id))) (es,s0,G0,tn0)
    (\res ee G tn t. ?tr slot p.
      res = INL (HashMapRef tr slot kt vt) /\
      vv = LocatedValue (expr_type (TopLevelName ann (src,id))) p /\
      p.ptr_location = slot_loc tr /\
      eval_operand p.ptr_operand t = SOME slot /\
      op_taint tn p.ptr_operand = {} /\
      place_ptr_rel cenv cx t (HashMapRef tr slot kt vt)
        slot (SOME p.ptr_location) (HashMapT kt vt) /\
      (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
      stmt_state_rel ctx func cenv cx ee t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
         aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) ==>
         mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
      locals_kept cenv es s0 t /\ ghost_inv d cenv cx ee G tn t /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r)
Proof
  rpt strip_tac >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all mapping_root_environment >> strip_tac >>
  drule mapping_root_compile >> strip_tac >> gvs[] >>
  irule mapping_root_counted >>
  simp[] >>
  simp[mk_ptr_def, eval_operand_def, op_taint_def, place_ptr_rel_def,
       locals_kept_refl, ghost_inv_def, ghost_kept_def] >>
  conj_tac
  >- (drule msg_gas_state_frame >>
      disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
      simp[NoAsms]) >>
  gvs[ghost_inv_def, op_taint_def] >> first_assum ACCEPT_TAC
QED

