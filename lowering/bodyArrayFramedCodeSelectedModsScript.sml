(* Extend the reached code array at the actual address selected by the key. *)
Theory bodyArrayFramedCodeSelectedMods
Ancestors
  bodyArrayNoCopyCutsMods gasOutcomeFullPostMods bodyForRangeScalarFrameMods
  bodyFullPathHistory stateRelProj bodyFullHashKeccakFixed bodyFullShadowBodyInv
  vyperStorageFootprint vyperInterpreter gasExplicitSites fragGasOriginPtr
  exprSimProps exprSimSubscriptArrayFramed exprSimMemDefs freshWrites
  loweringPosts bodyFullPostsMods bodyPtrDefs exprLoweringProps compileEnv context
  vyperState vyperAST vyperTypeInvariants vyperTypeSystem
  ptrDiscipline venomState words finite_map

Theorem selected_code_immutable_type[local]:
  place_type_value cx (ImmutablePlace src id path) mid = (INL tv,mid) /\
  mid.immutables = (fin:evaluation_state).immutables /\
  FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms)
    id = SOME (root,v) ==>
  subscripts_type root path = SOME tv
Proof
  strip_tac >>
  qpat_x_assum `place_type_value _ _ _ = _` mp_tac >>
  simp[place_type_value_def, get_immutables_def, get_address_immutables_def,
       bind_def, lift_option_type_def, return_def, raise_def] >>
  Cases_on `ALOOKUP fin.immutables cx.txn.target` >> gvs[] >>
  Cases_on `subscripts_type root path` >> simp[return_def, raise_def]
QED

Theorem selected_code_place_step[local]:
  vv_place_ptr_mods cenv cx fin it raw (LocatedValue (ArrayT et bd) p) /\
  p.ptr_location = LocCode /\
  (!v. raw <> Value v) /\
  eval_result_typed (env,cx,mid) raw (Type (ArrayT et bd)) /\
  env.type_defs = get_tenv cx /\
  mid.immutables = fin.immutables /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  select_result cx (ArrayT et bd) raw sb fin = (INL child,fin) /\
  mem_step_offset (ArrayTV etv bd) sb = SOME (j,etv) /\
  eval_operand p.ptr_operand it = SOME w /\
  eval_operand dst sf = SOME (w + n2w j) ==>
  (?src id path. child = PlaceR (ImmutablePlace src id (path ++ [sb]))) /\
  vv_place_ptr_mods cenv cx fin sf child (LocatedValue et (mk_ptr dst LocCode))
Proof
  strip_tac >> Cases_on `raw` >> gvs[eval_result_typed_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def, slot_loc_def, AllCaseEqs()] >>
  rename1 `PlaceR (ImmutablePlace src id path)` >>
  `child = PlaceR (ImmutablePlace src id (path ++ [sb]))` by
    gvs[select_result_def, extend_place_def, bind_def, return_def,
        lift_sum_def, raise_def, ignore_bind_def, AllCaseEqs(), extend_memory_place_def] >>
  qpat_x_assum `runtime_place_typed _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [runtime_place_typed_def]) >>
  `subscripts_type itv path = SOME (ArrayTV etv bd)` by
    (irule selected_code_immutable_type >>
     goal_assum (drule_at (Pat `place_type_value _ _ _ = _`)) >>
     qexistsl_tac [`fin:evaluation_state`,`iv`] >> simp[]) >>
  drule mem_path_offset_sound >> strip_tac >> gvs[] >>
  drule_all_then assume_tac mem_path_offset_snoc >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def, mk_ptr_def] >>
  simp[word_add_n2w, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem selected_code_holds_step[local]:
  vv_holds_mods cenv cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) fin it /\
  p.ptr_location = LocCode /\
  eval_operand p.ptr_operand it = SOME w /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  value_has_type etv v /\
  read_result cx child fin = (INL v,fin) /\
  mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv) /\
  eval_operand dst sf = SOME (w + n2w j) ==>
  vv_holds_mods cenv cx et child (LocatedValue et (mk_ptr dst LocCode)) fin sf
Proof
  strip_tac >>
  `j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv` by
    (Cases_on `bd` >> gvs[mem_step_offset_def, AllCaseEqs()]) >>
  gvs[vv_holds_mods_def, immutable_holds_mods_def, mk_ptr_def] >>
  qexistsl_tac [`src`,`tops`] >> simp[] >>
  drule_all_then mp_tac immutable_holds_array_element >>
  simp[immutable_holds_def, arithmeticTheory.ADD_COMM]
QED

Theorem selected_code_post_tail[local]:
  vv_post_mods H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
    es sa st2 s0 fin raw (LocatedValue (ArrayT et bd) p) it /\
  vv_holds_mods cenv cx et child (LocatedValue et (mk_ptr dst LocCode)) fin sf /\
  vv_place_ptr_mods cenv cx fin sf child (LocatedValue et (mk_ptr dst LocCode)) /\
  child = PlaceR (ImmutablePlace src id path) /\
  stmt_state_rel H ctx func cenv cx fin sf /\
  immutable_frame_mods func cenv cx fin sf /\
  sf.vs_memory = it.vs_memory /\ sf.vs_allocas = it.vs_allocas /\
  (!x. not_fresh_at sa x ==> lookup_var x sf = lookup_var x it) ==>
  vv_post_mods H ctx func cenv cx (Subscript et obj idx)
    es sa sb s0 fin child (LocatedValue et (mk_ptr dst LocCode)) sf
Proof
  simp[vv_post_mods_def, expr_type_def, vv_at_def, mk_ptr_def, vv_storage_live_def] >>
  strip_tac >>
  `locals_kept cenv es fin s0 sf` by
    (irule locals_kept_mem_tail >> qexists_tac `it` >> simp[]) >>
  `pure_frame cenv func es sa s0 sf <=> pure_frame cenv func es sa s0 it` by
    (irule pure_frame_state_cong >> simp[]) >>
  gvs[] >> first_assum ACCEPT_TAC
QED

Theorem selected_code_ghost_kept_tail[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP Gf x = FLOOKUP Gi x /\ op_taint tnf (Var x) = op_taint tni (Var x)) /\
  tnf.t_mem = tni.t_mem ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf
Proof
  simp[ghost_kept_at_def] >> strip_tac >> rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >> simp[] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem selected_code_cut_facts[local]:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,LocatedValue (ArrayT et bd) p,iop,dst,LocCode)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb) (gs1,mid,raw,s,G1,tn1)
    (gs2,fin,IntV i,it,Gi,tni) /\
  p.ptr_location = LocCode /\ post_value_type cenv obj = ArrayT et bd ==>
  fn_inst_ids_distinct func /\ ~it.vs_halted /\ fin.gas_obs = [] /\
  alloca_history func it /\ s0.vs_alloca_next <= it.vs_alloca_next /\
  local_ptrs_reserved cenv st2 /\
  (!x. not_fresh_at sa x ==> not_fresh_at st2 x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!v. raw <> Value v)
Proof
  simp[array_nocopy_cut_mods_def] >> strip_tac >>
  `sa.cs_next_var <= st2.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `!v. _ = Value v /\ _ ==> _` mp_tac >>
  simp[is_word_type_def,is_bytestring_type_def] >>
  simp[] >> strip_tac >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem selected_code_allocation_entry[local]:
  vv_post_mods H ctx func cenv cx e es sa st2 s0 fin raw bvv it /\
  ghost_inv_at_mods D lo d cenv cx fin Gi tni it ==>
  alloca_inv it /\ allocas_from lo it
Proof
  simp[vv_post_mods_def, ghost_inv_at_mods_def] >> strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> simp[]
QED

(* The successful path and its endpoints are fixed before choosing a horizon. *)
Theorem framed_code_selected_endpoint_mods:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,LocatedValue (ArrayT et bd) p,iop,dst,LocCode)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb) (gs1,mid,raw,s,G1,tn1)
    (gs2,fin,IntV i,it,Gi,tni) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ post_value_type cenv obj = ArrayT et bd /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
       vv_post_mods H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
         es sa st2 s0 fin raw (LocatedValue (ArrayT et bd) p) it /\
       ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
  eval_result_typed (env,cx,mid) raw (Type (ArrayT et bd)) /\
  env.type_defs = get_tenv cx /\ fin.immutables = mid.immutables /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\ value_has_type etv v /\
  read_result cx child fin = (INL v,fin) /\
  (!tail. select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i))
    (fin with gas_obs := tail) = (INL child,fin with gas_obs := tail)) /\
  mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv) /\
  eval_operand p.ptr_operand it = SOME w /\ eval_operand dst sf = SOME (w + n2w j) /\
  op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
  sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
  sf.vs_memory = it.vs_memory /\ sf.vs_allocas = it.vs_allocas /\
  sf.vs_alloca_next = it.vs_alloca_next /\ sf.vs_data_section = it.vs_data_section /\
  sf.vs_call_ctx = it.vs_call_ctx /\ sf.vs_accounts = it.vs_accounts /\
  sf.vs_transient = it.vs_transient /\ sf.vs_immutables = it.vs_immutables /\
  tnf.t_mem = tni.t_mem /\ tnf.t_stor = tni.t_stor /\
  tnf.t_trans = tni.t_trans /\ tnf.t_imm = tni.t_imm /\
  (!x. not_fresh_at st2 x ==> lookup_var x sf = lookup_var x it /\
       FLOOKUP Gf x = FLOOKUP Gi x /\ op_taint tnf (Var x) = op_taint tni (Var x)) /\
  (!H : (bool # bytes32 # type_value) list # num list.
     stmt_state_rel H ctx func cenv cx fin it ==> stmt_state_rel H ctx func cenv cx fin sf) /\
  (!D. allocas_from lo it ==>
       gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (it,Gi,tni) [] (OK sf,Gf,tnf)) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx et obj idx et bd st0 (es,s0,G0,tn0) (sa,sb,dst,LocCode)
    (raw,IntV i) (fin,it,Gi,tni)
Proof
  strip_tac >> drule_all_then strip_assume_tac selected_code_cut_facts >>
  `fin with gas_obs := [] = (fin:evaluation_state)` by
    (qpat_x_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i)) fin = (INL child,fin)` by
    (qpat_assum `!tail. select_result _ _ _ _ (fin with gas_obs := tail) =
         (INL child,fin with gas_obs := tail)` (qspec_then `[]` mp_tac) >>
     qpat_assum `fin with gas_obs := [] = fin` (fn th => PURE_ONCE_REWRITE_TAC [th]) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x sf = lookup_var x it /\
      FLOOKUP Gf x = FLOOKUP Gi x /\ op_taint tnf (Var x) = op_taint tni (Var x)` by
    (rpt strip_tac >> first_x_assum (drule_then assume_tac) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (irule selected_code_ghost_kept_tail >> qexistsl_tac [`Gi`,`tni`] >>
     simp[] >> rpt strip_tac >> first_x_assum (drule_then assume_tac) >> simp[]) >>
  rewrite_tac[array_select_outcome_mods_def, LET_THM] >> BETA_TAC >>
  irule gas_outcome_full_mods_pure >> (reverse conj_tac >- simp[]) >>
  qexistsl_tac [`Gf`,`fin:evaluation_state`,`INL (child:eval_result)`,`sf`,`tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  asm_rewrite_tac[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  suspend "success"
QED

Resume framed_code_selected_endpoint_mods[success]:
  drule_all_then strip_assume_tac selected_code_allocation_entry >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (it,Gi,tni) [] (OK sf,Gf,tnf)` by simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `alloca_history func sf` by (drule_all body_full_path_alloca_history >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx fin it /\ immutable_frame_mods func cenv cx fin it /\
   vv_holds_mods cenv cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) fin it /\
   vv_place_ptr_mods cenv cx fin it raw (LocatedValue (ArrayT et bd) p)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [vv_post_mods_def,expr_type_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx fin sf` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ ==> stmt_state_rel H _ _ _ _ _ _`
       (drule_then ACCEPT_TAC)) >>
  qpat_assum `stmt_state_rel H _ _ _ _ _ sf`
    (mp_then Any assume_tac stmt_state_rel_allocas_below_fmp) >>
  `immutable_frame_mods func cenv cx fin sf` by
    (irule immutable_frame_mods_exterior_frame >>
     goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
     qexists_tac `st2` >> simp[] >> rpt strip_tac >> first_x_assum (drule_then assume_tac) >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx fin Gf tnf sf` by
    (irule ghost_inv_at_mods_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `st2` >> asm_rewrite_tac[]) >>
  `mid.immutables = fin.immutables` by simp[] >>
  drule_all_then strip_assume_tac selected_code_place_step >>
  drule_all_then assume_tac selected_code_holds_step >>
  `vv_post_mods H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin child
       (LocatedValue et (mk_ptr dst LocCode)) sf` by
    (irule selected_code_post_tail >> simp[] >>
     goal_assum (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  BETA_TAC >> qexists_tac `child` >>
  simp[expr_type_def, mk_ptr_def, vv_location_def, vv_store_bound_nonmem, ptr_vv_ok_def]
QED
Finalise framed_code_selected_endpoint_mods
