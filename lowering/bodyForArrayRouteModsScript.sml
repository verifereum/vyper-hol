(* Array-iterator capture and indexed round inputs for linked For loops. *)
Theory bodyForArrayRouteMods
Ancestors
  bodyFullForStorageCapture forNestedArrayCapture whitelistForIterImmCopy
  bodyFullPredsMods bodyFullPostsMods exprBodyPreProps exprBodyPreTypingProps
  vyperValueOperation vyperBareGlobalName vyperStorageFootprint vyperValue
  vyperAST vyperInterpreter vyperState vyperTyping vyperTypeSystem
  valueEncodingTyping stmtSimAugAssignPlaceStorage fragExec list arithmetic words
  reasonSourceProps exprSimAttribute exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants vyperTypeValues
  loweringPosts bodyPtrDefs bodyPtrBopInLiveStorage accountsRelProps venomExecSemantics venomState
  compileEnv context fragGasOriginPtr finite_map alist option
  gasOutcomeFullMods gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  gasContext stmtSimForRounds vyperStorageTrace exprSimMemorySource
  stmtSimAppendStorageCompose
Libs
  monadsyntax

val _ = Parse.hide "body";

(* A slot operand may denote a proper subregion of a qualified root.
   Retain both the captured addresses and the original root witness. *)
Theorem for_array_storage_capture_mods:
  expr_body_pre_mods mods c cx env e es /\
  eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot (ArrayTV et bd))),ee) /\
  valid_horizon cx st0 H ee.storage_trace /\
  storage_well_formed_on cx es (FST H) /\
  storage_well_formed_on cx ee (FST H) /\
  len = (case bd of Fixed n => n | Dynamic n =>
           w2n (lookup_storage slot (get_storage cx ee tr))) /\
  bound_length bd <= n ==>
  ?vs off root path delta.
    eval_iterator cx (Array e) es = (INL vs,ee) /\
    vs = GENLIST (\i. PlaceR (StoragePlace tr
      ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
       n2w (i * type_slot_size et)) et)) len /\
    LENGTH vs = len /\ compatible_bound bd len /\
    compatible_bound (Dynamic n) (LENGTH vs) /\
    MEM (StorageRoot tr off root) ee.storage_trace /\
    storage_subregion root path delta (ArrayTV et bd) /\
    slot = n2w off + n2w delta
Proof
  strip_tac >> drule_all_then strip_assume_tac for_storage_iterator_capture_mods >>
  `len <= n` by decide_tac >>
  qpat_x_assum `len = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `GENLIST f len` >>
  qexistsl [`GENLIST f len`,`off`,`root`,`path`,`delta`] >>
  simp[compatible_bound_def,Abbr `f`]
QED

Theorem for_array_storage_round_input_mods:
  vs = GENLIST (\i. PlaceR (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
     n2w (i * type_slot_size et)) et)) len /\
  a::rs = DROP k vs /\ compatible_bound bd len /\
  MEM (StorageRoot tr off root) em.storage_trace /\
  storage_subregion root path delta (ArrayTV et bd) /\
  slot = n2w off + n2w delta /\
  ee.storage_trace = em.storage_trace ++ extra /\
  valid_horizon cx st0 H ee.storage_trace ==>
  k < len /\ rs = DROP (SUC k) vs /\
  a = PlaceR (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
      n2w (k * type_slot_size et)) et) /\
  storage_place_observed H (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
      n2w (k * type_slot_size et)) et)
Proof
  strip_tac >>
  qpat_assum `a::rs = DROP k vs` (strip_assume_tac o MATCH_MP DROP_EQ_CONS o SYM) >>
  `k < len` by
    (qpat_assum `vs = GENLIST _ _` (fn eq => fs[eq])) >>
  `len <= bound_length bd` by
    (Cases_on `bd` >> gvs[compatible_bound_def,bound_length_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac
  >- (qpat_assum `EL k vs = a` (rewrite_tac o single o SYM) >>
      qpat_assum `vs = GENLIST _ _` (rewrite_tac o single) >> simp[]) >>
  irule for_storage_iterator_child_observed >> conj_tac >- decide_tac >>
  `MEM (StorageRoot tr off root) ee.storage_trace` by simp[MEM_APPEND] >>
  irule aug_place_storage_rooted_observed >>
  qexistsl [`cx`,`delta`,`off`,`path`,`st0`,`ee.storage_trace`,`root`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The nonslot result is a snapshot of values, even when the input
   is a memory or immutable place. *)
Theorem for_array_value_capture_mods:
  eval_expr cx e es = (INL raw,ee) /\
  (!tr slot et bd. raw <> PlaceR (StoragePlace tr slot (ArrayTV et bd))) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  bound_length bd <= n ==>
  ?vs. eval_iterator cx (Array e) es = (INL vs,ee) /\
    vs = MAP Value (array_elements (ArrayTV et bd) av) /\
    compatible_bound bd (LENGTH vs) /\
    compatible_bound (Dynamic n) (LENGTH vs) /\
    !i ei. i < LENGTH vs ==>
      read_result cx (EL i vs) ei =
        (INL (EL i (array_elements (ArrayTV et bd) av)),ei)
Proof
  strip_tac >> simp[Once evaluate_def,bind_def] >>
  drule array_iterator_results_copy >>
  disch_then (fn th => simp[th,bind_def,lift_option_type_def,return_def,
                            extract_elements_def,EL_MAP,read_result_def]) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def,array_elements_def,compatible_bound_def,bound_length_def] >>
  decide_tac
QED

(* Re-observe the same qualified place at the current round, and relate
   the indexed snapshot value to the current saved immutable operand. *)
Theorem for_array_immutable_round_input_mods:
  raw = PlaceR (ImmutablePlace src id path) /\
  read_result cx raw em = (INL (ArrayV av),em) /\
  lookup_immutable cx ee src id = lookup_immutable cx em src id /\
  ALOOKUP c.ce_modules src = SOME tops /\
  immutable_holds (c with ce_module := src) cx (ArrayT et bd) raw bw ee s /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  well_formed_type_value (ArrayTV tv bd) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\ k < LENGTH vs ==>
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  ?v. EL k vs = Value v /\
    read_result cx (EL k vs) ee = (INL v,ee) /\
    value_has_type tv v /\ val_wf tv v /\
    immutable_holds_mods c cx et (Value v)
      (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
                 k * type_memory_size tv)) ee s
Proof
  strip_tac >>
  `read_result cx raw ee = (INL (ArrayV av),ee)` by
    gvs[read_result_immutable_place] >>
  `val_wf (ArrayTV tv bd) (ArrayV av)` by simp[value_has_type_val_wf] >>
  `k < LENGTH (array_elements (ArrayTV tv bd) av)` by gvs[] >>
  `immutable_holds (c with ce_module := src) cx et
       (Value (EL k (array_elements (ArrayTV tv bd) av)))
       (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
                  k * type_memory_size tv)) ee s /\
   value_has_type tv (EL k (array_elements (ArrayTV tv bd) av)) /\
   0 < type_memory_size tv` by
    (irule immutable_iter_element_ready >> simp[] >>
     qexistsl [`av`,`raw`] >> simp[]) >>
  simp[EL_MAP,read_result_def,return_def,value_has_type_val_wf] >>
  rewrite_tac[immutable_holds_mods_def] >> qexistsl [`src`,`tops`] >>
  gvs[AC ADD_ASSOC ADD_COMM]
QED

(* The linked VV post supplies the actual saved slot operand and, for a
   dynamic bound, the clean header used by the length instruction. *)
Theorem for_array_slot_operand_mods:
  vv_post_mods H ctx func c cx e es sa sb s0 ee
    (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv s /\
  ptr_vv_ok cx (post_value_type c e)
    (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv ee G tn s /\
  evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV et bd) /\
  ~is_word_type (post_value_type c e) ==>
  ?p. vv = LocatedValue (post_value_type c e) p /\ p.ptr_location = slot_loc tr /\
    eval_operand p.ptr_operand s = SOME slot /\ op_taint tn p.ptr_operand = {} /\
    (case bd of Fixed _ => T | Dynamic _ =>
       key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
       (if tr then tload slot s else sload slot s) =
         lookup_storage slot (get_storage cx ee tr))
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  Cases_on `vv` >> gvs[vv_at_def,vv_place_ptr_mods_def,vv_place_ptr_def] >>
  rename1 `ptr_vv_ok _ _ _ (LocatedValue ann p) _ _ _ _` >>
  `ann = post_value_type c e /\
   storage_holds cx tr (post_value_type c e)
       (PlaceR (StoragePlace tr slot (ArrayTV et bd))) slot ee s` by
    (Cases_on `tr` >> gvs[vv_holds_mods_def,vv_holds_def,slot_loc_def]) >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  simp[] >> Cases_on `bd` >> simp[] >> conj_tac
  >- (irule located_dynamic_header_clean >>
      qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[GSYM slot_loc_def]) >>
  qpat_x_assum `storage_holds _ _ _ _ _ _ _` mp_tac >>
  simp[storage_holds_def,type_slot_size_def] >> strip_tac >>
  drule storage_range_agree_head >>
  simp[type_slot_size_def] >> Cases_on `tr` >> simp[sload_def,tload_def]
QED

(* The local frame stays in c. Only the lookup for this place uses src. *)
Theorem for_array_immutable_operand_mods:
  vv_post_mods H ctx func c cx e es sa sb s0 ee
    (PlaceR (ImmutablePlace src name path)) vv s /\
  ~is_word_type (post_value_type c e) ==>
  ?p tops off itv iv delta tv.
    vv = LocatedValue (post_value_type c e) p /\ p.ptr_location = LocCode /\
    ALOOKUP c.ce_modules src = SOME tops /\
    FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    lookup_immutable cx ee src name = SOME (itv,iv) /\
    mem_path_offset itv path = SOME (delta,tv) /\
    eval_operand p.ptr_operand s = SOME (n2w (off + delta))
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  Cases_on `vv` >> gvs[vv_at_def,vv_place_ptr_mods_def,vv_place_ptr_def] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  gvs[vv_holds_mods_def,IS_SOME_EXISTS,lookup_immutable_def] >>
  qexistsl [`itv`,`iv`,`k`,`tvk`] >> simp[]
QED

Theorem for_array_nonslot_vv_capture_mods:
  expr_body_pre_mods mods c cx env e es /\ expr_type e = ArrayT elem bd /\
  eval_expr cx e es = (INL raw,ee) /\
  vv_post_mods H ctx func c cx e es sa sb s0 ee raw vv s /\
  (!tr slot et bd. raw <> PlaceR (StoragePlace tr slot (ArrayTV et bd))) /\
  bound_length bd <= n ==>
  ?et av vs. evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
    evaluate_type (get_tenv cx) elem = SOME et /\
    read_result cx raw ee = (INL (ArrayV av),ee) /\
    value_has_type (ArrayTV et bd) (ArrayV av) /\
    eval_iterator cx (Array e) es = (INL vs,ee) /\
    vs = MAP Value (array_elements (ArrayTV et bd) av) /\
    compatible_bound bd (LENGTH vs) /\ compatible_bound (Dynamic n) (LENGTH vs) /\
    !i ei. i < LENGTH vs ==>
      read_result cx (EL i vs) ei =
        (INL (EL i (array_elements (ArrayTV et bd) av)),ei)
Proof
  strip_tac >>
  `?v. read_result cx raw ee = (INL v,ee)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     Cases_on `vv` >> gvs[vv_holds_mods_def]
     >- (drule reason_vv_read_success >> simp[]) >>
     rename1 `if p.ptr_location = LocCode then _ else _` >>
     Cases_on `p.ptr_location = LocCode` >> gvs[immutable_holds_mods_def]
     >- (drule immutable_holds_read >> simp[]) >>
     drule reason_vv_read_success >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) es = (INL v,ee)` by simp[bind_def] >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  qpat_assum `bind _ _ _ = _`
    (mp_then Any mp_tac (REWRITE_RULE [ETA_THM] eval_expr_read_type_sound)) >>
  disch_then (qspec_then `env` mp_tac) >> fs[runtime_consistent_def] >> strip_tac >>
  fs[value_runtime_typed_def] >> drule_then strip_assume_tac evaluate_type_ArrayT_cases >>
  qpat_x_assum `tv = ArrayTV _ _` SUBST_ALL_TAC >>
  `?av. v = ArrayV av` by
    (qpat_x_assum `value_has_type _ v` mp_tac >>
     Cases_on `bd` >> Cases_on `v` >> simp[value_has_type_def]) >>
  gvs[] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV elem_tv bd)` by simp[] >>
  drule_all_then strip_assume_tac for_array_value_capture_mods >> gvs[]
QED

(* The raw VV execution and the captured-length path must meet at the
   same target/source endpoint. Failure in the expression bypasses capture. *)
Theorem for_array_expr_capture_bind_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx e) (es,s,G,tn)
    (\H res ee Gu tu u. (?raw. res = INL raw) /\ P H res ee Gu tu u)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks raw em Gu tu u.
    (!tail. eval_expr cx e (es with gas_obs :=
      gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,em with gas_obs := tail)) /\
    storage_trace_domain cx st0 em.storage_trace /\
    (!H. valid_horizon cx st0 H em.storage_trace ==> P H (INL raw) em Gu tu u) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (array_iterator_results cx (expr_type e) raw) (em,u,Gu,tu) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_iterator cx (Array e)) (es,s,G,tn) Q R
Proof
  strip_tac >> simp[Once evaluate_def] >> irule gas_outcome_full_mods_bind_all >>
  conj_tac >- simp[storage_trace_frame_array_iterator_results] >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
     goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[]) >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee Gu tu u. (?raw. res = INL raw) /\ P H res ee Gu tu u` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  Cases_on `res` >> gvs[] >>
  first_x_assum irule >> simp[] >> qexists_tac `marks` >> first_assum ACCEPT_TAC
QED

(* Start the linked rounds at the reached capture. The loop-bound check
   is discharged by the selected route, not assumed for an arbitrary list. *)
Theorem for_array_round_bind_mods:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_admissible (eval_stmt cx (For id typ (Array e) n body)) ok es /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_iterator cx (Array e)) (es,s,G,tn)
    (\H res ee Gu tu u. ee.gas_obs = [] /\ ?vs. res = INL vs /\
         compatible_bound (Dynamic n) (LENGTH vs) /\ P H vs ee Gu tu u)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks vs em Gu tu u.
    (!tail. eval_iterator cx (Array e) (es with gas_obs :=
      gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL vs,em with gas_obs := tail)) /\
    storage_trace_domain cx st0 em.storage_trace /\
    (!H. valid_horizon cx st0 H em.storage_trace ==> P H vs em Gu tu u) /\
    compatible_bound (Dynamic n) (LENGTH vs) /\
    gas_admissible (eval_for cx tyv id body vs) ok em ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (eval_for cx tyv id body vs) (em,u,Gu,tu) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmt cx (For id typ (Array e) n body)) (es,s,G,tn) Q R
Proof
  strip_tac >>
  qabbrev_tac `next = \vs. ignore_bind
    (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
    (eval_for cx tyv id body vs)` >>
  `eval_stmt cx (For id typ (Array e) n body) =
     bind (eval_iterator cx (Array e)) next` by
    simp[Once evaluate_def,lift_option_type_def,bind_return,Abbr `next`] >>
  pop_assum SUBST_ALL_TAC >> irule gas_outcome_full_mods_bind_all >>
  conj_tac >-
    (simp[Abbr `next`] >> gen_tac >> irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_checks,evaluate_storage_trace_frame]) >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_mods_bind_results >>
     goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_results >> simp[]) >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee Gu tu u. ee.gas_obs = [] /\ ?vs. res = INL vs /\
         compatible_bound (Dynamic n) (LENGTH vs) /\ P H vs ee Gu tu u` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  `next vs = eval_for cx tyv id body vs` by
    simp[Abbr `next`,ignore_bind_def,check_def,FUN_EQ_THM,assert_def,bind_def,return_def] >>
  `gas_admissible (eval_for cx tyv id body vs) ok mid` by
    (drule_all gas_admissible_bind_tail >> simp[]) >>
  simp[] >> first_x_assum irule >> simp[] >>
  qexists_tac `marks` >> first_assum ACCEPT_TAC
QED

(* Loaded lengths must be taken from the reached operand, not from a new
   evaluation of e. The root/nested distinction does not affect this slice. *)
Theorem for_array_storage_dynamic_length_mods:
  vv_post_mods H ctx func c cx e es sa sb s0 ee
    (PlaceR (StoragePlace tr slot (ArrayTV et (Dynamic cap)))) vv s /\
  ptr_vv_ok cx (post_value_type c e)
    (PlaceR (StoragePlace tr slot (ArrayTV et (Dynamic cap)))) vv ee G tn s /\
  evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV et (Dynamic cap)) /\
  ~is_word_type (post_value_type c e) /\
  len = w2n (lookup_storage slot (get_storage cx ee tr)) /\
  compile_ptr_load c.ce_is_ctor c.ce_imm_alloca (slot_loc tr) (vv_operand vv) sb =
    (len_op,sc) /\ fn_has_code sb sc func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?out t G1 tn1.
    len_op = Var out /\ t = (update_var out (n2w len) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)) /\
    t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    ~t.vs_halted /\ eval_operand len_op t = SOME (n2w len) /\
    op_taint tn1 len_op = {} /\ op_prov G1 len_op = NONE /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. not_fresh_at sb x ==> x <> out) /\
    (!x. x <> out ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all_then strip_assume_tac for_array_slot_operand_mods >>
  irule for_storage_iterator_dynamic_length_run_uniform >> simp[] >>
  qexistsl [`p.ptr_operand`,`c.ce_is_ctor`,`c.ce_imm_alloca`,`slot`,`tr`] >>
  gvs[vv_operand_def]
QED

(* Capturing the list itself does not consume a gas observation. In the
   held routes use the read of the actual immutable or memory subplace. *)
Theorem for_array_nonslot_result_replay_mods:
  (!tr slot et bd. raw <> PlaceR (StoragePlace tr slot (ArrayTV et bd))) /\
  read_result cx raw em = (INL (ArrayV av),em) /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV et bd) /\
  vs = MAP Value (array_elements (ArrayTV et bd) av) ==>
  !tail. array_iterator_results cx ty raw (em with gas_obs := tail) =
    (INL vs,em with gas_obs := tail)
Proof
  strip_tac >> drule_then assume_tac read_result_gas_obs >>
  drule array_iterator_results_copy >>
  disch_then (fn th => simp[th,bind_def,lift_option_type_def,return_def,
       extract_elements_def])
QED

Theorem for_array_slot_result_replay_mods:
  compatible_bound bd len /\
  len = (case bd of Fixed n => n | Dynamic n =>
           w2n (lookup_storage slot (get_storage cx em tr))) /\
  vs = GENLIST (\i. PlaceR (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
     n2w (i * type_slot_size et)) et)) len ==>
  !tail. array_iterator_results cx ty (PlaceR (StoragePlace tr slot (ArrayTV et bd)))
     (em with gas_obs := tail) = (INL vs,em with gas_obs := tail)
Proof
  Cases_on `bd` >> strip_tac >> gvs[compatible_bound_def] >>
  simp[array_iterator_results_storage,result_array_length_def,bind_def,
       ignore_bind_def,check_def,assert_def,return_def,compatible_bound_def,
       vyperStorageBackendTheory.get_storage_backend_eq,get_storage_gas_obs]
QED

(* The checked length slice is a pure capture at this boundary. Its
   uniform endpoint is threaded, unchanged, into the round invariant. *)
Theorem for_array_capture_outcome_mods:
  ~u.vs_halted /\ compatible_bound (Dynamic n) (LENGTH vs) /\
  (!tail. array_iterator_results cx (expr_type e) raw (em with gas_obs := tail) =
    (INL vs,em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz) /\
    P H vs (em with gas_obs := []) Gz tz z) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (array_iterator_results cx (expr_type e) raw) (em,u,Gu,tu)
    (\H res ee G tn t. ee.gas_obs = [] /\ ?vs. res = INL vs /\
       compatible_bound (Dynamic n) (LENGTH vs) /\ P H vs ee G tn t) R
Proof
  strip_tac >> irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`Gz`,`em`,`INL vs`,`z`,`tz`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* The array route has two continuation interfaces: install the captured
   operand on its checked length path, and run the loop from that endpoint. *)
Theorem for_array_outcome_from_capture_mods:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_admissible (eval_stmt cx (For id typ (Array e) n body)) ok es /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_expr cx e) (es,s,G,tn)
    (\H res ee Gu tu u. (?raw. res = INL raw) /\ P H res ee Gu tu u)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks raw em Gu tu u.
    (!tail. eval_expr cx e (es with gas_obs :=
      gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,em with gas_obs := tail)) /\
    storage_trace_domain cx st0 em.storage_trace /\
    (!H. valid_horizon cx st0 H em.storage_trace ==> P H (INL raw) em Gu tu u) ==>
    ~u.vs_halted /\ ?vs z Gz tz.
      compatible_bound (Dynamic n) (LENGTH vs) /\
      (!tail. array_iterator_results cx (expr_type e) raw (em with gas_obs := tail) =
        (INL vs,em with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H em.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz) /\
        Entry H vs (em with gas_obs := []) Gz tz z)) /\
  (!marks vs em Gu tu u.
    (!tail. eval_iterator cx (Array e) (es with gas_obs :=
      gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL vs,em with gas_obs := tail)) /\
    storage_trace_domain cx st0 em.storage_trace /\
    (!H. valid_horizon cx st0 H em.storage_trace ==> Entry H vs em Gu tu u) /\
    compatible_bound (Dynamic n) (LENGTH vs) /\
    gas_admissible (eval_for cx tyv id body vs) ok em ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (eval_for cx tyv id body vs) (em,u,Gu,tu) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmt cx (For id typ (Array e) n body)) (es,s,G,tn) Q R
Proof
  strip_tac >> irule for_array_round_bind_mods >> simp[] >>
  qexistsl [`Entry`,`ok`] >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  irule for_array_expr_capture_bind_mods >> qexists_tac `P` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!marks raw em Gu tu u. _` (drule_all_then strip_assume_tac) >>
  irule for_array_capture_outcome_mods >> simp[] >>
  qexistsl [`Gz`,`tz`,`z`] >> simp[]
QED
