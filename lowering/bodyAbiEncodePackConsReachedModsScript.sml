(* Transport the selected positional row at the reached suffix endpoint. *)
Theory bodyAbiEncodePackConsReachedMods
Ancestors
  bodyAbiEncodeConsPackedPostMods bodyAbiEncodeSuffixRowMods
  bodyAbiEncodeSuffixCodeRowMods bodyAbiEncodePosHeadPostMods
  bodyAbiEncodeSuffixObservationsMods bodyAbiEncodeRuntimeSuffixReadMods
  bodyExtNoncopyReachedFrameMods bodyCallSupport vyperStorageBackend
  exprSimWordArgs bodyFullPostsMods loweringPosts vyperTypeContract
  bodyAbiEncodePackedPostMods bodyFullPredsMods vyperState exprLowering bodyPtrDefs
  vyperInterpreter list venomState context vyperTypeCallGraph

Theorem abi_encode_suffix_call_keys_mods:
  !pre. EVERY P (int_calls_exprs (pre ++ e::xs)) ==> EVERY P (int_calls_exprs xs)
Proof
  Induct >> simp[int_calls_expr_def, EVERY_APPEND]
QED

Triviality pack_code_observation:
  ee.immutables = mid.immutables /\
  abi_encode_saved_row_mods lo ce cx sa ss e (LocatedValue ty p) v si sm ss vv copy H mid Gm tm m /\
  ty = lowered_value_type ce e /\ p.ptr_location = LocCode /\
  eval_operand p.ptr_operand m = SOME w ==>
  immutable_holds_mods ce cx ty (Value v) w ee t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `?raw. read_result cx raw mid = _ /\ _`
    (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_x_assum `vv_holds_mods` mp_tac >>
  simp[vv_holds_mods_def] >>
  simp[immutable_holds_mods_def, immutable_holds_def, read_result_def, return_def] >>
  metis_tac[]
QED

Triviality pack_slot_geometry:
  abi_encode_saved_row_mods lo ce cx sa ss e (LocatedValue ty p) v si sm ss vv copy H mid Gm tm m /\
  ty = lowered_value_type ce e /\ p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand m = SOME w /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
  storage_read_live H tr (get_storage cx mid tr) w tv /\
  slots_in_range (get_storage cx mid tr) (w2n w) tv
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `?raw. read_result cx raw mid = _ /\ _`
    (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `tr` >>
  gvs[vv_storage_live_def, slot_loc_def, vv_holds_mods_def, vv_holds_def, storage_holds_def]
QED

Triviality pack_suffix_nil:
  eval_exprs cx [] (mid with gas_obs := obs) = (INL vs,ee with gas_obs := []) /\
  mid.gas_obs = [] /\ ee.gas_obs = [] ==> ee = mid
Proof
  simp[eval_exprs_nil, evaluation_state_component_equality]
QED

Triviality pack_suffix_noncopy:
  contract_inv mods exps ctx ce cx /\
  (cx.in_deploy ==> exports_ok cx.layouts cx.txn.target mods exps /\
                   IS_SOME (check_contract F cx.layouts cx.txn.target mods)) /\
  body_const_cells_agree_mods mods cx env mid /\
  EVERY (source_body_call_supported cx) (int_calls_exprs xs) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs xs) /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := []) /\
  mid.gas_obs = [] /\ ee.gas_obs = [] /\ ~exprs_can_mutate ce xs ==>
  ee.immutables = mid.immutables /\ (!tr. get_storage cx ee tr = get_storage cx mid tr)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `xs` >- (drule_all pack_suffix_nil >> simp[]) >>
  qhdtm_x_assum `body_const_cells_agree_mods`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  Cases_on `cx.in_deploy`
  >- (qpat_assum `cx.in_deploy ==> _` (drule_then strip_assume_tac) >>
      drule_all_then strip_assume_tac ext_noncopy_reached_suffix_frame_mods >>
      `ee with gas_obs := [] = ee` by
        (qpat_assum `ee.gas_obs = []` (once_rewrite_tac o single o SYM) >> simp[]) >>
      gvs[]) >>
  irule abi_encode_runtime_suffix_observations_mods >>
  qpat_assum `eval_exprs _ _ _ = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `check_contract _ _ _ _ = SOME _` (irule_at Any) >> simp[]
QED

Triviality pack_suffix_slot_read:
  contract_inv mods exps ctx ce cx /\ body_const_cells_agree_mods mods cx env mid /\
  EVERY (source_body_call_supported cx) (int_calls_exprs xs) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs xs) /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := []) /\
  mid.gas_obs = [] /\ ee.gas_obs = [] /\ ~exprs_can_mutate ce xs /\
  (cx.in_deploy /\ xs <> [] ==> read_storage_slot cx tr w tv ee = (INL v,ee)) /\
  read_storage_slot cx tr w tv mid = (INL v,mid) ==>
  read_storage_slot cx tr w tv ee = (INL v,ee)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `xs` >- (drule_all pack_suffix_nil >> simp[]) >>
  Cases_on `cx.in_deploy` >- fs[] >>
  qhdtm_x_assum `body_const_cells_agree_mods`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
  irule abi_encode_runtime_suffix_read_mods >>
  qpat_assum `eval_exprs _ _ _ = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `check_contract _ _ _ _ = SOME _` (irule_at Any) >> simp[]
QED

Theorem abi_encode_pack_cons_reached_mods:
  contract_inv mods exps ctx ce cx /\ dead_lo_ok_mods H (DF H) lo ce cx /\
  (cx.in_deploy ==> exports_ok cx.layouts cx.txn.target mods exps /\
                   IS_SOME (check_contract F cx.layouts cx.txn.target mods)) /\
  EVERY (source_body_call_supported cx) (int_calls_exprs xs) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs xs) /\
  ci_mono sa ss /\ ci_mono ss sb /\ local_ptrs_reserved ce sa /\
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx func ce cx es s0 /\
  compile_abi_encode_args compile_expr ce xs ss = (svs,sb) /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := []) /\
  mid.gas_obs = [] /\ ee.gas_obs = [] /\ u.vs_labels = m.vs_labels /\
  abi_encode_pos_head_post_mods mods DF lo d ctx func ce cx env
    e sa sm ss vv sv (exprs_can_mutate ce xs) es s0 G0 tn0 H (INL v) mid Gm tm m /\
  abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
    xs svs ss sb mid m Gm tm H (INL vs : value list + exception) ee G tn u /\
  (!p tr w tv. cx.in_deploy /\ xs <> [] /\ ~exprs_can_mutate ce xs /\
       ~is_word_type (lowered_value_type ce e) /\ sv = LocatedValue (lowered_value_type ce e) p /\
       p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand m = SOME w /\
       evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
       read_storage_slot cx tr w tv mid = (INL v,mid) ==>
       read_storage_slot cx tr w tv ee = (INL v,ee)) ==>
  abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
    (e::xs) (sv::svs) sa sb es s0 G0 tn0 H (INL (v::vs) : value list + exception) ee G tn u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_encode_pos_head_post_mods`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_pos_head_post_mods_def]) >>
  qpat_assum `abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ [e] _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_packed_post_mods_def]) >>
  `~exprs_can_mutate ce xs ==>
    ee.immutables = mid.immutables /\ (!tr. get_storage cx ee tr = get_storage cx mid tr)` by
    (strip_tac >> irule pack_suffix_noncopy >>
     qpat_assum `eval_exprs _ _ _ = _` (irule_at Any) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `body_const_cells_agree_mods _ _ _ mid` (irule_at Any) >> simp[]) >>
  `abi_encode_saved_row_mods lo ce cx sa sb e sv v sa sm ss vv
      (exprs_can_mutate ce xs) H ee G tn u` by suspend "row" >>
  irule (INST_TYPE [beta |-> ``:exception``, gamma |-> ``:exception``,
                    ``:'d`` |-> ``:exception``] abi_encode_cons_packed_post_mods) >>
  simp[] >>
  conj_tac >- (qexistsl_tac [`exprs_can_mutate ce xs`,`sa`,`sm`,`ss`,`vv`] >> simp[]) >>
  qexistsl_tac [`Gm`,`mid`,`m`,`ss`,`tm`] >> simp[]
QED

Resume abi_encode_pack_cons_reached_mods[row]:
  Cases_on `~exprs_can_mutate ce xs /\ vv_location sv = SOME LocCode`
  >- suspend "code" >>
  suspend "other"
QED

Resume abi_encode_pack_cons_reached_mods[code]:
  Cases_on `sv` >> gvs[vv_location_def] >>
  rename1 `abi_encode_saved_row_mods _ _ _ _ _ _ (LocatedValue ty p) _ _ _ _ _ _ _ _ _ _ _` >>
  `ty = lowered_value_type ce e` by
    (qhdtm_assum `abi_encode_saved_row_mods`
       (mp_tac o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     simp[] >> strip_tac >> fs[]) >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  irule (INST_TYPE [beta |-> ``:exception``] abi_encode_suffix_code_row_mods) >>
  qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ sa sm ss vv _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ xs _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  qpat_assum `compile_abi_encode_args _ _ xs _ = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> irule (INST_TYPE [alpha |-> ``:256``] pack_code_observation) >>
  qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ sa sm ss vv _ _ _ _ _ _` (irule_at Any) >>
  simp[]
QED

Resume abi_encode_pack_cons_reached_mods[other]:
  irule (INST_TYPE [alpha |-> ``:exception``] abi_encode_suffix_row_mods) >>
  qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ sa sm ss vv _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ xs _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  qpat_assum `eval_exprs _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_abi_encode_args _ _ xs _ = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (qpat_x_assum `sv = LocatedValue _ _` SUBST_ALL_TAC >>
      irule pack_slot_geometry >>
      qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ sa sm ss vv _ _ _ _ _ _`
        (irule_at Any) >> simp[]) >>
  irule pack_suffix_slot_read >>
  qpat_assum `eval_exprs _ _ _ = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree_mods _ _ _ mid` (irule_at Any) >>
  simp[]
QED

Finalise abi_encode_pack_cons_reached_mods
