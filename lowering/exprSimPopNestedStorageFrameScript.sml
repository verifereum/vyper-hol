(*
 * Pop on a nested storage target whose indices leave storage alone
 * (storage_frame_expr): pop_nested_storage_frame_sim.  Such indices may
 * have other effects (a pop on a memory local, msg.gas), but every state
 * the target's evaluation passes through has the start's storage, so the
 * place it returns is live and in range there, as with pure indices
 * (exprSimPopNestedBase.pop_nested_storage_pure_sim).
 *)

Theory exprSimPopNestedStorageFrame
Ancestors
  exprSimPopNestedBase
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHypsDefs exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases targetPlaceLive vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance vyperStorageLayoutSafety
  vyperPlaceFrames vyperStatePreservation
  exprSimHash fragGasSeqAbort gasSummary exprSimVVFrame
  gasOutcome gasExemptCert gasSummaryCompose fragGasMode fragGasPath

(* Evaluating e, from any state, leaves both of the running contract's
   storage backends (storage and transient) alone. *)
Definition storage_frame_expr_def:
  storage_frame_expr cx e <=>
    !st res st' b. eval_expr cx e st = (res,st') ==>
      vyperStorageBackend$get_storage cx st' b =
      vyperStorageBackend$get_storage cx st b
End

Theorem storage_frame_expr_pure:
  pure_expr e ==> storage_frame_expr cx e
Proof
  rw[storage_frame_expr_def] >> metis_tac[eval_expr_preserves_state]
QED

Theorem nested_pop_result_slots_storage_frame:
  (!b. vyperStorageBackend$get_storage cx st' b =
       vyperStorageBackend$get_storage cx st b) ==>
  nested_pop_result_slots cx st' pv = nested_pop_result_slots cx st pv
Proof
  strip_tac >> Cases_on `pv` >> simp[nested_pop_result_slots_def] >>
  Cases_on `p` >>
  simp[nested_pop_result_slots_def, vyperStorageBackendTheory.get_storage_backend_eq]
QED

Theorem nested_pop_result_live_storage_frame:
  (!b. vyperStorageBackend$get_storage cx st' b =
       vyperStorageBackend$get_storage cx st b) ==>
  nested_pop_result_live cx st' pv = nested_pop_result_live cx st pv
Proof
  strip_tac >> Cases_on `pv` >> simp[nested_pop_result_live_def] >>
  Cases_on `p` >>
  simp[nested_pop_result_live_def, vyperStorageBackendTheory.get_storage_backend_eq]
QED

(* Along the target's evaluation: storage stays the start's, and the
   place found is in range and live in it. *)
Theorem nested_pop_eval_base_storage_frame:
  !bt cx st res st'.
    EVERY (storage_frame_expr cx) (target_indices bt) /\
    eval_base_place cx bt st = (res,st') ==>
    (!b. vyperStorageBackend$get_storage cx st' b =
         vyperStorageBackend$get_storage cx st b) /\
    (!pv. contract_storage_well_formed cx st /\ res = INL pv ==>
          nested_pop_result_slots cx st pv /\ nested_pop_result_live cx st pv)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def] >> strip_tac >>
      drule lookup_global_state >> strip_tac >> gvs[] >>
      metis_tac[nested_pop_lookup_global_slots, nested_pop_lookup_global_live])
  >~ [`eval_base_place cx (NameTarget nm) st`]
  >- (simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def] >>
      rpt strip_tac >> gvs[nested_pop_result_slots_def, nested_pop_result_live_def])
  >~ [`eval_base_place cx (AttributeTarget t fld) st`]
  >- (simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      qpat_x_assum `!y. _` (qspec_then `t` mp_tac) >>
      simp[expr_size_def] >> disch_then drule_all >> strip_tac >>
      drule extend_place_state >> strip_tac >> gvs[] >>
      metis_tac[nested_pop_extend_result_slots, nested_pop_extend_result_live,
                contract_storage_well_formed_storage_frame,
                nested_pop_result_slots_storage_frame,
                nested_pop_result_live_storage_frame]) >>
  rename1 `SubscriptTarget t e` >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `t` mp_tac) >>
  simp[expr_size_def] >> disch_then drule_all >> strip_tac >>
  rename1 `eval_expr cx e st1 = (_,st2)` >>
  `!b. vyperStorageBackend$get_storage cx st2 b =
       vyperStorageBackend$get_storage cx st b` by
    metis_tac[storage_frame_expr_def] >>
  gvs[] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  drule extend_place_state >> strip_tac >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac `extend_place cx pv (ValueSubscript _) s2 = _` >>
  `contract_storage_well_formed cx s2` by
    (irule contract_storage_well_formed_storage_frame >>
     qexists `st` >> simp[]) >>
  `nested_pop_result_slots cx s2 pv /\ nested_pop_result_live cx s2 pv` by
    metis_tac[nested_pop_result_slots_storage_frame,
              nested_pop_result_live_storage_frame] >>
  `nested_pop_result_slots cx s2 pv' /\ nested_pop_result_live cx s2 pv'` by
    metis_tac[nested_pop_extend_result_slots, nested_pop_extend_result_live] >>
  metis_tac[nested_pop_result_slots_storage_frame,
            nested_pop_result_live_storage_frame]
QED

Theorem nested_pop_eval_target_storage_frame:
  contract_storage_well_formed cx st /\
  EVERY (storage_frame_expr cx) (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') ==>
  (!b. vyperStorageBackend$get_storage cx st' b =
       vyperStorageBackend$get_storage cx st b) /\
  slots_in_range (vyperStorageBackend$get_storage cx st' tr) (w2n slot) tv /\
  storage_read_live cx tr (vyperStorageBackend$get_storage cx st' tr) slot tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all nested_pop_eval_base_storage_frame >> strip_tac >>
  first_x_assum drule >>
  simp[nested_pop_result_slots_def, nested_pop_result_live_def,
       vyperStorageBackendTheory.get_storage_backend_eq]
QED

(* The suffix of nested_pop_storage_suffix_sim (exprSimPopNestedBase),
   from the facts its proof draws from pure indices: the target's place is
   a storage region (storage_place_region), in range (slots_in_range) and
   live (storage_read_live) in the storage at the target's end. *)
Theorem nested_pop_storage_live_suffix_sim:
  storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) /\
  slots_in_range (vyperStorageBackend$get_storage cx es tr) (w2n slot)
    (ArrayTV tv (Dynamic n)) /\
  storage_read_live cx tr (vyperStorageBackend$get_storage cx es tr) slot
    (ArrayTV tv (Dynamic n)) /\
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n))))
    (Type (ArrayT ann (Dynamic n))) (hdr,SOME (slot_loc tr),pt) t /\
  compile_dynarray_pop hdr 1 (type_slot_size tv) cenv.ce_is_ctor
    cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sm = (q,r) /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) es = (res,es') /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm /\ es.gas_obs = [] /\
  fn_has_code sm r func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))) (es,t)
    (\res fin u. ?v. res = INL v /\ vv_post ctx func cenv cx (Pop ann bt) es0 sa r s0 fin v
      (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) u /\
      u.vs_current_bb = r.cs_current_bb /\ u.vs_inst_idx = LENGTH r.cs_current_insts)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `!tail. pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
       (es with gas_obs := tail) = (res,es' with gas_obs := tail)` by
    metis_tac[nested_pop_storage_gas_obs] >>
  `stmt_state_rel ctx func cenv cx es t` by fs[target_post_def] >>
  `~cx.txn.is_static /\ ~t.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  drule_all nested_pop_storage_natural_region >> strip_tac >>
  drule_all nested_pop_live_array_agree >> strip_tac >>
  drule nested_pop_array_header_load >> strip_tac >>
  qpat_x_assum `storage_layout_safe _` kall_tac >>
  qpat_x_assum `storage_place_region _ _` kall_tac >>
  qpat_x_assum `storage_read_live _ _ _ _ _` kall_tac >>
  qpat_x_assum `pop_place _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss())
      [pop_place_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, ignore_bind_def, check_def, assert_def, return_def, raise_def,
       vyperStorageBackendTheory.write_storage_slot_eq,
       vyperStorageTheory.encode_value_def, vyperStorageTheory.encode_base_to_slot_def,
       integer_wordTheory.i2w_def]) >>
  Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx es tr) = 0w`
  >- (simp[assert_def, bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
      drule nested_pop_suffix_shape >> strip_tac >> suspend "empty") >>
  `0 < w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr))` by
    (Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx es tr)` >> gvs[]) >>
  simp[] >> strip_tac >> gvs[] >>
  drule nested_pop_suffix_shape >> strip_tac >> suspend "positive"
QED

Resume nested_pop_storage_live_suffix_sim[empty]:
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (fs[] >> metis_tac[]) >>
  drule_all nested_pop_suffix_empty >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  `?j. gas_marked_path F ctx func t 0 (Abort a (s' with vs_inst_idx := j))` by
    (irule nested_pop_suffix_abort_path >> simp[] >> metis_tac[]) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "pop empty storage array"))`, `es`,
    `Abort a (s' with vs_inst_idx := j)`] >>
  simp[expr_exit_def, exit_result_def] >>
  qpat_x_assum `!tail. pop_place _ _ _ = _`
    (mp_tac o REWRITE_RULE [pop_place_def, check_def, ignore_bind_def]) >>
  simp[]
QED

Resume nested_pop_storage_live_suffix_sim[positive]:
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (fs[] >> metis_tac[]) >>
  ` (if tr then tload (root + n2w delta) t else sload (root + n2w delta) t) <> 0w` by
    metis_tac[] >>
  drule_all nested_pop_suffix_run >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  qpat_x_assum `ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0]` kall_tac >>
  qpat_x_assum `ALL_DISTINCT [x0; x1; x2; x3; x4; x5; x6]` kall_tac >>
  qmatch_asmsub_abbrev_tac `eval_operand hdr t = SOME slot` >>
  qmatch_asmsub_abbrev_tac `0 < w2n lenw` >>
  `lenw - 1w = n2w (w2n lenw - 1)` by
    (simp[wordsTheory.n2w_sub]) >>
  `u = (if tr then tstore slot (n2w (w2n lenw - 1)) t
         else sstore slot (n2w (w2n lenw - 1)) t) with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q t` by
    (fs[ci_mono_def, not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> fs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `stmt_state_rel ctx func cenv cx
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes slot [(0,n2w (w2n lenw - 1))]
        (vyperStorageBackend$get_storage cx es tr))) u` by
    (`w2n slot = w2n root + delta` by simp[arithmeticTheory.ADD_COMM] >>
     qunabbrev_tac `lenw` >> drule_all nested_pop_updated_state_rel >> simp[]) >>
  qmatch_asmsub_abbrev_tac
    `stmt_state_rel ctx func cenv cx fin u` >>
  `storage_holds cx tr ann
    (PlaceR (StoragePlace tr (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) tv))
    (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) fin u` by
    (qunabbrev_tac `fin` >> qunabbrev_tac `lenw` >>
     irule nested_pop_positive_holds >>
     rpt conj_tac >- first_assum ACCEPT_TAC >- REFL_TAC >- REFL_TAC
     >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`n`, `t`] >> rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qpat_assum `w2n slot = _` (fn th => REWRITE_TAC [th]) >>
         first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `u = _ with vs_vars := _` (fn th => ONCE_REWRITE_TAC [th]) >>
     Cases_on `tr` >>
     simp_tac (srw_ss()) [NoAsms, sstore_def, tstore_def, LET_THM]) >>
  qpat_x_assum `u = _ with vs_vars := _` kall_tac >>
  qpat_x_assum `u = _ with vs_vars := _` kall_tac >>
  `lookup_var x6 u =
     SOME (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv))` by
    (qpat_x_assum `lookup_var x6 u = _` mp_tac >>
     qpat_x_assum `(if tr then tload _ _ else sload _ _) = _`
       (fn th => REWRITE_TAC [th]) >>
     qpat_x_assum `lenw - 1w = _` (fn th => REWRITE_TAC [th]) >>
     simp_tac (srw_ss()) [NoAsms, wordsTheory.word_mul_n2w,
       GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC]) >>
  `!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q t` by
    (rpt strip_tac >> qpat_assum `!x. ~MEM x _ ==> _` irule >>
     fs[] >> rpt strip_tac >> gvs[]) >>
  `fin with gas_obs := [] = fin` by
    (qunabbrev_tac `fin` >> Cases_on `tr` >>
     simp[vyperStorageBackendTheory.set_storage_def,
          evaluation_state_component_equality]) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `sb` |-> `r`, `s` |-> `t`, `t` |-> `u`,
                  `id` |-> `sm.cs_next_id`, `esz` |-> `type_slot_size tv`,
                  `code` |-> `nested_pop_suffix hdr tr sm.cs_next_id
                     (type_slot_size tv) x0 x1 x2 x3 x4 x5 x6`]
          nested_pop_suffix_path) >>
  impl_tac >- simp[] >> strip_tac >>
  `res = INL (PlaceR (StoragePlace tr
            (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) tv)) /\
   es' = fin` by
    (qpat_x_assum `_ es = (res,es')` mp_tac >>
     simp[Abbr `fin`, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
          vyperStateTheory.assert_def, vyperStateTheory.return_def,
          vyperStorageBackendTheory.write_storage_slot_eq,
          vyperStorageTheory.encode_value_def,
          vyperStorageTheory.encode_base_to_slot_def,
          integer_wordTheory.i2w_def] >>
     strip_tac >> gvs[] >>
     simp[arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM]) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`res`, `es'`,
    `OK (u with vs_inst_idx := LENGTH r.cs_current_insts)`] >>
  simp[exprSimVVFrameTheory.vv_post_inst_idx] >>
  irule nested_pop_suffix_vv_post >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  qpat_x_assum `storage_holds _ _ _ _ _ fin u` mp_tac >> simp[]
QED

Finalise nested_pop_storage_live_suffix_sim

(* pop_nested_storage_pure_sim's proof, with the target's end state no
   longer the start: storage_frame_expr indices give it the start's
   storage, so the place is in range and live there
   (nested_pop_eval_target_storage_frame), which is all the suffix needs
   (nested_pop_storage_live_suffix_sim). *)
Theorem pop_nested_storage_frame_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    EVERY (storage_frame_expr cx) (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Pop ann bt)` by
    fs[expr_body_pre_def] >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    fs[well_typed_expr_def] >>
  pop_assum strip_assume_tac >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  PairCases_on `q` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr _ _ _ _ = ((hdr,loc,pt),sm)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  Cases_on
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `!h w e c i l s. ci_mono s (SND (compile_dynarray_pop h w e c i l s))` by
    simp[ci_mono_compile_dynarray_pop] >>
  `ci_mono sm r` by metis_tac[pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm r func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    metis_tac[nested_pop_target_admissible] >>
  qpat_x_assum `pop_target_frag _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [pop_target_frag_def]) >>
  disch_then (qspecl_then [`ArrayT ann (Dynamic n)`, `sa`, `sm`,
                           `(hdr,loc,pt)`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  `eval_expr cx (Pop ann bt) = vyperState$bind (eval_target_place cx bt) (pop_place cx)` by
    simp[FUN_EQ_THM, Once evaluate_def, vyperStateTheory.bind_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> suspend "summary") >>
  disj2_tac >> rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_place)
QED

Resume pop_nested_storage_frame_sim[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`tres`, `tend`, `tr0`] strip_assume_tac) >>
  gvs[]
  >- suspend "normal" >>
  Cases_on `tres` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR exc) tr0` >>
  qexistsl_tac [`INR exc`, `tend`, `tr0`] >> simp[] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  qpat_x_assum `expr_exit (INR exc) tr0` mp_tac >>
  Cases_on `tr0` >> simp[expr_exit_def] >>
  Cases_on `exc` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Resume pop_nested_storage_frame_sim[normal]:
  rename1 `target_post _ _ _ _ _ _ _ _ _ (PlaceR p) _ _ t` >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p, tend with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx es` by
    fs[expr_sim_inv_def] >>
  `contract_storage_well_formed cx
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    (irule contract_storage_well_formed_storage_frame >>
     qexists `es` >> simp[] >> Cases >>
     simp[vyperStorageBackendTheory.get_storage_def]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  drule_all nested_pop_eval_target_storage_class >> strip_tac >> gvs[] >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  drule_all nested_pop_eval_target_storage_frame >> strip_tac >>
  drule eval_target_place_region >> strip_tac >>
  drule_all pop_storage_element_size >>
  disch_then (qspec_then `tr` assume_tac) >>
  fs[GSYM slot_loc_def] >>
  `ws = 1` by
    (Cases_on `tr` >> fs[Abbr `ws`, Abbr `lc`, slot_loc_def, word_scale_def]) >>
  qunabbrev_tac `lc` >> qunabbrev_tac `ws` >>
  gvs[Abbr `esz`] >>
  simp[slot_loc_def] >>
  rename1 `evaluate_type (get_tenv cx) ann = SOME tv` >>
  Cases_on `pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
              (tend with gas_obs := [])` >>
  rename1 `_ = (pres, pend)` >>
  mp_tac (Q.INST [`es` |-> `tend with gas_obs := []`, `es0` |-> `es`,
                  `res` |-> `pres`, `es'` |-> `pend`,
                  `pt` |-> `SOME (ValPT (ArrayT ann (Dynamic n)))`]
          nested_pop_storage_live_suffix_sim) >>
  impl_tac >- fs[slot_loc_def] >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`pres'`, `pend'`, `pr`]
                (CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`pres'`, `pend'`, `pr`] >>
  conj_tac
  >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
             |> REWRITE_RULE [APPEND_NIL]) >>
      qpat_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _`
        (irule_at Any) >>
      asm_rewrite_tac[]) >>
  gvs[]
QED

Finalise pop_nested_storage_frame_sim
