Theory targetPurePostTransport
Ancestors
  valueEncodingDefs
  loweringStateRelDefs
  loweringPosts exprSimSubscriptArrayFrame exprBopSimProps compileEnv
  context arithmetic valueEncodingProofs valueEncoding targetPureSourceFrame
  exprSimMemorySource vyperState vyperStorageBackend
  exprSimWordArgs accountsRelProps

Theorem target_saved_value_region_frame:
  wb_frame cenv es es sm s u /\
  local_ptrs_reserved cenv sm /\
  local_ptrs_rel func cenv es.scopes s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\
  sm.cs_next_id <= sb.cs_next_id ==>
  (vv_at cenv cx ty sa sm es r vv s ==>
   vv_at cenv cx ty sa sb es r vv u) /\
  (vv_own cenv cx ty sa sm es r vv s ==>
   vv_own cenv cx ty sa sb es r vv u)
Proof
  strip_tac >>
  `!n b sz. local_region cenv es.scopes u n b sz <=>
            local_region cenv es.scopes s n b sz` by
    metis_tac[local_region_wb_frame] >>
  `!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) u = SOME w` by
    (rpt strip_tac >> irule eval_operand_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`sm`, `s`] >>
     fs[wb_frame_def]) >>
  Cases_on `vv` >>
  gvs[vv_at_def, vv_own_def, expr_val_at_def, expr_val_own_def, vv_operand_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  fs[wb_frame_def] >> simp[SF SFY_ss] >>
  disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> gvs[]
QED

Theorem target_saved_storage_oracles:
  read_storage_slot cx tr w tv (es with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) =
    (INL v, es with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) <=>
  read_storage_slot cx tr w tv es = (INL v,es)
Proof
  Cases_on `tr` >> simp[read_storage_slot_def, get_storage_backend_eq, bind_def,
       get_storage_def, lift_option_def] >>
  CASE_TAC >> simp[return_def, raise_def]
QED


Theorem target_saved_read_oracles:
  read_result cx r (es with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) =
    (INL v, es with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) <=>
  read_result cx r es = (INL v,es)
Proof
  Cases_on `r` >> simp[read_result_def, return_def, raise_def] >>
  rename1 `read_place cx p` >> Cases_on `p` >> simp[read_place_def]
  >~ [`read_storage_slot cx tr`]
  >- (Cases_on `tr` >>
      simp[vyperStorageBackendTheory.read_storage_slot_eq, get_storage_def] >>
      rpt CASE_TAC >> simp[]) >>
  simp[get_scopes_def, get_immutables_def, get_address_immutables_def,
       bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
       vyperMiscTheory.prod_CASE_rator, AllCaseEqs()] >>
  metis_tac[]
QED
Theorem target_saved_value_region_bytes:
  vv_at cenv cx ty sa sm es r (LocatedValue carried_ty p) s /\
  p.ptr_location = LocMemory /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  wb_frame cenv es es sm s u ==>
  mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[]
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (gvs[wb_frame_def, locals_kept_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem target_saved_regions_oracles:
  (vv_at cenv cx ty sa sb (es with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) r vv s <=>
   vv_at cenv cx ty sa sb es r vv s) /\
  (vv_own cenv cx ty sa sb (es with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) r vv s <=>
   vv_own cenv cx ty sa sb es r vv s) /\
  (vv_storage_live cx vv (es with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) s <=>
   vv_storage_live cx vv es s)
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_own_def, target_saved_read_oracles,
       expr_val_at_def, expr_val_own_def, vyperStorageBackendTheory.get_storage_def]
QED

Theorem target_saved_holds_oracles:
  vv_holds cenv cx ty r vv (es with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) s <=>
  vv_holds cenv cx ty r vv es s
Proof
  Cases_on `vv` >>
  simp[vv_holds_def, target_saved_read_oracles] >>
  Cases_on `p.ptr_location` >>
  simp[storage_holds_def, immutable_holds_def,
       target_saved_read_oracles, target_saved_storage_oracles,
       get_storage_def] >>
  simp[SRULE [] target_saved_read_oracles,
       SRULE [] target_saved_storage_oracles]
QED

Theorem target_saved_stack_value_frame:
  expr_val_rel cx ty v op s /\ expr_val_at cenv cx ty sa sm es v op s /\
  wb_frame cenv es es sm s u /\
  (!w. eval_operand op s = SOME w ==> eval_operand op u = SOME w) ==>
  expr_val_rel cx ty v op u
Proof
  strip_tac >> gvs[expr_val_rel_def] >>
  rpt strip_tac >>
  Cases_on `is_word_type ty` >- gvs[] >> simp[] >>
  `val_in_memory tv v (w2n w) s.vs_memory` by metis_tac[] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  irule exprSimPropsTheory.val_in_memory_footprint_agree >>
  simp[] >> qexists_tac `s.vs_memory` >> simp[] >>
  gvs[wb_frame_def, locals_kept_def]
  >- (`mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_x_assum `!aid off sz. FLOOKUP _ aid = SOME (off,sz) /\ _ ==> _` irule >>
         metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (`mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED


Theorem target_saved_word_footprint:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_footprint tv v = 32
Proof
  Cases_on `v` >> Cases_on `ty` >>
  simp[is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), is_word_type_def,
    val_footprint_def, type_memory_size_def]
QED

Theorem target_saved_memory_value_frame:
  vv_at cenv cx ty sa sm es r (LocatedValue ct p) s /\
  p.ptr_location = LocMemory /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  (is_word_type ty ==> mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tv v) /\
  wb_frame cenv es es sm s u ==>
  val_in_memory tv v (w2n w) u.vs_memory /\
  (is_word_type ty ==> mem_word_at (w2n w) u.vs_memory = typed_val_to_w256 tv v)
Proof
  strip_tac >>
  `mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
    (irule target_saved_value_region_bytes >> metis_tac[]) >>
  `val_wf tv v` by (gvs[vv_at_def] >> metis_tac[]) >>
  conj_tac
  >- (irule exprSimPropsTheory.val_in_memory_footprint_agree >>
      simp[] >> qexists_tac `s.vs_memory` >> simp[]) >>
  strip_tac >> drule_all target_saved_word_footprint >> strip_tac >>
  gvs[mem_word_at_def, mem_bytes_at_def]
QED

Theorem target_saved_holds_frame:
  vv_holds cenv cx ty r vv es s /\ vv_at cenv cx ty sa sm es r vv s /\
  wb_frame cenv es es sm s u /\
  (!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) u = SOME w) /\
  vv_storage_live cx vv es s /\
  storage_rel cx cx.txn.target es u /\
  transient_rel cx cx.txn.target es u ==>
  vv_holds cenv cx ty r vv es u
Proof
  Cases_on `vv`
  >- (simp[vv_holds_def, vv_at_def, vv_operand_def] >> rpt strip_tac >>
      qexists_tac `v` >> simp[] >> irule target_saved_stack_value_frame >>
      metis_tac[]) >>
  simp[vv_holds_def, vv_operand_def] >> strip_tac >> simp[] >>
  qexists_tac `w` >> simp[] >>
  Cases_on `p.ptr_location` >> gvs[]
  >- (rpt gen_tac >> disch_tac >>
      irule target_saved_memory_value_frame >> metis_tac[])
  >- (gvs[storage_holds_def] >>
      irule storage_range_agree_of_live >>
      conj_tac >- gvs[storage_range_agree_def] >>
      qexistsl_tac [`cx`, `F`] >>
      gvs[storage_rel_def, get_storage_def, vfmStateTheory.lookup_account_def])
  >- (gvs[storage_holds_def] >>
      irule storage_range_agree_of_live >>
      conj_tac >- gvs[storage_range_agree_def] >>
      qexistsl_tac [`cx`, `T`] >>
      gvs[transient_rel_def, get_storage_def])
  >- (gvs[vv_location_def, immutable_holds_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  irule target_saved_memory_value_frame >> metis_tac[]
QED

Theorem target_saved_storage_live_frame:
  vv_storage_live cx vv es s /\
  (?w. eval_operand (vv_operand vv) s = SOME w) /\
  (!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) u = SOME w) ==>
  vv_storage_live cx vv es u
Proof
  Cases_on `vv` >> simp[vv_operand_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem target_saved_operand_exists:
  vv_holds cenv cx ty r vv es s ==>
  ?w. eval_operand (vv_operand vv) s = SOME w
Proof
  Cases_on `vv` >> simp[vv_holds_def, vv_operand_def, expr_val_rel_def] >>
  metis_tac[]
QED


Theorem target_saved_post_transport:
  vv_post ctx func cenv cx e es sa sm s0 es1 r vv s /\
  target_post ctx func cenv cx es1 sm sb s ee pv vt op u /\
  ee = es1 with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|> /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  vv_storage_live cx vv es1 s ==>
  vv_post ctx func cenv cx e ee sa sb u ee r vv u /\
  wb_frame cenv es ee sa s0 u
Proof
  strip_tac >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    gvs[vv_post_def, locals_kept_def] >>
  `wb_frame cenv es1 es1 sm s u` by
    (gvs[target_post_def, wb_frame_def, locals_kept_def, popped_kept_def] >>
     metis_tac[]) >>
  `!w. eval_operand (vv_operand vv) s = SOME w ==>
        eval_operand (vv_operand vv) u = SOME w` by
    (rpt strip_tac >> irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`sm`, `s`] >> gvs[wb_frame_def]) >>
  `storage_rel cx cx.txn.target es1 u /\
   transient_rel cx cx.txn.target es1 u` by
    (gvs[target_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
         state_rel_def, storage_rel_def, transient_rel_def]) >>
  `wb_frame cenv es (es1 with <|gas_obs := gs; outcomes := os; requests := rq; logs := lg|>) sa s0 u` by
    (irule wb_frame_trans >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`es1`, `sm`, `s`] >>
     gvs[vv_post_def, target_post_def, wb_frame_def] >> metis_tac[]) >>
  simp[] >>
  gvs[vv_post_def] >>
  simp[SRULE [] target_saved_holds_oracles,
       SRULE [] target_saved_regions_oracles] >>
  rpt conj_tac
  >- gvs[target_post_def]
  >- (irule target_saved_holds_frame >>
      simp[] >> qexistsl_tac [`s`, `sa`, `sm`] >> simp[])
  >- (irule (cj 1 target_saved_value_region_frame) >>
      metis_tac[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def])
  >- (strip_tac >> irule (cj 2 target_saved_value_region_frame) >>
      metis_tac[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def])
  >- (strip_tac >> irule target_saved_storage_live_frame >>
      metis_tac[target_saved_operand_exists]) >>
  simp[exprSimPropsTheory.locals_kept_refl]
QED
