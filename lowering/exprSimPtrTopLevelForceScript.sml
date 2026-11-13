(* Forced word loads: live word regions contain no dead storage bytes. *)
Theory exprSimPtrTopLevelForce
Ancestors
  exprSimPtrTopLevelViews exprSimPtrTopLevelCopy exprSimPtrProps bodyPtrDefs
  compileEnv loweringStateRelDefs context vyperValue vyperAST ptrDiscipline words pred_set exprSimUnwrap
  emitHelper emitHelperProps fragExec venomInst venomState decoderGhostFramePtr memLocDefs codegenRel
  exprSimTopLevelStorage exprSimTopLevelImmutable exprSimTopLevelProps exprSimUnwrapProps exprSimProps exprSimMemorySource
  exprSimHypsDefs exprSimHyps exprSimDefs exprLowering exprLoweringProps loweringPosts
  accountsRelProps vyperStorageLayoutSafety vyperTypeGlobalLookupSoundness
  vyperInterpreter vyperState gasSummary fragGasPathPtr valueEncoding venomExecSemantics

Theorem toplevel_word_dead_bytes:
  !tenv t tv st base j b.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==>
    ~dead_bytes st base tv j b
Proof
  Cases_on `t` >> simp[is_word_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[dead_bytes_def, is_word_type_def]
QED

Theorem toplevel_word_key_taint:
  !cx tr tn s w t tv.
    stor_taint_ok cx tn s /\
    storage_read_live cx tr
      (if tr then s.vs_transient s.vs_call_ctx.cc_address
       else (s.vs_accounts s.vs_call_ctx.cc_address).storage) w tv /\
    is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv ==>
    key_taint (if tr then tn.t_trans else tn.t_stor) w = {}
Proof
  rpt strip_tac >> simp[EXTENSION, key_taint_def] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  `dead_bytes
    (if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage)
    (w2n w) tv (w2n w) x` by
    (irule toplevel_live_storage_taint >>
     simp[] >> metis_tac[]) >>
  metis_tac[toplevel_word_dead_bytes]
QED

Theorem toplevel_emit_load_path:
  emit_op opc [src] sa = (op,sb) /\ fn_has_code sa sb fn /\
  MEM opc [SLOAD;TLOAD;DLOAD] /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base
    (mk_inst sa.cs_next_id opc [src] [STRING #"%" (toString sa.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s) ==>
  !D PG. ?out G' tn'.
    op = Var out /\ out = STRING #"%" (toString sa.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
                     op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (op_taint tn' (Var out) =
      if opc = SLOAD then
        case eval_operand src s of NONE => {} | SOME a => key_taint tn.t_stor a
      else if opc = TLOAD then
        case eval_operand src s of NONE => {} | SOME a => key_taint tn.t_trans a
      else {}) /\
    op_prov G' (Var out) = NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [src]
       [STRING #"%" (toString sa.cs_next_var)]] /\
   op = Var (STRING #"%" (toString sa.cs_next_var)) /\
   (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var))` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id opc [src] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst sa.cs_next_id opc [src] [out]) s` by
    (irule toplevel_ptr_inst_ok_load >> fs[]) >>
  qpat_x_assum `s.vs_inst_idx = _` kall_tac >>
  qexistsl_tac [`out`,
    `step_prov PG G (mk_inst sa.cs_next_id opc [src] [out]) (update_var out w s)`,
    `step_taint (mk_inst sa.cs_next_id opc [src] [out]) s (update_var out w s) tn`] >>
  simp[] >>
  conj_tac
  >- (irule gas_path_ptr_one_step >>
      gvs[mk_inst_def, is_terminator_def, update_var_def]) >>
  `!x. x <> out ==>
    FLOOKUP (step_prov PG G (mk_inst sa.cs_next_id opc [src] [out])
       (update_var out w s)) x = FLOOKUP G x /\
    op_taint (step_taint (mk_inst sa.cs_next_id opc [src] [out]) s
       (update_var out w s) tn) (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac
     >- (irule step_prov_other_output >> simp[mk_inst_def]) >>
     irule step_taint_other_output >> simp[mk_inst_def]) >>
  `op_prov (step_prov PG G (mk_inst sa.cs_next_id opc [src] [out])
      (update_var out w s)) (Var out) = NONE` by
    (fs[step_prov_def, out_prov_def, set_prov_def, op_prov_def,
        mk_inst_def, finite_mapTheory.FLOOKUP_DRESTRICT]) >>
  gvs[] >>
  simp[step_taint_def, mk_inst_def, op_taint_def, set_var_taint_def,
       out_taint_def, finite_mapTheory.FLOOKUP_UPDATE, imm_taint_def,
       mem_taint_def, adopt_reset_def, store_taint_def,
       step_writes_def, written_taint_def, new_site_bytes_def,
       range_bytes_def, source_memory_write_ranges_def, update_var_def,
       finite_mapTheory.FLOOKUP_DEF] >>
  Cases_on `eval_operand src s` >> simp[EXTENSION] >> metis_tac[]
QED

Theorem toplevel_load_ghost_post:
  ghost_inv d cenv cx es G0 tn0 s0 /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> out) /\
  (!x. x <> out ==> FLOOKUP G x = FLOOKUP G0 x /\
                     op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  tn.t_mem = tn0.t_mem /\ tn.t_stor = tn0.t_stor /\
  tn.t_trans = tn0.t_trans /\ tn.t_imm = tn0.t_imm /\
  es'.scopes = es.scopes /\
  u = (update_var out w s0 with vs_inst_idx := SUC s0.vs_inst_idx) ==>
  ghost_inv d cenv cx es' G tn u /\
  ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >> conj_tac
  >- (irule ghost_inv_fresh_frame >>
      qexistsl_tac [`G0`, `es`, `s0`, `sa`, `tn0`] >>
      simp[update_var_def] >> rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[ghost_kept_def] >> metis_tac[]
QED

Theorem toplevel_storage_word_at:
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v)
    (LocatedValue ann (mk_ptr (Lit w) (if tr then LocTransient else LocStorage))) s /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv ==>
  (if tr then tload w s else sload w s) = typed_val_to_w256 tv v
Proof
  strip_tac >> irule storage_holds_load >>
  qexistsl_tac [`cx`, `ee`, `ann`] >> simp[] >>
  Cases_on `tr` >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, mk_ptr_def, eval_operand_def]
QED

Theorem toplevel_storage_word_sim_ptr:
  !d ctx PG func cenv cx env ty ann src id es ts tr typ id_str slot tvt v.
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\ is_word_type ann /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v,es) ==>
  expr_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  rw[expr_sim_ptr_def] >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >> gvs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >>
     qexistsl [`src`, `id`, `[]`] >> simp[declared_storage_region_def]) >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
    (LocatedValue ann (mk_ptr (Lit (n2w slot))
      (if tr then LocTransient else LocStorage)),sa)` by
    (Cases_on `tr` >> gvs[compile_expr_def, expr_type_def]) >>
  `emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (op,sb)` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     Cases_on `tr` >>
     simp[lower_value_def, comp_bind_def, unwrap_value_def, mk_ptr_def,
          compile_ptr_load_def]) >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    (irule toplevel_storage_slots_in_range >>
     gvs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `w2n ((n2w slot):bytes32) + type_slot_size tvt <= dimword (:256)` by
    (`storage_layout_safe cx` by fs[expr_sim_pre_def, expr_sim_inv_def] >>
     `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
       simp[declared_storage_region_def] >>
     drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  `vv_post ctx func cenv cx (TopLevelName ann (src,id)) es sa sa s0
     (es with gas_obs := []) (PlaceR (StoragePlace tr (n2w slot) tvt))
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
       (if tr then LocTransient else LocStorage))) s0` by
    (irule toplevel_storage_value_post >> simp[]) >>
  `read_result cx (PlaceR (StoragePlace tr (n2w slot) tvt))
     (es with gas_obs := []) = (INL v,es with gas_obs := [])` by
    (`read_result cx (PlaceR (StoragePlace tr (n2w slot) tvt)) es = (INL v,es)` by
       simp[read_result_def, read_place_def] >>
     drule read_result_gas_obs >> simp[]) >>
  `!tail. bind (eval_expr cx (TopLevelName ann (src,id))) (read_result cx)
      (es with gas_obs := tail) = (INL v,es with gas_obs := tail)` by
    (gen_tac >> simp[Once evaluate_def, lookup_global_def, bind_def,
       lift_option_type_def, return_def, raise_def, LET_THM] >>
     drule read_result_gas_obs >>
     disch_then (qspec_then `tail` mp_tac) >>
     simp[read_result_def, read_place_def]) >>
  suspend "load"
QED

Resume toplevel_storage_word_sim_ptr[load]:
  drule_all vv_post_read_result >> strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ (PlaceR _) _ _` kall_tac >> fs[] >>
  `(if tr then tload (n2w slot) s0 else sload (n2w slot) s0) =
    typed_val_to_w256 tvt v` by (irule toplevel_storage_word_at >> metis_tac[]) >>
  `step_inst_base
    (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit (n2w slot)]
      [STRING #"%" (toString sa.cs_next_var)]) s0 =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (typed_val_to_w256 tvt v) s0)` by
    (* Only the loaded value matters; gvs over the whole context took 5.9 s. *)
    (qpat_assum `(if tr then tload _ _ else sload _ _) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `tr`
     >- simp[step_inst_base_def, exec_read1_def, eval_operand_def, mk_inst_def] >>
     simp[step_inst_base_def, exec_read1_def, eval_operand_def, mk_inst_def]) >>
  `op_taint tn0 (Lit (n2w slot)) = {} /\
    MEM (if tr then TLOAD else SLOAD) [SLOAD;TLOAD;DLOAD]` by
    (Cases_on `tr` >> simp[op_taint_def]) >>
  drule_all toplevel_emit_load_path >>
  disch_then (qspecl_then [`G0`, `cx_dead cx`, `PG`] strip_assume_tac) >>
  qabbrev_tac `u = update_var out (typed_val_to_w256 tvt v) s0
    with vs_inst_idx := SUC s0.vs_inst_idx` >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`expr_sim_pre _ _ _ _ _`, `lower_value _ _ _ _ _ = _`,
     `compile_expr _ _ _ _ = _`, `get_module_code _ _ = _`,
     `find_var_decl_by_name _ _ = _`, `lookup_var_slot_from_layout _ _ _ _ = _`,
     `slots_in_range _ _ _`, `_ + slot MOD dimword (:256) <= _`,
     `read_storage_slot _ _ _ _ _ = _`, `read_result _ _ _ = _`,
     `storage_vars_rel _ _`, `transient_vars_rel _ _`,
     `FLOOKUP cenv.ce_module_vars _ = _`, `step_inst_base _ _ = _`,
     `gas_admissible _ _ _`] >>
  `key_taint (if tr then tn0.t_trans else tn0.t_stor) (n2w slot) = {}` by
    (irule toplevel_word_key_taint >> metis_tac[ghost_inv_def]) >>
  `op_taint tn' (Var out) = {}` by
    (Cases_on `tr` >> gvs[eval_operand_def]) >>
  suspend "post"
QED

Resume toplevel_storage_word_sim_ptr[post]:
  `u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
     gvs[Abbr `u`, update_var_def]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) u` by
    (simp[Abbr `u`] >>
     `not_local_ptr cenv (es with gas_obs := []).scopes out` by
       (simp[] >> qpat_assum `out = _` SUBST1_TAC >>
        irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
     `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
        (s0 with vs_inst_idx := SUC s0.vs_inst_idx)` by
       (drule msg_gas_state_frame >>
        disch_then (qspecl_then [`s0.vs_gas_readings`, `SUC s0.vs_inst_idx`, `[]`] mp_tac) >>
        simp[]) >>
     drule_all stmt_state_rel_update_var >> simp[update_var_def]) >>
  `expr_post ctx func cenv cx (TopLevelName ann (src,id)) es sa sb s0
    (es with gas_obs := []) v op u` by
    (drule expr_post_of_vv_post_load >> disch_then irule >>
     simp[expr_type_def] >>
     gvs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ghost_inv d cenv cx (es with gas_obs := []) G' tn' u /\
   ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule toplevel_load_ghost_post >> simp[Abbr `u`] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`, `es`, `G'`, `tn'`, `OK u`] >>
  simp[gas_explicit_def, ptr_val_ok_def, expr_type_def] >> metis_tac[]
QED

Finalise toplevel_storage_word_sim_ptr

Theorem toplevel_immutable_word_at:
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v)
    (LocatedValue ann (mk_ptr (Lit w) LocCode)) s /\
  ~cenv.ce_is_ctor /\ is_word_type ann ==>
  ?tv. evaluate_type (get_tenv cx) ann = SOME tv /\
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) =
      typed_val_to_w256 tv v
Proof
  strip_tac >> irule immutable_holds_dload >>
  simp[] >> qexistsl_tac [`cenv`, `ctx`, `ee`, `func`] >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, mk_ptr_def, eval_operand_def]
QED

Theorem toplevel_immutable_word_sim_ptr:
  !d ctx PG func cenv cx env ty ann src id es ts.
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\ is_word_type ann /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
  expr_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  rw[expr_sim_ptr_def] >>
  `gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  drule_all toplevel_immutable_lookup >> strip_tac >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode),sa)` by
    simp[compile_toplevel_immutable_ptr] >>
  `emit_op DLOAD [Lit (n2w off)] sa = (op,sb)` by
    (qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
     qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def, unwrap_value_def, mk_ptr_def,
          compile_ptr_load_def, compile_imm_load_word_def]) >>
  `vv_post ctx func cenv cx (TopLevelName ann (src,id)) es sa sa s0
     (es with gas_obs := []) (PlaceR (ImmutablePlace src id []))
     (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) s0` by
    (irule toplevel_immutable_post >> simp[] >> metis_tac[]) >>
  `!tail. bind (eval_expr cx (TopLevelName ann (src,id))) (read_result cx)
      (es with gas_obs := tail) = (INL v,es with gas_obs := tail)` by
    (qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
     gen_tac >> simp[Once evaluate_def, lookup_global_def, bind_def,
       lift_option_type_def, return_def, raise_def, LET_THM,
       read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, evaluate_subscripts_def, lift_sum_def]) >>
  `read_result cx (PlaceR (ImmutablePlace src id []))
     (es with gas_obs := []) = (INL v,es with gas_obs := [])` by
    (qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
     simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, evaluate_subscripts_def, lift_sum_def,
       bind_def, return_def, lift_option_type_def]) >>
  drule_all vv_post_read_result >> strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ (PlaceR _) _ _` kall_tac >> fs[] >>
  drule_all toplevel_immutable_word_at >> strip_tac >> gvs[] >>
  `step_inst_base
    (mk_inst sa.cs_next_id DLOAD [Lit (n2w off)]
      [STRING #"%" (toString sa.cs_next_var)]) s0 =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (typed_val_to_w256 tv v) s0)` by
    simp[step_inst_base_def, exec_read1_def, eval_operand_def] >>
  `op_taint tn0 (Lit (n2w off)) = {} /\
    MEM DLOAD [SLOAD;TLOAD;DLOAD]` by simp[op_taint_def] >>
  drule_all toplevel_emit_load_path >>
  disch_then (qspecl_then [`G0`, `cx_dead cx`, `PG`] strip_assume_tac) >>
  qabbrev_tac `u = update_var out (typed_val_to_w256 tv v) s0
    with vs_inst_idx := SUC s0.vs_inst_idx` >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`expr_sim_pre _ _ _ _ _`, `lower_value _ _ _ _ _ = _`,
     `compile_expr _ _ _ _ = _`, `get_module_code _ _ = _`,
     `find_var_decl_by_name _ _ = _`, `FLOOKUP cenv.ce_module_vars _ = _`,
     `ALOOKUP es.immutables _ = _`, `FLOOKUP (get_source_immutables _ _) _ = _`,
     `step_inst_base _ _ = _`, `read_result _ _ _ = _`,
     `gas_admissible (eval_expr _ _) _ _`, `gas_admissible (bind _ _) _ _`] >>
  `op_taint tn' (Var out) = {}` by gvs[] >>
  suspend "post"
QED

Resume toplevel_immutable_word_sim_ptr[post]:
  `u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
     gvs[Abbr `u`, update_var_def]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) u` by
    (simp[Abbr `u`] >>
     `not_local_ptr cenv (es with gas_obs := []).scopes out` by
       (simp[] >> qpat_assum `out = _` SUBST1_TAC >>
        irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
     `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
        (s0 with vs_inst_idx := SUC s0.vs_inst_idx)` by
       (drule msg_gas_state_frame >>
        disch_then (qspecl_then [`s0.vs_gas_readings`, `SUC s0.vs_inst_idx`, `[]`] mp_tac) >>
        simp[]) >>
     drule_all stmt_state_rel_update_var >> simp[update_var_def]) >>
  `expr_post ctx func cenv cx (TopLevelName ann (cenv.ce_module,id)) es sa sb s0
    (es with gas_obs := []) v op u` by
    (drule expr_post_of_vv_post_load >> disch_then irule >>
     simp[expr_type_def] >>
     gvs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ghost_inv d cenv cx (es with gas_obs := []) G' tn' u /\
   ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (irule toplevel_load_ghost_post >> simp[Abbr `u`] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`, `es`, `G'`, `tn'`, `OK u`] >>
  simp[gas_explicit_def, ptr_val_ok_def, expr_type_def] >> metis_tac[]
QED

Finalise toplevel_immutable_word_sim_ptr

Theorem compile_toplevel_word_sim_ptr:
  !d ctx PG func cenv cx env ty ann nsid es.
  expr_sim_pre cenv cx env (TopLevelName ann nsid) es /\ is_word_type ann ==>
  expr_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es
Proof
  rpt strip_tac >> PairCases_on `nsid` >>
  rename1 `TopLevelName ann (src,id)` >>
  Cases_on `get_module_code cx src`
  >- (rw[expr_sim_ptr_def] >>
      drule forced_expr_admissible_raw >>
      metis_tac[missing_module_not_gas_admissible]) >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `find_var_decl_by_name id ts`
  >- (irule toplevel_immutable_word_sim_ptr >> metis_tac[]) >>
  rename1 `find_var_decl_by_name id ts = SOME di` >>
  PairCases_on `di` >> Cases_on `di0`
  >~ [`HashMapVarDecl`]
  >- (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
      metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]) >>
  rename1 `StorageVarDecl tr typ` >>
  Cases_on `?slot tvt v. lookup_var_slot_from_layout cx tr src di1 = SOME slot /\
                         evaluate_type (get_tenv cx) typ = SOME tvt /\
                         read_storage_slot cx tr (n2w slot) tvt es = (INL v,es)`
  >- (gvs[] >> irule toplevel_storage_word_sim_ptr >> metis_tac[]) >>
  rw[expr_sim_ptr_def] >>
  `gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  `F` suffices_by simp[] >>
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
  `contract_storage_well_formed cx es` by
    gvs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_storage_read_decodes >> metis_tac[]
QED
