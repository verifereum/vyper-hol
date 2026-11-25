(* Force a linked qualified literal slot with its single word load. *)
Theory bodyQualifiedSlotWordMods
Ancestors
  bodyFullPostsMods bodyFullUnwrapRun exprPtrUnwrapStorage
  exprPtrUnwrapCopyEdges typedCopyOriginPtrBase allocasBelowFmpUpdatesProps
  emitHelperProps loweringShapeRules instMemFrontier fragExecMem
  exprSimMemDefs bodyPtrDefs bodyInvSplit bodyFullShadowBodyInv
  loweringPosts loweringStateRelDefs compileEnv context venomState venomExecSemantics
  exprLowering exprLoweringProps finite_map list ptrDiscipline fragGasOriginPtrDead
  fragGasOriginPtr vyperStorageFootprint venomInst memSafeRun bodyMemBopRestWordPath
  stmtSimDefs decoderGhostFramePtr
  arithmetic pred_set

Theorem slot_vv_post[local]:
  vv_post_mods H ctx func cenv cx e es sa sa s0 ee tv
    (LocatedValue t (mk_ptr (Lit slot) (slot_loc tr))) s0 ==>
  vv_post H ctx func cenv cx e es sa sa s0 ee tv
    (LocatedValue t (mk_ptr (Lit slot) (slot_loc tr))) s0
Proof
  Cases_on `tr` >> Cases_on `tv` >>
  TRY (rename1 `PlaceR p` >> Cases_on `p`) >>
  simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def, vv_place_ptr_def,
       vv_place_ptr_mods_def, slot_loc_def, mk_ptr_def]
QED

Theorem slot_old_lookup[local]:
  not_fresh_at sa x ==>
  lookup_var x (update_var (STRING #"%" (toString sa.cs_next_var)) w s
                  with vs_inst_idx := k) = lookup_var x s
Proof
  simp[not_fresh_at_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem slot_immutable_frame[local]:
  immutable_frame_mods func cenv cx ee s /\ local_ptrs_reserved cenv sa ==>
  immutable_frame_mods func cenv cx ee
    (update_var (STRING #"%" (toString sa.cs_next_var)) w s with vs_inst_idx := k)
Proof
  simp[immutable_frame_mods_def] >> strip_tac >> conj_tac
  >- (qpat_x_assum `immutables_rel_mods _ _ _ _ _` mp_tac >>
      simp[immutables_rel_mods_def, immutables_rel_def, update_var_def]) >>
  qabbrev_tac `z = (update_var (STRING #"%" (toString sa.cs_next_var)) w s with vs_inst_idx := k)` >>
  `z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next` by
     simp[Abbr `z`, update_var_def] >>
  fs[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  irule immutable_alloca_sep_fields >> qexistsl [`s`,`ee`] >> simp[] >>
  qpat_x_assum `!src tops. ALOOKUP _ _ = SOME _ ==> _` drule >> simp[] >>
  simp[local_region_def] >> rpt strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var p z = lookup_var p s` by
    (drule_then (qspecl_then [`w`,`s`,`k`] assume_tac) slot_old_lookup >> fs[Abbr `z`]) >>
  qexistsl [`id`,`entry`,`p`] >> simp[] >> metis_tac[]
QED

Theorem slot_ghost_frame[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
                           op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ghost_inv_at_mods D lo d cenv cx ee G' tn'
    (update_var (STRING #"%" (toString sa.cs_next_var)) w s with vs_inst_idx := k)
Proof
  rewrite_tac[ghost_inv_at_mods_def] >> strip_tac >>
  qabbrev_tac `z = (update_var (STRING #"%" (toString sa.cs_next_var)) w s with vs_inst_idx := k)` >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
       (!n. ptr_covers G' tn' x z n <=> ptr_covers G tn x s n)` by
    (gen_tac >> strip_tac >>
     `lookup_var x z = lookup_var x s` by
    (drule_then (qspecl_then [`w`,`s`,`k`] assume_tac) slot_old_lookup >> fs[Abbr `z`]) >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP G' x = _ /\ _`
       (drule_then strip_assume_tac) >> simp[ptr_covers_def]) >>
  `z.vs_memory = s.vs_memory /\ z.vs_call_ctx = s.vs_call_ctx /\
   z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
   z.vs_immutables = s.vs_immutables /\ z.vs_allocas = s.vs_allocas /\
   z.vs_alloca_next = s.vs_alloca_next` by simp[Abbr `z`,update_var_def] >>
  simp[stor_taint_ok_at_def,allocas_from_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      qpat_assum `!name entry p sz. lookup_scopes _ _ = SOME _ /\ _ ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`
        (drule_then strip_assume_tac) >> fs[] >> metis_tac[])
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def] >> rename1 `cenv.ce_return_buf = SOME (PtrVar (Var p) sz)` >>
      `not_fresh_at sa p` by metis_tac[] >>
      qpat_assum `!x. not_fresh_at sa x ==> lookup_var x z = _ /\ _`
        (drule_then strip_assume_tac) >>
      qexistsl [`p`,`sz`] >> simp[]) >>
  fs[stor_taint_ok_at_def,allocas_from_def] >> metis_tac[local_ptrs_reserved_imm_base]
QED

Theorem slot_word_load_path[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\ alloca_inv s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?z G' tn'.
    z = (update_var (STRING #"%" (toString sa.cs_next_var))
          (if tr then tload slot s else sload slot s) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn')) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ z.vs_alloca_next = s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
                             op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  qabbrev_tac `opc = if tr then TLOAD else SLOAD` >>
  qabbrev_tac `w = if tr then tload slot s else sload slot s` >>
  `!out. step_inst_base (mk_inst sa.cs_next_id opc [Lit slot] [out]) s =
         OK (update_var out w s)` by
    (Cases_on `tr` >> gvs[Abbr `opc`, Abbr `w`, step_inst_base_opcode_eqs,
                           mk_inst_def, exec_read1_def, eval_operand_def]) >>
  `!out. inst_mem_below_frontier (mk_inst sa.cs_next_id opc [Lit slot] [out]) s /\
         inst_dload_in_section (mk_inst sa.cs_next_id opc [Lit slot] [out]) s` by
    (gen_tac >> conj_tac
     >- (irule below_frontier_no_ranges >> Cases_on `tr` >> gvs[Abbr `opc`,mk_inst_def]) >>
     Cases_on `tr` >> gvs[Abbr `opc`,mk_inst_def,inst_dload_in_section_def]) >>
  qabbrev_tac `dead0 = <| d_stor := K (K {}); d_trans := K (K {});
                        d_imm := K {}; d_ret := K {} |>` >>
  `!out. ptr_inst_ok dead0 lo 0 ctx func G tn (mk_inst sa.cs_next_id opc [Lit slot] [out]) s` by
    (gen_tac >> irule ptr_inst_ok_slot_load >>
     Cases_on `tr` >> gvs[Abbr `opc`,eval_operand_def,op_taint_def]) >>
  `opc <> INVOKE /\ opc <> GAS /\ opc <> DALLOCA /\ ~is_terminator opc` by
    (Cases_on `tr` >> gvs[Abbr `opc`,is_terminator_def]) >>
  drule_all_then strip_assume_tac typed_copy_origin_ptr_emit_op_path >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  gvs[] >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id opc [Lit slot] [out]` >>
  qabbrev_tac `u = update_var out w s` >>
  qexistsl [`step_prov PG G i u`,`step_taint i s u tn`] >>
  `alloca_history func (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (`SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[ADD1] >>
     qspecl_then [`[i]`,`sa`,`sb`,`s`,`u`] mp_tac emitted_alloca_history >>
     simp[Abbr `i`,Abbr `u`,mk_inst_def,run_inst_seq_def]) >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_alloca_next = s.vs_alloca_next /\
   (allocas_below_fmp u <=> allocas_below_fmp s)` by
    simp[Abbr `u`,allocas_below_fmp_updates,update_var_def] >>
  fs[allocas_below_fmp_updates,ADD1] >> rpt conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
      qpat_assum `!off len explicit PG. gas_origin_ptr_path _ _ _ _ /\ _`
        (qspecl_then [`0`,`0`,`explicit`,`PG`] strip_assume_tac) >>
      fs[Abbr `dead0`,ADD1])
  >- (qpat_assum `alloca_history func (u with vs_inst_idx := _)` mp_tac >>
      qpat_assum `s.vs_inst_idx = _` (fn th => rewrite_tac [th]))
  >- (Cases_on `tr` >>
      gvs[Abbr `i`,Abbr `opc`,step_taint_def,set_var_taint_def,
          out_taint_def,op_taint_def,mk_inst_def,eval_operand_def,FLOOKUP_UPDATE])
  >- (irule step_prov_out_none >> simp[Abbr `i`,mk_inst_def] >>
      irule out_prov_other_none >> Cases_on `tr` >> gvs[Abbr `opc`,mk_inst_def])
  >- (rpt strip_tac >>
      `x <> out` by
        (fs[not_fresh_at_def] >>
         first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[Abbr `out`]) >>
      simp[step_prov_other_output,step_taint_other_output,Abbr `i`,mk_inst_def]) >>
  Cases_on `tr` >> gvs[Abbr `i`,Abbr `u`,Abbr `opc`,slot_load_ghost_frame]
QED

Theorem qualified_slot_word_read_mods:
  unwrap_value cenv (LocatedValue t (mk_ptr (Lit slot) (slot_loc tr))) sa = (op,sb) /\
  is_word_type t /\ evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  read_result cx tv ee = (INL v,ee) /\
  ptr_vv_ok cx (post_value_type cenv e) tv
    (LocatedValue t (mk_ptr (Lit slot) (slot_loc tr))) ee G0 tn0 s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func cenv cx e es sa sa s0 ee tv
         (LocatedValue t (mk_ptr (Lit slot) (slot_loc tr))) s0 /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G0 tn0 s0) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z G' tn'. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK z,G',tn') /\
    expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (op,sb)` by
    (Cases_on `tr` >>
     fs[slot_loc_def, mk_ptr_def, unwrap_value_def, compile_ptr_load_def]) >>
  qabbrev_tac `p = mk_ptr (Lit slot) (slot_loc tr)` >>
  `p.ptr_location = slot_loc tr /\ p.ptr_operand = Lit slot` by
    simp[Abbr `p`,mk_ptr_def] >>
  `eval_operand p.ptr_operand s0 = SOME slot` by simp[eval_operand_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sa s0 ee tv (LocatedValue t p) s0 /\
       immutable_frame_mods func cenv cx ee s0 /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G0 tn0 s0` by
    (gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
     simp[] >> conj_tac
     >- (qunabbrev_tac `p` >> irule slot_vv_post >> first_assum ACCEPT_TAC) >>
     fs[vv_post_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >>
  `t = post_value_type cenv e /\
   key_taint (if tr then tn0.t_trans else tn0.t_stor) slot = {}` by
    (drule_all unwrap_storage_word_input >> simp[mk_ptr_def,eval_operand_def]) >>
  `alloca_inv s0` by metis_tac[vv_post_def,rest_word_state_alloca_inv] >>
  `allocas_from lo s0` by fs[ghost_inv_at_mods_def] >>
  drule_all_then
    (qspecl_then [`explicit`,`PG`,`G0`] (qx_choosel_then [`z`,`G'`,`tn'`] strip_assume_tac))
    slot_word_load_path >>
  qexistsl [`z`,`G'`,`tn'`] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `is_word_type (post_value_type cenv e)` by metis_tac[] >>
  simp[expr_store_bound_word] >>
  conj_tac
  >- (simp[expr_post_mods_def] >> conj_tac
      >- (`emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sa = (op,sb)` by simp[] >>
          `sa.cs_next_var <= sa.cs_next_var` by simp[] >>
          drule_all unwrap_storage_word_post >> simp[]) >>
      irule slot_immutable_frame >> simp[]) >>
  conj_tac >- (irule slot_ghost_frame >> simp[] >> qexistsl [`G0`,`tn0`] >> simp[]) >>
  conj_tac >- (irule ptr_val_ok_word >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G0`,`tn0`] >> simp[ghost_kept_at_def]
QED
