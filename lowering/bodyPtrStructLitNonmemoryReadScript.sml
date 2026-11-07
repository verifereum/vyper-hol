(* Source and ghost boundaries for the single nonmemory word reads.
   Constructor code pointers require a separate address-generation protocol. *)
Theory bodyPtrStructLitNonmemoryRead
Ancestors
  bodyPtrStructLitNonmemoryLoad bodyPtrStructLitMemoryRead
  bodyPtrStructLitFreshGhost exprSimUnwrap exprSimUnwrapProps
  loweringPosts bodyPtrDefs ptrSafeRun ptrDiscipline venomState
  venomInst finite_map decoderGhostFramePtr list codegenRel
  context exprLowering compileEnv emitHelper fragExec exprLoweringProps
  gasSummaryComposePtr exprSimMemorySource venomExecSemantics venomInstProofs

Theorem vv_post_storage_word_read:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  p.ptr_location = slot_loc tr /\ is_word_type ty ==>
  ty = expr_type e /\
  ?v a tvt. read_result cx tv ee = (INL v,ee) /\
    eval_operand p.ptr_operand s = SOME a /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    (if tr then tload a s else sload a s) = typed_val_to_w256 tvt v
Proof
  strip_tac >>
  `ty = expr_type e /\ ?a. eval_operand p.ptr_operand s = SOME a /\
    storage_holds cx tr ty tv a ee s` by
    (Cases_on `tr` >> gvs[vv_post_def, vv_holds_def, slot_loc_def]) >>
  `?v tvt. read_result cx tv ee = (INL v,ee) /\
    evaluate_type (get_tenv cx) ty = SOME tvt` by
    gvs[storage_holds_def] >>
  `vv_post ctx fn cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s`
    by metis_tac[vv_post_read_result] >>
  `storage_holds cx tr ty (Value v) a ee s` by
    (Cases_on `tr` >> gvs[vv_post_def, vv_holds_def, slot_loc_def]) >>
  drule_all storage_holds_load >> strip_tac >> metis_tac[]
QED

Theorem vv_post_runtime_code_word_read:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type ty ==>
  ty = expr_type e /\
  ?v a tvt. read_result cx tv ee = (INL v,ee) /\
    eval_operand p.ptr_operand s = SOME a /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w)) =
      typed_val_to_w256 tvt v
Proof
  strip_tac >>
  `ty = expr_type e /\ ?a. eval_operand p.ptr_operand s = SOME a /\
    immutable_holds cenv cx ty tv a ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  `?v. read_result cx tv ee = (INL v,ee)` by gvs[immutable_holds_def] >>
  `vv_post ctx fn cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s`
    by metis_tac[vv_post_read_result] >>
  `immutable_holds cenv cx ty (Value v) a ee s /\
   stmt_state_rel ctx fn cenv cx ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  drule_all immutable_holds_dload >> strip_tac >> metis_tac[]
QED

Theorem nonmemory_read_taint_frame:
  MEM opc [SLOAD; TLOAD; DLOAD] ==>
  (step_taint (mk_inst id opc [src] [out]) s (update_var out w s) tn).t_mem =
    tn.t_mem /\
  (step_taint (mk_inst id opc [src] [out]) s (update_var out w s) tn).t_stor =
    tn.t_stor /\
  (step_taint (mk_inst id opc [src] [out]) s (update_var out w s) tn).t_trans =
    tn.t_trans /\
  (step_taint (mk_inst id opc [src] [out]) s (update_var out w s) tn).t_imm =
    tn.t_imm
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, update_var_def,
       step_writes_def, written_taint_def, range_bytes_def, mk_inst_def,
       source_memory_write_ranges_def, adopt_reset_def, store_taint_def,
       imm_taint_def, finite_mapTheory.FLOOKUP_DEF] >>
  SET_TAC[]
QED

Theorem nonmemory_read_frame:
  MEM opc [SLOAD; TLOAD; DLOAD] /\ ghost_inv d cenv cx ee G tn s /\
  (!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_buf = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_pc = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  ghost_kept cenv es sf G0 tn0 initial G tn /\ ~not_fresh_at sf out /\
  G1 = step_prov PG G (mk_inst id opc [src] [out]) (update_var out w s) /\
  tn1 = step_taint (mk_inst id opc [src] [out]) s (update_var out w s) tn /\
  s1 = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ghost_inv d cenv cx ee G1 tn1 s1 /\
  ghost_kept cenv es sf G0 tn0 initial G1 tn1 /\
  (!r sz. r <> out /\ ptr_covers G tn r s sz ==>
    ptr_covers G1 tn1 r s1 sz)
Proof
  strip_tac >>
  qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  conj_tac
  >- (irule ghost_inv_update_var_pc >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      qexistsl [`G`, `tn`] >> simp[nonmemory_read_taint_frame] >>
      rpt strip_tac >> simp[step_prov_other_output, step_taint_other_output,
                             mk_inst_def]) >>
  conj_tac
  >- (qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac [ghost_kept_def] >> strip_tac >>
      conj_tac
      >- (rpt strip_tac >> `x <> out` by metis_tac[] >>
          simp[step_prov_other_output, step_taint_other_output, mk_inst_def] >>
          metis_tac[]) >>
      simp[nonmemory_read_taint_frame] >>
      pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
      conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  gvs[ptr_covers_def, step_prov_other_output, step_taint_other_output,
      mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem nonmemory_word_unwrap_code:
  is_word_type ty /\
  ((p.ptr_location = LocStorage /\ opc = SLOAD) \/
   (p.ptr_location = LocTransient /\ opc = TLOAD) \/
   (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ opc = DLOAD)) /\
  unwrap_value cenv (LocatedValue ty p) sa = (Var out,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id opc [p.ptr_operand] [out]] /\
  ~not_fresh_at sa out
Proof
  strip_tac >> gvs[unwrap_value_def, compile_ptr_load_def,
    compile_imm_load_word_def, emit_op_def, comp_bind_def, comp_return_def,
    fresh_id_def, comp_ignore_bind_def, fresh_var_def, emit_def, not_fresh_at_def]
QED

Theorem nonmemory_word_unwrap_instruction:
  is_word_type ty /\
  ((p.ptr_location = LocStorage /\ opc = SLOAD) \/
   (p.ptr_location = LocTransient /\ opc = TLOAD) \/
   (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ opc = DLOAD)) /\
  unwrap_value cenv (LocatedValue ty p) sa = (Var out,sb) /\
  fn_has_code sa sb fn ==>
  ~not_fresh_at sa out /\
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id opc [p.ptr_operand] [out])
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [p.ptr_operand] [out]] /\
   ~not_fresh_at sa out` by
    (irule nonmemory_word_unwrap_code >> simp[] >> metis_tac[]) >> simp[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem nonmemory_word_load_source_post:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  is_word_type ty /\ read_result cx tv ee = (INL v,ee) /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
    w = typed_val_to_w256 tvt v) /\
  sa.cs_next_var <= sm.cs_next_var /\ ~not_fresh_at sm out /\
  not_local_ptr cenv ee.scopes out ==>
  expr_post ctx fn cenv cx e es sa sb s0 ee v (Var out)
    (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `ty = expr_type e` by gvs[vv_post_def, vv_holds_def, AllCaseEqs()] >>
  `vv_post ctx fn cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue ty p) s` by metis_tac[vv_post_read_result] >>
  `stmt_state_rel ctx fn cenv cx ee (update_var out w s)` by
    (irule stmt_state_rel_update_var >> gvs[vv_post_def]) >>
  `stmt_state_rel ctx fn cenv cx ee
     (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[stmt_state_rel_index] >>
  irule expr_post_of_vv_post_load >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists `w` >>
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- simp[] >>
  qexistsl [`p`, `s`, `sm`, `ty`] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem nonmemory_word_unwrap_counted:
  is_word_type ty /\
  ((p.ptr_location = LocStorage /\ opc = SLOAD) \/
   (p.ptr_location = LocTransient /\ opc = TLOAD) \/
   (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ opc = DLOAD)) /\
  unwrap_value cenv (LocatedValue ty p) sm = (Var out,sb) /\
  fn_has_code sm sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  op_taint tn p.ptr_operand = {} /\
  step_inst_base (mk_inst sm.cs_next_id opc [p.ptr_operand] [out]) s =
    OK (update_var out w s) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sm.cs_next_id opc [p.ptr_operand] [out])
      (update_var out w s))
    (step_taint (mk_inst sm.cs_next_id opc [p.ptr_operand] [out]) s
      (update_var out w s) tn)
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `~not_fresh_at sm out /\ ?bb.
    lookup_block sm.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sm.cs_current_insts) =
      SOME (mk_inst sm.cs_next_id opc [p.ptr_operand] [out])` by
    (irule nonmemory_word_unwrap_instruction >> simp[] >> metis_tac[]) >>
  irule nonmemory_word_load_counted >> simp[MEM] >> metis_tac[]
QED

(* Internal assembly boundary: the location-specific callers below derive the
   source equality, opcode execution and clean key facts from vv_post. *)
Theorem nonmemory_word_read_continuation:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  is_word_type ty /\
  ((p.ptr_location = LocStorage /\ opc = SLOAD) \/
   (p.ptr_location = LocTransient /\ opc = TLOAD) \/
   (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ opc = DLOAD)) /\
  unwrap_value cenv (LocatedValue ty p) sm = (Var out,sb) /\
  fn_has_code sm sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand p.ptr_operand s = SOME a /\ op_taint tn p.ptr_operand = {} /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) /\
  step_inst_base (mk_inst sm.cs_next_id opc [p.ptr_operand] [out]) s =
    OK (update_var out w s) /\
  read_result cx tv ee = (INL v,ee) /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
    w = typed_val_to_w256 tvt v) /\
  sa.cs_next_var <= sm.cs_next_var /\ not_local_ptr cenv ee.scopes out /\
  ghost_inv d cenv cx ee G tn s /\
  (!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_buf = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_pc = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  ghost_kept cenv es sf G0 tn0 initial G tn /\ ~not_fresh_at sf out /\
  G1 = step_prov PG G (mk_inst sm.cs_next_id opc [p.ptr_operand] [out])
    (update_var out w s) /\
  tn1 = step_taint (mk_inst sm.cs_next_id opc [p.ptr_operand] [out]) s
    (update_var out w s) tn /\
  s1 = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
    (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
  expr_post ctx fn cenv cx e es sa sb s0 ee v (Var out) s1 /\
  ptr_val_ok cx ty v (Var out) G1 tn1 s1 /\
  ghost_inv d cenv cx ee G1 tn1 s1 /\
  ghost_kept cenv es sf G0 tn0 initial G1 tn1 /\
  s1.vs_current_bb = sb.cs_current_bb /\
  s1.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!r sz. r <> out /\ ptr_covers G tn r s sz ==>
    ptr_covers G1 tn1 r s1 sz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
     [mk_inst sm.cs_next_id opc [p.ptr_operand] [out]] /\
   ~not_fresh_at sm out` by
    (irule nonmemory_word_unwrap_code >> simp[] >> metis_tac[]) >>
  `MEM opc [SLOAD; TLOAD; DLOAD] /\
   MEM opc [SLOAD; TLOAD; CALLDATALOAD; DLOAD]` by (simp[MEM] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
     irule nonmemory_word_unwrap_counted >> simp[] >> metis_tac[]) >>
  conj_tac >- (simp[gas_marked_exec_ptr_def] >>
    metis_tac[read_result_gas_obs]) >>
  conj_tac >- (qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
    irule nonmemory_word_load_source_post >> simp[] >> metis_tac[]) >>
  conj_tac >- (qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
    qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
    irule nonmemory_word_load_ptr_val_ok >> simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx ee G1 tn1 s1 /\
   ghost_kept cenv es sf G0 tn0 initial G1 tn1 /\
   (!r sz. r <> out /\ ptr_covers G tn r s sz ==>
     ptr_covers G1 tn1 r s1 sz)` by
    (irule nonmemory_read_frame >> metis_tac[]) >>
  simp[] >> qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  simp[update_var_def]
QED

Theorem runtime_code_word_unwrap_continuation:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type ty /\
  ptr_vv_ok cx ty tv (LocatedValue ty p) ee G tn s /\
  unwrap_value cenv (LocatedValue ty p) sm = (Var out,sb) /\
  fn_has_code sm sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ not_local_ptr cenv ee.scopes out /\
  ghost_inv d cenv cx ee G tn s /\
  (!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_buf = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_pc = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  ghost_kept cenv es sf G0 tn0 initial G tn /\ ~not_fresh_at sf out ==>
  ?v G1 tn1 s1. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v (Var out) s1 /\
    ptr_val_ok cx ty v (Var out) G1 tn1 s1 /\
    ghost_inv d cenv cx ee G1 tn1 s1 /\
    ghost_kept cenv es sf G0 tn0 initial G1 tn1 /\
    s1.vs_current_bb = sb.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!r sz. r <> out /\ ptr_covers G tn r s sz ==>
      ptr_covers G1 tn1 r s1 sz)
Proof
  strip_tac >> drule_all vv_post_runtime_code_word_read >> strip_tac >>
  qmatch_asmsub_abbrev_tac `w = typed_val_to_w256 tvt v` >>
  `step_inst_base (mk_inst sm.cs_next_id DLOAD [p.ptr_operand] [out]) s =
    OK (update_var out w s)` by
    (simp[step_inst_base_def, mk_inst_def, exec_read1_def,
          Abbr `w`]) >>
  `op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  qexistsl [`v`,
    `step_prov PG G (mk_inst sm.cs_next_id DLOAD [p.ptr_operand] [out])
      (update_var out w s)`,
    `step_taint (mk_inst sm.cs_next_id DLOAD [p.ptr_operand] [out]) s
      (update_var out w s) tn`,
    `update_var out w s with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- simp[] >>
  irule nonmemory_word_read_continuation >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`a`, `DLOAD`, `p`, `sm`] >> simp[] >> metis_tac[]
QED

Theorem storage_word_unwrap_continuation:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  p.ptr_location = slot_loc tr /\ is_word_type ty /\
  ptr_vv_ok cx ty tv (LocatedValue ty p) ee G tn s /\
  unwrap_value cenv (LocatedValue ty p) sm = (Var out,sb) /\
  fn_has_code sm sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ not_local_ptr cenv ee.scopes out /\
  ghost_inv d cenv cx ee G tn s /\
  (!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_buf = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_pc = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  ghost_kept cenv es sf G0 tn0 initial G tn /\ ~not_fresh_at sf out ==>
  ?v G1 tn1 s1. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v (Var out) s1 /\
    ptr_val_ok cx ty v (Var out) G1 tn1 s1 /\
    ghost_inv d cenv cx ee G1 tn1 s1 /\
    ghost_kept cenv es sf G0 tn0 initial G1 tn1 /\
    s1.vs_current_bb = sb.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!r sz. r <> out /\ ptr_covers G tn r s sz ==>
      ptr_covers G1 tn1 r s1 sz)
Proof
  strip_tac >> drule_all vv_post_storage_word_read >> strip_tac >>
  `type_slot_size tvt = 1` by metis_tac[word_type_slot_size] >>
  `0 < type_slot_size tvt` by simp[] >>
  `op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  qabbrev_tac `opc = if tr then TLOAD else SLOAD` >>
  qabbrev_tac `w = if tr then tload a s else sload a s` >>
  `(opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
   (opc = TLOAD ==> key_taint tn.t_trans a = {})` by
    (Cases_on `tr`
     >- (gvs[Abbr `opc`, slot_loc_def] >>
         irule located_transient_base_key_clean >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     gvs[Abbr `opc`, slot_loc_def] >>
     irule located_storage_base_key_clean >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `step_inst_base (mk_inst sm.cs_next_id opc [p.ptr_operand] [out]) s =
    OK (update_var out w s)` by
    (Cases_on `tr` >> simp[Abbr `opc`, Abbr `w`, step_inst_base_def,
                           mk_inst_def, exec_read1_def] >> gvs[]) >>
  qexistsl [`v`,
    `step_prov PG G (mk_inst sm.cs_next_id opc [p.ptr_operand] [out])
      (update_var out w s)`,
    `step_taint (mk_inst sm.cs_next_id opc [p.ptr_operand] [out]) s
      (update_var out w s) tn`,
    `update_var out w s with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- simp[] >>
  irule nonmemory_word_read_continuation >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`a`, `opc`, `p`, `sm`] >> simp[] >>
  Cases_on `tr` >> gvs[Abbr `opc`, Abbr `w`, slot_loc_def] >> metis_tac[]
QED
