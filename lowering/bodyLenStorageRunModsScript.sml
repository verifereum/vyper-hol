(* Len reads one live storage header slot, in either store. *)
Theory bodyLenStorageRunMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullHashKeccakFixed
  bodyPtrDefs bodyBinopFragMemory bodyPtrEnvBuiltinsEdges exprSimLen
  decoderNavigationPtr decoderGhostFramePtr emitHelperProps exprLoweringProps
  instMemFrontier memSafeRun ptrSafeRun ptrDiscipline accountsRelProps
  contextCodegenRel codegenRel builtinSimple context loweringPosts
  transientLockProps venomExecSemantics venomInst venomState
  stmtReasonLitFragMemory loweringStateRelDefs
  finite_map pred_set words list arithmetic prim_rec

Theorem len_storage_header_untainted[local]:
  vv_location vv = SOME (slot_loc tr) /\ ptr_vv_ok cx ty tv vv ee G tn t /\
  eval_operand (vv_operand vv) t = SOME w /\
  evaluate_type (get_tenv cx) ty = SOME pvt /\ is_sized_type ty ==>
  op_taint tn (vv_operand vv) = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) w = {}
Proof
  strip_tac >>
  `0 < type_slot_size pvt` by
    (drule sized_type_cases >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def,AllCaseEqs(),vyperValueTheory.type_slot_size_def]) >>
  Cases_on `vv` >> gvs[vv_location_def,vv_operand_def,ptr_vv_ok_def] >>
  simp[key_taint_def,EXTENSION] >> gen_tac >> Cases_on `x < 32` >> simp[] >>
  qpat_x_assum `!k b. _ ==> _` (qspecl_then [`w`,`x`] mp_tac) >>
  Cases_on `tr` >> simp[slot_loc_def] >>
  metis_tac[cj 1 accountsRelPropsTheory.dead_bytes_range,LESS_REFL]
QED

Theorem len_storage_load_step[local]:
  eval_operand a t = SOME w ==>
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [a] [x]) t =
    OK (update_var x (if tr then tload w t else sload w t) t)
Proof
  strip_tac >> Cases_on `tr`
  >- (simp[] >> irule step_TLOAD >> simp[]) >>
  simp[] >> irule step_SLOAD >> simp[]
QED

Theorem len_storage_ptr_guard[local]:
  eval_operand a t = SOME w /\ op_taint tn a = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst id (if tr then TLOAD else SLOAD) [a] [x]) t
Proof
  strip_tac >>
  drule_then (qspecl_then [`x`,`tr`,`id`] assume_tac) len_storage_load_step >>
  Cases_on `tr` >> fs[mk_inst_def] >>
  simp[ptr_inst_ok_def,access_ok_def,taint_ok_def,mk_inst_def,
       source_memory_read_ranges_def,source_memory_write_ranges_def,
       step_inst_non_invoke,update_var_def]
QED

Theorem len_storage_load_path[local]:
  let i = mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD) [a] [x];
      u = update_var x (n2w n) t in
  sb.cs_current_bb = sm.cs_current_bb /\ sb.cs_current_insts = sm.cs_current_insts ++ [i] /\
  fn_has_code sm sb func /\ ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ eval_operand a t = SOME w /\
  (if tr then tload w t else sload w t) = n2w n /\
  op_taint tn a = {} /\ allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
    (OK (u with vs_inst_idx := SUC t.vs_inst_idx),step_prov PG G i u,step_taint i t u tn)
Proof
  simp[LET_THM] >> strip_tac >>
  qpat_assum `t.vs_inst_idx = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule navigation_instruction_origin >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD) [a] [x]) t` by
    (irule len_storage_ptr_guard >> simp[] >> qexists_tac `w` >> simp[]) >>
  drule_then (qspecl_then [`x`,`tr`,`sm.cs_next_id`] assume_tac) len_storage_load_step >>
  Cases_on `tr` >> fs[mk_inst_def] >>
  simp[mk_inst_def,is_terminator_def,below_frontier_no_ranges,
       unitTransformDefsTheory.dalloca_no_wrap_def] >>
  qexistsl [`sm`,`sb`] >> simp[]
QED

Theorem len_storage_step_frame[local]:
  let i = mk_inst id (if tr then TLOAD else SLOAD) [a] [x];
      u = update_var x (n2w n) t;
      G2 = step_prov PG G i u;
      tn2 = step_taint i t u tn in
  eval_operand a t = SOME w /\ key_taint (if tr then tn.t_trans else tn.t_stor) w = {} ==>
  op_taint tn2 (Var x) = {} /\ op_prov G2 (Var x) = NONE /\
  (!q. q <> x ==> FLOOKUP G2 q = FLOOKUP G q /\
                   op_taint tn2 (Var q) = op_taint tn (Var q)) /\
  tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  simp[LET_THM] >> strip_tac >>
  conj_tac >-
    (Cases_on `tr` >> fs[step_taint_def,op_taint_def,set_var_taint_def,
                          out_taint_def,mk_inst_def,FLOOKUP_UPDATE]) >>
  conj_tac >-
    (Cases_on `tr` >> simp[step_prov_def,op_prov_def,out_prov_def,
                            set_prov_def,mk_inst_def,FLOOKUP_DRESTRICT]) >>
  conj_tac >-
    (simp[step_prov_other_output,step_taint_other_output,mk_inst_def]) >>
  conj_tac >-
    (irule step_taint_no_memory_effect >>
     Cases_on `tr` >> simp[mk_inst_def,update_var_def,source_memory_write_ranges_def,written_taint_def]) >>
  Cases_on `tr` >> simp[step_taint_nonmemory_frame,mk_inst_def]
QED

Theorem len_storage_slice_history[local]:
  fn_has_code sm sb func /\ sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ [i] /\ i.inst_opcode <> ALLOCA /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t ==>
  alloca_history func ((update_var x v t) with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> drule_all_then strip_assume_tac fn_has_code_code >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_assum `t.vs_inst_idx = _`
    (fn th => pure_rewrite_tac [GSYM th]) >>
  `SUC t.vs_inst_idx = t.vs_inst_idx + LENGTH [i]` by simp[] >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  irule alloca_history_no_alloca_slice >>
  simp[update_var_def] >>
  Cases_on `DROP (LENGTH sm.cs_current_insts) bb.bb_instructions` >> fs[]
QED

Theorem len_storage_run_mods:
  vv_location vv = SOME (slot_loc tr) /\
  compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
    (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
  fn_has_code sm sb func /\ ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
  ghost_inv_at_mods DH lo d cenv cx ee G tn t /\
  is_sized_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
  eval_operand (vv_operand vv) t = SOME w /\
  (if tr then tload w t else sload w t) = n2w n ==>
  ?z G2 tn2.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2)) /\
    eval_operand op z = SOME (n2w n) /\ op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (alloca_history func t ==> alloca_history func z) /\
    z = t with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  strip_tac >>
  `emit_op (if tr then TLOAD else SLOAD) [vv_operand vv] sm = (op,sb)` by
    (qpat_x_assum `compile_builtin_len _ _ _ _ _ = _` mp_tac >>
     Cases_on `tr` >> fs[compile_builtin_len_def,compile_ptr_load_def,slot_loc_def]) >>
  drule_all_then strip_assume_tac len_storage_header_untainted >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  `stmt_state_rel H ctx func cenv cx ee t` by fs[vv_post_mods_def] >>
  drule_then assume_tac (SPEC_ALL stmt_state_rel_allocas_below_fmp) >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `x = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD) [vv_operand vv] [x]` >>
  qabbrev_tac `u = update_var x (n2w n) t` >>
  `!q. not_fresh_at sm q ==> q <> x` by
    (simp[not_fresh_at_def,Abbr `x`] >> metis_tac[LESS_EQ_REFL]) >>
  qexistsl [`u with vs_inst_idx := SUC t.vs_inst_idx`, `step_prov PG G i u`, `step_taint i t u tn`] >>
  conj_tac >-
    (simp[Abbr `u`,Abbr `i`] >> gen_tac >>
     irule (SIMP_RULE (srw_ss()) [LET_THM] len_storage_load_path) >>
     simp[] >>
     qexists_tac `sb` >> simp[]) >>
  `i.inst_opcode <> ALLOCA` by (Cases_on `tr` >> simp[Abbr `i`,mk_inst_def]) >>
  `alloca_history func t ==> alloca_history func (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (simp[Abbr `u`] >> strip_tac >>
     qpat_assum `t.vs_inst_idx = _`
       (fn th => pure_rewrite_tac [GSYM th]) >>
     irule len_storage_slice_history >>
     simp[] >> qexistsl [`i`,`sb`,`sm`] >> simp[]) >>
  `op_taint
       (step_taint (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
          [vv_operand vv] [x]) t (update_var x (n2w n) t) tn) (Var x) = {} /\
   op_prov
       (step_prov PG G
          (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
             [vv_operand vv] [x]) (update_var x (n2w n) t)) (Var x) = NONE /\
   (!q. q <> x ==> FLOOKUP
       (step_prov PG G
          (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
             [vv_operand vv] [x]) (update_var x (n2w n) t)) q = FLOOKUP G q /\
       op_taint
          (step_taint (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
             [vv_operand vv] [x]) t (update_var x (n2w n) t) tn) (Var q) =
       op_taint tn (Var q)) /\
   (step_taint (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
       [vv_operand vv] [x]) t (update_var x (n2w n) t) tn).t_mem = tn.t_mem /\
   (step_taint (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
       [vv_operand vv] [x]) t (update_var x (n2w n) t) tn).t_stor = tn.t_stor /\
   (step_taint (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
       [vv_operand vv] [x]) t (update_var x (n2w n) t) tn).t_trans = tn.t_trans /\
   (step_taint (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
       [vv_operand vv] [x]) t (update_var x (n2w n) t) tn).t_imm = tn.t_imm` by
    (irule (SIMP_RULE (srw_ss()) [LET_THM] len_storage_step_frame) >>
     simp[]) >>
  fs[Abbr `i`,Abbr `u`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  conj_tac >-
    (qpat_assum `t.vs_inst_idx = _`
       (fn th => pure_rewrite_tac [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `x <> x'` by metis_tac[] >>
  qpat_assum `!q. q <> x ==> _`
    (qspecl_then [`x'`] strip_assume_tac) >>
  simp[FLOOKUP_UPDATE]
QED
