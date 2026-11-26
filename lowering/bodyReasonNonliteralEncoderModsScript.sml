(* Join the reason prefix, the reached value's normalization, and the revert. *)
Theory bodyReasonNonliteralEncoderMods
Ancestors
  bodyReasonHeadUnwrapMods bodyReasonRuntimeCodeMods bodyReasonCtorCodeMods
  bodyReasonNoncodeUnwrapMods bodyCopySlotRhsRunMods bodyPtrAttributeSource
  bodyFullRaiseReasonContinuation bodyFullAbiEncodeOriginFloor
  stmtReasonLitFragMemory revertReasonLayout fragGasOriginPtrLoop fragGasOriginPtr
  exprOperandVar exprLoweringProps exprSimMemDefs exprSimProps exprSimWordArgs wordArgsPtr
  bodyFullPostsMods bodyFullShadowBodyInv loweringPosts bodyPtrDefs
  vyperTypeValues valueEncodingTyping context compileEnv venomState
  finite_map arithmetic rich_list vyperValue vyperTypeSystem valueCopyBytes
  freshWrites exprLowering gasContext vyperStorageFootprint stateRelProj
  words list loweringStateRelDefs vyperState venomMemDefs fragExec stmtReasonMemory

Theorem reason_normalized_splice[local]:
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx ee su /\
  wb_frame cenv ee ee sb sh su /\
  ghost_kept_at lo cenv ee sb Gh tnh sh Gu tu /\
  expr_val_rel cx (BaseT (StringT cap)) (StringV str) op su /\
  ptr_val_ok cx (BaseT (StringT cap)) (StringV str) op Gu tu su /\
  expr_store_bound cx (BaseT (StringT cap)) (StringV str) op su /\
  (!x. op = Var x ==> not_fresh_at sc x) /\
  val_wf (BaseTV (StringT cap)) (StringV str) /\
  evaluate_type (get_tenv cx) (BaseT (StringT cap)) = SOME (BaseTV (StringT cap)) /\
  M = type_memory_bytes cenv (BaseT (StringT cap)) /\
  64+M < dimword(:256) /\ ~su.vs_halted /\
  allocas_from lo su /\ lo <= su.vs_alloca_next /\
  su.vs_current_bb = sc.cs_current_bb /\ su.vs_inst_idx = LENGTH sc.cs_current_insts /\
  fn_has_code sc sf func /\ sf.cs_current_bb = sc.cs_current_bb /\
  sf.cs_current_insts = sc.cs_current_insts ++ reason_tail sc.cs_next_id sc.cs_next_var vn op /\
  sb.cs_next_id = id+4 /\ sb.cs_next_var = vn+3 /\
  vn+3 <= sc.cs_next_var /\ id+4 <= sc.cs_next_id /\
  (!x. not_fresh_at sb x ==> lookup_var x su = lookup_var x sh) /\
  lookup_var ("%" ++ toString vn) sh = SOME (n2w B) /\
  lookup_var ("%" ++ toString (vn+1)) sh = SOME (n2w (B+32)) /\
  lookup_var ("%" ++ toString (vn+2)) sh = SOME (n2w TP) /\
  ptr_covers Gh tnh ("%" ++ toString vn) sh (64+M) /\
  ptr_covers Gh tnh ("%" ++ toString (vn+1)) sh (32+M) /\
  ptr_covers Gh tnh ("%" ++ toString (vn+2)) sh M /\
  FLOOKUP sh.vs_allocas id = SOME (B,64+M) /\
  FLOOKUP sh.vs_allocas (id+3) = SOME (TP,M) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK sh,Gh,tnh)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sh,Gh,tnh) [] (OK su,Gu,tu)) ==>
  ?z Gf tf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort z,Gf,tf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block su.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (reason_tail sc.cs_next_id sc.cs_next_var vn op)
      (DROP su.vs_inst_idx bb.bb_instructions)` by simp[] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ su`
    (mp_then Any mp_tac reason_normalized_tail_origin_ptr) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`z`,`Gf`,`tf`] assume_tac) >>
  qexistsl_tac [`z`,`Gf`,`tf`] >> gen_tac >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gh`,`sh`,`tnh`] >>
  conj_tac >- simp[] >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`su`,`tu`] >> simp[]
QED

Theorem reason_nonliteral_encoder_origin_ptr_mods:
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_revert_with_reason cenv vv mt M sm = ((),sf) /\
  expr_type e = BaseT (StringT cap) /\
  M = type_memory_bytes cenv (BaseT (StringT cap)) /\
  64+M < dimword(:256) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sf func /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       ~is_word_type (post_value_type cenv e) ==>
       type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
       type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!vt op0. vv = StackValue vt op0 /\ ~is_word_type (post_value_type cenv e) ==>
           ptr_buf_ok cenv e op0 G s) /\
  (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
   !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?z Gf tnf. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort z,Gf,tnf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule compile_revert_reason_layout >>
  disch_then (qx_choosel_then [`sb`,`sc`,`op`] (map_every assume_tac o CONJUNCTS)) >>
  `ci_mono sb sc` by
    (qspecl_then [`cenv`,`vv`,`sb`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `cs_extends sm sb /\ cs_extends sb sc /\ cs_extends sc sf /\
   sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\
   sm.cs_next_var <= sb.cs_next_var /\
   sb.cs_next_var = sm.cs_next_var+3 /\ sb.cs_next_id = sm.cs_next_id+4` by
    (qpat_assum `ci_mono sb sc` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
     conj_tac >- simp[cs_extends_def, IS_PREFIX_APPEND] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[cs_extends_def, IS_PREFIX_APPEND] >>
     asm_rewrite_tac[] >> simp[]) >>
  `fn_has_code sm sb func /\ fn_has_code sb sc func /\ fn_has_code sc sf func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `sf.cs_current_bb = sc.cs_current_bb /\
   sf.cs_current_insts = sc.cs_current_insts ++ reason_tail sc.cs_next_id sc.cs_next_var sm.cs_next_var op` by
    simp[reason_tail_def, revert_reason_copy_def, revert_reason_suffix_def] >>
  drule_at (Pat `sb = _`) reason_head_unwrap_inputs_mods >>
  disch_then drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`sh`,`Gh`,`tnh`,`B`,`TP`] (map_every assume_tac o CONJUNCTS))) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sh`
      (drule_then assume_tac) >>
  `post_value_type cenv e = BaseT (StringT cap)` by simp[is_bytestring_type_def] >>
  `~is_word_type (post_value_type cenv e)` by simp[is_word_type_def] >>
  `rty = BaseTV (StringT cap)` by fs[evaluate_type_def] >>
  `type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
   type_memory_size rty < 2**64` by
    (qpat_assum `!rt. evaluate_type _ _ = SOME rt /\ _ ==> _` (qspec_then `rty` mp_tac) >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (drule compiler_unwrap_value_var >> Cases_on `vv` >> simp[vv_operand_def]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `?v su Gu tu. read_result cx tv ee = (INL v,ee) /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sh,Gh,tnh) [] (OK su,Gu,tu)) /\
     stmt_state_rel H0 ctx func cenv cx ee su /\
     wb_frame cenv ee ee sb sh su /\ ghost_kept_at lo cenv ee sb Gh tnh sh Gu tu /\
     (!x. not_fresh_at sb x ==> lookup_var x su = lookup_var x sh) /\
     expr_val_rel cx (post_value_type cenv e) v op su /\
     ptr_val_ok cx (post_value_type cenv e) v op Gu tu su /\
     expr_store_bound cx (post_value_type cenv e) v op su /\
     ~su.vs_halted /\ su.vs_current_bb = sc.cs_current_bb /\
     su.vs_inst_idx = LENGTH sc.cs_current_insts /\ allocas_from lo su /\ lo <= su.vs_alloca_next` by
    suspend "middle" >>
  suspend "splice"
QED

Resume reason_nonliteral_encoder_origin_ptr_mods[middle]:
  Cases_on `vv_location vv = SOME LocCode`
  >- (Cases_on `vv`
      >- fs[vv_location_def] >>
      rename1 `LocatedValue ann p` >>
      qpat_x_assum `vv_location _ = SOME LocCode`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [vv_location_def]) >>
      Cases_on `cenv.ce_is_ctor` >- suspend "ctor" >> suspend "runtime") >>
  suspend "noncode"
QED

Resume reason_nonliteral_encoder_origin_ptr_mods[splice]:
  markerLib.RESUME_TAC >>
  qpat_assum `!v. read_result _ _ _ = _ ==> value_has_type _ v`
    (qspec_then `v` (drule_then assume_tac)) >>
  qpat_x_assum `rty = BaseTV (StringT cap)` SUBST_ALL_TAC >>
  drule value_has_type_StringTV >> disch_then (qx_choose_then `str` SUBST_ALL_TAC) >>
  `val_wf (BaseTV (StringT cap)) (StringV str)` by simp[value_has_type_val_wf] >>
  `?z Gf tf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort z,Gf,tf)` suffices_by
      (rpt strip_tac >> qexistsl_tac [`z`,`Gf`,`tf`] >> simp[]) >>
  qpat_assum `post_value_type cenv e = _` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_at (Pat `wb_frame _ _ _ _ _ _`) reason_normalized_splice >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_rel _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code sc sf func`)) >>
  disch_then (drule_at (Pat `sf.cs_current_insts = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP sh.vs_allocas _ = SOME (_,64+_)`)) >>
  disch_then (drule_at (Pat `FLOOKUP sh.vs_allocas (_+3) = _`)) >>
  disch_then irule >> asm_rewrite_tac[] >> simp[]
QED

Resume reason_nonliteral_encoder_origin_ptr_mods[noncode]:
  markerLib.RESUME_TAC >>
  qpat_assum `vv_location _ <> SOME LocCode ==> _` (drule_then assume_tac) >>
  qhdtm_assum `vv_holds` (mp_then Any (qx_choosel_then [`v`,`w`] strip_assume_tac)
    attribute_vv_holds_read_operand) >>
  `value_has_type rty v` by
    (qpat_assum `!v. read_result _ _ _ = _ ==> value_has_type _ v`
      (drule_then ACCEPT_TAC)) >>
  `vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv sh` by
    (qpat_assum `post_value_type cenv e = _` SUBST1_TAC >>
     qpat_assum `expr_type e = _` (fn th =>
       qpat_assum `vv_store_bound _ (expr_type e) _ _ _ _ sh`
         (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  qpat_assum `vv_holds _ _ _ _ _ _ sh`
    (mp_then Any mp_tac reason_noncode_unwrap_normalized_from_slot_run_mods) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ sh`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ Gh tnh sh`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code sb sc func`)) >>
  disch_then (drule_at (Pat `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ sh`)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- ((rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
    >- (Cases_on `vv` >> simp[NoAsms] >> rename1 `LocatedValue ann p` >>
        qpat_x_assum `vv_location _ <> SOME LocCode` mp_tac >>
        qpat_x_assum `vv_holds _ _ _ _ _ _ sh` mp_tac >>
        Cases_on `p.ptr_location` >>
        qpat_assum `p.ptr_location = _` (fn th =>
          simp[NoAsms, th, vv_location_def, vv_holds_def])) >>
    suspend "physical")) >>
  disch_then (qx_choosel_then [`su`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v`,`su`,`Gu`,`tu`] >> simp[] >> decide_tac
QED
Resume reason_nonliteral_encoder_origin_ptr_mods[physical]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule copy_slot_rhs_run_physical_mods >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`e`,`p`,`t`,`tv`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume reason_nonliteral_encoder_origin_ptr_mods[ctor]:
  markerLib.RESUME_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [vv_operand_def, vv_location_def]) >>
  `ann = post_value_type cenv e` by
    (qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qhdtm_x_assum `vv_holds_mods` mp_tac >> simp[vv_holds_mods_def]) >>
  qpat_assum `ann = post_value_type cenv e` SUBST_ALL_TAC >>
  `type_memory_size rty < dimword(:256)` by
    (irule LESS_TRANS >> qexists `2 ** 64` >> asm_rewrite_tac[] >> simp[dimword_def]) >>
  qpat_assum `cenv.ce_is_ctor /\ SOME p.ptr_location = SOME LocCode ==> ?v. read_result cx tv ee = _ /\
    (!rty w. evaluate_type _ _ = _ /\ eval_operand _ sh = _ ==> _)` mp_tac >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  `value_has_type rty v` by
    (qpat_assum `!v. read_result _ _ _ = _ ==> value_has_type _ v` (qspec_then `v` (drule_then ACCEPT_TAC))) >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac reason_ctor_code_copy_origin_execution_mods) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ s`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ Gh tnh sh`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (qspecl_then [`rty`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choosel_then [`su`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v`,`su`,`Gu`,`tu`] >> asm_rewrite_tac[] >> simp[]
QED
Resume reason_nonliteral_encoder_origin_ptr_mods[runtime]:
  markerLib.RESUME_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [vv_operand_def]) >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac reason_runtime_code_copy_origin_execution_mods) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ sh`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ G tn s`)) >>
  simp[vv_operand_def] >>
  disch_then (qspecl_then [`tnh`,`lo`,`explicit`,`PG`,`Gh`] mp_tac) >>
  (impl_tac >- simp[vv_operand_def]) >>
  disch_then (qx_choosel_then [`v`,`su`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v`,`su`,`Gu`,`tu`] >> simp[] >> decide_tac
QED
Finalise reason_nonliteral_encoder_origin_ptr_mods
