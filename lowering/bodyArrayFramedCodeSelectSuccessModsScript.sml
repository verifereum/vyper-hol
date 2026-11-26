(* Successful linked runtime-code array selection. *)
Theory bodyArrayFramedCodeSelectSuccessMods
Ancestors
  bodyArrayFramedCodeSelectInputsDefsMods bodyArrayNoCopyCutsMods
  bodySubscriptArrayRouteDefsMods bodyArrayNoCopySourceMods
  bodyArrayFramedCodeBaseMods bodyArrayFramedCodeFixedMods
  bodyArrayFramedCodeDynamicMods bodyArrayFramedCodeLengthMods
  bodyArrayFramedCodeSelectedMods bodyAssignNameLinkedSetup
  exprSimSubscriptArraySource exprSimSubscriptArrayFramed exprSimSubscriptArraySuffix
  exprWordOperand exprSimHypsDefs exprBodyPreProps bodyPtrDefs exprSimSource
  exprSimArrayIndex exprSimCopy exprLoweringProps
  bodyFullPostsMods bodyFullPredsMods gasOutcomeFullPostMods
  fragExec fragGasOriginPtr fragGasOriginPtrLoop ptrDiscipline freshWrites
  compileEnv context vyperInterpreter vyperState vyperAST vyperTypeSystem
  vyperTypeSoundness vyperPlaceTyping vyperTypeEvalCaseProofs vyperTypeConstantFold
  vyperTyping vyperValueOperation vyperTypeInvariants vyperArray vyperStorageFootprint
  integer_word words finite_map

Theorem framed_code_select_valid_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  subscript_array_framed_code_case_mods cenv cx obj idx bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  framed_code_select_inputs_mods cenv cx env ty obj idx ann et bd
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni)
    p etv av i iw w /\
  valid_index (ArrayTV etv bd) av i ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0
    (es,s0,G0,tn0) (sa,sb,dst,LocCode) (raw,IntV i) (fin,it,Gi,tni)
Proof
  strip_tac >>
  qhdtm_x_assum `framed_code_select_inputs_mods`
    (strip_assume_tac o REWRITE_RULE [framed_code_select_inputs_mods_def]) >>
  drule_all_then (qx_choosel_then [`p0`,`etv0`,`av0`,`w0`] strip_assume_tac)
    framed_code_reached_base_mods >>
  `~subscript_reads_base cx obj idx /\ ~cenv.ce_is_ctor` by
    fs[subscript_array_framed_code_case_mods_def] >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  `eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid) /\
   lower_value compile_expr cenv ty idx sm = (iop,st2) /\
   ptr_val_ok cx (post_value_type cenv idx) key iop Gi tni it /\
   storage_trace_domain cx st0 fin.storage_trace /\
   (!v. raw = Value v /\ ~is_word_type (post_value_type cenv obj) /\
        ~is_bytestring_type (post_value_type cenv obj) ==>
        vv_own cenv cx (post_value_type cenv obj) sa sm mid raw bvv s /\
        !t p. bvv = LocatedValue t p ==> p.ptr_location = LocMemory)` by
    (qhdtm_assum `array_nocopy_cut_mods`
       (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >> asm_rewrite_tac[]) >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  qhdtm_x_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  `post_value_type cenv obj = ArrayT et bd` by simp[] >>
  qpat_x_assum `bvv = LocatedValue _ p` SUBST_ALL_TAC >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `i = if _ then _ else _` (fn ieq =>
    qpat_x_assum `valid_index (ArrayTV etv bd) av i` (fn ok =>
      gvs[] >> assume_tac ieq >> assume_tac ok)) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `vv_place_ptr_mods cenv cx fin it raw (LocatedValue (ArrayT et bd) p)` by
    (qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  suspend "typed_place"
QED

Resume framed_code_select_valid_mods[typed_place]:
  `?owner id path. raw = PlaceR (ImmutablePlace owner id path)` by
    (Cases_on `raw` >-
       gvs[is_word_type_def, is_bytestring_type_def, read_result_def] >-
       (Cases_on `p'` >> gvs[vv_place_ptr_mods_def, loweringPostsTheory.vv_place_ptr_def]) >-
       gvs[read_result_def, raise_def]) >>
  qpat_x_assum `raw = PlaceR (ImmutablePlace _ _ _)` SUBST_ALL_TAC >>
  `env.type_defs = get_tenv cx /\
   eval_result_typed (env,cx,mid) (PlaceR (ImmutablePlace owner id path)) (Type (ArrayT et bd))` by
    (`expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs1)` by simp[] >>
     qpat_x_assum `expr_sim_inv_mods _ _ _ _ (es with gas_obs := gs1)`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     drule_then assume_tac env_consistent_type_defs_get_tenv >>
     drule_all_then strip_assume_tac typed_expr_success_preserves_type >>
     qpat_assum `expr_type obj = ArrayT et bd` (fn ty_eq =>
       qhdtm_assum `eval_result_typed` (assume_tac o REWRITE_RULE [ty_eq])) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `runtime_place_typed cx mid (ImmutablePlace owner id path) (ArrayTV etv bd)` by
    (qhdtm_assum `eval_result_typed` (mp_tac o REWRITE_RULE [eval_result_typed_def]) >>
     qpat_assum `env.type_defs = get_tenv cx` (fn tenv =>
       qpat_assum `evaluate_type (get_tenv cx) (ArrayT et bd) = SOME _`
         (fn ty_eq => PURE_REWRITE_TAC [tenv,ty_eq])) >> simp[]) >>
  `runtime_place_typed cx fin (ImmutablePlace owner id path) (ArrayTV etv bd)` by
    (qpat_x_assum `runtime_place_typed cx mid _ (ArrayTV etv bd)` mp_tac >>
     Cases_on `ALOOKUP mid.immutables cx.txn.target` >>
     simp[runtime_place_typed_immutable,get_immutables_def,get_address_immutables_def,
          lift_option_type_def,bind_def,return_def,raise_def]) >>
  drule_then (qx_choose_then `v` assume_tac)
    (REWRITE_RULE [optionTheory.IS_SOME_EXISTS] array_index_valid) >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_array_subscript_result] >>
  drule_all select_typed_immutable_read >>
  disch_then (qspec_then `ArrayT et bd` strip_assume_tac) >>
  suspend "machine_setup"
QED

Resume framed_code_select_valid_mods[machine_setup]:
  qabbrev_tac `child = PlaceR (ImmutablePlace owner id (path ++ [ValueSubscript (IntV i)]))` >>
  `!tail. select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace owner id path))
       (ValueSubscript (IntV i)) (fin with gas_obs := tail) =
       (INL child,fin with gas_obs := tail)` by
    (qpat_assum `select_result _ _ _ _ fin = _`
       (fn th => simp[select_result_nonstorage_gas_obs,th])) >>
  `well_formed_type_value etv` by
    (drule_then ACCEPT_TAC vyperTypeValuesTheory.evaluate_type_well_formed_type_value) >>
  `value_has_type etv v` by
    (irule vyperAssignPreservesTypeTheory.array_index_has_type >>
     simp[] >> qexistsl_tac [`av`,`bd`,`i`] >> asm_rewrite_tac[]) >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by simp[valueEncodingTypingTheory.value_has_type_val_wf] >>
  drule_all_then assume_tac array_element_step_offset >>
  `0 <= i` by (qpat_x_assum `valid_index _ _ _` mp_tac >> simp[NoAsms,valid_index_def]) >>
  `Num i = w2n iw` by
    (Cases_on `is_signed_type (expr_type idx)` >>
     gvs[overflowElimHelpersTheory.nonneg_w2i_eq_w2n]) >>
  `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (array_length (ArrayTV etv bd) av))` by
    fs[valid_index_def] >>
  `is_int_type (expr_type idx)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  `is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> gvs[] >> rename1 `is_int_type (BaseT bt)` >>
     Cases_on `bt` >> gvs[is_word_type_def]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `elem_size_in_location cenv LocCode et = type_memory_size etv` by
    (qpat_assum `evaluate_type (get_tenv cx) et = SOME etv`
       (mp_then (Pat `evaluate_type _ _ = _`) drule assign_name_memory_bytes_mods) >>
     simp[elem_size_in_location_def,is_slot_addressed_def]) >>
  `op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = NONE /\
   val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n w) it.vs_data_section /\
   w2n w + type_memory_size (ArrayTV etv bd) <= LENGTH it.vs_data_section` by
    (drule_all framed_code_reached_view_mods >> strip_tac >> gvs[]) >>
  `(!x. iop = Var x ==> not_fresh_at st2 x) /\ (!l. iop <> Label l)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ idx mid`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     drule_then assume_tac expr_sim_inv_mods_env >>
     `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
       (simp[well_formed_type_def] >> rpt strip_tac >>
        drule_all_then ACCEPT_TAC env_consistent_var_type_evaluates) >>
     drule_all_then strip_assume_tac lower_value_word_shape >> simp[]) >>
  suspend "compile_cut"
QED

Resume framed_code_select_valid_mods[compile_cut]:
  `!x. p.ptr_operand = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> qpat_assum `!x. p.ptr_operand = Var x ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `fn_has_code st2 sb func /\ ~it.vs_halted /\
   it.vs_current_bb = st2.cs_current_bb /\ it.vs_inst_idx = LENGTH st2.cs_current_insts /\
   local_ptrs_reserved cenv st2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp it) /\
   compile_array_subscript p.ptr_operand iop
     (case bd of Fixed _ => F | Dynamic _ => T) (case bd of Fixed n => n | Dynamic _ => 0)
     32 (type_memory_size etv) (is_signed_type (expr_type idx))
     (compile_ptr_load F cenv.ce_imm_alloca LocCode) st2 = (dst,sb)` by
    (qhdtm_assum `array_nocopy_cut_mods`
      (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
     qpat_x_assum `LocCode = (case vv_location _ of NONE => _ | SOME l => l)` kall_tac >>
     `cenv.ce_is_ctor = F` by simp[] >>
     qpat_assum `cenv.ce_is_ctor = F` (fn ctor =>
       qpat_assum `elem_size_in_location cenv LocCode et = _` (fn bytes =>
         qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
           (assume_tac o REWRITE_RULE [ctor,bytes,vv_operand_def,word_scale_def]))) >>
     asm_rewrite_tac[] >> strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> _ /\ _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  Cases_on `bd` >- suspend "fixed" >> suspend "dynamic"
QED

Resume framed_code_select_valid_mods[fixed]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >> fs[value_has_type_def,array_length_def]) >>
  `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)` by fs[] >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  drule_all (INST_TYPE [alpha |-> ``:256``] framed_code_fixed_address_mods) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac)) >>
  `mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
   SOME (w2n iw * type_memory_size etv,etv)` by
    (qpat_assum `mem_step_offset _ _ = _` mp_tac >> simp[]) >>
  `!H : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx fin it ==> stmt_state_rel H ctx func cenv cx fin sf` by
    (rpt strip_tac >> first_assum irule >> asm_rewrite_tac[]) >>
  `!D. allocas_from lo it ==>
       gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (it,Gi,tni) [] (OK sf,Gf,tnf)` by
    (rpt strip_tac >> first_assum irule >> simp[]) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  drule framed_code_selected_endpoint_mods >> disch_then irule >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexistsl_tac [`Gf`,`av`,`child`,`etv`,`w2n iw * type_memory_size etv`,`sf`,`tnf`,`v`,`w`] >>
      asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
  qexists `env` >> asm_rewrite_tac[]
QED

Resume framed_code_select_valid_mods[dynamic]:
  `?len sl sk.
    compile_imm_load_word F cenv.ce_imm_alloca p.ptr_operand st2 = (len,sl) /\
    array_bounds_check iop len (is_signed_type (expr_type idx)) sl = ((),sk) /\
    array_elem_ptr p.ptr_operand iop T 32 (type_memory_size etv) sk = (dst,sb)` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_array_subscript_split,comp_bind_def,comp_ignore_bind_def,compile_ptr_load_def] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[oneTheory.one]) >>
  `ci_mono st2 sl` by
    (qspecl_then [`F`,`cenv.ce_imm_alloca`,`LocCode`,`p.ptr_operand`,`st2`] mp_tac
       ci_mono_compile_ptr_load >> simp[compile_ptr_load_def]) >>
  `ci_mono sl sk` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     Cases_on `is_signed_type (expr_type idx)` >>
     simp[array_bounds_check_def,array_bounds_valid_def] >>
     rpt (irule ci_mono_bind >> conj_tac >> rpt gen_tac >>
          simp[NoAsms,ci_mono_emit_op,ci_mono_emit_void,ci_mono_comp_return])) >>
  `ci_mono sk sb` by
    (qpat_assum `array_elem_ptr _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[NoAsms,array_elem_ptr_def] >>
     rpt (irule ci_mono_bind >> conj_tac >> rpt gen_tac >>
          simp[NoAsms,ci_mono_emit_op,ci_mono_comp_return])) >>
  `cs_extends st2 sl /\ cs_extends sl sk /\ cs_extends sk sb` by fs[ci_mono_def] >>
  `cs_extends sl sb` by (irule cs_extends_trans >> qexists `sk` >> simp[]) >>
  qspecl_then [`st2`,`sl`,`sb`,`func`] (drule_all_then strip_assume_tac) fn_has_code_split >>
  qspecl_then [`sl`,`sk`,`sb`,`func`] (drule_all_then strip_assume_tac) fn_has_code_split >>
  drule_all (INST_TYPE [alpha |-> ``:256``] framed_code_dynamic_length_mods) >>
  disch_then (qspecl_then [`PG`,`Gi`]
    (qx_choosel_then [`Gl`,`tnl`,`il`] strip_assume_tac)) >>
  `copy_old_operand st2 p.ptr_operand /\ copy_old_operand st2 iop` by
    simp[copy_old_operand_def] >>
  `eval_operand p.ptr_operand il = SOME w /\ op_taint tnl p.ptr_operand = {} /\
   op_prov Gl p.ptr_operand = NONE` by
    (qpat_assum `!op. copy_old_operand st2 op /\ _ ==> _`
       (qspec_then `p.ptr_operand` mp_tac) >> simp[]) >>
  `eval_operand iop il = SOME iw /\ op_taint tnl iop = {} /\ op_prov Gl iop = NONE` by
    (qpat_assum `!op. copy_old_operand st2 op /\ _ ==> _`
       (qspec_then `iop` mp_tac) >> simp[]) >>
  `copy_old_operand sl p.ptr_operand /\ copy_old_operand sl iop` by
    (conj_tac >> irule copy_old_operand_mono >> qexists `st2` >> simp[]) >>
  `(!q. p.ptr_operand = Var q ==> not_fresh_at sl q) /\
   (!q. iop = Var q \/ len = Var q ==> not_fresh_at sl q)` by
    fs[copy_old_operand_def,DISJ_IMP_THM] >>
  `!l. iop <> Label l /\ len <> Label l` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``] framed_code_dynamic_address_mods) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac)) >>
  suspend "dynamic_finish"
QED

Resume framed_code_select_valid_mods[dynamic_finish]:
  `!D. allocas_from lo it ==>
       gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (it,Gi,tni) [] (OK sf,Gf,tnf)` by
    (rpt strip_tac >>
     `allocas_from lo il` by
       (qpat_assum `il.vs_allocas = it.vs_allocas`
          (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
        qpat_assum `allocas_from lo it` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     irule gas_origin_ptr_path_trans >> qexistsl [`Gl`,`il`,`tnl`] >>
     conj_tac >> first_assum irule >> simp[]) >>
  `local_ptrs_reserved cenv sl` by
    (irule local_ptrs_reserved_next_var >> qexists `st2` >> simp[]) >>
  `!H : (bool # bytes32 # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx fin it ==> stmt_state_rel H ctx func cenv cx fin sf` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx fin il` by
       (first_assum irule >> asm_rewrite_tac[]) >>
     first_assum irule >> asm_rewrite_tac[]) >>
  `!q. not_fresh_at st2 q ==> lookup_var q sf = lookup_var q it /\
       FLOOKUP Gf q = FLOOKUP Gi q /\ op_taint tnf (Var q) = op_taint tni (Var q)` by
    (rpt strip_tac >>
     `not_fresh_at sl q` by (irule not_fresh_at_mono >> qexists `st2` >> simp[]) >>
     qpat_assum `!q. not_fresh_at st2 q ==> lookup_var q il = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!q. not_fresh_at sl q ==> lookup_var q sf = _ /\ _` (drule_then strip_assume_tac) >>
     simp[]) >>
  `mem_step_offset (ArrayTV etv (Dynamic n)) (ValueSubscript (IntV i)) =
   SOME (32 + w2n iw * type_memory_size etv,etv)` by
    (qpat_assum `mem_step_offset _ _ = _` mp_tac >> simp[]) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  drule framed_code_selected_endpoint_mods >> disch_then irule >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexistsl [`Gf`,`av`,`child`,`etv`,`32 + w2n iw * type_memory_size etv`,`sf`,`tnf`,`v`,`w`] >>
      asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
  qexists `env` >> asm_rewrite_tac[]
QED
Finalise framed_code_select_valid_mods
