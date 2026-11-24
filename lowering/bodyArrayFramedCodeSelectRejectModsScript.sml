(* Reject a linked runtime-code selector without constructing a child place. *)
Theory bodyArrayFramedCodeSelectRejectMods
Ancestors
  bodyArrayFramedCodeSelectInputsDefsMods bodyArrayFramedCodeBaseMods
  bodyArrayFramedCodeLengthMods bodyArrayFramedCodeExitMods bodyArrayNoCopySourceMods
  exprSimSubscriptArraySuffix exprBodyPreProps exprBodyPreTypingProps exprWordOperand
  exprLoweringProps bodyPtrDefs vyperTypeSoundness vyperTypeConstantFold
  vyperTypeEvalCaseProofs vyperPlaceTyping vyperStorageFootprint
  vyperTypeInvariants vyperTyping vyperArray freshWrites
  exprSimSubscriptArraySource vyperInterpreter vyperState vyperTypeSystem
  exprSimSource exprSimCopy exprSimHypsDefs exprSimArrayIndex compileEnv fragExec
  bodySubscriptArrayRouteDefsMods bodyArrayNoCopyCutsMods context loweringPosts
  fragGasOriginPtr ptrDiscipline venomState vyperAST vyperValueOperation
  bodyFullShadowBodyInv
Libs
  monadsyntax

Theorem framed_code_source_oob[local]:
  eval_result_typed (env,cx,mid) raw (Type (ArrayT et bd)) /\
  env.type_defs = get_tenv cx /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  ~valid_index (ArrayTV etv bd) av i ==>
  !tail. select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i))
        (fin with gas_obs := tail) =
      (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin with gas_obs := tail)
Proof
  strip_tac >>
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (Cases_on `bd` >> simp[] >> rpt strip_tac >> gvs[value_has_type_def]) >>
  drule_all_then assume_tac evaluate_array_subscript_oob >>
  qpat_x_assum `~valid_index _ _ _` kall_tac >>
  `select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i)) fin =
     (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)` by
    (Cases_on `raw` >> gvs[eval_result_typed_def] >-
      (fs[read_result_def, return_def] >> gvs[] >>
       drule_then (qspecl_then [`ArrayV av`,`ValueSubscript (IntV i)`,`fin`] mp_tac)
         select_value_result >> simp[bind_def,lift_sum_def,raise_def]) >>
     irule select_nonstorage_place_error >> simp[] >>
     qexists `ArrayTV etv bd` >> simp[] >>
     Cases_on `p` >> gvs[runtime_place_typed_memory] >>
     qpat_x_assum `runtime_place_typed _ mid _ _` mp_tac >>
     Cases_on `ALOOKUP mid.immutables cx.txn.target` >>
     simp[runtime_place_typed_immutable,get_immutables_def,
          get_address_immutables_def,bind_def,ignore_bind_def,return_def,raise_def]) >>
  gen_tac >>
  qpat_assum `select_result _ _ _ _ fin = _`
    (fn th => simp[select_result_nonstorage_gas_obs, th])
QED

Theorem framed_code_reject_index_shape[local]:
  expr_body_pre_mods mods cenv cx env idx mid /\
  is_word_type (expr_type idx) /\
  lower_value compile_expr cenv ty idx sm = (iop,st2) ==>
  copy_old_operand st2 iop /\ (!l. iop <> Label l)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC env_consistent_var_type_evaluates) >>
  drule_all_then strip_assume_tac lower_value_word_shape >> simp[copy_old_operand_def]
QED

Theorem framed_code_reject_source_type[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env obj /\
  call_evaluation_safe cx (int_calls_expr obj) /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) ==>
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,mid) raw (Type (expr_type obj))
Proof
  strip_tac >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs)` by simp[] >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ (es with gas_obs := gs)`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all_then strip_assume_tac typed_expr_success_preserves_type >> simp[]
QED

Theorem framed_code_reject_compiler_cuts[local]:
  (!st op st'. loader bop st = (op,st') ==> cs_extends st st') /\
  compile_array_subscript bop iop dyn n ws esz sgn loader sa = (dst,sb) /\
  fn_has_code sa sb func ==>
  ?len sh sk.
    (if dyn then loader bop else comp_return (Lit (n2w n))) sa = (len,sh) /\
    array_bounds_check iop len sgn sh = ((),sk) /\
    fn_has_code sa sh func /\ fn_has_code sh sk func
Proof
  strip_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split,comp_bind_def,comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  rename1 `array_bounds_check iop len sgn sh = ((),sk)` >>
  `cs_extends sa sh` by (Cases_on `dyn` >> gvs[comp_return_def,cs_extends_refl]) >>
  `ci_mono sh sk` by
    (qpat_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
     qsuff_tac `ci_mono sh (SND (array_bounds_check iop len sgn sh))` >- simp[] >>
     Cases_on `sgn` >> simp[NoAsms,array_bounds_check_def,array_bounds_valid_def] >>
     rpt (irule ci_mono_bind >> conj_tac >> rpt gen_tac >>
          simp[NoAsms,ci_mono_emit_op,ci_mono_emit_void,ci_mono_comp_return])) >>
  `ci_mono sk sb` by
    (qpat_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     qsuff_tac `ci_mono sk (SND (array_elem_ptr bop iop dyn ws esz sk))` >- simp[] >>
     Cases_on `dyn` >> simp[NoAsms,array_elem_ptr_def] >>
     rpt (irule ci_mono_bind >> conj_tac >> rpt gen_tac >>
          simp[NoAsms,ci_mono_emit_op,ci_mono_comp_return])) >>
  `cs_extends sh sk /\ cs_extends sk sb` by fs[ci_mono_def] >>
  `cs_extends sh sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sh func /\ fn_has_code sh sb func` by
    (qspecl_then [`sa`,`sh`,`sb`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sh sk func` by
    (qspecl_then [`sh`,`sk`,`sb`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem framed_code_select_invalid_mods:
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
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) p etv av i iw w /\
  ~valid_index (ArrayTV etv bd) av i ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0 (es,s0,G0,tn0) (sa,sb,dst,loc)
    (raw,key) (fin,it,Gi,tni)
Proof
  strip_tac >>
  qhdtm_x_assum `framed_code_select_inputs_mods`
    (strip_assume_tac o REWRITE_RULE [framed_code_select_inputs_mods_def]) >>
  `~subscript_reads_base cx obj idx /\ ~cenv.ce_is_ctor` by
    fs[subscript_array_framed_code_case_mods_def] >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  `eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid) /\
   lower_value compile_expr cenv ty idx sm = (iop,st2) /\
   ptr_val_ok cx (post_value_type cenv idx) key iop Gi tni it` by
    (qhdtm_assum `array_nocopy_cut_mods`
      (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >> asm_rewrite_tac[]) >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  drule_all_then strip_assume_tac framed_code_reject_source_type >>
  `expr_type obj = ArrayT et bd /\ is_int_type (expr_type idx)` by
    (qhdtm_assum `linked_subscript_array_context_mods`
       (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
     drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  `is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> gvs[] >> rename1 `is_int_type (BaseT bt)` >>
     Cases_on `bt` >> gvs[is_word_type_def]) >>
  drule_all_then strip_assume_tac framed_code_reject_index_shape >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  suspend "routes"
QED

Resume framed_code_select_invalid_mods[routes]:
  `fin.scopes = mid.scopes /\ fin.immutables = mid.immutables` by
    (drule_all framed_code_reached_base_mods >> rw[]) >>
  `eval_result_typed (env,cx,mid) raw (Type (ArrayT et bd))` by fs[] >>
  drule_all_then assume_tac framed_code_source_oob >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw (n2w (array_length (ArrayTV etv bd) av))` by
    metis_tac[] >>
  qpat_x_assum `~valid_index _ _ _` kall_tac >>
  qpat_x_assum `valid_index _ _ _ <=> _` kall_tac >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `cenv.ce_is_ctor = F` by simp[] >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  `fn_has_code st2 sb func /\ ~it.vs_halted /\
   it.vs_current_bb = st2.cs_current_bb /\ it.vs_inst_idx = LENGTH st2.cs_current_insts /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp it) /\
   storage_trace_domain cx st0 fin.storage_trace /\
   compile_array_subscript p.ptr_operand iop
     (case bd of Fixed _ => F | Dynamic _ => T) (case bd of Fixed n => n | Dynamic _ => 0)
     (word_scale LocCode) (elem_size_in_location cenv LocCode et) (is_signed_type (expr_type idx))
     (compile_ptr_load F cenv.ce_imm_alloca LocCode) st2 = (dst,sb)` by
    (qhdtm_assum `array_nocopy_cut_mods`
      (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
     qpat_x_assum `LocCode = (case vv_location _ of NONE => _ | SOME l => l)` kall_tac >>
     qpat_assum `cenv.ce_is_ctor = F` (fn ctor =>
       qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
         (assume_tac o REWRITE_RULE [ctor,vv_operand_def])) >>
     simp[IMP_CONJ_THM]) >>
  `!st op st'. compile_ptr_load F cenv.ce_imm_alloca LocCode p.ptr_operand st = (op,st') ==>
      cs_extends st st'` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`F`,`cenv.ce_imm_alloca`,`LocCode`,`p.ptr_operand`,`st`]
              ci_mono_compile_ptr_load) >> simp[ci_mono_def]) >>
  drule_all_then (qx_choosel_then [`len`,`sh`,`sk`] strip_assume_tac)
    framed_code_reject_compiler_cuts >>
  Cases_on `bd` >- suspend "fixed" >> suspend "dynamic"
QED

Resume framed_code_select_invalid_mods[fixed]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >> fs[value_has_type_def,array_length_def]) >>
  qpat_x_assum `(if _ then _ else _) st2 = (len,sh)` mp_tac >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  `!D. allocas_from lo it ==>
       gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (it,Gi,tni) [] (OK it,Gi,tni)` by simp[Once gas_origin_ptr_path_rules] >>
  drule framed_code_bounds_exit_mods >>
  disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gi`,`iw`,`n2w n`,`Lit (n2w n)`,`sh`,`sk`,`it`,`tni`] >>
  simp[op_prov_def,op_taint_def,eval_operand_def] >>
  fs[copy_old_operand_def]
QED

Resume framed_code_select_invalid_mods[dynamic]:
  rename1 `value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av)` >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  `op_taint tni p.ptr_operand = {} /\
   val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV av) (w2n w) it.vs_data_section /\
   w2n w + type_memory_size (ArrayTV etv (Dynamic cap)) <= LENGTH it.vs_data_section` by
    (drule_all_then (qx_choosel_then [`p'`,`etv'`,`av'`,`w'`] strip_assume_tac)
       framed_code_reached_base_mods >>
     gvs[] >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_all_then strip_assume_tac framed_code_reached_view_mods >> gvs[]) >>
  qpat_x_assum `(if _ then _ else _) st2 = (len,sh)` mp_tac >>
  simp[compile_ptr_load_def] >> strip_tac >>
  drule_all framed_code_dynamic_length_mods >>
  disch_then (qspecl_then [`PG`,`Gi`]
    (qx_choosel_then [`Gl`,`tnl`,`sl`] strip_assume_tac)) >>
  `eval_operand iop sl = SOME iw /\ op_taint tnl iop = {} /\ op_prov Gl iop = NONE` by
    (qpat_assum `!op. copy_old_operand st2 op /\ _ ==> _`
       (qspec_then `iop` mp_tac) >> simp[]) >>
  `copy_old_operand sh iop` by
    (irule copy_old_operand_mono >> qexists `st2` >> simp[]) >>
  `!q. iop = Var q \/ len = Var q ==> not_fresh_at sh q` by
    fs[copy_old_operand_def,DISJ_IMP_THM] >>
  `!D. allocas_from lo it ==>
       gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (it,Gi,tni) [] (OK sl,Gl,tnl)` by
    (gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  drule framed_code_bounds_exit_mods >> disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gl`,`iw`,`n2w (array_length (ArrayTV etv (Dynamic cap)) av)`,
            `len`,`sh`,`sk`,`sl`,`tnl`] >> simp[] >> first_assum ACCEPT_TAC
QED
Finalise framed_code_select_invalid_mods
