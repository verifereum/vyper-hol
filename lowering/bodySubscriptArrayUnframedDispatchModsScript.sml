(* Dispatch a non-reading array subscript at the actual base and key cuts. *)
Theory bodySubscriptArrayUnframedDispatchMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodyFullPredsMods bodyFullPostsMods
  bodyArrayNoCopySourceMods bodyArrayNoCopyCodeMods bodyArrayNoCopyBindMods
  bodyArrayNoCopyCutsMods bodyArraySlotBaseVVMods bodyFullIfExpReach
  bodyArraySelectSlotMods bodyArraySelectCapturedMods bodyArraySelectMemoryMods
  bodyArraySelectValueMods bodyArraySubscriptReadMods
  compileEnv exprLowering vyperAST vyperState vyperInterpreter context
  venomExecSemantics venomInst

Theorem unframed_child_sims[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >>
  qhdtm_x_assum `body_expr_full_ok_mods`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx sh fn sf ce env ty es.
                _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (irule o SPEC_ALL) >>
  simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
  qexists_tac `env` >> simp[]
QED

Theorem subscript_array_unframed_dispatch_mods:
  !mods exps cx ann obj idx DF lo d PG src tops ctx shadow_ctx func shadow_func
   cenv env ty es et bd.
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  subscript_array_unframed_case_mods cenv cx obj idx et bd /\
  (!st0 s0 G0 tn0 sa sm st2 sb bvv iop dst loc shadow_sa shadow_sm shadow_st2 shadow_sb
    gs1 mid raw s G1 tn1 gs2 fin key it Gi tni owner id path.
    array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj idx et bd st0
      (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
      (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
      (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
    raw = PlaceR (ImmutablePlace owner id path) ==>
    array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func) cenv cx ann obj idx et bd st0
      (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,key) (fin,it,Gi,tni)) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Subscript ann obj idx) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >> conj_asm2_tac
  >- (irule array_subscript_value_of_located_mods >> asm_rewrite_tac[] >>
      qexistsl_tac [`bd`,`env`,`et`,`exps`,`mods`,`src`,`tops`] >> asm_rewrite_tac[]) >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty obj es` by
    (Cases_on `array_slot_base cenv obj`
     >- (qpat_assum `array_slot_base _ _ ==> _` (drule_then strip_assume_tac) >>
         gvs[expr_type_def] >> irule array_slot_base_vv_mods >>
         rename1 `find_var_decl_by_name _ ts = SOME (StorageVarDecl tr _,id_str)` >>
         rename1 `lookup_var_slot_from_layout _ tr _ id_str = SOME slot` >>
         conj_tac >- (qexistsl_tac [`id_str`,`slot`,`tr`,`ts`,`ArrayT et bd`] >> asm_rewrite_tac[]) >>
         simp[] >> qexistsl_tac [`env`,`mods`] >> asm_rewrite_tac[]) >>
     irule (unframed_child_sims |> CONV_RULE (REWR_CONV IMP_CONJ_THM) |> cj 2) >>
     qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  `!obs raw mid. eval_expr cx obj (es with gas_obs := obs) = (INL raw,mid) ==>
     expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty idx mid` by
    (rpt gen_tac >> strip_tac >> drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
     irule (unframed_child_sims |> CONV_RULE (REWR_CONV IMP_CONJ_THM) |> cj 1) >>
     qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac array_nocopy_paired_parts_mods >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  irule (PURE_REWRITE_RULE [LET_THM] array_nocopy_children_bind_mods |> BETA_RULE) >>
  suspend "select"
QED

Resume subscript_array_unframed_dispatch_mods[select]:
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bd`,`bvv`,`et`,`iop`,`shadow_func`,`shadow_sa`,`shadow_sb`,
                `shadow_sm`,`shadow_st2`,`sm`,`st2`,`ty`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`gs1`,`mid`,`raw`,`s`,`G1`,`tn1`,`gs2`,`fin`,`key`,`it`,`Gi`,`tni`] >>
  strip_tac >>
  `eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid)` by
    (qhdtm_assum `array_nocopy_cut_mods`
      (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  Cases_on `raw`
  >- (irule array_select_value_mods >>
      qhdtm_assum `array_nocopy_cut_mods` (irule_at Any) >>
      qhdtm_assum `linked_subscript_array_context_mods` (irule_at Any) >> simp[])
  >- (rename1 `PlaceR pl` >> Cases_on `pl`
      >- (irule array_select_slot_mods >>
          qhdtm_assum `array_nocopy_cut_mods` (irule_at Any) >>
          qhdtm_assum `linked_subscript_array_context_mods` (irule_at Any) >> simp[])
      >- (Cases_on `?n. bd = vyperAST$Fixed n /\ base_from_pop obj`
          >- (pop_assum strip_assume_tac >> irule array_select_captured_mods >>
              qhdtm_assum `array_nocopy_cut_mods` (irule_at Any) >>
              qhdtm_assum `linked_subscript_array_context_mods` (irule_at Any) >> simp[]) >>
          irule array_select_memory_mods >>
          qhdtm_assum `array_nocopy_cut_mods` (irule_at Any) >>
          qhdtm_assum `linked_subscript_array_context_mods` (irule_at Any) >> fs[]) >>
      qpat_assum `!st0 s0 G0 tn0 sa sm st2 sb bvv iop dst loc shsa shsm shst2 shsb
                    gs1 mid raw s G1 tn1 gs2 fin key it Gi tni owner id path.
                 _ ==> array_select_outcome_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule o SPEC_ALL) >>
      qhdtm_assum `array_nocopy_cut_mods` (irule_at Any) >> simp[]) >>
  fs[is_HashMapRef_def]
QED

Finalise subscript_array_unframed_dispatch_mods
