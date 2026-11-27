(* A selected default reads the owner key at the reached caller-pinned cut. *)
Theory bodyIntCallDefaultReadCutMods
Ancestors
  bodyIntCallDefaultSelectedReadsMods
  bodyIntCallStagePacketMods immutableRegionFrameProps exprSimTopLevelImmutable
  exprSimTopLevelProps exprSimMemorySource gasShadowCompileStmtHelpers
  gasShadowState bodyQualifiedLookupPlaceMods bodyFullPostsMods bodyInvSplit
  bodyFullShadowBodyInv bodyPtrDefs context exprBodyPreProps
  vyperBareGlobalName vyperTypeInvariants vyperInterpreter vyperState

(* No forced load or allocation is asserted by this zero-code cut. *)
Definition intcall_default_read_at_mods_def[nocompute]:
  intcall_default_read_at_mods ce p es s tn lo ann owner id ts off rt v <=>
    let tv = PlaceR (ImmutablePlace owner id []) in
    let vv = LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode) in
    ALOOKUP ce.ce_modules owner = SOME ts /\
    FLOOKUP ce.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    evaluate_type (get_tenv p) ann = SOME rt /\
    off + type_memory_size rt < dimword (:256) /\
    (!tail. eval_expr p (TopLevelName ann (owner,id)) (es with gas_obs := tail) =
            (INL tv,es with gas_obs := tail)) /\
    read_result p tv es = (INL v,es) /\
    (!tail. read_result p tv (es with gas_obs := tail) = (INL v,es with gas_obs := tail)) /\
    vv_holds_mods ce p ann tv vv es s /\ vv_place_ptr_mods ce p es s tv vv /\
    immutable_value_admissible rt v /\
    (~ce.ce_is_ctor ==> off + type_memory_size rt <= LENGTH s.vs_data_section) /\
    val_in_memory rt v off (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section) /\
    (ce.ce_is_ctor ==> off + type_memory_size rt <= lo /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v off mem)
End

(* Only owner-key projections ignore the pin. No stmt_state_rel is moved. *)
Theorem default_read_owner_views[local]:
  (immutable_frame_mods func (ce with ce_module := src) p es s <=>
   immutable_frame_mods func ce p es s) /\
  (vv_holds_mods (ce with ce_module := src) p ann (PlaceR (ImmutablePlace owner id []))
       (LocatedValue ann (mk_ptr (Lit w) LocCode)) es s <=>
   vv_holds_mods ce p ann (PlaceR (ImmutablePlace owner id []))
       (LocatedValue ann (mk_ptr (Lit w) LocCode)) es s) /\
  (vv_place_ptr_mods (ce with ce_module := src) p es s (PlaceR (ImmutablePlace owner id []))
       (LocatedValue ann (mk_ptr (Lit w) LocCode)) <=>
   vv_place_ptr_mods ce p es s (PlaceR (ImmutablePlace owner id []))
       (LocatedValue ann (mk_ptr (Lit w) LocCode)))
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       loweringStateRelDefsTheory.immutables_rel_def, immutable_alloca_sep_mods_def,
       vv_holds_mods_def, vv_place_ptr_mods_def, immutable_holds_mods_def, mk_ptr_def]
QED

Theorem default_read_ctor_views[local]:
  (dead_lo_ok_mods H D lo (ce with ce_module := src) p <=>
   dead_lo_ok_mods H D lo ce p) /\
  (ghost_inv_at_mods D lo d (ce with ce_module := src) p es G tn s <=>
   ghost_inv_at_mods D lo d ce p es G tn s)
Proof
  `return_buf_ptr d (ce with ce_module := src) G tn s <=> return_buf_ptr d ce G tn s` by
    (Cases_on `d` >- simp[return_buf_ptr_def] >> PairCases_on `x` >> simp[return_buf_ptr_def]) >>
  simp[dead_lo_ok_mods_def, ghost_inv_at_mods_def, imm_section_dead_mods_def]
QED

Theorem default_read_typed_cell[local]:
  expr_body_pre_mods mods cd p env (TopLevelName ann (owner,id)) es /\
  get_module_code p owner = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  lookup_immutable p es owner id = SOME (rt,v) ==>
  evaluate_type (get_tenv p) ann = SOME rt /\
  ?imms. ALOOKUP es.immutables p.txn.target = SOME imms /\
         FLOOKUP (get_source_immutables owner imms) id = SOME (rt,v)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac toplevel_find_NONE_bare_global >>
  qpat_x_assum `lookup_immutable _ _ _ _ = _` mp_tac >>
  simp[lookup_immutable_def, AllCaseEqs()] >> strip_tac >> simp[] >>
  qpat_x_assum `env_consistent env p es`
    (mp_tac o cj 3 o REWRITE_RULE [env_consistent_def]) >>
  simp[env_immutables_consistent_def] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem default_read_ctor_memory[local]:
  contract_inv mods exps ctx (ce with ce_module := src) p /\
  expr_sim_inv_mods mods (ce with ce_module := src) p env es /\
  dead_lo_ok_mods H D lo ce p /\ ghost_inv_at_mods D lo d ce p es G tn s /\
  immutable_frame_mods func ce p es s /\
  ALOOKUP ce.ce_modules owner = SOME ts /\
  FLOOKUP ce.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables p.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (rt,v) /\ ce.ce_is_ctor ==>
  off + type_memory_size rt <= lo /\
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v off mem
Proof
  strip_tac >>
  `immutable_frame_mods func (ce with ce_module := src) p es s` by
    simp[default_read_owner_views] >>
  qpat_x_assum `immutable_frame_mods func (ce with ce_module := src) p es s`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def]) >>
  `dead_lo_ok_mods H D lo (ce with ce_module := src) p /\
   ghost_inv_at_mods D lo d (ce with ce_module := src) p es G tn s` by
    simp[default_read_ctor_views] >>
  `ALOOKUP (ce with ce_module := src).ce_modules owner = SOME ts /\
   FLOOKUP (ce with ce_module := src).ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
   (ce with ce_module := src).ce_is_ctor` by simp[] >>
  irule qualified_immutable_ctor_frame_mods >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem default_read_horizon[local]:
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0 origin (si,es,s,G,tn) pin /\
  valid_horizon p st0 H es.storage_trace ==>
  immutable_frame_mods func ce p es s /\ ghost_inv_at_mods (DF H) lo d ce p es G tn s
Proof
  PairCases_on `origin` >> simp[intcall_stage_frame_mods_def] >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _` (drule_then strip_assume_tac) >>
  simp[]
QED

Theorem intcall_default_qualified_immutable_read_cut_mods:
  contract_inv mods exps ctx (ce with ce_module := src) p /\
  expr_body_pre_mods mods (ce with ce_module := src) p env (TopLevelName ann (owner,id)) es /\
  body_const_cells_agree mods p env es /\
  get_module_code p src = SOME tops /\
  lookup_callable_function p.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  raw = DROP (LENGTH dflts - (LENGTH args - nargs)) dflts /\
  ds = DROP (LENGTH dflts - (LENGTH args - nargs))
            (subst_consts_exprs_mods (consts_env_mods mods) dflts) /\
  EVERY (runtime_constant_expr mods) raw /\ EVERY (runtime_constant_expr mods) ds /\
  ~supported_exprs_exists (const_name_root_mods mods) ds /\
  ~supported_exprs_exists (unallocated_bare_global_root ce env) ds /\
  supported_exprs_exists ($= (TopLevelName ann (owner,id))) ds /\
  lookup_immutable p es owner id = SOME (rt,v) /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0 origin (si,es,s,G,tn) pin /\
  valid_horizon p st0 H es.storage_trace /\ dead_lo_ok_mods H (DF H) lo ce p ==>
  ?ts off. declared_immutable mods owner id /\
    intcall_default_read_at_mods ce p es s tn lo ann owner id ts off rt v /\
    compile_expr ce ty (TopLevelName ann (owner,id)) si =
      (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode),si) /\
    (!sd sh. gas_shadow_state si sh ==>
       compile_expr (gas_shadow_env sd ce) ty (gas_shadow_expr (TopLevelName ann (owner,id))) sh =
       (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode),sh))
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_all_then strip_assume_tac default_read_horizon >>
  drule_all_then (strip_assume_tac o cj 2) selected_default_read_inputs_mods >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac default_read_typed_cell >>
  `immutable_frame_mods func (ce with ce_module := src) p es s /\
   FLOOKUP (ce with ce_module := src).ce_module_vars (owner,id) = SOME (ImmutableLoc off)` by
    simp[default_read_owner_views] >>
  drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) [default_read_owner_views])
    qualified_lookup_place_mods >>
  qexistsl [`ts`,`off`] >> simp[compile_toplevel_immutable_ptr] >>
  conj_tac
  >- (simp[intcall_default_read_at_mods_def] >>
      conj_tac
      >- simp[Once evaluate_def, lookup_global_def, bind_def, get_immutables_def,
              get_address_immutables_def, lift_option_type_def, return_def, raise_def] >>
      conj_tac >- (drule read_result_gas_obs >> simp[]) >>
      disch_tac >> drule_all default_read_ctor_memory >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `compile_expr (gas_shadow_env sd ce) ty (gas_shadow_expr e) sh` >>
  `gas_shadow_compiles (compile_expr ce ty e)
     (compile_expr (gas_shadow_env sd ce) ty (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (drule_then mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  `compile_expr ce ty e si = (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode),si)` by
    (unabbrev_all_tac >> irule compile_toplevel_immutable_ptr >> simp[]) >>
  `SND (compile_expr (gas_shadow_env sd ce) ty (gas_shadow_expr e) sh) = sh` by
    (unabbrev_all_tac >> simp[gasShadowTheory.gas_shadow_expr_def] >>
     `FLOOKUP (gas_shadow_env sd ce).ce_module_vars (owner,id) = SOME (ImmutableLoc off)` by simp[] >>
     drule compile_toplevel_immutable_ptr >> simp[]) >>
  Cases_on `compile_expr (gas_shadow_env sd ce) ty (gas_shadow_expr e) sh` >> gvs[]
QED
