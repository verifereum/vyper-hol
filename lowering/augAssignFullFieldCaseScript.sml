(* A storage-field AugAssign uses the joint judgment at the observed
   struct root, including constructor frames and their reserved prefix. *)
Theory augAssignFullFieldCase
Ancestors
  augAssignStorageFieldSource augAssignFullFieldRead augAssignFullAddress
  augAssignFullLoad augAssignFullStore augAssignFullStoreGhost augAssignFullOperator
  augAssignFullStateFrame augAssignFullHistory augAssignFullFieldStore freshWrites
  augAssignFullSource augAssignFullSourcePrefix augAssignFullRhs
  bodyFullPreds bodySimFull bodySim bodyMemoryDefs stmtSimProps
  bodyFullShared gasShadowCompileStmtHelpers gasShadowCompileArith gasShadowCompilePure
  gasShadow gasShadowCompileContext gasShadowState
  gasOutcomeFullRunning gasOutcomeFullCompose gasOutcomeFull
  fragGasOriginPtr fragExec ptrDiscipline
  exprSimHypsDefs exprSimTopLevelProps exprSimFieldLayout exprSimAttributeFields
  exprSimSource exprSimUnwrap vyperTypeStatePreservation vyperTypeValues
  exprSimHyps exprBopSimProps exprOperandVar typedMemoryCopy
  augAssignPtrCompiler augAssignPtrTypedNumeric
  vyperTypeBuiltins
  exprSimProps accountsRelProps loweringPosts stmtSimDefs stmtSimAugAssign
  stmtSimAugAssignStorage
  stmtSimAssignStorage stmtSimAssignStorageFacts stmtSimAssignAttrStorage
  exprLoweringProps exprLowering stmtLowering emitHelper emitHelperProps exprOpenPrimitives
  compileEnv loweringStateRelDefs bodyPtrDefs
  vyperStorageFootprint vyperStorageTrace vyperStorageBackend
  vyperInterpreter vyperState vyperValue vyperTypeSystem vyperTyping
  venomState venomExecSemantics venomInst venomMemDefs list finite_map

Theorem compile_augassign_attr_storage_full:
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld) s'' =
       (INL p,t') /\ read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==>
     body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  well_formed_type_value (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) /\
  evaluate_type (get_tenv cx) ty = SOME ftv /\
  well_formed_type env.type_defs ty /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
    SOME (ty,fsz) /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e))
    (stmt_env cenv lctx ret_ty
      (gas_shadow_stmt
        (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e)))
    (eval_stmt cx
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e)) es
Proof
  strip_tac >> simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `!st. eval_target_place cx
      (AttributeTarget (TopLevelNameTarget (src,id)) fld) st =
      (INL (StoragePlace tr (n2w slot + n2w off) ftv),
       st with storage_trace :=
         st.storage_trace ++ [StorageRoot tr slot (StructTV fs)])` by
    (gen_tac >> irule (cj 1 eval_target_place_attr_toplevel_field) >>
     metis_tac[]) >>
  reverse (Cases_on `storage_trace_domain cx st0
    (es.storage_trace ++ [StorageRoot tr slot (StructTV fs)])`)
  >- (irule gas_outcome_full_bad_intro >>
      qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`, `G0`,
                    `PG`, `tn0`, `[]`, `s0`] >>
      simp[storage_trace_domain_def, gas_origin_ptr_focus_nil] >>
      irule augassign_storage_place_bad_root >> metis_tac[]) >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty /\ type_slot_size ftv = 1` by
    metis_tac[word_value_type_word, word_type_slot_size] >>
  `0 < type_slot_size ftv` by simp[] >>
  drule_all observed_storage_field_clean_read_full >> strip_tac >>
  rename1 `read_storage_slot cx tr (n2w slot + n2w off) ftv es = (INL cur,es)` >>
  qabbrev_tac `root_es = es with storage_trace :=
    es.storage_trace ++ [StorageRoot tr slot (StructTV fs)]` >>
  `body_expr_full_ok cx e` by
    (qpat_x_assum `!s'' p t' s'3' cur t'' s'4' ptv t'3'. _`
       (qspecl_then [`es`, `StoragePlace tr (n2w slot + n2w off) ftv`,
         `root_es`, `es`, `cur`, `es`, `es`, `ftv`, `es`] mp_tac) >>
     simp[Abbr `root_es`, read_place_def, place_type_value_def, return_def]) >>
  `expr_body_pre cenv cx env e root_es` by simp[Abbr `root_es`] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e root_es` by
    (qpat_assum `body_expr_full_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
       `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ty`, `root_es`]
       mp_tac) >> simp[]) >>
  qabbrev_tac `H0 = storage_trace_horizon root_es.storage_trace` >>
  `valid_horizon cx st0 H0 root_es.storage_trace` by
    fs[storage_trace_domain_def, Abbr `H0`, Abbr `root_es`] >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    fs[valid_horizon_def, Abbr `root_es`] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  `!rhs a b ce.
   stmt_env cenv lctx ret_ty
     (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop rhs)
     a = (ce,b) ==>
   ce = cenv /\
   ?dst sn cur_op s1 rhs_op s2 res_op s3.
     emit_op ADD [Lit (n2w slot); Lit (n2w off)] a = (dst,sn) /\
     emit_op (if tr then TLOAD else SLOAD) [dst] sn = (cur_op,s1) /\
     lower_value compile_expr cenv ty rhs s1 = (rhs_op,s2) /\
     compile_binop bop cur_op rhs_op ty NONE
       (if bop = Exp then expr_int_literal rhs else NONE) s2 = (res_op,s3) /\
     emit_void (if tr then TSTORE else SSTORE) [dst;res_op] s3 = ((),b)` by
    (rpt gen_tac >> strip_tac >>
     drule_all compile_get_target_ptr_toplevel >> strip_tac >>
     qpat_x_assum `stmt_env cenv lctx ret_ty
       (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop rhs)
       a = (ce,b)` mp_tac >>
     Cases_on `tr` >>
     asm_simp_tac (srw_ss())
       [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
        Once compile_get_target_ptr_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, LET_THM] >>
     Cases_on `emit_op ADD [Lit (n2w slot); Lit (n2w off)] a` >>
     rename1 `_ = (dst,sn)` >>
     asm_simp_tac (srw_ss())
       [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     qmatch_goalsub_abbrev_tac `emit_op load [dst] sn` >>
     Cases_on `emit_op load [dst] sn` >> rename1 `_ = (cur_op,s1)` >>
     Cases_on `lower_value compile_expr cenv ty rhs s1` >>
     rename1 `_ = (rhs_op,s2)` >>
     Cases_on `compile_binop bop cur_op rhs_op ty NONE
       (if bop = Exp then expr_int_literal rhs else NONE) s2` >>
     rename1 `_ = (res_op,s3)` >>
     qmatch_goalsub_abbrev_tac `emit_void store [dst;res_op] s3` >>
     Cases_on `emit_void store [dst;res_op] s3` >>
     asm_simp_tac (srw_ss())
       [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
        oneTheory.one] >> strip_tac >> gvs[oneTheory.one]) >>
  qpat_assum `!rhs a b ce. _`
    (qspecl_then [`e`, `sa`, `sb`, `cenv'`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `stmt_env cenv lctx ret_ty
     (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld)
       bop (gas_shadow_expr e)) shadow_sa = (cenv,shadow_sb)` by
    fs[gas_shadow_stmt_def, gas_shadow_expr_def] >>
  qpat_x_assum `!rhs a b ce. _`
    (qspecl_then [`gas_shadow_expr e`, `shadow_sa`, `shadow_sb`, `cenv`]
      mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choosel_then [`sdst`, `ssn`, `scur`, `ss1`, `srhs`, `ss2`,
    `sres`, `ss3`] strip_assume_tac o CONJUNCT2) >>
  `sdst = dst /\ gas_shadow_state sn ssn` by
    (irule gas_shadow_step >>
     qexistsl_tac [`emit_op ADD [Lit (n2w slot); Lit (n2w off)]`,
       `emit_op ADD [Lit (n2w slot); Lit (n2w off)]`, `sa`, `shadow_sa`] >>
     simp[]) >>
  qpat_x_assum `sdst = dst` SUBST_ALL_TAC >>
  `scur = cur_op /\ gas_shadow_state s1 ss1` by
    (irule gas_shadow_step >>
     qexistsl_tac [`emit_op (if tr then TLOAD else SLOAD) [dst]`,
       `emit_op (if tr then TLOAD else SLOAD) [dst]`, `sn`, `ssn`] >> simp[]) >>
  qpat_x_assum `scur = cur_op` SUBST_ALL_TAC >>
  `srhs = rhs_op /\ gas_shadow_state s2 ss2` by
    (irule gas_shadow_step >>
     qexistsl_tac [`lower_value compile_expr cenv ty e`,
       `lower_value compile_expr cenv ty (gas_shadow_expr e)`, `s1`, `ss1`] >>
     simp[gas_shadow_stmt_lower_value]) >>
  qpat_x_assum `srhs = rhs_op` SUBST_ALL_TAC >>
  `cs_extends sa sn /\ cs_extends sn s1` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sa s1` by metis_tac[cs_extends_trans] >>
  qpat_assum `lower_value compile_expr cenv ty e s1 = (rhs_op,s2)`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  qpat_assum `compile_binop _ _ _ _ _ _ s2 = (res_op,s3)`
    (strip_assume_tac o MATCH_MP compile_binop_grows) >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s1 s3` by
    (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends s1 sb` by
    (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s2 sb` by
    (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends sa s2` by
    (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `cs_extends sa s3` by
    (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends sn sb` by
    (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `fn_has_code sa sn func` by
    (qspecl_then [`sa`, `sa`, `sn`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[cs_extends_refl]) >>
  `fn_has_code sn s1 func` by
    (qspecl_then [`sa`, `sn`, `s1`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[]) >>
  `fn_has_code s1 s2 func` by
    (qspecl_then [`sa`, `s1`, `s2`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[]) >>
  `cs_extends shadow_sa ssn /\ cs_extends ssn ss1` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends shadow_sa ss1` by
    (irule cs_extends_trans >> qexists_tac `ssn` >> simp[]) >>
  qpat_assum `lower_value compile_expr cenv ty (gas_shadow_expr e) ss1 = (rhs_op,ss2)`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  qpat_assum `compile_binop _ _ _ _ _ _ ss2 = (sres,ss3)`
    (strip_assume_tac o MATCH_MP compile_binop_grows) >>
  `cs_extends ss3 shadow_sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends ss2 shadow_sb` by
    (irule cs_extends_trans >> qexists_tac `ss3` >> simp[]) >>
  `fn_has_code ss1 ss2 shadow_func` by
    (qspecl_then [`shadow_sa`, `ss1`, `ss2`, `shadow_sb`, `shadow_func`]
       mp_tac fn_has_code_mid >> simp[]) >>
  `fn_has_code s2 s3 func` by
    (qspecl_then [`sa`, `s2`, `s3`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[]) >>
  `fn_has_code s3 sb func` by
    (qspecl_then [`sa`, `s3`, `sb`, `sb`, `func`] mp_tac fn_has_code_mid >>
     simp[cs_extends_refl]) >>
  `?dv. dst = Var dv` by metis_tac[emitted_insts_emit_op] >>
  qpat_x_assum `dst = Var dv` SUBST_ALL_TAC >>
  `?cv. cur_op = Var cv` by metis_tac[emitted_insts_emit_op] >>
  qpat_x_assum `cur_op = Var cv` SUBST_ALL_TAC >>
  `allocas_from lo s0` by metis_tac[ghost_inv_at_def] >>
  mp_tac (Q.INST [`sa` |-> `sa`, `sb` |-> `sn`, `s` |-> `s0`,
    `lhs_word` |-> `n2w slot`, `rhs_word` |-> `n2w off`, `out` |-> `dv`,
    `G` |-> `G0`, `tn` |-> `tn0`, `PG` |-> `PG`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    literal_slot_add_origin_ptr) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`tadd`, `Gadd`, `tnadd`] strip_assume_tac) >>
  `~tadd.vs_halted /\ tadd.vs_current_bb = sn.cs_current_bb /\
   tadd.vs_inst_idx = LENGTH sn.cs_current_insts /\
   allocas_from lo tadd /\
   eval_operand (Var dv) tadd = SOME (n2w slot + n2w off)` by
    (qpat_assum `emit_op ADD _ sa = (Var dv,sn)`
       (strip_assume_tac o MATCH_MP emit_op_same_blocks) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`tadd = _`, `same_blocks sa sn`, `allocas_from lo s0`,
        `~s0.vs_halted`, `s0.vs_current_bb = sa.cs_current_bb`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[same_blocks_def, update_var_def, eval_operand_def, lookup_var_def,
          FLOOKUP_UPDATE, allocas_from_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `key_taint (if tr then tnadd.t_trans else tnadd.t_stor)
     (n2w slot + n2w off) = {}` by
    (qpat_assum `!H. valid_horizon _ _ H (_ ++ _) ==> _`
       (qspec_then `H0` mp_tac) >>
     impl_tac >- fs[Abbr `root_es`] >> simp[]) >>
  qabbrev_tac `field_key = (n2w slot + n2w off : 256 word)` >>
  mp_tac (Q.INST [`sa` |-> `sn`, `sb` |-> `s1`, `s` |-> `tadd`,
    `addr` |-> `Var dv`, `slot` |-> `field_key`, `out` |-> `cv`,
    `G` |-> `Gadd`, `tn` |-> `tnadd`, `PG` |-> `PG`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    storage_address_load_origin_ptr) >>
  impl_tac >- simp[Abbr `field_key`] >>
  disch_then (qx_choosel_then [`tloaded`, `Gload`, `tnload`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path
     (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) [] (OK tloaded,Gload,tnload)` by
    (qx_gen_tac `D` >>
     qpat_assum `!D lo. allocas_from lo s0 ==> _`
       (qspecl_then [`D`, `lo`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_tac >>
     qpat_assum `!D lo. allocas_from lo tadd ==> _`
       (qspecl_then [`D`, `lo`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> disch_tac >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) [] (OK tadd,Gadd,tnadd)`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`tadd`, `Gadd`, `tnadd`, `[]`,
       `OK tloaded`, `Gload`, `tnload`] mp_tac) >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sn.cs_next_var <= s1.cs_next_var` by
    (rpt conj_tac >>
     metis_tac[emitted_insts_emit_op, arithmeticTheory.LESS_EQ_ADD]) >>
  `!H. valid_horizon cx st0 H root_es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es tadd /\
     ghost_inv_at (DF H) lo d cenv cx es Gadd tnadd tadd /\
     return_buf_frame d cenv sn tadd /\ ret_pc_ok cenv sn tadd /\
     local_ptrs_reserved cenv sn` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       fs[valid_horizon_def, Abbr `root_es`] >>
     `stmt_state_rel H ctx func cenv cx es s0 /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
          stmt_state_rel H _ _ _ _ _ s0 /\ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     match_mp_tac (Q.INST [`H` |-> `H`, `s` |-> `s0`, `t` |-> `tadd`, `D` |-> `DF H`,
       `G` |-> `G0`, `tn` |-> `tn0`, `G'` |-> `Gadd`, `tn'` |-> `tnadd`,
       `sb` |-> `sn`, `pc` |-> `LENGTH sn.cs_current_insts`]
       augassign_exterior_state_frame) >>
     fs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sn x` by
    (rpt strip_tac >>
     qspecl_then [`sa`, `sn`, `x`] mp_tac freshWritesTheory.not_fresh_at_mono >>
     simp[]) >>
  `!H. valid_horizon cx st0 H root_es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es tloaded /\
     ghost_inv_at (DF H) lo d cenv cx es Gload tnload tloaded /\
     return_buf_frame d cenv s1 tloaded /\ ret_pc_ok cenv s1 tloaded /\
     local_ptrs_reserved cenv s1` by
    (qx_gen_tac `H` >> strip_tac >>
     `stmt_state_rel H ctx func cenv cx es tadd /\
      ghost_inv_at (DF H) lo d cenv cx es Gadd tnadd tadd /\
      return_buf_frame d cenv sn tadd /\ ret_pc_ok cenv sn tadd /\
      local_ptrs_reserved cenv sn` by
       (qpat_assum `!H. valid_horizon _ _ H root_es.storage_trace ==>
          stmt_state_rel H _ _ _ _ _ tadd /\ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     match_mp_tac (Q.INST [`H` |-> `H`, `s` |-> `tadd`, `t` |-> `tloaded`, `D` |-> `DF H`,
       `G` |-> `Gadd`, `tn` |-> `tnadd`, `G'` |-> `Gload`, `tn'` |-> `tnload`,
       `sa` |-> `sn`, `sb` |-> `s1`, `pc` |-> `LENGTH s1.cs_current_insts`]
       augassign_exterior_state_frame) >>
     fs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `~tloaded.vs_halted /\ tloaded.vs_current_bb = s1.cs_current_bb /\
   tloaded.vs_inst_idx = LENGTH s1.cs_current_insts` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ sn = (Var cv,s1)`
       (strip_assume_tac o MATCH_MP emit_op_same_blocks) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`tloaded = _`, `same_blocks sn s1`, `~tadd.vs_halted`,
        `tadd.vs_current_bb = sn.cs_current_bb`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[same_blocks_def, update_var_def]) >>
  `!H. valid_horizon cx st0 H root_es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx root_es tloaded /\
     storage_well_formed_on cx root_es (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx root_es Gload tnload tloaded` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       fs[valid_horizon_def, Abbr `root_es`] >>
     `stmt_state_rel H ctx func cenv cx es tloaded /\
      ghost_inv_at (DF H) lo d cenv cx es Gload tnload tloaded` by
       (qpat_assum `!H. valid_horizon _ _ H root_es.storage_trace ==>
          stmt_state_rel H _ _ _ _ _ tloaded /\ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     `storage_well_formed_on cx es (FST H)` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
          stmt_state_rel H _ _ _ _ _ s0 /\ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     fs[Abbr `root_es`, storage_well_formed_on_def]) >>
  `alloca_inv s0` by
    (qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==>
       stmt_state_rel H _ _ _ _ _ s0 /\ _`
       (qspec_then `H0` mp_tac) >> simp[stmt_state_rel_def]) >>
  `alloca_inv tadd` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`tadd = _`, `alloca_inv s0`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[update_var_def, alloca_inv_def, allocas_non_overlapping_def,
          alloca_next_valid_def] >> rpt strip_tac >> metis_tac[]) >>
  `alloca_history func tadd` by
    (qpat_assum `tadd = _` SUBST1_TAC >>
     match_mp_tac (Q.INST [`opc` |-> `ADD`,
       `args` |-> `[Lit (n2w slot); Lit (n2w off)]`,
       `sa` |-> `sa`, `sb` |-> `sn`, `out` |-> `dv`,
       `s` |-> `s0`, `w` |-> `field_key`] augassign_emit_word_history) >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          eval_operand_def, is_terminator_def, Abbr `field_key`]) >>
  qpat_assum `eval_operand (Var dv) tadd = SOME field_key`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  `step_inst_base
     (mk_inst sn.cs_next_id (if tr then TLOAD else SLOAD) [Var dv] [cv]) tadd =
   OK (update_var cv
     (if tr then tload field_key tadd else sload field_key tadd) tadd)` by
    (qpat_assum `lookup_var dv tadd = SOME field_key` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> Cases_on `tr` >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
          eval_operand_def]) >>
  `alloca_history func tloaded` by
    (qpat_assum `tloaded = _` SUBST1_TAC >>
     match_mp_tac (Q.INST [`opc` |-> `if tr then TLOAD else SLOAD`,
       `args` |-> `[Var dv]`, `sa` |-> `sn`, `sb` |-> `s1`,
       `out` |-> `cv`, `s` |-> `tadd`,
       `w` |-> `if tr then tload field_key tadd else sload field_key tadd`]
       augassign_emit_word_history) >>
     Cases_on `tr` >> simp[is_terminator_def]) >>
  `storage_holds cx tr ty (Value cur) field_key es s0` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==>
       storage_holds _ _ _ _ _ _ _ /\ _`
       (qspec_then `H0` mp_tac) >> fs[Abbr `root_es`]) >>
  `(if tr then tload field_key s0 else sload field_key s0) =
     typed_val_to_w256 ftv cur` by
    (irule storage_holds_load >> metis_tac[]) >>
  `(if tr then tload field_key tadd else sload field_key tadd) =
     typed_val_to_w256 ftv cur` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`tadd = _`, `(if tr then tload field_key s0 else sload field_key s0) = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `tr` >>
     gvs[update_var_def, tload_def, sload_def,
         contract_transient_def, contract_storage_def]) >>
  `eval_operand (Var cv) tloaded = SOME (typed_val_to_w256 ftv cur)` by
    (qpat_assum `tloaded = _` SUBST1_TAC >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `well_formed_type_value ftv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type ftv cur` by
    metis_tac[read_storage_slot_success_type] >>
  `word_value cur /\ is_word_type (expr_type e)` by
    metis_tac[word_value_type_typed, word_value_type_word] >>
  `not_fresh_at sn dv /\ not_fresh_at s1 cv` by
    (conj_tac
     >- (qpat_assum `emit_op ADD _ sa = (Var dv,sn)`
           (mp_tac o MATCH_MP typed_copy_emit_op_fresh) >> simp[]) >>
     qpat_assum `emit_op _ _ sn = (Var cv,s1)`
       (mp_tac o MATCH_MP typed_copy_emit_op_fresh) >> simp[]) >>
  `not_fresh_at s1 dv` by
    (qspecl_then [`sn`, `s1`, `dv`] mp_tac
      freshWritesTheory.not_fresh_at_mono >> simp[]) >>
  `return_buf_frame d cenv s1 tloaded /\ ret_pc_ok cenv s1 tloaded /\
   local_ptrs_reserved cenv s1` by
    (qpat_x_assum `!H. valid_horizon _ _ H root_es.storage_trace ==>
       stmt_state_rel H _ _ _ _ es tloaded /\ _`
       (qspec_then `H0` mp_tac) >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at s1 x)` by
    (conj_tac
     >- (rpt strip_tac >>
         qspecl_then [`sn`, `s1`, `x`] mp_tac
           freshWritesTheory.not_fresh_at_mono >> simp[]) >>
     fs[ret_pc_ok_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok root_es` by
    (simp[Abbr `root_es`] >>
     match_mp_tac (Q.INST
       [`tgt` |-> `AttributeTarget (TopLevelNameTarget (src,id)) fld`,
        `tr` |-> `tr`, `k` |-> `field_key`, `ftv` |-> `ftv`,
        `v0` |-> `cur`, `ty` |-> `ty`, `bop` |-> `bop`,
        `lctx` |-> `lctx`, `evs` |-> `[StorageRoot tr slot (StructTV fs)]`]
       augassign_storage_place_rhs_admissible) >> simp[]) >>
  mp_tac (Q.INST [`es` |-> `root_es`, `s0` |-> `tloaded`,
    `G0` |-> `Gload`, `tn0` |-> `tnload`, `sa` |-> `s1`, `sb` |-> `s2`,
    `shadow_sa` |-> `ss1`, `shadow_sb` |-> `ss2`, `op` |-> `rhs_op`,
    `RetQ` |-> `RetQ`] augassign_rhs_invoke_full) >>
  impl_tac >- simp[] >>
  disch_then (assume_tac o BETA_RULE o HO_MATCH_MP gas_outcome_full_value_running) >>
  match_mp_tac (Q.INST
    [`p` |-> `StoragePlace tr field_key ftv`, `mid` |-> `root_es`,
     `cur` |-> `cur`, `ptv` |-> `ftv`,
     `obs` |-> `[StorageRoot tr slot (StructTV fs)]`,
     `s1` |-> `tloaded`, `G1` |-> `Gload`, `tn1` |-> `tnload`]
    augassign_pure_prefix_full) >> rpt conj_tac
  >- (gen_tac >> simp[read_place_def, place_type_value_def, return_def,
       Abbr `root_es`] >>
      drule read_storage_slot_gas_obs >>
      disch_then (qspec_then `gs` mp_tac) >> strip_tac >>
      drule read_storage_slot_storage_trace >> simp[])
  >- simp[Abbr `root_es`]
  >- simp[Abbr `root_es`]
  >- simp[] >>
  match_mp_tac (Q.INST [`Qrhs` |->
    `\H v ee G tn t. ~t.vs_halted /\
      expr_post H ctx func cenv cx e root_es s1 s2 tloaded ee v rhs_op t /\
      expr_store_bound cx (expr_type e) v rhs_op t /\
      t.vs_current_bb = s2.cs_current_bb /\
      t.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func t /\ tloaded.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v rhs_op G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e rhs_op G t) /\
      ghost_kept_at lo cenv root_es s1 Gload tnload tloaded G tn`]
    augassign_rhs_bind_full) >>
  conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`marks`, `rhs`, `mid`, `Gr`, `tnr`, `u`] >>
  BETA_TAC >> strip_tac >>
  qabbrev_tac `H2 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H2 mid.storage_trace` by
    fs[storage_trace_domain_def, Abbr `H2`] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H2` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H root_es.storage_trace` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `bind (eval_expr cx e) _ _ = (INL rhs,_)` assume_tac >>
     drule_at (Pos (el 2)) valid_horizon_frame >>
     simp[augassign_rhs_trace_frame]) >>
  `expr_body_pre cenv cx env e
     (root_es with gas_obs := gas_explicit marks tloaded.vs_gas_readings)` by
    simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >>
  `?etv. word_value rhs /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
     value_has_type etv rhs` by metis_tac[] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  qpat_assum `bind (eval_expr cx e) _ _ = (INL rhs,_)`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ETA_AX] eval_expr_read_INL)) >>
  `!n. expr_int_literal e = SOME n ==> rhs = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i)` by
    (strip_tac >> `shift_amount_ok e` by metis_tac[] >>
     drule_all eval_expr_shift_amount >> simp[]) >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] cur rhs
       (mid with gas_obs := []))` by
    (match_mp_tac (Q.INST
       [`tgt` |-> `AttributeTarget (TopLevelNameTarget (src,id)) fld`,
        `tr` |-> `tr`, `k` |-> `field_key`, `ftv` |-> `ftv`,
        `v0` |-> `cur`, `v` |-> `rhs`,
        `ee` |-> `mid with gas_obs := []`,
        `gs` |-> `gas_explicit marks tloaded.vs_gas_readings`,
        `evs` |-> `[StorageRoot tr slot (StructTV fs)]`, `lctx` |-> `lctx`]
       augassign_storage_place_binop_admissible) >> fs[Abbr `root_es`]) >>
  qpat_assum `expr_post H2 _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `is_word_type (expr_type e)` by
    fs[word_value_type_def, is_word_type_def] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `expr_val_rel cx (expr_type e) rhs rhs_op u` by metis_tac[] >>
  `eval_operand rhs_op u = SOME (val_to_w256 rhs)` by
    (qspecl_then [`cx`, `expr_type e`, `rhs`, `rhs_op`, `u`]
       mp_tac expr_val_rel_word >> simp[]) >>
  `eval_operand (Var cv) u = SOME (val_to_w256 cur)` by
    (qspecl_then [`Var cv`, `s1`, `tloaded`, `u`, `val_to_w256 cur`]
       mp_tac eval_operand_frame >> simp[typed_val_to_w256_word_value]) >>
  `eval_operand (Var dv) u = SOME field_key` by
    (`eval_operand (Var dv) tloaded = SOME field_key` by
       (qspecl_then [`Var dv`, `sn`, `tadd`, `tloaded`, `field_key`]
          mp_tac eval_operand_frame >> simp[] >> metis_tac[]) >>
     qspecl_then [`Var dv`, `s1`, `tloaded`, `u`, `field_key`]
       mp_tac eval_operand_frame >> simp[]) >>
  `(bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n)` by
    (strip_tac >> qpat_x_assum `bop = Exp ==> nonneg_int_literal e` mp_tac >>
     simp[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> simp[]) >>
  mp_tac (Q.INST [`ann` |-> `ty`, `t1` |-> `ty`, `t2` |-> `expr_type e`,
    `tenv` |-> `get_tenv cx`, `tv1` |-> `ftv`, `tv2` |-> `etv`,
    `v1` |-> `cur`, `v2` |-> `rhs`, `tys` |-> `[ty; expr_type e]`,
    `bl` |-> `NONE`, `el` |-> `if bop = Exp then expr_int_literal e else NONE`,
    `es` |-> `mid with gas_obs := []`] binop_typed_numeric_witness) >>
  impl_tac
  >- (simp[] >> strip_tac >> fs[]) >>
  disch_tac >>
  drule_all typed_binop_scalar_member_ptr >> disch_tac >>
  `straight_fresh (compile_binop bop (Var cv) rhs_op ty NONE
     (if bop = Exp then expr_int_literal e else NONE))` by
    (irule compile_binop_straight_fresh_ptr >> simp[]) >>
  qpat_assum `ghost_kept_at lo cenv root_es s1 Gload tnload tloaded Gr tnr`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  `op_prov Gr (Var cv) = NONE /\ op_taint tnr (Var cv) = {}` by
    (fs[op_prov_def] >> metis_tac[]) >>
  `op_prov Gr rhs_op = NONE /\ op_taint tnr rhs_op = {}` by
    fs[ptr_val_ok_def] >>
  `(!x. rhs_op = Var x ==> not_fresh_at s2 x) /\ (!l. rhs_op <> Label l)` by
    (qspecl_then [`cenv`, `cx`, `env`, `e`, `root_es`, `ty`, `s1`, `rhs_op`, `s2`]
       mp_tac expr_body_pre_lower_value_word_shape >>
     impl_tac >- simp[] >> strip_tac >> simp[]) >>
  mp_tac (Q.INST [`x` |-> `Var cv`, `y` |-> `rhs_op`, `ty` |-> `ty`,
    `bl` |-> `NONE`, `el` |-> `if bop = Exp then expr_int_literal e else NONE`,
    `sa` |-> `s2`, `sb` |-> `s3`, `op` |-> `res_op`,
    `G` |-> `Gr`, `tn` |-> `tnr`] compile_binop_clean_certificate_ptr) >>
  impl_tac >- simp[] >> strip_tac >>
  `not_fresh_at s2 cv /\ not_fresh_at s2 dv` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `bop_result cx ty bop [ty; expr_type e] cur rhs (mid with gas_obs := []) =
    case evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      ftv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[] >>
     metis_tac[word_value_not_bytes]) >>
  `return_buf_frame d cenv s2 u` by
    (qspecl_then [`d`, `cenv`, `cenv`, `s1`, `s2`, `tloaded`, `u`]
       mp_tac return_buf_frame_frame >> simp[]) >>
  `ret_pc_ok cenv s2 u` by
    (qspecl_then [`cenv`, `cenv`, `s1`, `s2`, `tloaded`, `u`]
       mp_tac ret_pc_ok_frame >> simp[]) >>
  `local_ptrs_reserved cenv s2` by
    (qspecl_then [`cenv`, `s1`, `s2`] mp_tac local_ptrs_reserved_next_var >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at s2 x` by
    (rpt strip_tac >>
     qspecl_then [`s1`, `s2`, `x`] mp_tac freshWritesTheory.not_fresh_at_mono >>
     simp[]) >>
  mp_tac (Q.INST [`ann` |-> `ty`, `ty` |-> `ty`,
    `tys` |-> `[ty; expr_type e]`, `v1` |-> `cur`, `v2` |-> `rhs`,
    `es0` |-> `mid with gas_obs := []`, `x` |-> `Var cv`, `y` |-> `rhs_op`,
    `bl` |-> `NONE`, `el` |-> `if bop = Exp then expr_int_literal e else NONE`,
    `sa` |-> `s2`, `sb` |-> `s3`, `op` |-> `res_op`,
    `s` |-> `u`, `G` |-> `Gr`, `tn` |-> `tnr`, `A` |-> `A`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    binop_numeric_origin_ptr_continuation) >>
  impl_tac >- simp[] >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `result` (qx_choose_then `oprun`
      (qx_choose_then `Gop` (qx_choose_then `tnop` strip_assume_tac))))
    (qx_choose_then `msg` (qx_choose_then `abort_state`
      (qx_choose_then `abort_idx` (qx_choose_then `Gabort`
        (qx_choose_then `tnabort` strip_assume_tac))))))
  >- (
    `evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      ftv bop cur rhs = INL result` by
      (qpat_x_assum `bop_result _ _ _ _ _ _ _ = INL result` mp_tac >>
       simp[] >> Cases_on `evaluate_binop
         (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
         ftv bop cur rhs` >> simp[]) >>
    `value_has_type ftv result` by
      (mp_tac (Q.INST [`t1` |-> `ty`, `t2` |-> `expr_type e`,
        `tenv` |-> `get_tenv cx`, `result_tv` |-> `ftv`,
        `tv1` |-> `ftv`, `tv2` |-> `etv`, `tv` |-> `ftv`,
        `v1` |-> `cur`, `v2` |-> `rhs`, `v` |-> `result`,
        `u` |-> `case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u`]
        well_typed_binop_success_type) >> simp[]) >>
    `encode_value ftv result = SOME [(0, val_to_w256 result)]` by
      metis_tac[encode_value_word_typed, typed_val_to_w256_word_value] >>
    qabbrev_tac `operated = oprun with vs_inst_idx := LENGTH s3.cs_current_insts` >>
    `operated = (u with vs_inst_idx := LENGTH s3.cs_current_insts)
      with vs_vars := operated.vs_vars` by
      (simp[Abbr `operated`] >>
       qpat_assum `oprun = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
    `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid operated /\
       ghost_inv_at (DF H) lo d cenv cx mid Gop tnop operated /\
       return_buf_frame d cenv s3 operated /\ ret_pc_ok cenv s3 operated /\
       local_ptrs_reserved cenv s3` by
      (qx_gen_tac `H` >> strip_tac >>
       `stmt_state_rel H ctx func cenv cx mid u /\
        ghost_inv_at (DF H) lo d cenv cx mid Gr tnr u` by
         (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
            (qspec_then `H` mp_tac) >> simp[expr_post_def]) >>
       match_mp_tac (Q.INST [`H` |-> `H`, `D` |-> `DF H`, `s` |-> `u`,
         `t` |-> `operated`, `G` |-> `Gr`, `tn` |-> `tnr`,
         `G'` |-> `Gop`, `tn'` |-> `tnop`, `es` |-> `mid`,
         `sa` |-> `s2`, `sb` |-> `s3`, `pc` |-> `LENGTH s3.cs_current_insts`]
         augassign_exterior_state_frame) >> fs[Abbr `operated`, lookup_var_def]) >>
    `s3.cs_current_bb = s2.cs_current_bb /\
     s3.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 s3` by
      (qpat_assum `straight_fresh _`
         (mp_tac o REWRITE_RULE [straight_fresh_def]) >>
       disch_then (qspecl_then [`s2`, `res_op`, `s3`] mp_tac) >> simp[]) >>
    `~operated.vs_halted /\ operated.vs_current_bb = s3.cs_current_bb /\
     operated.vs_inst_idx = LENGTH s3.cs_current_insts /\
     operated.vs_allocas = u.vs_allocas /\
     operated.vs_alloca_next = u.vs_alloca_next` by
      (simp[Abbr `operated`] >>
       qpat_assum `oprun = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
    `eval_operand res_op operated = SOME (val_to_w256 result)` by
      simp[Abbr `operated`, eval_operand_def] >>
    `allocas_from lo operated /\ lo <= operated.vs_alloca_next` by
      (map_every (fn pat => qpat_assum pat mp_tac)
         [`allocas_from lo u`, `lo <= u.vs_alloca_next`,
          `operated.vs_allocas = u.vs_allocas`,
          `operated.vs_alloca_next = u.vs_alloca_next`] >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def] >>
       rpt strip_tac >> metis_tac[]) >>
    `eval_operand (Var dv) operated = SOME field_key` by
      (qunabbrev_tac `operated` >>
       qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z oprun = lookup_var z u`
         (qspec_then `dv` mp_tac) >>
       qpat_assum `eval_operand (Var dv) u = SOME field_key` mp_tac >>
       qpat_assum `not_fresh_at s2 dv` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[eval_operand_def, lookup_var_def]) >>
    `op_taint tnop (Var dv) = {}` by
      (qpat_assum `!x. not_fresh_at s1 x ==> FLOOKUP Gr x = _ /\ _`
         (qspec_then `dv` mp_tac) >>
       qpat_assum `!p. not_fresh_at sn p ==> lookup_var p tloaded = _ /\ _`
         (qspec_then `dv` mp_tac) >>
       qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP Gop z = _ /\ _`
         (qspec_then `dv` mp_tac) >> simp[]) >>
    `stmt_state_rel H2 ctx func cenv cx mid operated` by
      (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
         stmt_state_rel H _ _ _ _ _ operated /\ _`
         (qspec_then `H2` mp_tac) >> simp[]) >>
    `alloca_inv u /\ ~cx.txn.is_static /\ ~operated.vs_call_ctx.cc_static /\
     operated.vs_call_ctx.cc_address = cx.txn.target` by
      fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
    `alloca_history func operated` by
      (simp[Abbr `operated`] >>
       qspecl_then [`emitted_insts s2 s3`, `s2`, `s3`, `u`, `oprun`]
         mp_tac bodyFullUnwrapRunTheory.emitted_alloca_history >>
       simp[] >>
       metis_tac[augAssignPtrScalarCertificateTheory.scalar_code_nonterminators]) >>
    Cases_on `write_storage_slot cx tr field_key ftv result (mid with gas_obs := [])` >>
    rename1 `write_storage_slot _ _ _ _ _ _ = (store_res,fin)` >>
    `store_res = INL ()` by
      (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
       simp[write_storage_slot_eq]) >>
    pop_assum SUBST_ALL_TAC >>
    `fin.gas_obs = [] /\ fin.scopes = mid.scopes /\
     fin.storage_trace = mid.storage_trace` by
      (map_every (fn pat => qpat_assum pat mp_tac)
         [`write_storage_slot _ _ _ _ _ _ = (INL (),fin)`,
          `encode_value ftv result = SOME _`, `~cx.txn.is_static`] >>
       POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
       fs[write_storage_slot_eq] >> Cases_on `tr` >> gvs[set_storage_def]) >>
    qabbrev_tac `last = (if tr then tstore field_key (val_to_w256 result) operated
                         else sstore field_key (val_to_w256 result) operated)
                        with vs_inst_idx := LENGTH sb.cs_current_insts` >>
    qabbrev_tac `tnlast = if tr then tnop with t_trans := key_update tnop.t_trans field_key {}
                         else tnop with t_stor := key_update tnop.t_stor field_key {}` >>
    `!D lo. allocas_from lo operated /\ lo <= operated.vs_alloca_next ==>
       gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (operated,Gop,tnop) [] (OK last,Gop,tnlast)` by
      (mp_tac (Q.INST [`sa` |-> `s3`, `sb` |-> `sb`, `s` |-> `operated`,
         `addr` |-> `Var dv`, `slot` |-> `field_key`, `op` |-> `res_op`,
         `w` |-> `val_to_w256 result`, `G` |-> `Gop`, `tn` |-> `tnop`,
         `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
         storage_word_store_origin_ptr) >>
       impl_tac >- simp[] >> simp[Abbr `last`, Abbr `tnlast`]) >>
    `!H. valid_horizon cx st0 H fin.storage_trace ==>
       stmt_state_rel H ctx func cenv cx fin last /\
       storage_well_formed_on cx fin (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx fin Gop tnlast last` by
      (qx_gen_tac `H` >> strip_tac >>
       `valid_horizon cx st0 H mid.storage_trace` by
         (qpat_assum `fin.storage_trace = mid.storage_trace`
            (fn th => ONCE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
       `valid_horizon cx st0 H root_es.storage_trace` by
         (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
            valid_horizon _ _ H root_es.storage_trace`
            (qspec_then `H` mp_tac) >> simp[]) >>
       `MEM (tr,n2w slot,StructTV fs) (FST H) /\ regions_consistent (FST H)` by
         (qunabbrev_tac `root_es` >>
          qpat_assum `valid_horizon cx st0 H _`
            (strip_assume_tac o SIMP_RULE (srw_ss())
              [valid_horizon_def, storage_observations_ok_def,
               storage_trace_regions_def]) >> simp[]) >>
       `stmt_state_rel H ctx func cenv cx mid operated /\
        ghost_inv_at (DF H) lo d cenv cx mid Gop tnop operated` by
         (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
            stmt_state_rel H _ _ _ _ _ operated /\ _`
            (qspec_then `H` mp_tac) >> simp[]) >>
       `storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
         (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
            ~u.vs_halted /\ expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            (qspec_then `H` mp_tac) >>
          simp[expr_post_def] >> strip_tac >>
          `storage_well_formed_on cx (mid with gas_obs := []) (FST H) <=>
           storage_well_formed_on cx mid (FST H)` by
            (irule storage_well_formed_on_backends >> simp[]) >> simp[]) >>
       `storage_well_formed_on cx fin (FST H) /\
        (!w st. storage_dead H tr (update_storage field_key w st) =
                storage_dead H tr st)` by
         (qunabbrev_tac `field_key` >>
          match_mp_tac (Q.INST [`k` |-> `(n2w slot : 256 word)`,
            `H` |-> `H`, `tr` |-> `tr`, `fs` |-> `fs`, `fld` |-> `fld`,
            `off` |-> `off`, `ftv` |-> `ftv`,
            `es` |-> `mid with gas_obs := []`, `ee` |-> `fin`,
            `v` |-> `result`] storage_struct_field_word_write_frame) >>
          simp[]) >>
       `stmt_state_rel H ctx func cenv cx fin
          (if tr then tstore field_key (val_to_w256 result) operated
           else sstore field_key (val_to_w256 result) operated)` by
         (qspecl_then [`H`, `func`, `cenv`, `cx`, `mid with gas_obs := []`,
            `operated`, `tr`, `field_key`, `ftv`, `result`, `val_to_w256 result`,
            `INL ()`, `fin`, `ctx`] mp_tac stmt_state_rel_write_storage_word >>
          simp[stmt_state_rel_start_gas_obs]) >>
       mp_tac (Q.INST [`H` |-> `H`, `D` |-> `DF H`, `es` |-> `mid`,
         `es'` |-> `fin`, `s` |-> `operated`, `G` |-> `Gop`, `tn` |-> `tnop`,
         `slot` |-> `field_key`, `w` |-> `val_to_w256 result`,
         `pc` |-> `LENGTH sb.cs_current_insts`]
         (INST_TYPE [alpha |-> ``:256``] ghost_inv_at_storage_word_store)) >>
       impl_tac >- simp[] >>
       simp[Abbr `last`, Abbr `tnlast`, stmt_state_rel_inst_idx]) >>
    qpat_assum `emit_void _ _ s3 = ((),sb)`
      (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
    qpat_assum `emit_void _ _ s3 = ((),sb)`
      (strip_assume_tac o MATCH_MP emit_void_same_blocks) >>
    qpat_assum `same_blocks s3 sb`
      (strip_assume_tac o REWRITE_RULE [same_blocks_def]) >>
    `~last.vs_halted /\ last.vs_current_bb = sb.cs_current_bb /\
     last.vs_inst_idx = LENGTH sb.cs_current_insts /\
     last.vs_allocas = operated.vs_allocas /\
     last.vs_alloca_next = operated.vs_alloca_next /\
     (!x. lookup_var x last = lookup_var x oprun) /\
     (!x. op_taint tnlast (Var x) = op_taint tnop (Var x))` by
      (Cases_on `tr` >> simp[Abbr `last`, Abbr `tnlast`,
         sstore_def, tstore_def, op_taint_def, same_blocks_def] >>
       simp[Abbr `operated`, lookup_var_def]) >>
    `alloca_inv operated` by fs[stmt_state_rel_def] >>
    `alloca_history func last` by
      (qunabbrev_tac `last` >>
       match_mp_tac (Q.INST [`opc` |-> `if tr then TSTORE else SSTORE`,
         `args` |-> `[Var dv; res_op]`, `sa` |-> `s3`, `sb` |-> `sb`,
         `s` |-> `operated`,
         `t` |-> `if tr then tstore field_key (val_to_w256 result) operated
                   else sstore field_key (val_to_w256 result) operated`]
         augassign_emit_void_history) >> simp[] >> Cases_on `tr` >>
       simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, is_terminator_def]) >>
    `~block_is_terminated sb` by
      (qpat_assum `emit_void _ _ s3 = _`
         (mp_tac o MATCH_MP emit_void_terminated) >>
       Cases_on `tr` >> simp[is_terminator_def]) >>
    `return_buf_frame d cenv sb last` by
      (`s2.cs_next_var <= sb.cs_next_var` by decide_tac >>
       match_mp_tac (Q.SPECL [`d`, `cenv`, `cenv`, `s2`, `sb`, `u`, `last`]
         return_buf_frame_frame) >> simp[] >> rpt strip_tac >>
       qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z oprun = lookup_var z u`
         (qspec_then `x` mp_tac) >> simp[]) >>
    `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
     sa.cs_next_var <= sb.cs_next_var` by decide_tac >>
    `!x. not_fresh_at sa x ==>
         not_fresh_at sn x /\ not_fresh_at s1 x /\ not_fresh_at s2 x` by
      (rpt strip_tac >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`not_fresh_at sa x`, `sa.cs_next_var <= sn.cs_next_var`,
          `sa.cs_next_var <= s1.cs_next_var`, `s1.cs_next_var <= s2.cs_next_var`] >>
       POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
       metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
    `!x. not_fresh_at sa x ==>
         (!w. lookup_var x s0 = SOME w ==> lookup_var x last = SOME w) /\
         FLOOKUP Gop x = FLOOKUP G0 x /\
         op_taint tnlast (Var x) = op_taint tn0 (Var x)` by
      (qx_gen_tac `x` >> strip_tac >>
       `not_fresh_at sn x /\ not_fresh_at s1 x /\ not_fresh_at s2 x` by simp[] >>
       map_every (fn pat => qpat_assum pat (qspec_then `x` mp_tac))
         [`!p. not_fresh_at sa p ==> lookup_var p tadd = _ /\ _`,
          `!p. not_fresh_at sn p ==> lookup_var p tloaded = _ /\ _`,
          `!x. not_fresh_at s1 x ==> FLOOKUP Gr x = _ /\ _`,
          `!z. not_fresh_at s2 z ==> FLOOKUP Gop z = _ /\ _`,
          `!z. not_fresh_at s2 z ==> lookup_var z oprun = _`] >>
       qpat_assum `!x w. not_fresh_at s1 x /\ lookup_var x tloaded = SOME w ==> _`
         (qspec_then `x` mp_tac) >>
       qpat_assum `!x. lookup_var x last = lookup_var x oprun`
         (qspec_then `x` mp_tac) >>
       qpat_assum `!x. op_taint tnlast (Var x) = op_taint tnop (Var x)`
         (qspec_then `x` mp_tac) >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`not_fresh_at sa x`, `not_fresh_at sn x`,
          `not_fresh_at s1 x`, `not_fresh_at s2 x`] >>
       POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> metis_tac[]) >>
    `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP last.vs_allocas aid = SOME b` by
      (rpt strip_tac >>
       `tloaded.vs_allocas = s0.vs_allocas` by
         (qpat_assum `tloaded = _` (fn th => ONCE_REWRITE_TAC [th]) >>
          qpat_assum `tadd = _` (fn th => ONCE_REWRITE_TAC [th]) >>
          simp[update_var_def]) >>
       simp[] >> qpat_assum `!aid b. FLOOKUP tloaded.vs_allocas aid = SOME b ==> _`
         (qspecl_then [`aid`, `b`] mp_tac) >> simp[]) >>
    `s0.vs_alloca_next <= last.vs_alloca_next` by
      (`tloaded.vs_alloca_next = s0.vs_alloca_next` by
         (qpat_assum `tloaded = _` (fn th => ONCE_REWRITE_TAC [th]) >>
          qpat_assum `tadd = _` (fn th => ONCE_REWRITE_TAC [th]) >>
          simp[update_var_def]) >> decide_tac) >>
    irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
    qexistsl_tac [`Gop`, `fin`, `INL ()`, `last`, `tnlast`] >>
    conj_tac
    >- (gen_tac >>
        qspecl_then [`cx`, `tr`, `field_key`, `ftv`, `result`,
          `mid with gas_obs := []`, `tail`] mp_tac write_storage_slot_gas_obs >>
        simp[lift_sum_def, bind_def, return_def, write_place_def]) >>
    qx_gen_tac `H` >> strip_tac >>
    `valid_horizon cx st0 H mid.storage_trace` by
      (qpat_assum `fin.storage_trace = mid.storage_trace`
         (fn th => ONCE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
    conj_tac
    >- (`gas_origin_ptr_path
           (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (u,Gr,tnr) [] (OK operated,Gop,tnop)` by
          (qpat_assum `!D lo. allocas_from lo u /\ lo <= u.vs_alloca_next ==> _`
             (qspecl_then [`DF H`, `lo`] mp_tac) >> simp[Abbr `operated`]) >>
        qpat_assum `gas_origin_ptr_path _ (u,Gr,tnr) [] (OK operated,Gop,tnop)`
          (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
        disch_then (qspecl_then [`operated`, `Gop`, `tnop`, `[]`, `OK last`,
          `Gop`, `tnlast`] mp_tac) >> simp[]) >>
    BETA_TAC >> qexists_tac `cenv` >>
    `fin with gas_obs := [] = fin` by
      simp[evaluation_state_component_equality] >>
    simp[stmt_lands_def, cenv_top_ext_refl] >>
    qpat_x_assum `!H. valid_horizon _ _ H fin.storage_trace ==>
      stmt_state_rel H _ _ _ _ _ last /\ _`
      (qspec_then `H` mp_tac) >>
    simp[]) >>
  `evaluate_binop
    (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
    ftv bop cur rhs = INR (RuntimeError msg)` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = INR (Error (RuntimeError msg))` mp_tac >>
     simp[] >> Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       ftv bop cur rhs` >> simp[]) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gabort`, `mid`,
    `Abort Revert_abort (abort_state with vs_inst_idx := abort_idx)`,
    `INR (Error (RuntimeError msg))`, `tnabort`] >>
  simp[lift_sum_def, bind_def, raise_def, exit_result_def, stmt_exit_ptr_def,
       exprSimDefsTheory.expr_exit_def]
QED
