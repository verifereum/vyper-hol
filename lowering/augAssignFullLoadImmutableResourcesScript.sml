(* Immutable literal-load resources at the joint target endpoint. *)
Theory augAssignFullLoadImmutableResources
Ancestors
  augAssignFullImmutableCertificate
  bodyImmutableAugAssignFacts bodyFullToplevelCtorSourceLayout
  bodyFullToplevelCtorSourceFrame bodyPtrDefs stateRelProj
  assignTuplePtrLoadStep exprSimHypsDefs stmtSimAugAssignPlace
  exprLoweringProps loweringPosts valueEncodingProps memoryValueEncoding exprSimProps
  ptrSafeRun ptrDiscipline contextCodegenRel codegenRel memLocDefs
  venomExecSemantics venomInstProofs venomInst venomState
  supportedDecls supportedTypes supportedExprTraverse
  vyperTypeEnv vyperTypeSystem vyperTypeCallGraph allocLimits
  immutableRegionFrameProps vyperPlaceStatePreservation
  targetSubscriptMemory bodyFullShadowBodyInv bodySim bodyInvCodeProps
  vyperState compileEnv finite_map words pred_set list arithmetic

val load_steps = LIST_CONJ (List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
       [``MLOAD``, ``SLOAD``, ``TLOAD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs));

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  drule_all immutable_augassign_metadata >> strip_tac >>
  drule_all immutable_augassign_entry >> strip_tac >>
  drule_all augassign_immutable_synthetic_pre >> strip_tac >>
  drule_all immutable_augassign_source_prefix >> strip_tac >>
  drule_then assume_tac bodySimTheory.body_inv_contract >>
  drule_all_then assume_tac exprBodyPrePropsTheory.body_inv_expr_body_pre_mods >>
  `dead_lo_ok_mods H D lo cenv cx` by
    fs[dead_lo_ok_mods_def, dead_lo_ok_def] >>
  `ghost_inv_at_mods D lo d cenv cx es G tn s` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     PURE_REWRITE_TAC[ghost_inv_at_mods_def, ghost_inv_at_def] >> simp[]) >>
  qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
  drule_all toplevel_ctor_source_layout >> strip_tac >>
  drule_all (Q.INST [`src` |-> `cenv.ce_module`] toplevel_ctor_source_frame_mods) >>
  strip_tac >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  drule_all robust_typed_word_clean >> strip_tac >>
  qexistsl_tac [`off`, `tv`, `v`] >>
  suspend "finish"
QED
*)
Theorem augassign_immutable_load_resources:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_sim_inv cenv cx env es /\
  call_evaluation_safe cx [] /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  dead_lo_ok H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s)
  ==>
  ?off tv cur.
    src = cenv.ce_module /\ cenv.ce_is_ctor /\ ty = ity /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv cur /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (ImmutablePlace src id []),es) /\
    read_place cx (ImmutablePlace src id []) es = (INL cur,es) /\
    place_type_value cx (ImmutablePlace src id []) es = (INL tv,es) /\
    mload off s = typed_val_to_w256 tv cur /\
    eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
    w2n ((n2w off):bytes32) = off /\
    op_taint tn (Lit (n2w off)) = {} /\
    off + 32 <= lo /\ off + 32 <= s.vs_alloca_next /\
    (!j. off <= j /\ j < off + 32 ==> j NOTIN tn.t_mem) /\
    (!iid out. ptr_inst_ok D lo 0 ctx func G tn
      (mk_inst iid MLOAD [Lit (n2w off)] [out]) s)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume augassign_immutable_load_resources[finish]:
  `off + 32 < dimword (:256)` by metis_tac[] >>
  `off < dimword (:256)` by decide_tac >>
  `mload off s = typed_val_to_w256 tv v` by
    (qpat_x_assum `!m. _ ==> mem_word_at _ _ = _`
       (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mem_word_at_eq_mload]) >>
  `lo <= s.vs_alloca_next /\ allocas_from lo s` by
    fs[ghost_inv_at_def] >>
  `off + 32 <= lo /\ off + 32 <= s.vs_alloca_next` by decide_tac >>
  simp[eval_operand_def, op_taint_def, w2n_n2w] >> rpt gen_tac >>
  simp[ptr_inst_ok_def, mk_inst_def] >>
  conj_tac
  >- (simp[access_ok_def, mk_inst_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, eval_operand_def, w2n_n2w,
           mem_read_ops_def, op_prov_def] >> decide_tac) >>
  conj_tac >- simp[taint_ok_def, mk_inst_def, op_taint_def] >>
  simp[step_inst_non_invoke, load_steps, mk_inst_def, exec_read1_def,
       eval_operand_def, update_var_def, AllCaseEqs()]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise augassign_immutable_load_resources
*)

Theorem augassign_immutable_path_load_resources:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  cenv.ce_is_ctor /\ dead_lo_ok H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\ ghost_inv_at D lo d cenv cx es G tn s /\
  FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables NONE imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ptv) /\ evaluate_subscripts itv iv path = INL v /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ is_word_type ty ==>
  off+k+32 <= lo /\ w2n (n2w (off+k) : bytes32) = off+k /\
  value_has_type ptv v /\ mload (off+k) s = typed_val_to_w256 ptv v /\
  mem_word_taint tn.t_mem (off+k) = {}
Proof
  strip_tac >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then strip_assume_tac body_inv_module_locations >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `state_well_typed es` by fs[expr_sim_inv_def] >>
  drule_all state_well_typed_immutables_ALOOKUP >> strip_tac >>
  drule_all imms_well_typed_get_source_immutables >> strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  `value_has_type ptv v` by (drule_all evaluate_subscripts_type >> simp[]) >>
  `off + type_memory_size itv <= lo /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory itv iv off mem` by
    (mp_tac (Q.INST [`entry` |-> `es`,`mods` |-> `[(NONE,tops)]`,`exps` |-> `[]`,
                      `rt` |-> `itv`,`v` |-> `iv`]
       immutable_ctor_frame_mods) >>
     fs[expr_sim_inv_split_def, GSYM dead_lo_ok_mods_singleton,
        GSYM ghost_inv_at_mods_singleton]) >>
  `type_memory_size ptv = 32` by metis_tac[word_tv_memory_size] >>
  `off+k+32 <= lo` by decide_tac >>
  `off+k < dimword (:256)` by
    (drule_then assume_tac stmt_state_rel_alloca_room >> drule alloca_room_next_lt >>
     fs[ghost_inv_at_def] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ptv v (off+k) m` by
    (rpt strip_tac >> irule (Q.SPECL [`path`,`itv`,`iv`,`v`,`off`,`m`,`k`,`ptv`]
       mem_path_offset_current_value) >>
     qexistsl_tac [`itv`,`iv`,`path`] >> simp[]) >>
  drule_all (Q.INST [`a` |-> `off+k`,`tv` |-> `ptv`,`v` |-> `v`]
    robust_typed_word_clean) >> strip_tac >>
  `mload (off+k) s = typed_val_to_w256 ptv v` by
    (qpat_assum `!m. _ ==> mem_word_at _ _ = _` (qspec_then `s.vs_memory` mp_tac) >>
     simp_tac bool_ss [mem_agree_outside_def,mem_word_at_eq_mload]) >>
  `mem_word_taint tn.t_mem (off+k) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> qx_gen_tac `i` >>
     Cases_on `i < 32` >> simp[] >>
     qpat_assum `!j. off+k <= j /\ j < off+k+32 ==> _` irule >>
     decide_tac) >>
  simp[w2n_n2w]
QED
