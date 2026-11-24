(* Mapping roots return a reference at the declaration's literal slot. *)
Theory entryCreateSubscriptMapBase
Ancestors
  entryCreateSubscriptMapSpec bodyFullSubscriptMapBase entryCreateCompositeFocus
  entryCreateFocusSpec entryCreatePendingScope entryCreateEffectFocus
  createSizeCutCode createSizePrefixReplay exprSimFullBundleProps
  exprLowering emitHelperProps bodySim stateRelProj exprLoweringProps
  gasOutcomeFull gasStorage gasSummary vyperStorageFootprint
  loweringStateRelDefs bodyPtrDefs ptrDiscipline venomState context
  vyperAST vyperState fragExec venomInst compileEnv list
  exprSimAbiGasBridge wordArgsPtr entryCreateCompletedCut

Theorem map_root_cut[local]:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  compile_expr ce ty (TopLevelName ann nsid) sa = (vv,sb) /\
  fn_has_code sa sb func /\ create_operand_at sa s ==>
  create_operand_cut sa sb E ctx func targets cx st0
    (eval_expr cx (TopLevelName ann nsid)) (es,s)
Proof
  strip_tac >>
  `sb = sa \/ emit_inst INVALID [] [] sa = ((),sb)` by
    (Cases_on `emit_inst INVALID [] [] sa` >> Cases_on `q` >>
     Cases_on `FLOOKUP ce.ce_module_vars nsid`
     >- gvs[compile_expr_def,expr_type_def] >>
     rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >>
     gvs[compile_expr_def,expr_type_def]) >>
  Cases_on `sb = sa`
  >- (gvs[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]) >>
  gvs[] >> irule create_effect_suffix_cut >>
  qexistsl_tac [`tops`,`ce`] >> simp[] >> conj_tac
  >- (`create_cut_code {} sa (SND (emit_inst INVALID [] [] sa))` by
       simp[create_cut_code_emit_inst, create_cut_targets_def] >> fs[]) >>
  drule emitted_insts_emit_inst >> strip_tac >>
  simp[frag_code_def,emitted_blocks_def,mk_inst_def,DROP_LENGTH_NIL]
QED

Theorem map_root_at[local]:
  body_inv tops ctx ce cx /\ expr_map_pre ce cx env (TopLevelName ann (src,id)) es ==>
  expr_map_sim_scoped_at L (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (TopLevelName ann (src,id)) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0)
Proof
  simp[expr_map_sim_scoped_at_def, expr_map_sim_full_pre_def, expr_sim_full_code_def] >>
  strip_tac >> strip_tac >> reverse conj_tac
  >- (irule map_root_cut >> metis_tac[]) >>
  drule_all toplevel_map_landing >> strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
        by fs[storage_trace_domain_def] >>
      `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es s0`
        by simp[] >>
      `vv = LocatedValue ann (mk_ptr (Lit (n2w slot)) (slot_loc tr)) /\ sb = sa` by
        metis_tac[stmt_state_rel_vars_rels] >>
      gvs[] >> irule scoped_operand_pure >> simp[] >>
      qexistsl_tac [`es`,`INL (HashMapRef tr (n2w slot) kt vt)`] >> simp[] >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> disch_then strip_assume_tac >>
      simp[expr_map_sim_full_post_def, expr_sim_full_endpoint_def, create_operand_at_def,
           mk_ptr_def, eval_operand_def, op_taint_def, op_prov_def, ghost_kept_at_refl,
           stmt_state_rel_start_gas_obs] >>
      conj_tac
      >- (qpat_assum `storage_well_formed_on cx es _` mp_tac >>
          simp[NoAsms, storage_well_formed_on_def, boolTheory.FORALL_BOOL,
               vyperStorageBackendTheory.get_storage_def]) >>
      qpat_assum `ghost_inv_at _ _ _ _ _ es _ _ _` mp_tac >>
      simp[NoAsms, ghost_inv_at_def] >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj1_tac >> simp[gas_bad_storage_at_def, gas_explicit_def] >>
  conj_tac
  >- (irule create_operand_focus_scope_caller >> qexists_tac `s0` >>
      simp[create_expr_prefix_marked]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G0`,`tn0`,`s0`] >>
  simp[storage_trace_domain_def, gas_origin_ptr_focus_nil]
QED

Theorem create_map_base_at:
  body_inv tops ctx ce cx /\ expr_map_pre ce cx env e es /\
  (!ann obj idx. e = Subscript ann obj idx ==>
    expr_map_sim_scoped_at L (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
      (st0,sa,sb,sha,shb,vv,s0,G0,tn0)) ==>
  expr_map_sim_scoped_at L (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0)
Proof
  strip_tac >> drule expr_map_pre_shape >> strip_tac >> gvs[] >>
  PairCases_on `id` >> irule map_root_at >> metis_tac[]
QED
