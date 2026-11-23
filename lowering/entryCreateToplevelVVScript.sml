(* A top-level lookup returns a place; it does not load through that place.
   Use the supplier's source trace before packing the scoped outcome. *)
Theory entryCreateToplevelVV
Ancestors
  entryCreateCompositeFocus entryCreateFocusSpec entryCreatePendingScope
  entryCreateStmtCases bodyFullToplevelVV bodyFullToplevelVVNil s1PrefixDefs
  entryCreateCompletedCut fragGasOriginPtr fragGasOrigin gasOutcomeFull gasStorage gasSummary
  vyperStorageFootprint
  createSizePrefixReplay exprLowering exprLoweringProps emitHelperProps emitHelper
  compileEnv fragExec abiEncoderProps venomInst venomExecProofs venomFnInstsProofs
  vyperAST finite_map list pair

Theorem toplevel_vv_nil_scoped[local]:
  toplevel_vv_nil (DF,lo,d,ctx,func) ce cx ty e es ==>
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
Proof
  rw[expr_vv_sim_scoped_def] >> fs[expr_vv_sim_full_pre_def,toplevel_vv_nil_def] >>
  first_x_assum drule_all >> strip_tac >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (`sb = sa` by metis_tac[storage_trace_domain_def] >> gvs[] >>
      irule scoped_operand_pure >> reverse conj_tac >- simp[] >>
      qexistsl_tac [`ee`,`INL tv`] >> simp[] >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` drule >>
      simp[create_operand_vv_post_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj1_tac >> simp[gas_bad_storage_at_def,gas_explicit_def] >>
  conj_tac
  >- (irule create_operand_focus_scope_caller >> qexists_tac `s0` >>
      simp[create_expr_prefix_marked]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G0`,`tn0`,`s0`] >>
  simp[storage_trace_domain_def,gas_origin_ptr_focus_nil]
QED

(* On an invalid layout the compiler can emit INVALID instead of returning
   a literal pointer. This exception cannot own a selected CREATE visit. *)
Theorem compile_toplevel_vv_layout[local]:
  compile_expr ce ty (TopLevelName ann nsid) a = (vv,b) ==>
  b = a \/ emit_inst INVALID [] [] a = ((),b)
Proof
  Cases_on `emit_inst INVALID [] [] a` >> Cases_on `q` >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid`
  >- simp[compile_expr_def,expr_type_def] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >>
  simp[compile_expr_def,expr_type_def]
QED

Theorem fetch_fn_insts[local]:
  lookup_block lbl f.fn_blocks = SOME bb /\ get_instruction bb n = SOME i ==>
  MEM i (fn_insts f)
Proof
  strip_tac >> irule MEM_fn_insts >> qexists_tac `bb` >>
  conj_tac >- metis_tac[lookup_block_MEM] >>
  fs[get_instruction_def,AllCaseEqs(),MEM_EL] >> metis_tac[]
QED

Theorem toplevel_invalid_fetch[local]:
  emit_inst INVALID [] [] a = ((),b) /\ fn_has_code a b f /\
  fn_inst_ids_distinct f /\ create_operand_fetch a b f u i ==>
  i.inst_opcode = INVALID
Proof
  strip_tac >> drule emitted_insts_emit_inst >> strip_tac >>
  `b.cs_current_insts = a.cs_current_insts ++ [mk_inst a.cs_next_id INVALID [] []]` by
    gvs[emit_inst_def,comp_bind_def,comp_return_def,fresh_id_def,emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!j. j < LENGTH _ ==> _`
    (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  fs[create_operand_fetch_def,frag_ids_def] >>
  `i.inst_id = a.cs_next_id` by decide_tac >>
  `i = mk_inst a.cs_next_id INVALID [] []` by
    (`(mk_inst a.cs_next_id INVALID [] []).inst_id = a.cs_next_id` by simp[mk_inst_def] >>
     irule fn_insts_id_unique >> conj_tac >- simp[] >> qexists_tac `f` >>
     metis_tac[fetch_fn_insts]) >>
  simp[mk_inst_def]
QED

Theorem toplevel_vv_cut[local]:
  compile_expr ce ty (TopLevelName ann nsid) a = (vv,b) /\
  fn_has_code a b f /\ fn_inst_ids_distinct f /\ create_operand_at a s ==>
  create_operand_cut a b E C f tops cx st0 (eval_expr cx (TopLevelName ann nsid)) (es,s)
Proof
  strip_tac >> drule compile_toplevel_vv_layout >> strip_tac
  >- (gvs[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]) >>
  rw[create_operand_cut_def] >> drule create_interior_visit_cases >> strip_tac
  >- (gvs[] >> drule_all toplevel_invalid_fetch >> strip_tac >>
      irule create_cut_noncreate_visit >> simp[]) >>
  drule_all toplevel_invalid_fetch >> simp[]
QED

Theorem create_toplevel_name_vv_case:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env (TopLevelName ann nsid) es ==>
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (TopLevelName ann nsid) es /\
  !st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx ty (TopLevelName ann nsid) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (TopLevelName ann nsid)) (es,s0)
Proof
  strip_tac >> conj_tac
  >- (irule toplevel_vv_nil_scoped >> irule toplevel_name_vv_nil >> metis_tac[]) >>
  rw[expr_vv_sim_full_pre_def] >> irule toplevel_vv_cut >>
  simp[create_operand_at_def] >> metis_tac[]
QED
