(* Counted traversal of the remaining struct fields. *)
Theory bodyIntCallFamAggStructLoop
Ancestors
  bodyIntCallFamAggStructFields bodyIntCallFamAggStructSource bodyIntCallFamAggStructCode
  bodyIntCallJointAggCore stmtReasonVvMemory exprSimAggregateLoops
  exprSimHypsDefs exprSimHyps exprLowering compileEnv exprSimMemDefs
  valueEncoding vyperValue

Theorem intcall_struct_fields_counted:
  !fields tvs off sa sb es s out.
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  EVERY (\(name,e). ALOOKUP (get_struct_fields ce.ce_struct_fields
    (case ty of StructT n => nsid_to_string n | _ => "")) name =
    SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields /\
  OPT_MMAP (evaluate_type (get_tenv fp.jc_cx)) (MAP expr_type (MAP SND fields)) = SOME tvs /\
  (!e. MEM e (MAP SND fields) ==> intcall_expr_producer fp e /\
    supportedExprs$supported_expr fp.jc_tops e /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) /\
  (!e ee. MEM e (MAP SND fields) /\ expr_sim_inv ce fp.jc_cx env ee ==>
    expr_body_pre ce fp.jc_cx env e ee) /\
  compile_struct_lit compile_expr ce ty fields buf off sa = (out,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es0 sa0 s0 /\
  intcall_expr_cont fp ce env es0 sa0 s0 es sa s /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  sa0.cs_next_var <= sa.cs_next_var /\ sa0.cs_next_id <= sa.cs_next_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  sa0.cs_next_id <= inst.inst_id /\ inst.inst_id < sa.cs_next_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  eval_operand buf s = SOME bw /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  fp.jc_lo <= b /\ b <= w2n bw /\
  w2n bw + off + type_memory_size_list tvs <= b+k /\ b+k < dimword (:256) /\
  EVERY (\tv. type_memory_size tv + 64 < dimword (:256)) tvs /\
  (!name a n. local_region ce es.scopes s name a n ==> regions_disjoint b k a n) /\
  (!name a n. local_region ce es0.scopes s0 name a n ==> regions_disjoint b k a n)
  ==>
  out = buf /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx (MAP SND fields)) (es,s)
    (\res ee u. ?vs. res = INL vs /\ LENGTH vs = LENGTH fields /\
      fields_in_memory (ZIP (MAP FST fields,vs)) (ZIP (MAP FST fields,tvs))
        (w2n bw+off) u.vs_memory /\
      intcall_expr_cont fp ce env es0 sa0 s0 ee sb u /\
      FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
      eval_operand buf u = SOME bw /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      (!name a n. local_region ce ee.scopes u name a n ==> regions_disjoint b k a n) /\
      (!a n. b <= a /\ a+n <= b+k /\
        (a+n <= w2n bw+off \/ w2n bw+off+type_memory_size_list tvs <= a) ==>
        mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory))
    (\res ee r. expr_exit res r)
Proof
  Induct_on `fields`
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_struct_lit_def, comp_return_def] >>
      drule intcall_struct_fields_nil >>
      disch_tac >> irule gas_outcome_post_mono >>
      goal_assum (drule_at Any) >>
      simp[valueEncodingTheory.val_in_memory_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qx_gen_tac `h` >> PairCases_on `h` >> rename1 `(name,e)::fields` >>
  rpt gen_tac >> strip_tac >>
  gvs[CaseEq "option"] >>
  drule_all compile_struct_lit_cons_code >> strip_tac >>
  `expr_body_pre ce fp.jc_cx env e es` by
    (first_assum irule >> simp[] >>
     fs[bodyIntCallJointContractTheory.intcall_expr_cont_def,
        bodyIntCallJointContractTheory.intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def]) >>
  drule struct_child_store_types >> strip_tac >>
  pop_assum (qspecl_then [`op`,`dst`] strip_assume_tac) >>
  conj_tac >- metis_tac[exprOperandVarTheory.compiler_struct_lit_result] >>
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,s)
    (\res ee u. ?v. res = INL v /\
      val_in_memory h v (w2n bw + off) u.vs_memory /\
      intcall_expr_cont fp ce env es0 sa0 s0 ee st u /\
      FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
      eval_operand buf u = SOME bw /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      (!name a n. local_region ce ee.scopes u name a n ==> regions_disjoint b k a n) /\
      (!a n. b <= a /\ a+n <= b+k /\
        (a+n <= w2n bw+off \/ w2n bw+off+type_memory_size h <= a) ==>
        mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory))
    (\res ee r. expr_exit res r)` by suspend "head_store" >>
  rewrite_tac[listTheory.MAP, pairTheory.SND, exprSimWordArgsTheory.eval_exprs_cons_action] >>
  irule gas_outcome_bind_value >> goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac
  >- (Cases >> simp[exprSimDefsTheory.expr_exit_INL,
       stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all gas_marked_materialised_child_wf >> strip_tac >>
  suspend "tail"
QED

Resume intcall_struct_fields_counted[head_store]:
    (`intcall_expr_producer fp e /\
      supportedExprs$supported_expr fp.jc_tops e /\
      calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)` by
       (qpat_x_assum `!e'. _ \/ _ ==> _` (qspec_then `e` mp_tac) >> simp[]) >>
     irule intcall_counted_child_store >>
     simp[] >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- (fs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
     qexistsl_tac [`dst`,`expr_type e`,`op`,`sa`,`sm`,`sn`,`su`,`vv`] >>
     fs[] >> decide_tac)
QED

Resume intcall_struct_fields_counted[tail]:
  rename1 `val_in_memory h v (off + w2n bw) landed.vs_memory` >>
  `type_memory_bytes ce (expr_type e) = type_memory_size h` by
    (irule expr_sim_inv_memory_size >>
     qexistsl_tac [`fp.jc_cx`,`env`,`es`] >>
     fs[expr_body_pre_def]) >>
  `!x. buf = Var x ==> not_fresh_at st x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  qpat_x_assum `!off' sa' sb' es' s'' out'. _`
    (qspecl_then [`off + type_memory_size h`,`st`,`sb`,
      `mid with gas_obs := []`,`landed`,`out`] mp_tac) >>
  simp[] >>
  impl_tac >- (fs[type_memory_size_def] >> rpt conj_tac >>
    first_assum MATCH_ACCEPT_TAC) >>
  strip_tac >>
  irule gas_outcome_return_map >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (Cases >> simp[exprSimDefsTheory.expr_exit_INL,
    stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  conj_tac
  >- (pure_rewrite_tac[Once val_in_memory_def] >>
      simp[] >>
      irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
      conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      qexistsl_tac [`type_memory_size h`,`landed.vs_memory`] >>
      simp[] >> sym_tac >> first_x_assum irule >>
      fs[type_memory_size_def] >> decide_tac) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at a n t'.vs_memory = mem_bytes_at a n landed.vs_memory` by
    (first_x_assum irule >> fs[type_memory_size_def] >> decide_tac) >>
  `mem_bytes_at a n landed.vs_memory = mem_bytes_at a n s.vs_memory` by
    (first_x_assum irule >> fs[type_memory_size_def] >> decide_tac) >>
  simp[]
QED

Finalise intcall_struct_fields_counted
