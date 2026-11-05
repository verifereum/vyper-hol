(*
 * Counted struct literal store loop (#636)
 *
 * The gas-counted form of exprSimAggregateLoops' struct field loop, for
 * the struct literal case of exprSimAggregates.
 *
 * TOP-LEVEL:
 *   aggregate_struct_fields_counted — compile_struct_lit
 *)
Theory exprSimAggregatesStructCounted
Ancestors
  exprSimAggregatesLoopsCounted
  exprSimAggregateLoops exprSimAggregateChildren exprSimAlloc
  exprSimHyps exprSimHypsDefs exprSimSource exprSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasSummaryCompose gasContext
  fragGasMode fragGasPath fragGasSeq fragExec
  exprLowering exprLoweringProps compileEnv valueEncoding
  vyperInterpreter vyperState

(* Post transport keeps the counted execution and exemption witnesses intact. *)
Theorem struct_gas_outcome_post[local]:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R /\
  (!res es' r. Q res es' r ==> Q' res es' r) ==>
  gas_outcome memory tops (ctx,func) source (es,s0) Q' R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED

Theorem struct_tuple_memory_post[local]:
  !names tvs vs ptr mem.
  LENGTH names = LENGTH tvs /\ tuple_in_memory vs tvs ptr mem ==>
  fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) ptr mem
Proof
  Induct_on `names` >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[listTheory.ZIP_def, valueEncodingTheory.val_in_memory_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem aggregate_struct_fields_counted:
  !fields ce cx env ty off sa out sb es tvs func inst x b asz s0 ctx nocalls.
  EVERY (\(name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields
      (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields /\
  compile_struct_lit compile_expr ce ty fields (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (MAP SND fields)) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx (MAP SND fields) /\
  (~nocalls ==> !e. MEM e (MAP SND fields) ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx (MAP SND fields)) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      fields_in_memory (ZIP (MAP FST fields,vs))
        (ZIP (MAP FST fields,tvs)) (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  drule exprSimAggregateLayoutTheory.compile_struct_lit_as_tuple >>
  disch_then (qspecl_then [`compile_expr`, `Var x`, `off`] assume_tac) >>
  gvs[] >>
  drule aggregate_make_tuple_counted >>
  disch_then drule >>
  disch_then (drule_at (Pat `exprs_case _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspec_then `es` mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- metis_tac[] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >> simp[] >>
  drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[] >> strip_tac >>
  irule struct_gas_outcome_post >>
  goal_assum (drule_at Any) >>
  BETA_TAC >> rpt strip_tac >> qexists_tac `vs` >> gvs[] >> simp[] >>
  conj_tac >- (irule struct_tuple_memory_post >> simp[]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
