(* Successful decoder paths transport the frontier charge across instructions
   and PHI updates. *)
Theory decoderOriginAllocationFrame
Ancestors
  fragGasOriginPtr allocaFrontierRoom allocaFrontierBound allocaBudgetProps
  ctxLookupAgreeHelpers exprLoweringProps ptrDiscipline
  allocaRemapSSA venomExecProofs venomInstIdsProps venomWf venomInst
  venomState venomMemDefs venomExecSemantics fragExec finite_map list arithmetic

Theorem decoder_origin_edge_allocation_frame[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,H,u) /\
  fn_inst_ids_distinct fn ==>
  t.vs_initial_fmp = s.vs_initial_fmp /\
  t.vs_alloca_next + pending_alloca_size fn t =
    s.vs_alloca_next + pending_alloca_size fn s
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists_tac `bb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    fs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id] >>
  Cases_on `middle` >> gvs[exit_result_def] >>
  drule_all step_inst_alloca_budget >>
  rewrite_tac[GSYM deploy_ctor_pending_alloca_eq] >> disch_tac >>
  drule step_inst_initial_fmp >> strip_tac >>
  imp_res_tac eval_phis_preserves_alloca_fields >>
  imp_res_tac eval_phis_initial_fmp >>
  fs[pending_alloca_size_def] >> metis_tac[]
QED

Theorem decoder_origin_path_allocation_frame:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,H,u) /\
  fn_inst_ids_distinct fn ==>
  t.vs_initial_fmp = s.vs_initial_fmp /\
  t.vs_alloca_next + pending_alloca_size fn t =
    s.vs_alloca_next + pending_alloca_size fn s
Proof
  qsuff_tac
    `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
      case (cx, st, out) of
        ((D,lo,explicit,ctx,fn,PG), (s,G,tn), (r,H,u)) =>
        !t. r = OK t /\ fn_inst_ids_distinct fn ==>
          t.vs_initial_fmp = s.vs_initial_fmp /\
          t.vs_alloca_next + pending_alloca_size fn t =
            s.vs_alloca_next + pending_alloca_size fn s`
  >- (rpt strip_tac >>
      first_x_assum drule >> simp[]) >>
  ho_match_mp_tac gas_origin_ptr_path_ind >>
  simp[exit_result_def] >> rpt strip_tac >> gvs[] >>
  drule_all decoder_origin_edge_allocation_frame >> strip_tac >>
  metis_tac[]
QED

Theorem decoder_origin_path_allocas_below_fmp:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,H,u) /\
  fn_inst_ids_distinct fn /\ t.vs_fmp = s.vs_fmp /\ alloca_inv t /\
  allocas_below_fmp s /\
  s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp ==>
  allocas_below_fmp t
Proof
  strip_tac >> drule_all decoder_origin_path_allocation_frame >> strip_tac >>
  qpat_x_assum `allocas_below_fmp s` (strip_assume_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
  qpat_x_assum `alloca_inv t`
    (strip_assume_tac o REWRITE_RULE [alloca_inv_def, alloca_next_valid_def]) >>
  simp[allocas_below_fmp_def] >> rpt strip_tac >> res_tac >> decide_tac
QED

Theorem decoder_origin_path_room:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,H,u) /\
  fn_inst_ids_distinct fn /\ t.vs_fmp = s.vs_fmp /\ alloca_inv t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
    t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp)
Proof
  strip_tac >> strip_tac >>
  qpat_assum `ctx_has_dalloca ctx ==> _` (drule_then strip_assume_tac) >>
  drule_all decoder_origin_path_allocation_frame >> strip_tac >>
  drule_all decoder_origin_path_allocas_below_fmp >> simp[]
QED
