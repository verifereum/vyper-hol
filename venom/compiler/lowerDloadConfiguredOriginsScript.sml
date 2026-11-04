(* Positions in the actual supply-threaded instruction expansion. *)
Theory lowerDloadConfiguredOrigins
Ancestors
  o1ContractLowerDload o1PassContract lowerDloadDefs
  venomPassDispatcher irSupply list rich_list arithmetic

Theorem lower_dload_insts_supply_at:
  lower_dload_insts_supply u ins = (outs,v) /\ j < LENGTH ins ==>
  ?pre u0 X u1 post.
    lower_dload_insts_supply u (TAKE j ins) = (pre,u0) /\
    lower_dload_inst_supply u0 (EL j ins) = (X,u1) /\
    lower_dload_insts_supply u1 (DROP (SUC j) ins) = (post,v) /\
    outs = pre ++ X ++ post
Proof
  qid_spec_tac `u` >> qid_spec_tac `ins` >>
  qid_spec_tac `outs` >> qid_spec_tac `v` >>
  Induct_on `j` >> rpt gen_tac >> Cases_on `ins` >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac
  >- (qexistsl_tac [`[]`,`u`,`out`,`s1`,`outs'`] >>
      simp[lower_dload_insts_supply_def]) >>
  first_x_assum (qspecl_then [`v`,`outs'`,`t`,`s1`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`out ++ pre`,`u0`,`X`,`u1`,`post`] >>
  simp[Once lower_dload_insts_supply_def, APPEND_ASSOC] >>
  gvs[APPEND_ASSOC]
QED

(* The prefix supply at the next source boundary is exactly the supply
   returned by the current expansion, including the final boundary. *)
Theorem lower_dload_insts_supply_next:
  lower_dload_insts_supply u (TAKE j ins) = (pre,u0) /\
  lower_dload_inst_supply u0 (EL j ins) = (X,u1) /\
  j < LENGTH ins ==>
  lower_dload_insts_supply u (TAKE (SUC j) ins) = (pre ++ X,u1)
Proof
  qid_spec_tac `u` >> qid_spec_tac `ins` >>
  qid_spec_tac `pre` >> Induct_on `j` >> rpt gen_tac >>
  Cases_on `ins` >>
  simp[lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once lower_dload_insts_supply_def, APPEND_ASSOC]
QED

Theorem lower_dload_blocks_supply_at:
  lower_dload_blocks_supply u bs = (cs,v) /\ j < LENGTH bs ==>
  ?pre u0 b u1 post.
    lower_dload_blocks_supply u (TAKE j bs) = (pre,u0) /\
    lower_dload_block_supply u0 (EL j bs) = (b,u1) /\
    lower_dload_blocks_supply u1 (DROP (SUC j) bs) = (post,v) /\
    cs = pre ++ b::post /\ LENGTH pre = j /\ EL j cs = b
Proof
  qid_spec_tac `u` >> qid_spec_tac `bs` >>
  qid_spec_tac `cs` >> qid_spec_tac `v` >>
  Induct_on `j` >> rpt gen_tac >> Cases_on `bs` >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  rpt strip_tac
  >- (gvs[] >> qexistsl_tac [`u`,`s1`] >>
      simp[lower_dload_blocks_supply_def]) >>
  first_x_assum (qspecl_then [`v`,`bbs'`,`t`,`s1`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`bb'::pre`,`u0`,`u1`,`post`] >>
  simp[Once lower_dload_blocks_supply_def] >> gvs[]
QED

(* Use an index rather than an inverse lookup on instruction ids: the
   threaded supply belongs to this occurrence of the block. *)
Theorem lower_dload_function_supply_block_at:
  lower_dload_function_supply u f = (g,v) /\
  j < LENGTH f.fn_blocks ==>
  ?pre u0 is u1 post.
    lower_dload_blocks_supply u (TAKE j f.fn_blocks) = (pre,u0) /\
    lower_dload_insts_supply u0 (EL j f.fn_blocks).bb_instructions = (is,u1) /\
    lower_dload_blocks_supply u1 (DROP (SUC j) f.fn_blocks) = (post,v) /\
    g.fn_blocks = pre ++ ((EL j f.fn_blocks) with bb_instructions := is)::post /\
    LENGTH pre = j /\
    EL j g.fn_blocks = (EL j f.fn_blocks) with bb_instructions := is
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all lower_dload_blocks_supply_at >> strip_tac >>
  gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  simp[EL_APPEND, NoAsms]
QED

(* The stage provides a supply for each function occurrence.  Keeping the
   coverage and freshness facts here avoids inventing an unrelated supply. *)
Theorem lower_dload_stage_supply_at:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  n < LENGTH C.ctx_functions ==>
  ?observed u out v.
    fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed u
      (EL n C.ctx_functions) out /\
    out.fpo_function = EL n C'.ctx_functions /\
    lower_dload_function_supply u (EL n C.ctx_functions) =
      (EL n C'.ctx_functions,v) /\
    ir_supply_covers_unit u observed /\
    ir_supply_extends u out.fpo_supply /\
    observed.cu_context.ctx_entry = C.ctx_entry /\
    observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
    ctx_fn_names observed.cu_context = ctx_fn_names C /\
    view C' (EL n C.ctx_functions) observed
Proof
  rw[ctx_pass_stage_def, LIST_REL_EL_EQN] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`observed`,`s`,`out`] >> simp[] >>
  gvs[fn_pass_step_def, AllCaseEqs()] >> metis_tac[]
QED
