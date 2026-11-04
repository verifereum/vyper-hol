(* Positions in the actual supply-threaded instruction expansion. *)
Theory lowerDloadConfiguredOrigins
Ancestors
  o1ContractLowerDload o1PassContract lowerDloadDefs
  venomPassDispatcher irSupply venomExecSemantics contextCodegenRel
  venomInst venomWf list rich_list arithmetic

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

Theorem lower_dload_inst_supply_phi_length:
  lower_dload_inst_supply u i = (xs,v) ==>
  phi_prefix_length (xs ++ rest) =
    if i.inst_opcode = PHI then SUC (phi_prefix_length rest) else 0
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[phi_prefix_length_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[phi_prefix_length_def]) >>
  simp[lower_dload_inst_supply_def] >> strip_tac >>
  gvs[phi_prefix_length_def]
QED

Theorem lower_dload_insts_supply_phi_length:
  !u xs v. lower_dload_insts_supply u ins = (xs,v) ==>
  phi_prefix_length xs = phi_prefix_length ins
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> drule lower_dload_inst_supply_phi_length >>
  disch_then (qspec_then `outs` mp_tac) >>
  first_x_assum drule >> simp[phi_prefix_length_def]
QED

Theorem lower_dload_inst_supply_eval_phis:
  lower_dload_inst_supply u i = (xs,v) ==>
  eval_phis s (xs ++ rest) = eval_phis s (i::rest)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[eval_phis_def]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[eval_phis_def]) >>
  simp[lower_dload_inst_supply_def] >> strip_tac >> gvs[]
QED

Theorem lower_dload_insts_supply_eval_phis:
  !u xs v. lower_dload_insts_supply u ins = (xs,v) ==>
  eval_phis s xs = eval_phis s ins
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> drule lower_dload_inst_supply_eval_phis >>
  disch_then (qspecl_then [`s`,`outs`] mp_tac) >>
  first_x_assum drule >> simp[eval_phis_def]
QED

Theorem lower_dload_blocks_supply_lookup:
  !u cs v. lower_dload_blocks_supply u bs = (cs,v) /\
  lookup_block label bs = SOME b ==>
  ?u0 is u1.
    lower_dload_insts_supply u0 b.bb_instructions = (is,u1) /\
    lookup_block label cs = SOME (b with bb_instructions := is)
Proof
  Induct_on `bs`
  >- simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs(), lookup_block_def, FIND_thm] >> strip_tac >>
  Cases_on `h.bb_label = label` >> gvs[]
  >- (qexistsl_tac [`u`,`insts`,`s1`] >> simp[FIND_thm]) >>
  simp[FIND_thm] >>
  gvs[GSYM lookup_block_def] >> first_x_assum drule_all >> simp[]
QED

Theorem lower_dload_function_supply_enters_block:
  lower_dload_function_supply u f = (g,v) /\ enters_block f s s1 ==>
  enters_block g s s1
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[enters_block_def] >>
  drule_all lower_dload_blocks_supply_lookup >> strip_tac >>
  drule lower_dload_insts_supply_eval_phis >>
  disch_then (qspec_then `s` assume_tac) >>
  drule lower_dload_insts_supply_phi_length >> strip_tac >>
  qexistsl_tac [`bb with bb_instructions := is`,`s_phi`] >> simp[]
QED

Theorem lower_dload_blocks_supply_lookup_origin:
  !u cs v. lower_dload_blocks_supply u bs = (cs,v) /\
  lookup_block label cs = SOME b' ==>
  ?b u0 is u1.
    lookup_block label bs = SOME b /\
    lower_dload_insts_supply u0 b.bb_instructions = (is,u1) /\
    b' = b with bb_instructions := is
Proof
  Induct_on `bs`
  >- simp[lower_dload_blocks_supply_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs(), lookup_block_def, FIND_thm] >> strip_tac >>
  Cases_on `h.bb_label = label` >> gvs[FIND_thm]
  >- (qexistsl_tac [`u`,`insts`,`s1`] >> simp[]) >>
  gvs[GSYM lookup_block_def] >> first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`b`,`u0`,`is`,`u1`] >>
  simp[lookup_block_def, FIND_thm]
QED

Theorem lower_dload_function_supply_enters_block_origin:
  lower_dload_function_supply u f = (g,v) /\ enters_block g s s1 ==>
  enters_block f s s1
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[enters_block_def] >>
  drule_all lower_dload_blocks_supply_lookup_origin >> strip_tac >>
  drule lower_dload_insts_supply_eval_phis >>
  disch_then (qspec_then `s` assume_tac) >>
  drule lower_dload_insts_supply_phi_length >> strip_tac >>
  qexistsl_tac [`b`,`s_phi`] >> gvs[]
QED

(* Resolving original operands through the expanded prefix must not see
   private definitions.  A malformed DLOADBYTES may carry outputs that
   lowering drops, hence the well-formedness premise is essential. *)
Theorem lower_dload_inst_supply_resolve:
  lower_dload_inst_supply u i = (xs,v) /\ inst_wf i /\
  (!w. op = Var w ==> MEM w u.irs_used_vars) ==>
  resolve_block_assigns (REVERSE xs ++ rest) op =
  resolve_block_assigns (i::rest) op
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >>
      Cases_on `op` >> gvs[resolve_block_assigns_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >>
      gvs[inst_wf_def] >>
      Cases_on `op` >> gvs[resolve_block_assigns_def] >> metis_tac[]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem lower_dload_inst_supply_used_vars_mono:
  lower_dload_inst_supply u i = (xs,v) /\ MEM w u.irs_used_vars ==>
  MEM w v.irs_used_vars
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem lower_dload_insts_supply_used_vars_mono:
  !u xs v. lower_dload_insts_supply u ins = (xs,v) /\ MEM w u.irs_used_vars ==>
  MEM w v.irs_used_vars
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all lower_dload_inst_supply_used_vars_mono >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem lower_dload_insts_supply_resolve:
  !u xs v rest op.
  lower_dload_insts_supply u ins = (xs,v) /\ EVERY inst_wf ins /\
  (!i w. MEM i ins /\ MEM (Var w) i.inst_operands ==>
         MEM w u.irs_used_vars) /\
  (!w. op = Var w ==> MEM w u.irs_used_vars) ==>
  resolve_block_assigns (REVERSE xs ++ rest) op =
  resolve_block_assigns (REVERSE ins ++ rest) op
Proof
  Induct_on `ins` using SNOC_INDUCT
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> rewrite_tac[SNOC_APPEND] >> strip_tac >>
  drule lower_dload_insts_supply_append >> strip_tac >>
  gvs[lower_dload_insts_supply_def, AllCaseEqs(), EVERY_APPEND] >>
  `!w. op = Var w ==> MEM w u'.irs_used_vars` by
    metis_tac[lower_dload_insts_supply_used_vars_mono] >>
  drule_all lower_dload_inst_supply_resolve >>
  disch_then (qspec_then `REVERSE ys ++ rest` mp_tac) >>
  pure_rewrite_tac[REVERSE_APPEND, GSYM APPEND_ASSOC, REVERSE_DEF, APPEND] >>
  disch_then SUBST1_TAC >>
  Cases_on `op` >> simp[resolve_block_assigns_def] >>
  IF_CASES_TAC >> simp[]
  >- (IF_CASES_TAC >> simp[] >>
      first_x_assum irule >> qexistsl_tac [`u`,`u'`] >> simp[] >> conj_tac
      >- metis_tac[] >>
      Cases_on `x.inst_operands` >> gvs[] >> metis_tac[MEM]) >>
  first_x_assum irule >> qexistsl_tac [`u`,`u'`] >> simp[] >> metis_tac[]
QED

Theorem lower_dload_insts_supply_length:
  !u xs v. lower_dload_insts_supply u ins = (xs,v) ==>
  LENGTH ins <= LENGTH xs
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  drule lower_dload_inst_supply_nonempty >> strip_tac >>
  first_x_assum drule >> Cases_on `out` >> gvs[]
QED

Theorem lower_dload_insts_supply_append_eq:
  !u xs v ys w.
  lower_dload_insts_supply u pre = (xs,v) /\
  lower_dload_insts_supply v post = (ys,w) ==>
  lower_dload_insts_supply u (pre ++ post) = (xs ++ ys,w)
Proof
  Induct_on `pre`
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once lower_dload_insts_supply_def] >> gvs[APPEND_ASSOC]
QED
