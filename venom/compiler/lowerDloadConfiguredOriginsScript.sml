(* Positions in the actual supply-threaded instruction expansion. *)
Theory lowerDloadConfiguredOrigins
Ancestors
  o1ContractLowerDload o1PassContract o1PassLift o1ScheduleDecompHelpers
  fmpStepBridge lowerDloadDefs
  venomPassDispatcher irSupply venomExecSemantics contextCodegenRel
  venomInst venomWf venomFnScheduleRunner venomExecProofs passSharedDefs list rich_list arithmetic
  contextCodegenRelProps

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

Theorem lower_dload_blocks_supply_used_vars_mono:
  !u cs v. lower_dload_blocks_supply u bs = (cs,v) /\
    MEM w u.irs_used_vars ==> MEM w v.irs_used_vars
Proof
  Induct_on `bs`
  >- simp[lower_dload_blocks_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> strip_tac >>
  first_x_assum (qspec_then `s1` irule) >>
  qexists_tac `bbs'` >> simp[] >>
  drule lower_dload_insts_supply_used_vars_mono >> metis_tac[]
QED

Theorem lower_dload_blocks_supply_lookup:
  !u cs v. lower_dload_blocks_supply u bs = (cs,v) /\
  lookup_block label bs = SOME b ==>
  ?u0 is u1.
    lower_dload_insts_supply u0 b.bb_instructions = (is,u1) /\
    lookup_block label cs = SOME (b with bb_instructions := is) /\
    (!w. MEM w u.irs_used_vars ==> MEM w u0.irs_used_vars)
Proof
  Induct_on `bs`
  >- simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs(), lookup_block_def, FIND_thm] >> strip_tac >>
  Cases_on `h.bb_label = label` >> gvs[]
  >- (qexistsl_tac [`u`,`insts`,`s1`] >> simp[FIND_thm]) >>
  simp[FIND_thm] >>
  gvs[GSYM lookup_block_def] >> first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`u0`,`is`,`u1`] >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[lower_dload_insts_supply_used_vars_mono]
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

(* The same for comparing two original operands through the expanded
   prefix: the expansion's private variables are never compared, and the
   DLOAD output is clobbered by its MLOAD as by the DLOAD itself. *)
Theorem same_after_assigns_non_assign_cons[local]:
  a.inst_opcode <> ASSIGN ==>
  (same_after_assigns (a::rest) op1 op2 <=>
   op1 = op2 \/
   ((!v. op1 = Var v ==> ~MEM v a.inst_outputs) /\
    (!v. op2 = Var v ==> ~MEM v a.inst_outputs) /\
    same_after_assigns rest op1 op2))
Proof
  strip_tac >> Cases_on `op1 = op2` >- simp[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  simp[same_after_assigns_def, step_back_assign_def] >> rw[] >> gvs[]
QED

Theorem lower_dload_inst_supply_same_after:
  lower_dload_inst_supply u i = (xs,v) /\ inst_wf i /\
  (!w. op1 = Var w ==> MEM w u.irs_used_vars) /\
  (!w. op2 = Var w ==> MEM w u.irs_used_vars) ==>
  same_after_assigns (REVERSE xs ++ rest) op1 op2 =
  same_after_assigns (i::rest) op1 op2
Proof
  `!w s s'. fresh_ir_var s = (w,s') ==>
     ~MEM w s.irs_used_vars /\ s'.irs_used_vars = w :: s.irs_used_vars` by
    metis_tac[fresh_ir_var_contract] >>
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      `~MEM alloca_v u.irs_used_vars /\ ~MEM add_v u.irs_used_vars` by
        metis_tac[MEM] >>
      simp[same_after_assigns_non_assign_cons] >>
      Cases_on `op1 = op2` >> simp[] >>
      Cases_on `op1` >> Cases_on `op2` >> simp[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[inst_wf_def] >>
      `~MEM add_v u.irs_used_vars` by metis_tac[] >>
      simp[same_after_assigns_non_assign_cons] >>
      Cases_on `op1 = op2` >> simp[] >>
      Cases_on `op1` >> Cases_on `op2` >> simp[] >> metis_tac[]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem step_back_assign_used_vars[local]:
  step_back_assign inst op = SOME op' /\
  (!w. op = Var w ==> MEM w l) /\
  (!w. MEM (Var w) inst.inst_operands ==> MEM w l) /\
  op' = Var w ==> MEM w l
Proof
  mp_tac (Q.INST [`P` |-> `set l`] step_back_assign_preserves_vars) >>
  simp[] >> metis_tac[]
QED

Theorem resolve_block_assigns_used_vars[local]:
  (!w. op = Var w ==> MEM w l) /\
  EVERY (\inst. !w. MEM (Var w) inst.inst_operands ==> MEM w l) xs /\
  resolve_block_assigns xs op = Var w ==> MEM w l
Proof
  mp_tac (Q.SPECL [`xs`,`op`,`set l`] resolve_block_assigns_preserves_vars) >>
  simp[] >> metis_tac[]
QED

Theorem lower_dload_insts_supply_same_after:
  !u xs v rest op1 op2.
  lower_dload_insts_supply u ins = (xs,v) /\ EVERY inst_wf ins /\
  (!i w. MEM i ins /\ MEM (Var w) i.inst_operands ==>
         MEM w u.irs_used_vars) /\
  (!w. op1 = Var w ==> MEM w u.irs_used_vars) /\
  (!w. op2 = Var w ==> MEM w u.irs_used_vars) ==>
  same_after_assigns (REVERSE xs ++ rest) op1 op2 =
  same_after_assigns (REVERSE ins ++ rest) op1 op2
Proof
  Induct_on `ins` using SNOC_INDUCT
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> rewrite_tac[SNOC_APPEND] >> strip_tac >>
  drule lower_dload_insts_supply_append >> strip_tac >>
  gvs[lower_dload_insts_supply_def, AllCaseEqs(), EVERY_APPEND] >>
  `(!w. op1 = Var w ==> MEM w u'.irs_used_vars) /\
   (!w. op2 = Var w ==> MEM w u'.irs_used_vars)` by
    metis_tac[lower_dload_insts_supply_used_vars_mono] >>
  `same_after_assigns (REVERSE zs ++ (REVERSE ys ++ rest)) op1 op2 <=>
   same_after_assigns (x::(REVERSE ys ++ rest)) op1 op2` by
    (irule lower_dload_inst_supply_same_after >>
     simp[] >> qexistsl_tac [`u'`,`v`] >> simp[]) >>
  pop_assum (fn th => simp[REVERSE_APPEND, REWRITE_RULE [APPEND_ASSOC] th]) >>
  simp[same_after_assigns_def] >> Cases_on `op1 = op2` >> simp[] >>
  Cases_on `step_back_assign x op1` >> Cases_on `step_back_assign x op2` >>
  simp[] >>
  first_x_assum irule >> qexistsl_tac [`u`,`u'`] >> simp[] >>
  `!w. MEM (Var w) x.inst_operands ==> w IN set u.irs_used_vars` by
    metis_tac[MEM] >>
  rpt conj_tac >- metis_tac[] >>
  rpt strip_tac >> metis_tac[step_back_assign_used_vars]
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

Theorem lower_dload_insts_supply_prefix_strict:
  !ins u k a u1 b u2.
  lower_dload_insts_supply u (TAKE j ins) = (a,u1) /\
  lower_dload_insts_supply u (TAKE k ins) = (b,u2) /\
  j < k /\ k <= LENGTH ins ==>
  LENGTH a < LENGTH b
Proof
  Induct_on `j`
  >- (rpt strip_tac >>
      gvs[lower_dload_insts_supply_def] >>
      drule lower_dload_insts_supply_length >>
      simp[LENGTH_TAKE] >> decide_tac) >>
  rpt gen_tac >> Cases_on `ins` >> Cases_on `k` >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

Theorem lower_dload_insts_supply_boundary_unique:
  lower_dload_insts_supply u (TAKE j ins) = (a,u1) /\
  lower_dload_insts_supply u (TAKE k ins) = (b,u2) /\
  j <= LENGTH ins /\ k <= LENGTH ins /\ LENGTH a = LENGTH b ==>
  j = k
Proof
  rpt strip_tac >> Cases_on `j < k`
  >- (drule_all lower_dload_insts_supply_prefix_strict >> simp[]) >>
  Cases_on `k < j`
  >- (drule_all lower_dload_insts_supply_prefix_strict >> simp[]) >>
  decide_tac
QED

(* Locate a target program counter inside the expansion of one source
   instruction, retaining both surrounding lists and their supply states. *)
Theorem lower_dload_insts_supply_position:
  !s xs t n. lower_dload_insts_supply s ins = (xs,t) /\ n < LENGTH xs ==>
  ?pre i post ys u zs v ws k.
    ins = pre ++ i::post /\
    lower_dload_insts_supply s pre = (ys,u) /\
    lower_dload_inst_supply u i = (zs,v) /\
    lower_dload_insts_supply v post = (ws,t) /\
    xs = ys ++ zs ++ ws /\ n = LENGTH ys + k /\ k < LENGTH zs
Proof
  Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `n < LENGTH out`
  >- (qexistsl [`[]`,`h`,`ins`,`[]`,`s`,`out`,`s1`,`outs`,`n`] >>
      simp[lower_dload_insts_supply_def]) >>
  `n - LENGTH out < LENGTH outs` by (gvs[] >> decide_tac) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`h::pre`,`i`,`post`,`out ++ ys`,`u`,`zs`,`v`,`ws`,`k`] >>
  simp[Once lower_dload_insts_supply_def] >>
  gvs[APPEND_ASSOC] >> decide_tac
QED

(* Unique source boundary covering a target instruction, even when the
   target instruction lies in the middle of a generated expansion. *)
Theorem lower_dload_insts_supply_envelope:
  lower_dload_insts_supply u ins = (xs,v) /\ n < LENGTH xs ==>
  ?j pre u0 X u1 post k.
    j < LENGTH ins /\
    lower_dload_insts_supply u (TAKE j ins) = (pre,u0) /\
    lower_dload_inst_supply u0 (EL j ins) = (X,u1) /\
    lower_dload_insts_supply u1 (DROP (SUC j) ins) = (post,v) /\
    xs = pre ++ X ++ post /\ n = LENGTH pre + k /\ k < LENGTH X
Proof
  strip_tac >> drule_all lower_dload_insts_supply_position >> strip_tac >>
  qexists_tac `LENGTH pre` >>
  simp[TAKE_APPEND, DROP_APPEND, EL_APPEND, DROP_LENGTH_TOO_LONG] >> metis_tac[]
QED

Theorem lower_dload_insts_supply_prefix_mono:
  lower_dload_insts_supply u (TAKE j ins) = (a,u1) /\
  lower_dload_insts_supply u (TAKE k ins) = (b,u2) /\
  j <= k /\ k <= LENGTH ins ==>
  LENGTH a <= LENGTH b
Proof
  rpt strip_tac >> Cases_on `j = k`
  >- gvs[] >>
  `j < k` by decide_tac >>
  drule_all lower_dload_insts_supply_prefix_strict >> simp[]
QED

Theorem lower_dload_insts_supply_envelope_order:
  lower_dload_insts_supply u (TAKE j ins) = (a,u0) /\
  lower_dload_inst_supply u0 (EL j ins) = (X,u1) /\
  lower_dload_insts_supply u (TAKE k ins) = (b,u2) /\
  j < k /\ k <= LENGTH ins ==>
  LENGTH a + LENGTH X <= LENGTH b
Proof
  rpt strip_tac >>
  `j < LENGTH ins` by decide_tac >>
  drule_all lower_dload_insts_supply_next >> strip_tac >>
  `SUC j <= k` by decide_tac >>
  qpat_x_assum `lower_dload_insts_supply u (TAKE j ins) = _` kall_tac >>
  qpat_x_assum `j < k` kall_tac >>
  drule_all lower_dload_insts_supply_prefix_mono >> simp[]
QED

Theorem lower_dload_insts_supply_envelope_unique:
  lower_dload_insts_supply u (TAKE j ins) = (a,u0) /\
  lower_dload_inst_supply u0 (EL j ins) = (X,u1) /\
  lower_dload_insts_supply u (TAKE k ins) = (b,v0) /\
  lower_dload_inst_supply v0 (EL k ins) = (Y,v1) /\
  j < LENGTH ins /\ k < LENGTH ins /\
  LENGTH a <= n /\ n < LENGTH a + LENGTH X /\
  LENGTH b <= n /\ n < LENGTH b + LENGTH Y ==>
  j = k
Proof
  rpt strip_tac >> Cases_on `j < k`
  >- (`k <= LENGTH ins` by decide_tac >>
      drule_all lower_dload_insts_supply_envelope_order >> decide_tac) >>
  Cases_on `k < j`
  >- (`j <= LENGTH ins` by decide_tac >>
      drule_all lower_dload_insts_supply_envelope_order >> decide_tac) >>
  decide_tac
QED

Theorem lower_dload_insts_supply_special:
  EVERY (\i. ~MEM i.inst_opcode [DLOAD; DLOADBYTES]) ins ==>
  lower_dload_insts_supply u ins = (ins,u)
Proof
  qid_spec_tac `u` >> Induct_on `ins`
  >- simp[lower_dload_insts_supply_def] >>
  rpt strip_tac >> gvs[] >>
  `lower_dload_inst_supply u h = ([h],u)` by
    (irule lower_dload_inst_supply_special >> simp[]) >>
  simp[Once lower_dload_insts_supply_def]
QED

(* A stable list interface for the two endpoints and their ASSIGN-only gap. *)
Theorem revert_forward_pair_segment:
  bb.bb_instructions = pre ++ a::mid ++ b::post /\
  EVERY (\i. i.inst_opcode = ASSIGN) mid /\
  a.inst_opcode = RETURNDATACOPY /\ a.inst_operands = [p;src;rds] /\
  b.inst_opcode = REVERT /\ b.inst_operands = [p';rds'] /\
  same_after_assigns (REVERSE pre) src (Lit 0w) /\
  same_after_assigns (REVERSE pre) p
    (resolve_block_assigns (REVERSE mid) p') /\
  same_after_assigns (REVERSE pre) rds
    (resolve_block_assigns (REVERSE mid) rds') ==>
  revert_forward_pair bb (LENGTH pre) (LENGTH pre + SUC (LENGTH mid))
Proof
  strip_tac >> simp[revert_forward_pair_def] >> conj_tac
  >- (rpt strip_tac >>
      `?n. k = LENGTH pre + SUC n /\ n < LENGTH mid` by
        (qexists_tac `k - LENGTH pre - 1` >> decide_tac) >>
      gvs[get_instruction_def, EL_APPEND, EVERY_MEM] >>
      metis_tac[MEM_EL]) >>
  qexistsl_tac [`a`,`b`,`p`,`src`,`rds`,`p'`,`rds'`] >>
  simp[get_instruction_def, EL_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  `LENGTH pre + SUC (LENGTH mid) - SUC (LENGTH pre) = LENGTH mid` by
    decide_tac >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
       DECIDE ``n - (n + SUC m) = 0``, DECIDE ``SUC n - n = 1``]
QED

Theorem revert_forward_pair_split:
  revert_forward_pair bb i j ==>
  ?pre a mid b post p src rds p' rds'.
    bb.bb_instructions = pre ++ a::mid ++ b::post /\
    i = LENGTH pre /\ j = LENGTH pre + SUC (LENGTH mid) /\
    EVERY (\x. x.inst_opcode = ASSIGN) mid /\
    a.inst_opcode = RETURNDATACOPY /\ a.inst_operands = [p;src;rds] /\
    b.inst_opcode = REVERT /\ b.inst_operands = [p';rds'] /\
    same_after_assigns (REVERSE pre) src (Lit 0w) /\
    same_after_assigns (REVERSE pre) p
      (resolve_block_assigns (REVERSE mid) p') /\
    same_after_assigns (REVERSE pre) rds
      (resolve_block_assigns (REVERSE mid) rds')
Proof
  rw[revert_forward_pair_def, get_instruction_def] >>
  qexistsl_tac [`TAKE i bb.bb_instructions`,`EL i bb.bb_instructions`,
    `TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)`,
    `EL j bb.bb_instructions`,`DROP (SUC j) bb.bb_instructions`,
    `p`,`src`,`rds`,`p'`,`rds'`] >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `j - SUC i <= LENGTH bb.bb_instructions - SUC i` by decide_tac >>
  `bb.bb_instructions = TAKE i bb.bb_instructions ++
     EL i bb.bb_instructions :: DROP (SUC i) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL, TAKE_DROP] >>
  `TAKE j bb.bb_instructions = TAKE i bb.bb_instructions ++
     EL i bb.bb_instructions ::
       TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)` by
    (qpat_assum `bb.bb_instructions = _` (fn th =>
       GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     simp[TAKE_APPEND] >>
     `j - i = SUC (j - SUC i)` by decide_tac >>
     simp[TAKE_TAKE, MIN_DEF, ADD1]) >>
  `DROP (j - SUC i) (DROP (SUC i) bb.bb_instructions) =
     EL j bb.bb_instructions :: DROP (SUC j) bb.bb_instructions` by
    (`j - SUC i + SUC i = j` by decide_tac >>
     simp[DROP_DROP, DROP_CONS_EL]) >>
  conj_tac
  >- metis_tac[TAKE_DROP, APPEND_ASSOC, CONS_APPEND] >>
  qpat_x_assum `bb.bb_instructions = _` kall_tac >>
  simp[LENGTH_TAKE, LENGTH_DROP] >>
  simp[EVERY_EL, EL_TAKE, EL_DROP] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem lower_dload_insts_supply_revert_forward:
  lower_dload_insts_supply u bb.bb_instructions = (ys,v) /\
  EVERY inst_wf bb.bb_instructions /\
  (!inst w. MEM inst bb.bb_instructions /\ MEM (Var w) inst.inst_operands ==>
     MEM w u.irs_used_vars) /\
  revert_forward_pair bb i j ==>
  ?pi ui pj uj.
    lower_dload_insts_supply u (TAKE i bb.bb_instructions) = (pi,ui) /\
    lower_dload_insts_supply u (TAKE j bb.bb_instructions) = (pj,uj) /\
    revert_forward_pair (bb with bb_instructions := ys) (LENGTH pi) (LENGTH pj)
Proof
  strip_tac >> drule revert_forward_pair_split >> strip_tac >> gvs[] >>
  `EVERY (\x. ~MEM x.inst_opcode [DLOAD;DLOADBYTES]) (a::mid ++ [b])` by
    (gvs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `lower_dload_insts_supply u pre` >>
  rename1 `lower_dload_insts_supply u pre = (xs,u0)` >>
  `lower_dload_insts_supply u0 (a::mid ++ [b]) = (a::mid ++ [b],u0)` by
    (irule lower_dload_insts_supply_special >> simp[]) >>
  `lower_dload_insts_supply u0 (a::mid ++ b::post) =
     ((a::mid ++ [b]) ++ FST (lower_dload_insts_supply u0 post),
       SND (lower_dload_insts_supply u0 post))` by
    (`a::mid ++ b::post = (a::mid ++ [b]) ++ post` by simp[] >>
     pop_assum (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
       empty_rewrites [th]) >>
     irule lower_dload_insts_supply_append_eq >>
     qexists_tac `u0` >> simp[]) >>
  `lower_dload_insts_supply u (pre ++ a::mid ++ b::post) =
    (xs ++ a::mid ++ b::FST (lower_dload_insts_supply u0 post),
     SND (lower_dload_insts_supply u0 post))` by
    (pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     irule lower_dload_insts_supply_append_eq >> qexists_tac `u0` >> simp[]) >>
  `lower_dload_insts_supply u0 (a::mid) = (a::mid,u0)` by
    (irule lower_dload_insts_supply_special >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  `lower_dload_insts_supply u (pre ++ a::mid) = (xs ++ a::mid,u0)` by
    (irule lower_dload_insts_supply_append_eq >> qexists_tac `u0` >> simp[]) >>
  gvs[] >>
  qexistsl_tac [`xs`,`u0`,`xs ++ a::mid`,`u0`] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
       DECIDE ``(n:num) - (n + SUC m) = 0``] >>
  irule revert_forward_pair_segment >>
  simp[] >> suspend "resolve"
QED

Resume lower_dload_insts_supply_revert_forward[resolve]:
  `EVERY inst_wf pre` by gvs[EVERY_APPEND] >>
  `!i w. MEM i pre /\ MEM (Var w) i.inst_operands ==>
     MEM w u.irs_used_vars` by metis_tac[MEM_APPEND] >>
  `!op w. MEM op [p;src;rds] /\ op = Var w ==> MEM w u.irs_used_vars` by
    (rpt strip_tac >> first_x_assum (qspec_then `a` mp_tac) >>
     simp[MEM_APPEND] >> gvs[] >> metis_tac[MEM]) >>
  `EVERY (\inst. !w. MEM (Var w) inst.inst_operands ==>
                     MEM w u.irs_used_vars) mid` by
    (simp[EVERY_MEM] >> metis_tac[MEM, MEM_APPEND]) >>
  `!op w. MEM op [p';rds'] /\
     resolve_block_assigns (REVERSE mid) op = Var w ==>
     MEM w u.irs_used_vars` by
    (rpt strip_tac >> irule resolve_block_assigns_used_vars >>
     qexistsl_tac [`op`,`REVERSE mid`] >> simp[EVERY_REVERSE] >>
     rpt strip_tac >> gvs[] >> metis_tac[MEM, MEM_APPEND]) >>
  `!op1 op2. MEM op1 [p;src;rds] /\ MEM op2 [p';rds'] ==>
     (same_after_assigns (REVERSE xs) op1
        (resolve_block_assigns (REVERSE mid) op2) <=>
      same_after_assigns (REVERSE pre) op1
        (resolve_block_assigns (REVERSE mid) op2))` by
    (rpt strip_tac >>
     qspecl_then [`u`,`xs`,`u0`,`[]`,`op1`,
       `resolve_block_assigns (REVERSE mid) op2`] mp_tac
       (Q.GEN `ins` lower_dload_insts_supply_same_after |> Q.SPEC `pre`) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  `same_after_assigns (REVERSE xs) src (Lit 0w) <=>
   same_after_assigns (REVERSE pre) src (Lit 0w)` by
    (qspecl_then [`u`,`xs`,`u0`,`[]`,`src`,`Lit 0w`] mp_tac
       (Q.GEN `ins` lower_dload_insts_supply_same_after |> Q.SPEC `pre`) >>
     simp[] >> disch_then irule >> metis_tac[MEM]) >>
  simp[]
QED

Finalise lower_dload_insts_supply_revert_forward

Theorem lower_dload_insts_supply_revert_at:
  lower_dload_insts_supply u bb.bb_instructions = (ys,v) /\
  EVERY inst_wf bb.bb_instructions /\
  (!inst w. MEM inst bb.bb_instructions /\ MEM (Var w) inst.inst_operands ==>
     MEM w u.irs_used_vars) /\
  lower_dload_insts_supply u (TAKE i bb.bb_instructions) = (pre,u0) /\
  revert_forward_at bb i ==>
  revert_forward_at (bb with bb_instructions := ys) (LENGTH pre)
Proof
  rw[revert_forward_at_def] >>
  drule_all lower_dload_insts_supply_revert_forward >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem lower_dload_function_supply_revert_forward:
  lower_dload_function_supply u f = (g,v) /\
  EVERY inst_wf (fn_insts f) /\ ir_supply_covers_fn u f /\
  in_revert_forward f s ==>
  ?bb u0 ys u1 pre u2.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    lower_dload_insts_supply u0 bb.bb_instructions = (ys,u1) /\
    lookup_block s.vs_current_bb g.fn_blocks =
      SOME (bb with bb_instructions := ys) /\
    lower_dload_insts_supply u0 (TAKE s.vs_inst_idx bb.bb_instructions) = (pre,u2) /\
    in_revert_forward g (s with vs_inst_idx := LENGTH pre)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs(), in_revert_forward_def] >>
  strip_tac >> gvs[] >>
  drule_all lower_dload_blocks_supply_lookup >> strip_tac >>
  `MEM bb f.fn_blocks` by
    metis_tac[lookup_block_MEM] >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_insts_def, fn_insts_blocks_def, EVERY_MEM] >>
     metis_tac[fn_insts_blocks_MEM]) >>
  `!inst w. MEM inst bb.bb_instructions /\ MEM (Var w) inst.inst_operands ==>
     MEM w u0.irs_used_vars` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
     first_x_assum irule >>
     simp[fn_ir_vars_def, block_ir_vars_def, inst_ir_vars_def,
          MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     qexistsl_tac [`bb`,`inst`] >>
     simp[inst_uses_def, MEM_operand_vars_eq_Var]) >>
  Cases_on `lower_dload_insts_supply u0 (TAKE s.vs_inst_idx bb.bb_instructions)` >>
  rename1 `lower_dload_insts_supply u0 (TAKE s.vs_inst_idx bb.bb_instructions) = (pre,u2)` >>
  drule_all lower_dload_insts_supply_revert_at >> strip_tac >>
  qexistsl_tac [`u0`,`is`,`u1`,`pre`,`u2`] >> simp[] >> metis_tac[]
QED

(* Named lookup keeps the configured observation and its actual supply. *)
Theorem lower_dload_stage_supply_lookup:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  lookup_function name C.ctx_functions = SOME f ==>
  ?g observed u out v.
    lookup_function name C'.ctx_functions = SOME g /\
    fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed u f out /\
    out.fpo_function = g /\ lower_dload_function_supply u f = (g,v) /\
    ir_supply_covers_fn u f /\ ir_supply_covers_unit u observed /\
    ir_supply_extends u out.fpo_supply /\
    observed.cu_context.ctx_entry = C.ctx_entry /\
    observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
    ctx_fn_names observed.cu_context = ctx_fn_names C /\ view C' f observed
Proof
  rw[ctx_pass_stage_def] >>
  drule list_rel_lookup_function >>
  impl_tac
  >- (rpt strip_tac >> gvs[fn_pass_step_def]) >>
  disch_then (qspec_then `name` mp_tac) >> simp[] >> strip_tac >>
  gvs[optionTheory.OPTREL_def] >>
  qexistsl_tac [`observed`,`s`,`out`] >> simp[] >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  gvs[fn_pass_step_def, AllCaseEqs()] >>
  drule venomFnScheduleRunnerPropsTheory.lookup_unique_function_member >>
  strip_tac >> metis_tac[ir_supply_covers_unit_member]
QED

(* Prefix freshness needs bounds on original ids, not arbitrary reservations. *)
Theorem lower_dload_inst_supply_prefix:
  lower_dload_inst_supply s i = (xs,t) ==>
  s.irs_next_inst <= t.irs_next_inst /\
  (?ids. t.irs_used_inst_ids = ids ++ s.irs_used_inst_ids /\
     ALL_DISTINCT ids /\
     EVERY (\k. s.irs_next_inst <= k /\ k < t.irs_next_inst) ids /\
     EVERY (\j. j.inst_id = i.inst_id \/ MEM j.inst_id ids) xs) /\
  (?vars. t.irs_used_vars = vars ++ s.irs_used_vars /\
     ALL_DISTINCT vars /\
     EVERY (\w. ~MEM w s.irs_used_vars) vars /\
     EVERY (\w. MEM w (inst_ir_vars i) \/ MEM w vars)
       (FLAT (MAP inst_ir_vars xs)))
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >>
      map_every imp_res_tac [cj 1 fresh_ir_var_contract, cj 2 fresh_ir_var_contract,
        cj 4 fresh_ir_var_contract, cj 6 fresh_ir_var_contract] >>
      gvs[EVERY_MEM] >>
      gvs[inst_ir_vars_def, inst_uses_def, operand_vars_def, operand_var_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >>
      map_every imp_res_tac [cj 1 fresh_ir_var_contract, cj 2 fresh_ir_var_contract,
        cj 4 fresh_ir_var_contract, cj 6 fresh_ir_var_contract] >>
      gvs[EVERY_MEM] >>
      gvs[inst_ir_vars_def, inst_uses_def, venomInstTheory.operand_vars_def,
        venomInstTheory.operand_var_def] >>
      Cases_on `venomInst$operand_var dst_op` >>
      Cases_on `venomInst$operand_var src_op` >>
      Cases_on `venomInst$operand_var size_op` >> gvs[] >> metis_tac[]) >>
  simp[lower_dload_inst_supply_def] >> strip_tac >> gvs[] >>
  simp[EVERY_MEM]
QED

Theorem lower_dload_inst_supply_distinct_ids:
  lower_dload_inst_supply s i = (xs,t) ==>
  ALL_DISTINCT (MAP (\j. j.inst_id) xs)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >>
      map_every imp_res_tac [cj 4 fresh_ir_var_contract] >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac (cj 4 fresh_ir_var_contract) >> gvs[]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem lower_dload_insts_supply_prefix:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) ==>
  s.irs_next_inst <= t.irs_next_inst /\
  (?ids. t.irs_used_inst_ids = ids ++ s.irs_used_inst_ids /\
     ALL_DISTINCT ids /\
     EVERY (\k. s.irs_next_inst <= k /\ k < t.irs_next_inst) ids /\
     EVERY (\j. MEM j.inst_id (MAP (\i. i.inst_id) ins) \/ MEM j.inst_id ids) xs) /\
  (?vars. t.irs_used_vars = vars ++ s.irs_used_vars /\
     ALL_DISTINCT vars /\
     EVERY (\w. ~MEM w s.irs_used_vars) vars /\
     EVERY (\w. MEM w (FLAT (MAP inst_ir_vars ins)) \/ MEM w vars)
       (FLAT (MAP inst_ir_vars xs)))
Proof
  Induct_on `ins`
  >- (simp[lower_dload_insts_supply_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  drule lower_dload_inst_supply_prefix >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (qexists_tac `ids' ++ ids` >>
      gvs[EVERY_MEM, ALL_DISTINCT_APPEND] >>
      rpt strip_tac >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS, LESS_EQ_LESS_TRANS,
        NOT_LESS]) >>
  qexists_tac `vars' ++ vars` >>
  gvs[EVERY_MEM, ALL_DISTINCT_APPEND] >> rpt strip_tac >> metis_tac[]
QED

Theorem lower_dload_insts_supply_distinct_ids:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) ins) /\
    EVERY (\i. i.inst_id < s.irs_next_inst) ins ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) xs)
Proof
  Induct_on `ins`
  >- (simp[lower_dload_insts_supply_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> strip_tac >>
  drule lower_dload_inst_supply_prefix >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) out)` by
    metis_tac[lower_dload_inst_supply_distinct_ids] >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) ins` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     metis_tac[LESS_LESS_EQ_TRANS]) >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule lower_dload_insts_supply_prefix >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >>
  metis_tac[LESS_LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, NOT_LESS]
QED

(* Flattening commutes with the threaded block traversal. *)
Theorem lower_dload_blocks_supply_flat:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) ==>
  lower_dload_insts_supply s (FLAT (MAP (\b. b.bb_instructions) bbs)) =
    (FLAT (MAP (\b. b.bb_instructions) bs),t)
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def, lower_dload_insts_supply_def] >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
    AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule lower_dload_insts_supply_append_eq >> metis_tac[]
QED

Theorem lower_dload_function_supply_prefix:
  lower_dload_function_supply s f = (g,t) ==>
  s.irs_next_inst <= t.irs_next_inst /\
  (?ids. t.irs_used_inst_ids = ids ++ s.irs_used_inst_ids /\
     ALL_DISTINCT ids /\
     EVERY (\k. s.irs_next_inst <= k /\ k < t.irs_next_inst) ids /\
     EVERY (\k. MEM k (fn_ir_inst_ids f) \/ MEM k ids) (fn_ir_inst_ids g)) /\
  (?vars. t.irs_used_vars = vars ++ s.irs_used_vars /\
     ALL_DISTINCT vars /\
     EVERY (\w. ~MEM w s.irs_used_vars) vars /\
     EVERY (\w. MEM w (fn_ir_vars f) \/ MEM w vars) (fn_ir_vars g))
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule lower_dload_blocks_supply_flat >> strip_tac >>
  drule lower_dload_insts_supply_prefix >>
  simp[fn_ir_inst_ids_def, block_ir_inst_ids_def, fn_ir_vars_def,
    block_ir_vars_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem lower_dload_function_supply_distinct_ids:
  lower_dload_function_supply s f = (g,t) /\
  ALL_DISTINCT (fn_ir_inst_ids f) /\
  EVERY (\k. k < s.irs_next_inst) (fn_ir_inst_ids f) ==>
  ALL_DISTINCT (fn_ir_inst_ids g)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule lower_dload_blocks_supply_flat >> strip_tac >>
  drule lower_dload_insts_supply_distinct_ids >>
  simp[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF,
    fn_ir_inst_ids_def, block_ir_inst_ids_def, EVERY_MEM, MEM_FLAT, MEM_MAP,
    PULL_EXISTS] >>
  gvs[fn_ir_inst_ids_def, lambdify block_ir_inst_ids_def, EVERY_MEM,
    MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem lower_dload_function_supply_fresh:
  ir_supply_covers_fn s f /\ ALL_DISTINCT (fn_ir_inst_ids f) /\
  lower_dload_function_supply s f = (g,t) ==>
  ALL_DISTINCT (fn_ir_inst_ids g) /\
  EVERY (\k. MEM k (fn_ir_inst_ids f) \/
    (s.irs_next_inst <= k /\ k < t.irs_next_inst)) (fn_ir_inst_ids g) /\
  ?vars. t.irs_used_vars = vars ++ s.irs_used_vars /\
    ALL_DISTINCT vars /\ EVERY (\w. ~MEM w s.irs_used_vars) vars /\
    EVERY (\w. MEM w (fn_ir_vars f) \/ MEM w vars) (fn_ir_vars g)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_ir_inst_ids g)` by
    (irule lower_dload_function_supply_distinct_ids >>
     gvs[ir_supply_covers_fn_def] >> metis_tac[]) >>
  drule lower_dload_function_supply_prefix >> strip_tac >>
  simp[] >> gvs[EVERY_MEM] >> metis_tac[]
QED

(* Choose covered supplies by source name, retaining the stage's actual
   transformation rather than choosing an unrelated fresh supply. *)
Theorem lower_dload_stage_covered_supplies:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  ALL_DISTINCT (MAP (\fn. fn.fn_name) C.ctx_functions) ==>
  ?Sigma.
    !fn. MEM fn C.ctx_functions ==>
      ir_supply_covers_fn (Sigma fn.fn_name) fn /\
      lookup_function fn.fn_name C'.ctx_functions =
        SOME (FST (lower_dload_function_supply (Sigma fn.fn_name) fn))
Proof
  strip_tac >>
  `!nm. ?u. !fn. lookup_function nm C.ctx_functions = SOME fn ==>
    ir_supply_covers_fn u fn /\
    lookup_function nm C'.ctx_functions =
      SOME (FST (lower_dload_function_supply u fn))` by
    (gen_tac >> Cases_on `lookup_function nm C.ctx_functions`
     >- simp[] >>
     drule_all lower_dload_stage_supply_lookup >> strip_tac >>
     qexists_tac `u` >> simp[]) >>
  fs[SKOLEM_THM] >> qexists_tac `f` >> rpt strip_tac >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (simp[lookup_function_member_iff]) >>
  metis_tac[]
QED

Theorem o1_ctx_shape_distinct_names:
  o1_ctx_shape C ==>
  ALL_DISTINCT (MAP (\fn. fn.fn_name) C.ctx_functions)
Proof
  simp[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def,
       ctx_fn_names_def]
QED

val _ = if null (hyp lower_dload_stage_covered_supplies) andalso
           null (hyp o1_ctx_shape_distinct_names)
        then () else raise Fail "covered supply boundary has hypotheses";
