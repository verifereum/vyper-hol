Theory o1LabelFlowLowerDload
Ancestors
  codegenSymRel lowerDloadPtrReachableStatic lowerDloadPtrStatic
  lowerDloadConfiguredOrigins lowerDloadDefs irSupply list o1ContractLowerDload
  venomFnScheduleRunner o1PassContract venomInst

Theorem lower_dload_inst_code_end_seed:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  ~MEM (Label "code_end") i.inst_operands /\
  j.inst_opcode = ADD /\ j.inst_operands = [op; Label "code_end"] /\
  MEM x j.inst_outputs ==>
  j.inst_outputs = [x] /\ ~MEM x s.irs_used_vars
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac fresh_ir_var_contract >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac fresh_ir_var_contract >> gvs[]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def]
QED

Theorem lower_dload_inst_fresh_read:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  (!v. MEM (Var v) i.inst_operands ==> MEM v s.irs_used_vars) /\
  MEM (Var x) j.inst_operands /\ ~MEM x s.irs_used_vars ==>
  ?d. MEM d xs /\ MEM x d.inst_outputs /\
    (d.inst_opcode = ADD ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                dst <> Var x /\ sz <> Var x) /\
      ?pre post. xs = pre ++ d::j::post)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac fresh_ir_var_contract >> gvs[] >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> metis_tac[APPEND]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac fresh_ir_var_contract >> gvs[] >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> metis_tac[APPEND]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def] >> metis_tac[]
QED

Theorem lower_dload_function_code_end_seed:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
  MEM j (fn_insts g) /\ j.inst_opcode = ADD /\
  j.inst_operands = [op; Label "code_end"] /\ MEM x j.inst_outputs ==>
  j.inst_outputs = [x] /\ ~MEM x (fn_ir_vars f)
Proof
  rpt strip_tac >>
  drule_all lower_dload_function_supply_member_covered >> strip_tac >>
  `j.inst_outputs = [x] /\ ~MEM x u.irs_used_vars` by
    (irule lower_dload_inst_code_end_seed >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem lower_dload_function_seed_read:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
  MEM d (fn_insts g) /\ d.inst_opcode = ADD /\
  d.inst_operands = [op; Label "code_end"] /\ MEM x d.inst_outputs /\
  MEM j (fn_insts g) /\ MEM (Var x) j.inst_operands ==>
  j.inst_opcode = CODECOPY /\
  ?dst sz. j.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x
Proof
  rpt strip_tac >>
  `~MEM x (fn_ir_vars f)` by
    metis_tac[lower_dload_function_code_end_seed] >>
  drule_all lower_dload_function_supply_member_covered >> strip_tac >>
  `!v. MEM (Var v) i.inst_operands ==> MEM v u.irs_used_vars` by
    (gvs[EVERY_MEM] >> metis_tac[fn_ir_vars_operand]) >>
  `~MEM x u.irs_used_vars` by
    (strip_tac >> drule_all lower_dload_inst_supply_reserved_operand >>
     metis_tac[fn_ir_vars_operand]) >>
  drule_all lower_dload_inst_fresh_read >> strip_tac >>
  `d' = d` by
    (irule lower_dload_function_supply_fresh_output_unique >>
     qexistsl [`f`,`g`,`s`,`t`,`x`] >> gvs[EVERY_MEM]) >>
  gvs[]
QED

Theorem lower_dload_function_code_end_origin:
  !g x. code_end_var g x ==>
  !s f t. lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) ==>
  ?d op. MEM d (fn_insts g) /\ d.inst_opcode = ADD /\
         d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x]
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- (drule_all lower_dload_function_code_end_seed >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  `MEM x' d.inst_outputs /\ MEM (Var x') inst.inst_operands` by simp[] >>
  drule_all lower_dload_function_seed_read >> simp[]
QED

Theorem lower_dload_code_end_var_retained:
  !f x. code_end_var f x ==>
  !s g t. lower_dload_function_supply s f = (g,t) ==> code_end_var g x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `MEM inst (fn_insts g)` by
    (irule lower_dload_function_supply_retained >> simp[] >> metis_tac[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem lower_dload_inst_codecopy_origin:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  j.inst_opcode = CODECOPY ==>
  j = i \/
  ?d op x dst sz. MEM d xs /\ d.inst_opcode = ADD /\
    d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
    j.inst_operands = [dst; Var x; sz]
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def]
QED

Theorem lower_dload_inst_no_codesize:
  lower_dload_inst_supply s i = (xs,t) /\ MEM j xs /\
  i.inst_opcode <> CODESIZE ==> j.inst_opcode <> CODESIZE
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def]
QED

Theorem lower_dload_function_codecopy_source:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  label_flow_ok (ctx with ctx_functions := [f]) /\
  MEM j (fn_insts g) /\ j.inst_opcode = CODECOPY ==>
  ?dst src sz. j.inst_operands = [dst; src; sz] /\
    (src = Label "runtime_begin" \/ ?x. src = Var x /\ code_end_var g x)
Proof
  rpt strip_tac >>
  drule_all lower_dload_function_supply_member_covered >> strip_tac >>
  drule_all lower_dload_inst_codecopy_origin >> strip_tac
  >- (gvs[label_flow_ok_def] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      metis_tac[lower_dload_code_end_var_retained]) >>
  `MEM d (fn_insts g)` by gvs[EVERY_MEM] >>
  `code_end_var g x` by (irule code_end_var_seed >> metis_tac[MEM]) >>
  metis_tac[]
QED

Theorem lower_dload_function_label_flow_ok:
  ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
  label_flow_ok (ctx with ctx_functions := [f]) /\
  lower_dload_function_supply s f = (g,t) ==>
  label_flow_ok (ctx with ctx_functions := [g])
Proof
  rpt strip_tac >> simp[label_flow_ok_def] >> rpt strip_tac
  >- (drule_all lower_dload_function_supply_member_covered >> strip_tac >>
      `i.inst_opcode <> CODESIZE` by
        (gvs[label_flow_ok_def] >> metis_tac[]) >>
      drule_all lower_dload_inst_no_codesize >> simp[])
  >- (drule_all lower_dload_function_code_end_origin >> strip_tac >>
      `MEM x d.inst_outputs` by simp[] >>
      drule_all lower_dload_function_seed_read >> simp[]) >>
  drule_all lower_dload_function_codecopy_source >> simp[]
QED

Theorem lower_dload_insts_supply_segment_covered:
  !s xs t. lower_dload_insts_supply s ins = (xs,t) /\ MEM j xs /\
    EVERY (\v. MEM v s.irs_used_vars) reserved ==>
  ?i u ys w pre post. MEM i ins /\ lower_dload_inst_supply u i = (ys,w) /\
    MEM j ys /\ EVERY (\v. MEM v u.irs_used_vars) reserved /\
    xs = pre ++ ys ++ post
Proof
  Induct_on `ins` >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (qexistsl [`h`,`s`,`out`,`s1`,`[]`,`outs`] >> simp[]) >>
  drule lower_dload_inst_supply_preserves_vars >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars) reserved` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`i`,`u`,`ys`,`w`,`out ++ pre`,`post`] >> simp[]
QED

Theorem lower_dload_blocks_supply_segment_covered:
  !s bs t. lower_dload_blocks_supply s bbs = (bs,t) /\
    MEM bg bs /\ MEM j bg.bb_instructions /\
    EVERY (\v. MEM v s.irs_used_vars) reserved ==>
  ?bf i u ys w pre post. MEM bf bbs /\ bf.bb_label = bg.bb_label /\
    MEM i bf.bb_instructions /\ lower_dload_inst_supply u i = (ys,w) /\
    MEM j ys /\ EVERY (\v. MEM v u.irs_used_vars) reserved /\
    bg.bb_instructions = pre ++ ys ++ post
Proof
  Induct_on `bbs` >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, lower_dload_block_supply_def,
       AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (drule_all lower_dload_insts_supply_segment_covered >> strip_tac >>
      qexistsl [`h`,`i`,`u`,`ys`,`w`,`pre`,`post`] >> simp[]) >>
  drule (cj 1 lower_dload_insts_supply_reserved_operand) >> strip_tac >>
  `EVERY (\v. MEM v s1.irs_used_vars) reserved` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`bf`,`i`,`u`,`ys`,`w`,`pre`,`post`] >> simp[]
QED

Theorem lower_dload_function_supply_segment_covered:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  MEM bg g.fn_blocks /\ MEM j bg.bb_instructions ==>
  ?bf i u ys w pre post. MEM bf f.fn_blocks /\ bf.bb_label = bg.bb_label /\
    MEM i bf.bb_instructions /\ lower_dload_inst_supply u i = (ys,w) /\
    MEM j ys /\ EVERY (\v. MEM v u.irs_used_vars) (fn_ir_vars f) /\
    bg.bb_instructions = pre ++ ys ++ post
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `EVERY (\v. MEM v s.irs_used_vars) (fn_ir_vars f)` by
    gvs[ir_supply_covers_fn_def, list_subset_def] >>
  drule_all lower_dload_blocks_supply_segment_covered >> simp[]
QED

Theorem lower_dload_function_seed_read_adjacent:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
  MEM d (fn_insts g) /\ d.inst_opcode = ADD /\
  d.inst_operands = [op; Label "code_end"] /\ MEM x d.inst_outputs /\
  MEM bg g.fn_blocks /\ MEM j bg.bb_instructions /\
  MEM (Var x) j.inst_operands ==>
  ?pre post. bg.bb_instructions = pre ++ d::j::post
Proof
  rpt strip_tac >>
  `~MEM x (fn_ir_vars f)` by
    metis_tac[lower_dload_function_code_end_seed] >>
  drule_all lower_dload_function_supply_segment_covered >> strip_tac >>
  `MEM i (fn_insts f)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `!v. MEM (Var v) i.inst_operands ==> MEM v u.irs_used_vars` by
    (gvs[EVERY_MEM] >> metis_tac[fn_ir_vars_operand]) >>
  `~MEM x u.irs_used_vars` by
    (strip_tac >> drule_all lower_dload_inst_supply_reserved_operand >>
     metis_tac[fn_ir_vars_operand]) >>
  drule_all lower_dload_inst_fresh_read >> strip_tac >>
  `MEM d' (fn_insts g)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >>
     qexists_tac `bg` >> simp[] >> metis_tac[MEM_APPEND]) >>
  `d' = d` by
    (irule lower_dload_function_supply_fresh_output_unique >>
     qexistsl [`f`,`g`,`s`,`t`,`x`] >> simp[]) >>
  gvs[] >> qexistsl [`pre ++ pre'`,`post' ++ post`] >> simp[]
QED

(* This is the consumer-facing lifetime boundary: every code-end variable
   has one defining ADD, and every read has that ADD immediately before it
   in the same block.  In particular no PHI or ASSIGN reads these variables. *)
Theorem lower_dload_function_code_end_lifetime:
  lower_dload_function_supply s f = (g,t) /\ ir_supply_covers_fn s f /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
  code_end_var g x ==>
  ?d op. MEM d (fn_insts g) /\ d.inst_opcode = ADD /\
    d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts g) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb g.fn_blocks /\ MEM j bb.bb_instructions /\
       MEM (Var x) j.inst_operands ==>
       j.inst_opcode = CODECOPY /\
       (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                 dst <> Var x /\ sz <> Var x) /\
       ?pre post. bb.bb_instructions = pre ++ d::j::post)
Proof
  rpt strip_tac >>
  drule_all lower_dload_function_code_end_origin >> strip_tac >>
  qexistsl [`d`,`op`] >> simp[] >>
  `MEM x d.inst_outputs` by simp[] >>
  `~MEM x (fn_ir_vars f)` by
    metis_tac[lower_dload_function_code_end_seed] >>
  conj_tac
  >- (rpt strip_tac >> irule lower_dload_function_supply_fresh_output_unique >>
      qexistsl [`f`,`g`,`s`,`t`,`x`] >> simp[]) >>
  rpt strip_tac >>
  `MEM j (fn_insts g)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all lower_dload_function_seed_read >> strip_tac >> simp[] >>
  drule_all lower_dload_function_seed_read_adjacent >> simp[]
QED
