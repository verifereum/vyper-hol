(* Forwarding assembly, conditional only on source-operand prefix transport. *)
Theory fmpStageCoverForwardAssemble
Ancestors
  fmpStageCoverForwardInterval fmpStageRel contextCodegenRel
  contextCodegenRelProps lowerDloadPtrForward fmpStepSupply
  livenessTransferProofs o1PassContract venomExecSemantics venomExecProofs
  venomInst irSupply rich_list list

Theorem fmp_cover_interval_slice[local]:
  p < j /\
  (!h. h <= j-p ==> get_instruction tb (tp+h) = get_instruction bb (p+h)) /\
  get_instruction bb j = SOME last ==>
  TAKE (tp+(j-p)-SUC tp) (DROP (SUC tp) tb.bb_instructions) =
  TAKE (j-SUC p) (DROP (SUC p) bb.bb_instructions)
Proof
  strip_tac >>
  `j < LENGTH bb.bb_instructions` by gvs[get_instruction_def, AllCaseEqs()] >>
  `get_instruction tb (tp+(j-p)) = SOME last` by
    (first_x_assum (qspec_then `j-p` mp_tac) >> simp[]) >>
  `tp+(j-p) < LENGTH tb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  irule LIST_EQ >> simp[LENGTH_TAKE, LENGTH_DROP] >>
  rpt strip_tac >>
  `x < j-SUC p /\ SUC x <= j-p /\
   x + SUC p < LENGTH bb.bb_instructions /\
   x + SUC tp < LENGTH tb.bb_instructions` by decide_tac >>
  simp[EL_TAKE, EL_DROP] >>
  first_x_assum (qspec_then `SUC x` mp_tac) >>
  simp[get_instruction_def, arithmeticTheory.ADD_CLAUSES,
       arithmeticTheory.ADD_COMM]
QED

Theorem fmp_cover_block_operand[local]:
  lookup_block lbl fn.fn_blocks = SOME bb /\ MEM q bb.bb_instructions /\
  MEM (Var v) q.inst_operands ==> MEM v (fn_ir_vars fn)
Proof
  strip_tac >> simp[fn_ir_vars_member] >>
  qexistsl_tac [`bb`,`q`] >> simp[] >>
  drule lookup_block_mem >> strip_tac >> simp[] >>
  simp[inst_uses_def, MEM_operand_vars_eq_Var]
QED

Theorem fmp_cover_forward_from_prefix:
  (!rpolicy D C C' vs vs' fmp eom fn fn' lbl bb bb' p tp inst a b.
    fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
    MEM fn C.ctx_functions /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block lbl fn'.fn_blocks = SOME bb' /\
    get_instruction bb p = SOME inst /\ inst.inst_opcode = RETURNDATACOPY /\
    get_instruction bb' tp = SOME inst /\
    (!v. a = Var v ==> MEM v (fn_ir_vars fn)) /\
    (!v. b = Var v ==> MEM v (fn_ir_vars fn)) /\
    same_after_assigns (REVERSE (TAKE p bb.bb_instructions)) a b ==>
    same_after_assigns (REVERSE (TAKE tp bb'.bb_instructions)) a b) ==>
  !rpolicy D C C' vs vs' fmp eom fn fn' infos ctx runner lbl bb p j.
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ revert_forward_pair bb p j ==>
  ?bb'. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    revert_forward_pair bb'
      (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
         (fmp_stage_root infos ctx fn) lbl bb.bb_instructions p)
      (fmp_stage_tidx (fmp_stage_plan infos ctx fn)
         (fmp_stage_root infos ctx fn) lbl bb.bb_instructions j)
Proof
  strip_tac >> pop_assum (mk_asm "prefix") >> rpt gen_tac >> strip_tac >>
  drule_all fmp_stage_forward_interval >> strip_tac >>
  qmatch_goalsub_abbrev_tac `revert_forward_pair bb' tp tj` >>
  `tp < tp+(j-p)` by gvs[revert_forward_pair_def] >>
  qpat_x_assum `revert_forward_pair bb p j` mp_tac >>
  rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  `get_instruction bb' tp = SOME inst1 /\
   get_instruction bb' (tp+(j-p)) = SOME inst2` by
    (conj_tac >- (qpat_x_assum `!h. h <= j-p ==> _`
       (qspec_then `0` mp_tac) >> simp[]) >>
     qpat_x_assum `!h. h <= j-p ==> _` (qspec_then `j-p` mp_tac) >> simp[]) >>
  `TAKE (tp+(j-p)-SUC tp) (DROP (SUC tp) bb'.bb_instructions) =
   TAKE (j-SUC p) (DROP (SUC p) bb.bb_instructions)` by
    (irule fmp_cover_interval_slice >> metis_tac[]) >>
  qexists_tac `bb'` >> simp[revert_forward_pair_def] >>
  conj_tac >- suspend "middle" >>
  suspend "operands"
QED

Resume fmp_cover_forward_from_prefix[middle]:
  rpt strip_tac >>
  `p < p+(k-tp) /\ p+(k-tp) < j /\ k-tp <= j-p /\
   tp+(k-tp) = k` by decide_tac >>
  `get_instruction bb (p+(k-tp)) = SOME inst` by metis_tac[] >>
  metis_tac[]
QED

Resume fmp_cover_forward_from_prefix[operands]:
  `MEM inst1 bb.bb_instructions /\ MEM inst2 bb.bb_instructions` by
    (qpat_assum `get_instruction bb p = SOME inst1` mp_tac >>
     qpat_assum `get_instruction bb j = SOME inst2` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[get_instruction_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[] >> simp[MEM_EL] >> metis_tac[]) >>
  `!op v. MEM op [p'; src; rds; p''; rds'] /\ op = Var v ==>
      MEM v (fn_ir_vars fn)` by
    (qpat_assum `lookup_block lbl fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `MEM inst1 bb.bb_instructions` mp_tac >>
     qpat_assum `MEM inst2 bb.bb_instructions` mp_tac >>
     qpat_assum `inst1.inst_operands = _` mp_tac >>
     qpat_assum `inst2.inst_operands = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[] >> metis_tac[fmp_cover_block_operand, MEM]) >>
  qmatch_asmsub_abbrev_tac `same_after_assigns _ p' (resolve_block_assigns mid p'')` >>
  `!q v. MEM q mid /\ MEM (Var v) q.inst_operands ==> MEM v (fn_ir_vars fn)` by
    (rpt strip_tac >> irule fmp_cover_block_operand >>
     qexistsl_tac [`bb`,`lbl`,`q`] >> simp[] >>
     qpat_x_assum `MEM q mid` mp_tac >> simp[Abbr `mid`] >>
     strip_tac >> drule MEM_TAKE >> strip_tac >>
     drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  `!op v. (!v. op = Var v ==> MEM v (fn_ir_vars fn)) /\
     resolve_block_assigns mid op = Var v ==> MEM v (fn_ir_vars fn)` by
    (rpt strip_tac >> irule resolve_block_assigns_tracked >>
     qexistsl_tac [`op`,`mid`] >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`inst2`,`p''`,`rds'`] >>
  `j+tp-p = tp+(j-p) /\ j+tp-(p+SUC tp) = tp+(j-p)-SUC tp` by decide_tac >>
  qpat_x_assum `j+tp-p = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `j+tp-(p+SUC tp) = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `TAKE _ (DROP _ bb'.bb_instructions) = _`
    (fn th => rewrite_tac[th]) >>
  qpat_x_assum `Abbrev (mid = _)` (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  pure_asm_rewrite_tac[] >> simp[NoAsms] >>
  rpt conj_tac >> asm "prefix" irule >>
  qpat_assum `fmp_stage_ctx rpolicy D C C' vs vs' fmp eom` (irule_at Any) >>
  qpat_assum `lookup_block lbl fn.fn_blocks = SOME bb` (irule_at Any) >>
  qpat_assum `get_instruction bb p = SOME inst1` (irule_at Any) >>
  qpat_assum `lookup_function fn.fn_name C'.ctx_functions = SOME fn'` (irule_at Any) >>
  simp[] >> metis_tac[MEM]
QED

Finalise fmp_cover_forward_from_prefix
