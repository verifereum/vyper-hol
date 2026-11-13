(* TOP-LEVEL: fresh allocation outputs belong to the containing emitted
   function. Initial instructions are distinguished explicitly from newly
   generated code, including code moved into completed blocks.
   Helpers expose compiler-state instruction membership and monadic provenance. *)
Theory compileAllocaProvenance
Ancestors
  compileAllocaFlow compileVarFlow compileEnv fragExec exprLoweringProps
  allocaRemapSSA venomExecProps venomInst list rich_list pair arithmetic

Definition compiler_instruction_member_def:
  compiler_instruction_member cs inst <=>
    MEM inst cs.cs_current_insts \/
    ?bb. MEM bb cs.cs_blocks /\ MEM inst bb.bb_instructions
End

Definition compiler_alloca_ids_def:
  compiler_alloca_ids before after =
    MAP (\inst. inst.inst_id)
      (FILTER (\inst. inst.inst_opcode = ALLOCA /\ ~compiler_instruction_member before inst)
        (after.cs_current_insts ++ fn_insts_blocks after.cs_blocks))
End

Theorem compiler_blocks_instruction_member:
  !blocks inst. MEM inst (fn_insts_blocks blocks) <=>
    ?bb. MEM bb blocks /\ MEM inst bb.bb_instructions
Proof
  Induct_on `blocks` >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem compiler_alloca_ids_member:
  !before after id. MEM id (compiler_alloca_ids before after) <=>
    ?inst. compiler_instruction_member after inst /\ ~compiler_instruction_member before inst /\
      inst.inst_opcode = ALLOCA /\ inst.inst_id = id
Proof
  simp[compiler_alloca_ids_def, MEM_MAP, MEM_FILTER, MEM_APPEND,
    compiler_blocks_instruction_member, compiler_instruction_member_def] >> metis_tac[]
QED

Theorem compiler_alloca_code_member:
  !P cs inst.
    compiler_alloca_code P cs /\ compiler_instruction_member cs inst /\ inst.inst_opcode = ALLOCA ==> P inst
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_alloca_code_def, compiler_instruction_member_def] >> strip_tac >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem compiler_alloca_code_initial:
  !cs Q. compiler_alloca_code (\inst. compiler_instruction_member cs inst \/ Q inst) cs
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_alloca_code_def, EVERY_MEM] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[compiler_instruction_member_def]) >>
  qx_gen_tac `bb` >> DISCH_TAC >> qx_gen_tac `inst` >> rpt strip_tac >>
  simp_tac bool_ss [compiler_instruction_member_def] >>
  disj1_tac >> disj2_tac >> qexists_tac `bb` >> simp[]
QED

Theorem compiler_alloca_fresh_output:
  !m cs ret cs' inst.
    (!P. compiler_alloca_pred P m) /\ m cs = (ret,cs') /\
    compiler_instruction_member cs' inst /\ ~compiler_instruction_member cs inst /\ inst.inst_opcode = ALLOCA ==>
    ?n. cs.cs_next_var <= n /\ inst.inst_outputs = ["%" ++ toString n]
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P = \i. compiler_instruction_member cs i \/
    ?n. cs.cs_next_var <= n /\ i.inst_outputs = ["%" ++ toString n]` >>
  `compiler_alloca_code P cs` by simp[Abbr`P`, compiler_alloca_code_initial] >>
  `!id ops n. cs.cs_next_var <= n ==> P (mk_inst id ALLOCA ops ["%" ++ toString n])` by
    (rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [Abbr`P`] >> disj2_tac >>
     qexists_tac `n` >> simp[mk_inst_def]) >>
  `compiler_alloca_code P cs'` by
    (qpat_x_assum `!P. compiler_alloca_pred P m` (qspec_then `P` mp_tac) >>
     simp_tac bool_ss [compiler_alloca_pred_def] >> strip_tac >>
     qpat_x_assum `!cs. _` (qspec_then `cs` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`P`, `cs'`, `inst`] compiler_alloca_code_member) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[Abbr`P`]
QED

Theorem fn_has_code_current_member:
  !cs cs' func inst.
    fn_has_code cs cs' func /\ MEM inst cs'.cs_current_insts ==> MEM inst (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  rename1 `lookup_block cs'.cs_current_bb func.fn_blocks = SOME bb` >>
  `MEM bb func.fn_blocks` by (drule lookup_block_MEM >> simp[]) >>
  `MEM inst bb.bb_instructions` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >> simp[IS_PREFIX_APPEND] >> strip_tac >> simp[MEM_APPEND]) >>
  drule_all mem_fn_insts_intro >> simp[]
QED

Theorem fn_has_code_block_member:
  !cs cs' func bb inst.
    fn_has_code cs cs' func /\ MEM bb (emitted_blocks cs cs') /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  `lookup_block bb.bb_label func.fn_blocks = SOME bb` by
    (qpat_x_assum `!bb. _` (qspec_then `bb` mp_tac) >> simp[]) >>
  `MEM bb func.fn_blocks` by (drule lookup_block_MEM >> simp[]) >>
  drule_all mem_fn_insts_intro >> simp[]
QED

Theorem compiler_new_instruction_member:
  !cs cs' func inst.
    cs_extends cs cs' /\ fn_has_code cs cs' func /\
    compiler_instruction_member cs' inst /\ ~compiler_instruction_member cs inst ==>
    MEM inst (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `MEM inst cs'.cs_current_insts`
  >- (drule_all fn_has_code_current_member >> simp[]) >>
  qpat_x_assum `compiler_instruction_member cs' inst`
    (mp_tac o REWRITE_RULE [compiler_instruction_member_def]) >> asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qpat_x_assum `cs_extends _ _` (mp_tac o REWRITE_RULE [cs_extends_def]) >>
  disch_then (qx_choose_then `added` strip_assume_tac) >>
  `~MEM bb cs.cs_blocks` by
    (DISCH_TAC >> qpat_x_assum `~compiler_instruction_member cs inst` mp_tac >>
     simp_tac bool_ss [compiler_instruction_member_def] >> disj2_tac >> qexists_tac `bb` >> simp[]) >>
  `MEM bb added` by fs[MEM_APPEND] >>
  `emitted_blocks cs cs' = added` by simp[emitted_blocks_def, TAKE_LENGTH_APPEND] >>
  mp_tac (Q.SPECL [`cs`, `cs'`, `func`, `bb`, `inst`] fn_has_code_block_member) >>
  impl_tac >- simp[] >> simp[]
QED
