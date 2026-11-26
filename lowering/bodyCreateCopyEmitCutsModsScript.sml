Theory bodyCreateCopyEmitCutsMods
Ancestors
  dallocaCreateGeometry externalEntryShape
  emitHelperProps loweringShapeRules loweringShapeDefs stmtReasonLitFragMemory
  ptrDiscipline fragExec compileEnv exprLoweringProps rich_list list venomInst
  context builtinCreate

(* For a straight-line cut, the old completed blocks are unchanged.
   Normalize the instruction appends before applying the prefix simp rules. *)
val copy_cut_growth_tac =
  rewrite_tac[cs_extends_def] >> qexists `[]` >>
  asm_rewrite_tac[APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[NoAsms]

Theorem copy_dalloca_in_context[local]:
  emit_op DALLOCA [req] a = (v,b) /\ fn_has_code a b func /\
  MEM func ctx.ctx_functions ==> ctx_has_dalloca ctx
Proof
  strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE[same_blocks_def]) emit_op_same_blocks >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  drule fn_has_code_code >> disch_then (qspec_then `emitted_insts a b` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  simp[ctx_has_dalloca_def,EXISTS_MEM] >> qexists `func` >> simp[] >>
  qexists `mk_inst a.cs_next_id DALLOCA [req] [STRING #"%" (toString a.cs_next_var)]` >>
  simp[mk_inst_def]
QED

Theorem create_copy_emit_cuts_mods:
  compile_create_copy target amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ MEM func ctx.ctx_functions /\
  (!x. target = Var x \/ amount = Var x \/ sop = SOME (Var x) ==>
       not_fresh_at sm x) ==>
  ?code' a1 a2 shifted a3 preamble a4 size' a5 p a6 a7 code_dst a8 a9 buf a10 len sc.
    emit_op EXTCODESIZE [target] sm = (code',a1) /\
    emit_void ASSERT [code'] a1 = ((),a2) /\
    emit_op SHL [Lit 56w;code'] a2 = (shifted,a3) /\
    emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
    emit_op ADD [code';Lit 32w] a4 = (size',a5) /\
    emit_op DALLOCA [size'] a5 = (Var p,a6) /\
    emit_void MSTORE [Var p;preamble] a6 = ((),a7) /\
    emit_op ADD [Var p;Lit 32w] a7 = (code_dst,a8) /\
    emit_void EXTCODECOPY [target;code_dst;Lit 0w;code'] a8 = ((),a9) /\
    emit_op ADD [Var p;Lit 21w] a9 = (buf,a10) /\
    emit_op ADD [code';Lit 11w] a10 = (len,sc) /\
    compile_create_dispatch buf len amount sop rof sc = (result,sb) /\
    fn_has_code sm a2 func /\ fn_has_code a2 a5 func /\ fn_has_code a5 a6 func /\
    fn_has_code a6 a7 func /\ fn_has_code a7 a8 func /\ fn_has_code a8 a9 func /\
    fn_has_code a9 a10 func /\ fn_has_code a10 sc func /\
    fn_has_code sm sc func /\ fn_has_code sc sb func /\
    cs_extends sm sc /\ ctx_has_dalloca ctx /\
    sm.cs_next_var <= a2.cs_next_var /\ a2.cs_next_var <= a5.cs_next_var /\
    a5.cs_next_var <= a6.cs_next_var /\ a6.cs_next_var <= sc.cs_next_var /\
    sm.cs_next_var <= sc.cs_next_var /\
    same_blocks sm a2 /\ same_blocks sm a5 /\ same_blocks sm a6 /\ same_blocks sm sc /\
    (!x. code' = Var x \/ preamble = Var x ==> not_fresh_at a5 x) /\
    (!x. MEM (Var x) [Var p;target;code'] ==> not_fresh_at a6 x) /\
    ~not_fresh_at a5 p /\
    (?is. sc.cs_current_insts = sm.cs_current_insts ++ is /\
          EVERY (\i. i.inst_opcode <> ALLOCA) is)
Proof
  strip_tac >>
  drule_then strip_assume_tac create_copy_create_prefix >>
  qpat_x_assum `compile_alloc_dynamic _ _ = _`
    (assume_tac o REWRITE_RULE[compile_alloc_dynamic_def]) >>
  `compile_create_dispatch buf len amount sop rof sc = (result,sb)` by
    (Cases_on `sop` >> fs[compile_create_dispatch_def,comp_bind_def]) >>
  `cs_extends sc sb` by
    (qspecl_then [`buf`,`len`,`amount`,`sop`,`rof`,`sc`] mp_tac
       compile_create_dispatch_labels >> simp[]) >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >>
  imp_res_tac emit_op_same_blocks >>
  imp_res_tac emit_void_same_blocks >>
  rpt (qpat_x_assum `same_blocks _ _`
    (strip_assume_tac o REWRITE_RULE[same_blocks_def])) >>
  suspend "geometry"
QED

Resume create_copy_emit_cuts_mods[geometry]:
  `cs_extends sm a2 /\ cs_extends a2 a5 /\ cs_extends a5 a6 /\
   cs_extends a6 a7 /\ cs_extends a7 a8 /\ cs_extends a8 a9 /\
   cs_extends a9 a10 /\ cs_extends a10 sc` by
    (rpt conj_tac >> copy_cut_growth_tac) >>
  `cs_extends sm sc` by copy_cut_growth_tac >>
  qspecl_then [`sm`,`sc`,`sb`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  suspend "intervals"
QED

Resume create_copy_emit_cuts_mods[intervals]:
  (* Split backwards from the real dispatch boundary. *)
  map_every (fn (b,c) =>
    qspecl_then [`sm`,b,c,`func`] mp_tac fn_has_code_split >>
    (impl_tac >- (conj_tac >- copy_cut_growth_tac >> asm_rewrite_tac[])) >>
    strip_tac)
    [(`a10`,`sc`),(`a9`,`a10`),(`a8`,`a9`),(`a7`,`a8`),(`a6`,`a7`),
     (`a5`,`a6`),(`a2`,`a5`)] >>
  `ctx_has_dalloca ctx` by (drule_all copy_dalloca_in_context >> simp[]) >>
  suspend "freshness"
QED

Resume create_copy_emit_cuts_mods[freshness]:
  map_every (fn pat => qpat_assum pat
    (strip_assume_tac o MATCH_MP (SPEC_ALL fresh_output_props)))
    [`a6.cs_next_var = a5.cs_next_var + 1`,
     `a1.cs_next_var = sm.cs_next_var + 1`,
     `a4.cs_next_var = a3.cs_next_var + 1`] >>
  `(!x. code = Var x \/ preamble = Var x ==> not_fresh_at a5 x)` by
    (rpt gen_tac >> strip_tac
     >- (qpat_x_assum `code = Var x` mp_tac >> simp[] >>
         disch_then (SUBST1_TAC o SYM) >>
         irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `a1` >> simp[]) >>
     qpat_x_assum `preamble = Var x` mp_tac >> simp[] >>
     disch_then (SUBST1_TAC o SYM) >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists `a4` >>
     qpat_x_assum `not_fresh_at a4 _` mp_tac >> simp[]) >>
  qpat_x_assum `alloc_ptr = _` SUBST_ALL_TAC >>
  `!x. MEM (Var x) [Var (STRING #"%" (toString a5.cs_next_var));target;code] ==>
       not_fresh_at a6 x` by
    (rpt gen_tac >> pure_rewrite_tac[MEM] >> pure_rewrite_tac[boolTheory.OR_CLAUSES] >>
     strip_tac
     >- (qpat_x_assum `Var x = Var _` mp_tac >>
         qpat_x_assum `not_fresh_at a6 _` mp_tac >> simp[]) >>
     irule loweringShapeDefsTheory.not_fresh_at_mono
     >- (qexists `sm` >> conj_tac >- simp[] >>
         qpat_assum `!x. target = _ \/ _ ==> _` irule >> metis_tac[]) >>
     qexists `a5` >> conj_tac >- simp[] >>
     qpat_assum `!x. code = _ \/ _ ==> _` irule >> metis_tac[]) >>
  suspend "pack"
QED

Resume create_copy_emit_cuts_mods[pack]:
  qexistsl_tac [`code`,`a1`,`a2`,`shifted`,`a3`,`preamble`,`a4`,`size'`,`a5`,
    `STRING #"%" (toString a5.cs_next_var)`,`a6`,`a7`,`code_dst`,`a8`,`a9`,
    `buf`,`a10`,`len`,`sc`] >>
  asm_rewrite_tac[same_blocks_def] >> simp[NoAsms]
QED

Finalise create_copy_emit_cuts_mods
