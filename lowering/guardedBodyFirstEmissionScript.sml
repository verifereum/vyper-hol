(* Strong original-block emission for the external guarded stmts. *)
Theory guardedBodyFirstEmission
Ancestors
  stmtCompilerFirstEmission entryContainingExitPhi compilerFirstEmission
  moduleLowering stmtLowering compileEnv fragExec emitHelper

Theorem guarded_body_first_emission:
  ~block_is_terminated a /\
  compile_guarded_body ce F nk ut iv stmts rt a = ((),b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==>
    ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
      i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_guarded_body_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def, comp_get_def, LET_THM,
    pairTheory.UNCURRY_DEF] >>
  Cases_on `compile_stmts ce NoLoop
    (case rt of SOME t => t | NONE => BaseT BoolT) stmts a` >>
  rename1 `compile_stmts _ _ _ _ a = (u,c)` >>
  asm_simp_tac bool_ss [LET_THM, pairTheory.UNCURRY_DEF,
    comp_ignore_bind_def, comp_bind_def, comp_return_def] >> strip_tac >>
  drule (cj 2 first_emission_stmt_compilers) >> strip_tac
  >- ( `~block_is_terminated c` by gvs[block_is_terminated_def] >>
       `compile_guarded_body ce F nk ut iv [] rt c = ((),b)` by
         gvs[compile_guarded_body_def, compile_stmt_def, comp_ignore_bind_def,
           comp_bind_def, comp_return_def, comp_get_def, pairTheory.UNCURRY_DEF] >>
       drule_all entry_guarded_empty_body_emission >> strip_tac >>
       `opc <> PHI` by simp[] >>
       drule_all (cj 1 first_emission_emit_helpers) >> strip_tac >>
       (conj_tac >- metis_tac[cs_extends_trans] >>
       rpt strip_tac >>
       qspecl_then [`a`, `c`, `b`, `fn`] mp_tac fn_has_code_split >>
       asm_rewrite_tac[] >> strip_tac >>
       gvs[] >> first_x_assum drule >> simp[])) >>
  Cases_on `block_is_terminated c`
  >- (gvs[comp_return_def] >> simp[]) >>
  `compile_guarded_body ce F nk ut iv [] rt c = ((),b)` by
    gvs[compile_guarded_body_def, compile_stmt_def, comp_ignore_bind_def,
      comp_bind_def, comp_return_def, comp_get_def, pairTheory.UNCURRY_DEF] >>
  drule_all entry_guarded_empty_body_emission >> strip_tac >>
  `opc <> PHI` by simp[] >>
  drule_all (cj 1 first_emission_emit_helpers) >> strip_tac >>
  (conj_tac >- metis_tac[cs_extends_trans] >>
   rpt strip_tac >>
   qspecl_then [`a`, `c`, `b`, `fn`] mp_tac fn_has_code_split >>
   asm_rewrite_tac[] >> strip_tac >>
   qpat_x_assum `!fn. fn_has_code a c fn ==> _` drule >> simp[])
QED
