(* Concrete output and instruction boundary for multi-output operations. *)
Theory bodyIntCallEmitBoundary
Ancestors
  emitHelper emitHelperProps compileEnv loweringStateRelDefs venomInst list rich_list arithmetic

Theorem fresh_vars_result:
  !n sa outs sb.
    fresh_vars n sa = (outs,sb) ==>
    outs = GENLIST (\i. "%" ++ toString (sa.cs_next_var + i)) n /\
    sb = sa with cs_next_var := sa.cs_next_var + n
Proof
  Induct >> simp[fresh_vars_def, comp_return_def, comp_bind_def,
    fresh_var_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
  gvs[] >> pure_once_rewrite_tac[GENLIST_CONS] >>
  simp[combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
  gen_tac >> AP_TERM_TAC >> decide_tac
QED

Theorem emit_multi_op_result:
  emit_multi_op opc ops n sa = (results,sb) ==>
  ?outs.
    results = MAP Var outs /\
    outs = GENLIST (\i. "%" ++ toString (sa.cs_next_var + i)) n /\
    LENGTH outs = n /\
    sb = sa with <|
      cs_next_var := sa.cs_next_var + n;
      cs_next_id := sa.cs_next_id + 1;
      cs_current_insts := sa.cs_current_insts ++
        [mk_inst sa.cs_next_id opc ops outs] |>
Proof
  simp[emit_multi_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule fresh_vars_result >> strip_tac >>
  gvs[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def]
QED

(* The allocated outputs are old at the following code, and cannot clobber
   variables that were already old before the operation. *)
Theorem emit_multi_op_output_bounds:
  emit_multi_op opc ops n sa = (results,sb) ==>
  LENGTH results = n /\
  (!x. MEM (Var x) results ==> not_fresh_at sb x) /\
  (!x. not_fresh_at sa x ==> ~MEM (Var x) results)
Proof
  strip_tac >> drule emit_multi_op_result >> strip_tac >>
  gvs[MEM_MAP, MEM_GENLIST, not_fresh_at_def] >> rpt strip_tac
  >- (gvs[ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  first_x_assum (qspec_then `sa.cs_next_var + i` mp_tac) >> simp[]
QED
