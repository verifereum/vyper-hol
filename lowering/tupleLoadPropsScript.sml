(*
 * The run of compile_tuple_load_all over word and memory-backed elements.
 *
 * TOP-LEVEL:
 *   compile_tuple_load_all_run — the loads' run
 *   eval_operands_length, eval_operands_index — evaluated operand lists
 *)
Theory tupleLoadProps
Ancestors
  stmtSimReturn stmtLowering context list rich_list freshWrites
  venomExecSemantics venomState exprLoweringProps emitHelperProps
  compileEnv valueEncoding

Theorem compile_tuple_load_all_values:
  !tys cenv bop off sa elems sb s w.
    compile_tuple_load_all cenv bop tys off sa = (elems, sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    ?t vs. run_inst_seq (emitted_insts sa sb) s = OK t /\
           t = s with vs_vars := vs /\
           (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
           eval_operands elems t = SOME
             (GENLIST (\i. if is_word_type (EL i tys) then
                mem_word_at (w2n (w + n2w (off +
                  SUM (MAP (type_memory_bytes cenv) (TAKE i tys))))) s.vs_memory
              else w + n2w (off +
                  SUM (MAP (type_memory_bytes cenv) (TAKE i tys)))) (LENGTH tys))
Proof
  Induct
  >- (rw[compile_tuple_load_all_def, comp_return_def] >>
      simp[emitted_insts_def, same_blocks_def, run_inst_seq_def,
           eval_operands_def] >>
      qexists `s.vs_vars` >> simp[venom_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` mp_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, LET_THM] >>
  rename1 `type_memory_bytes cenv ht` >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv, sm)` >>
  rename1 `compile_load_memory _ _ sm = (v, sh)` >>
  rename1 `compile_tuple_load_all _ _ _ _ sh = (rest, sf)` >>
  drule_all tuple_elem_load_head_run >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sh.cs_next_var` by simp[] >>
  `(!x. bop = Var x ==> not_fresh_at sh x) /\
   eval_operand bop (s with vs_vars := vs) = SOME w` by
    (conj_tac >- metis_tac[not_fresh_at_mono] >>
     `eval_operand bop (s with vs_vars := vs) = eval_operand bop s` by
       (irule eval_operand_old_vars >> simp[] >> qexists `sa` >> simp[]) >> simp[]) >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sh.cs_next_var` by simp[] >>
  `sh.cs_next_var <= sf.cs_next_var` by simp[] >>
  `sf.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sf` by simp[] >>
  drule_all tuple_load_cons_compose >> strip_tac >>
  gvs[] >> simp[Once GENLIST_CONS, combinTheory.o_DEF] >>
  metis_tac[]
QED

Theorem eval_operands_length:
  !ops s ws. eval_operands ops s = SOME ws ==> LENGTH ws = LENGTH ops
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem eval_operands_index:
  !ops s ws i.
    eval_operands ops s = SOME ws /\ i < LENGTH ops ==>
    eval_operand (EL i ops) s = SOME (EL i ws)
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `i` >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Theorem compile_tuple_load_all_run:
  !tys cenv bop off sa elems sb s w.
    compile_tuple_load_all cenv bop tys off sa = (elems, sb) /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    eval_operand bop s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    (!x. MEM (Var x) elems ==> not_fresh_at sb x) /\
    LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
    ?t vs. run_inst_seq (emitted_insts sa sb) s = OK t /\
           t = s with vs_vars := vs /\
           (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
           (!i. i < LENGTH tys ==>
             eval_operand (EL i elems) t = SOME
               (if is_word_type (EL i tys) then
                  mem_word_at (w2n (w + n2w (off +
                    SUM (MAP (type_memory_bytes cenv) (TAKE i tys))))) s.vs_memory
                else w + n2w (off +
                    SUM (MAP (type_memory_bytes cenv) (TAKE i tys)))))
Proof
  rpt strip_tac >> drule_all compile_tuple_load_all_values >> strip_tac >>
  gvs[] >> qexists `vs` >> simp[] >>
  rpt strip_tac >>
  drule eval_operands_index >> disch_then (qspec_then `i` mp_tac) >>
  simp[]
QED
