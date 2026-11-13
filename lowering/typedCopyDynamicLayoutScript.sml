(* Compiler-only decomposition of the dynamic typed-copy prefix. *)
Theory typedCopyDynamicLayout
Ancestors context immutableCopyExecution placeMemoryCodeLayout fragExec
  typedCopyDynamicSlowLayoutPtr externalEntryShape exprSimAccounts
  emitHelperProps typedCopyLoopCompilerBoundaryPtr

Theorem compile_copy_dynarray_typed_layout:
 !ce dst dty dc src sty sa sz.
 compile_copy_dynarray_typed ce (Var dst) dty dc (Var src) sty sa = ((),sz) ==>
 ?len gt ok sp dp s1 s2 s3 s4 s5 s6 s7.
 emit_op MLOAD [Var src] sa = (Var len,s1) /\
 emit_op GT [Var len; Lit (n2w dc)] s1 = (Var gt,s2) /\
 emit_op ISZERO [Var gt] s2 = (Var ok,s3) /\
 emit_void ASSERT [Var ok] s3 = ((),s4) /\
 emit_void MSTORE [Var dst;Var len] s4 = ((),s5) /\
 emit_op ADD [Var src;Lit 32w] s5 = (Var sp,s6) /\
 emit_op ADD [Var dst;Lit 32w] s6 = (Var dp,s7) /\
 cs_extends sa s1 /\ cs_extends s1 s7 /\ cs_extends s7 sz /\
 (!fn. fn_has_code sa sz fn ==>
   fn_has_code sa s1 fn /\ fn_has_code s1 s7 fn /\ fn_has_code s7 sz fn) /\
 (!p. not_fresh_at sa p ==> not_fresh_at s1 p /\ not_fresh_at s7 p /\
   ~MEM p [len;gt;ok;sp;dp]) /\
 not_fresh_at s1 len /\ not_fresh_at s7 len /\
 not_fresh_at s7 sp /\ not_fresh_at s7 dp /\
 (if type_memory_bytes ce dty = type_memory_bytes ce sty /\ dty = sty then
    do data_sz <- emit_op MUL [Var len; Lit (n2w (type_memory_bytes ce dty))];
       compile_copy_memory_dynamic (Var dp) (Var sp) data_sz od
  else
    do cond_lbl <- fresh_label "typed_dyn_cond";
       body_lbl <- fresh_label "typed_dyn_body";
       exit_lbl <- fresh_label "typed_dyn_exit";
       counter <- fresh_var;
       emit_inst ASSIGN [Lit 0w] [counter];
       emit_inst JMP [Label cond_lbl] [];
       new_block cond_lbl;
       lt_op <- emit_op LT [Var counter;Var len];
       done_op <- emit_op ISZERO [lt_op];
       emit_inst JNZ [done_op;Label exit_lbl;Label body_lbl] [];
       new_block body_lbl;
       src_off <- emit_op MUL [Var counter;Lit (n2w (type_memory_bytes ce sty))];
       dst_off <- emit_op MUL [Var counter;Lit (n2w (type_memory_bytes ce dty))];
       src_elem <- emit_op ADD [Var sp;src_off];
       dst_elem <- emit_op ADD [Var dp;dst_off];
       compile_store_memory_typed ce dst_elem dty src_elem sty;
       new_ctr <- emit_op ADD [Var counter;Lit 1w];
       emit_inst ASSIGN [new_ctr] [counter];
       emit_inst JMP [Label cond_lbl] [];
       _ <- new_block exit_lbl;
       return () od) s7 = ((),sz)
Proof
 rpt gen_tac >>
 disch_then (mp_tac o PURE_ONCE_REWRITE_RULE [compile_store_memory_typed_def]) >>
 pure_rewrite_tac [LET_THM, compileEnvTheory.comp_ignore_bind_def] >>
 BETA_TAC >>
 simp[Once immutable_comp_bind_cases] >>
 strip_tac >>
 ntac 6 (qpat_x_assum `compileEnv$comp_bind _ _ _ = _` mp_tac >>
   simp[Once immutable_comp_bind_cases] >> strip_tac) >>
 rename1 `emit_op MLOAD [Var src] sa = (lv,a1)` >>
 rename1 `emit_op ADD [Var dst;Lit 32w] a6 = (dv,a7)` >>
 qmatch_asmsub_abbrev_tac `tail a7 = ((),sz)` >>
 `cs_extends a7 (SND (tail a7)) /\
  EVERY (isPREFIX "@") (added_labels a7 (SND (tail a7)))` by
   (qpat_x_assum `tail a7 = _` kall_tac >>
    simp[Abbr `tail`] >>
    IF_CASES_TAC >> gvs[] >>
    rpt (FIRST [irule fresh_label_bind_labels,
                irule new_block_action_labels >>
                  rename1 `isPREFIX "@" lab` >> Cases_on `lab` >> gvs[],
                irule comp_bind_labels >> conj_tac,
                irule comp_ignore_bind_labels >> conj_tac, disch_tac] >>
         rpt gen_tac >> BETA_TAC >>
         simp[comp_return_labels, emit_op_labels, emit_inst_labels,
              fresh_var_action_labels, compile_copy_memory_dynamic_labels,
              cj 1 typed_memory_family_labels])) >>
 imp_res_tac emit_op_next_var >>
 imp_res_tac emit_op_extends_next_var >>
 `!opc ops x y. emit_void opc ops x = ((),y) ==> cs_extends x y` by
   (rpt strip_tac >> mp_tac (Q.SPECL [`opc`,`ops`,`x`,`\x:string. T`] emit_void_labels) >> simp[]) >>
 qpat_x_assum `!opc ops x y. _` imp_res_tac >>
 imp_res_tac emitted_insts_emit_void >>
 gvs[] >>
 `cs_extends a1 a7` by metis_tac[compileEnvTheory.cs_extends_trans] >>
 `cs_extends sa a7` by metis_tac[compileEnvTheory.cs_extends_trans] >>
 simp[GSYM markerTheory.Abbrev_def] >>
 conj_tac >- metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
 conj_tac >-
   (rpt strip_tac >>
    fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
    metis_tac[arithmeticTheory.LE_ADD, arithmeticTheory.LESS_EQ_TRANS]) >>
 simp[loweringStateRelDefsTheory.not_fresh_at_def,
      ASCIInumbersTheory.toString_11] >>
 simp[Abbr `tail`]
QED
