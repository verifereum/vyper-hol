(* Layout of the dynamic-array slow tail, with an arbitrary recursive exit. *)
Theory typedCopyDynamicSlowLayoutPtr
Ancestors typedCopyLoopLayoutPtr

Theorem compile_copy_dynarray_typed_slow_tail_layout:
 !ce dst dty src sty len sa sz.
 (do cond_lbl <- fresh_label "typed_dyn_cond";
     body_lbl <- fresh_label "typed_dyn_body";
     exit_lbl <- fresh_label "typed_dyn_exit";
     counter <- fresh_var;
     emit_inst ASSIGN [Lit 0w] [counter];
     emit_inst JMP [Label cond_lbl] [];
     new_block cond_lbl;
     lt_op <- emit_op LT [Var counter; len];
     done_op <- emit_op ISZERO [lt_op];
     emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
     new_block body_lbl;
     src_off <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes ce sty))];
     dst_off <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes ce dty))];
     src_elem <- emit_op ADD [src; src_off];
     dst_elem <- emit_op ADD [dst; dst_off];
     compile_store_memory_typed ce dst_elem dty src_elem sty;
     new_ctr <- emit_op ADD [Var counter; Lit 1w];
     emit_inst ASSIGN [new_ctr] [counter];
     emit_inst JMP [Label cond_lbl] [];
     _ <- new_block exit_lbl;
     return () od) sa = ((),sz) ==>
 ?cond body exit ctr lt done so doff sp dp sc sb si se tail.
 cond = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
 body = fresh_label_output "typed_dyn_body" (sa.cs_next_label + 1) /\
 exit = fresh_label_output "typed_dyn_exit" (sa.cs_next_label + 2) /\
 ctr = "%" ++ toString sa.cs_next_var /\
 lt = "%" ++ toString (sa.cs_next_var + 1) /\
 done = "%" ++ toString (sa.cs_next_var + 2) /\
 so = "%" ++ toString (sa.cs_next_var + 3) /\
 doff = "%" ++ toString (sa.cs_next_var + 4) /\
 sp = "%" ++ toString (sa.cs_next_var + 5) /\
 dp = "%" ++ toString (sa.cs_next_var + 6) /\
 sc = sa with <|
   cs_next_label := sa.cs_next_label + 3;
   cs_next_var := sa.cs_next_var + 1;
   cs_next_id := sa.cs_next_id + 2;
   cs_blocks := <|bb_label := sa.cs_current_bb;
     bb_instructions := sa.cs_current_insts ++
       [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
        mk_inst (sa.cs_next_id+1) JMP [Label cond] []]|> :: sa.cs_blocks;
   cs_current_bb := cond; cs_current_insts := [] |> /\
 sb = sc with <|
   cs_next_var := sc.cs_next_var + 2;
   cs_next_id := sc.cs_next_id + 3;
   cs_blocks := <|bb_label := cond; bb_instructions :=
     [mk_inst sc.cs_next_id LT [Var ctr; len] [lt];
      mk_inst (sc.cs_next_id+1) ISZERO [Var lt] [done];
      mk_inst (sc.cs_next_id+2) JNZ
        [Var done; Label exit; Label body] []]|> :: sc.cs_blocks;
   cs_current_bb := body; cs_current_insts := [] |> /\
 si = sb with <|
   cs_next_var := sb.cs_next_var + 4;
   cs_next_id := sb.cs_next_id + 4;
   cs_current_insts :=
     [mk_inst sb.cs_next_id MUL
        [Var ctr; Lit (n2w (type_memory_bytes ce sty))] [so];
      mk_inst (sb.cs_next_id+1) MUL
        [Var ctr; Lit (n2w (type_memory_bytes ce dty))] [doff];
      mk_inst (sb.cs_next_id+2) ADD [src; Var so] [sp];
      mk_inst (sb.cs_next_id+3) ADD [dst; Var doff] [dp]] |> /\
 compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) /\
 tail = se with <|
   cs_next_var := se.cs_next_var + 1;
   cs_next_id := se.cs_next_id + 3;
   cs_current_insts := se.cs_current_insts ++
     [mk_inst se.cs_next_id ADD [Var ctr; Lit 1w]
        ["%" ++ toString se.cs_next_var];
      mk_inst (se.cs_next_id+1) ASSIGN
        [Var ("%" ++ toString se.cs_next_var)] [ctr];
      mk_inst (se.cs_next_id+2) JMP [Label cond] []] |> /\
 sz = tail with <|
   cs_blocks := <|bb_label := se.cs_current_bb;
     bb_instructions := tail.cs_current_insts|> :: se.cs_blocks;
   cs_current_bb := exit; cs_current_insts := [] |>
Proof
 rpt gen_tac >>
 simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def, compileEnvTheory.fresh_label_def,
   compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
   emitHelperTheory.emit_inst_def, emitHelperTheory.emit_op_def,
   compileEnvTheory.emit_def, compileEnvTheory.new_block_def, listTheory.APPEND_ASSOC] >>
 strip_tac >>
 qmatch_asmsub_abbrev_tac `compile_store_memory_typed ce dop dty sop sty child` >>
 simp[listTheory.APPEND_ASSOC] >>
 pairarg_tac >> gvs[] >> qexists_tac `cs'` >> fs[Abbr `child`] >>
 rule_assum_tac (PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
 pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
 asm_rewrite_tac[]
QED
