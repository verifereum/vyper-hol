(* Exact compiler shape for the constructor loop without a base operand. *)
Theory immutableLoopOptionCode
Ancestors
  immutableCopyExecution fragExec context compileEnv emitHelper emitHelperProps
  exprLoweringProps loweringStateRelDefs venomState venomExecSemantics venomInst
  words arithmetic list rich_list finite_map

val _ = Parse.hide "count";

Theorem immutable_loop_none_code:
  compile_word_copy_loop_base src dst count LocMemory LocCode T
    NONE sa = (u,sb) /\
  fn_has_code sa sb func ==>
  ?hdr body_lbl cv tv mv sv vv dm dv nv id0 idh idb bb0 bbh bbb.
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb0 /\
    isPREFIX
      [mk_inst id0 ASSIGN [Lit 0w] [cv];
       mk_inst (id0+1) JMP [Label hdr] []]
      (DROP (LENGTH sa.cs_current_insts) bb0.bb_instructions) /\
    lookup_block hdr func.fn_blocks = SOME bbh /\
    isPREFIX
      [mk_inst idh EQ [Var cv; count] [tv];
       mk_inst (idh+1) JNZ [Var tv; Label sb.cs_current_bb; Label body_lbl] []]
      bbh.bb_instructions /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    isPREFIX
      [mk_inst idb MUL [Var cv; Lit 32w] [mv];
       mk_inst (idb+1) ADD [src; Var mv] [sv];
       mk_inst (idb+2) MLOAD [Var sv] [vv];
       mk_inst (idb+3) MUL [Var cv; Lit 32w] [dm];
       mk_inst (idb+4) ADD [dst; Var dm] [dv];
       mk_inst (idb+5) ISTORE [Var dv; Var vv] [];
       mk_inst (idb+6) ADD [Var cv; Lit 1w] [nv];
       mk_inst (idb+7) ASSIGN [Var nv] [cv];
       mk_inst (idb+8) JMP [Label hdr] []]
      bbb.bb_instructions /\
    LENGTH sb.cs_current_insts = 0 /\
    sb.cs_next_var = sa.cs_next_var + 8 /\
    ALL_DISTINCT [cv;tv;mv;sv;vv;dm;dv;nv] /\
    (!x. MEM x [cv;tv;mv;sv;vv;dm;dv;nv] ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dm;dv;nv])
Proof
  strip_tac >>
  gvs[compile_word_copy_loop_base_def, word_scale_def,
      compile_ptr_load_def, compile_ptr_store_def, compile_imm_store_word_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_label_def, fresh_var_def, emit_inst_def, emit_op_def,
      emit_void_def, fresh_id_def, emit_def, new_block_def,
      not_fresh_at_def, fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
      Excl "isPREFIX"] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, arithmeticTheory.ADD1, Excl "isPREFIX"] >>
  qmatch_asmsub_abbrev_tac `mk_inst _ MUL [Var cv; Lit 32w] [mv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ EQ _ [tv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [src; Var mv] [sv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ MLOAD _ [vv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [dst; Var dm] [dv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [Var cv; Lit 1w] [nv]` >>
  qexistsl_tac [`fresh_label_output "wcopy_cond" sa.cs_next_label`,
    `fresh_label_output "wcopy_body" (sa.cs_next_label + 1)`,
    `cv`, `tv`, `mv`, `sv`, `vv`, `dm`, `dv`, `nv`,
    `sa.cs_next_id`, `sa.cs_next_id + 2`, `sa.cs_next_id + 4`] >>
  rpt (goal_assum (drule_at Any)) >>
  once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, Excl "isPREFIX"] >>
  simp[Abbr `cv`, Abbr `tv`, Abbr `mv`, Abbr `sv`, Abbr `vv`,
       Abbr `dm`, Abbr `dv`, Abbr `nv`, fresh_var_distinct] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

