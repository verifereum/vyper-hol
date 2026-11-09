(* Task-local compiler certificate; local interfaces from stmtSimStoreCopy. *)
Theory bodyMemAssignTopCopyCompiler
Ancestors
  list rich_list finite_map pred_set fragExec loweringSlice
  emitHelper emitHelperProps exprLoweringProps context compileEnv
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

Theorem topcopy_compile_layout[local]:
  !loc src dst n.
    (loc = LocStorage \/ loc = LocTransient) ==>
    compile_word_copy_loop src dst n LocMemory loc F =
    do
      hdr <- fresh_label "wcopy_cond";
      body <- fresh_label "wcopy_body";
      exit <- fresh_label "wcopy_exit";
      counter <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [counter];
      emit_inst JMP [Label hdr] [];
      new_block hdr;
      done_op <- emit_op EQ [Var counter; Lit (n2w n)];
      emit_inst JNZ [done_op; Label exit; Label body] [];
      new_block body;
      scaled <- emit_op MUL [Var counter; Lit 32w];
      src_off <- emit_op ADD [src; scaled];
      value <- emit_op MLOAD [src_off];
      dst_off <- emit_op ADD [dst; Var counter];
      emit_void (if loc = LocStorage then SSTORE else TSTORE) [dst_off; value];
      next <- emit_op ADD [Var counter; Lit 1w];
      emit_inst ASSIGN [next] [counter];
      emit_inst JMP [Label hdr] [];
      new_block exit
    od
Proof
  rpt strip_tac >> gvs[compile_word_copy_loop_def, word_scale_def,
                        compile_ptr_load_def, compile_ptr_store_def,
                        comp_bind_assoc]
QED

Theorem topcopy_bind_eq[local]:
  comp_bind m f s = (u,t) <=>
  ?v s1. m s = (v,s1) /\ f v s1 = (u,t)
Proof
  Cases_on `m s` >> simp[comp_bind_def]
QED

Theorem topcopy_compile_boundaries[local]:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) ==>
    ?hdr body exit cv test scaled so value dest next old0 oldh
     s1 s2 s3 s4 s0 sj sth stj st2 stb s5 s6 s7 s8 s9 s10 ste st3.
      fresh_label "wcopy_cond" sa = (hdr,s1) /\
      fresh_label "wcopy_body" s1 = (body,s2) /\
      fresh_label "wcopy_exit" s2 = (exit,s3) /\
      fresh_var s3 = (cv,s4) /\
      emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0) /\
      emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
      new_block hdr sj = (old0,sth) /\
      emit_op EQ [Var cv; Lit (n2w n)] sth = (test,stj) /\
      emit_inst JNZ [test; Label exit; Label body] [] stj = ((),st2) /\
      new_block body st2 = (oldh,stb) /\
      emit_op MUL [Var cv; Lit 32w] stb = (scaled,s5) /\
      emit_op ADD [src; scaled] s5 = (so,s6) /\
      emit_op MLOAD [so] s6 = (value,s7) /\
      emit_op ADD [dst; Var cv] s7 = (dest,s8) /\
      emit_void (if loc = LocStorage then SSTORE else TSTORE) [dest; value] s8 = ((),s9) /\
      emit_op ADD [Var cv; Lit 1w] s9 = (next,s10) /\
      emit_inst ASSIGN [next] [cv] s10 = ((),ste) /\
      emit_inst JMP [Label hdr] [] ste = ((),st3) /\
      new_block exit st3 = (u,sb)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[topcopy_compile_layout, comp_ignore_bind_def,
      comp_bind_assoc, topcopy_bind_eq]
QED

Theorem topcopy_body_layout[local]:
  !loc src dst cv scaled so value dest next stb s1 s2 s3 s4 s5 s6 ste.
    (loc = LocStorage \/ loc = LocTransient) /\
    emit_op MUL [Var cv; Lit 32w] stb = (scaled,s1) /\
    emit_op ADD [src; scaled] s1 = (so,s2) /\
    emit_op MLOAD [so] s2 = (value,s3) /\
    emit_op ADD [dst; Var cv] s3 = (dest,s4) /\
    emit_void (if loc = LocStorage then SSTORE else TSTORE) [dest; value] s4 = ((),s5) /\
    emit_op ADD [Var cv; Lit 1w] s5 = (next,s6) /\
    emit_inst ASSIGN [next] [cv] s6 = ((),ste) ==>
    ?mv sv vv dv nv.
      scaled = Var mv /\ so = Var sv /\ value = Var vv /\
      dest = Var dv /\ next = Var nv /\
      ALL_DISTINCT [mv; sv; vv; dv; nv] /\
      (!x. not_fresh_at stb x ==> ~MEM x [mv; sv; vv; dv; nv]) /\
      same_blocks stb ste /\
      isPREFIX stb.cs_current_insts ste.cs_current_insts /\
      ste.cs_next_var = stb.cs_next_var + 5 /\
      ste.cs_next_id = stb.cs_next_id + 7 /\
      emitted_insts stb ste =
       [mk_inst stb.cs_next_id MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+1) ADD [src; Var mv] [sv];
        mk_inst (stb.cs_next_id+2) MLOAD [Var sv] [vv];
        mk_inst (stb.cs_next_id+3) ADD [dst; Var cv] [dv];
        mk_inst (stb.cs_next_id+4)
          (if loc = LocStorage then SSTORE else TSTORE) [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def,
      comp_ignore_bind_def, comp_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem topcopy_header_layout[local]:
  !cv n sth test stj.
    emit_op EQ [Var cv; Lit (n2w n)] sth = (test,stj) ==>
    ?tv. test = Var tv /\
      (!x. not_fresh_at sth x ==> x <> tv) /\
      same_blocks sth stj /\ stj.cs_next_id = sth.cs_next_id + 1 /\
      isPREFIX sth.cs_current_insts stj.cs_current_insts /\
      emitted_insts sth stj =
        [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, comp_ignore_bind_def, comp_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem topcopy_init_layout[local]:
  !sa hdr body exit cv tv s1 s2 s3 s4 s0 sj sth stj n old.
    fresh_label "wcopy_cond" sa = (hdr,s1) /\
    fresh_label "wcopy_body" s1 = (body,s2) /\
    fresh_label "wcopy_exit" s2 = (exit,s3) /\
    fresh_var s3 = (cv,s4) /\
    emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0) /\
    emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
    new_block hdr sj = (old,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) ==>
    cv <> tv /\ same_blocks sa s0 /\ s0.cs_next_id = sa.cs_next_id + 1 /\
    isPREFIX sa.cs_current_insts s0.cs_current_insts /\
    emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
    (!x. not_fresh_at sa x ==> x <> cv /\ x <> tv) /\
    not_fresh_at sth cv
Proof
  rpt gen_tac >> strip_tac >>
  gvs[fresh_label_def, fresh_var_def, new_block_def, emit_inst_def,
      emit_op_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, fresh_var_distinct] >>
  conj_tac
  >- (rw[not_fresh_at_def] >> first_x_assum irule >> simp[]) >>
  rw[not_fresh_at_def, fresh_var_distinct] >> decide_tac
QED

Theorem topcopy_prefix_freshness[local]:
  !sa hdr body exit cv tv s1 s2 s3 s4 s0 sj sth stj st2 stb n old0 oldh.
    fresh_label "wcopy_cond" sa = (hdr,s1) /\
    fresh_label "wcopy_body" s1 = (body,s2) /\
    fresh_label "wcopy_exit" s2 = (exit,s3) /\
    fresh_var s3 = (cv,s4) /\
    emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0) /\
    emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
    new_block hdr sj = (old0,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    emit_inst JNZ [Var tv; Label exit; Label body] [] stj = ((),st2) /\
    new_block body st2 = (oldh,stb) ==>
    sth.cs_next_var = sa.cs_next_var + 1 /\
    stb.cs_next_var = sa.cs_next_var + 2 /\
    not_fresh_at stb cv /\ not_fresh_at stb tv /\
    (!x. not_fresh_at sa x ==> not_fresh_at stb x)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[fresh_label_def, fresh_var_def, new_block_def, emit_inst_def,
      emit_op_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  simp[not_fresh_at_def, fresh_var_distinct] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem topcopy_compile_certificate:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) ==>
    ?s0 sj sth stj st2 stb ste st3 hdr loop_body exit cv tv mv sv vv dv nv old0 oldh.
      emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
      new_block hdr sj = (old0,sth) /\
      emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
      emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2) /\
      new_block loop_body st2 = (oldh,stb) /\
      emit_inst JMP [Label hdr] [] ste = ((),st3) /\
      new_block exit st3 = (u,sb) /\
      same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
      emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
      same_blocks sth stj /\ isPREFIX sth.cs_current_insts stj.cs_current_insts /\
      emitted_insts sth stj = [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]] /\
      same_blocks stb ste /\ isPREFIX stb.cs_current_insts ste.cs_current_insts /\
      emitted_insts stb ste =
       [mk_inst stb.cs_next_id MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+1) ADD [src; Var mv] [sv];
        mk_inst (stb.cs_next_id+2) MLOAD [Var sv] [vv];
        mk_inst (stb.cs_next_id+3) ADD [dst; Var cv] [dv];
        mk_inst (stb.cs_next_id+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
      s0.cs_next_id = sa.cs_next_id + 1 /\
      stj.cs_next_id = sth.cs_next_id + 1 /\
      ste.cs_next_id = stb.cs_next_id + 7 /\
      cs_extends sa s0 /\ cs_extends s0 sb /\
      cs_extends sth stj /\ cs_extends stb ste /\
      ALL_DISTINCT [cv;tv;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dv;nv])
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule_all topcopy_compile_boundaries >> strip_tac >>
  drule topcopy_header_layout >> strip_tac >> gnvs[] >>
  drule_all topcopy_init_layout >> strip_tac >>
  drule_all topcopy_prefix_freshness >> strip_tac >>
  rename1 `emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0)` >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj)` >>
  rename1 `emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2)` >>
  rename1 `new_block loop_body st2 = (oldh,stb)` >>
  drule_all topcopy_body_layout >> strip_tac >> gnvs[] >>
  rename1 `emit_inst ASSIGN [Var nv] [cv] s10 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `emit_op MUL [Var cv; Lit 32w] stb = (Var mv,s5)` >>
  rename1 `emit_op ADD [src; Var mv] s5 = (Var sv,s6)` >>
  rename1 `emit_op MLOAD [Var sv] s6 = (Var vv,s7)` >>
  rename1 `emit_op ADD [dst; Var cv] s7 = (Var dv,s8)` >>
  `cs_extends sa s0 /\ cs_extends sth stj /\ cs_extends stb ste` by
    (rpt conj_tac >> irule cs_extends_same_block >> gvs[same_blocks_def]) >>
  `cs_extends s0 sb` by
    (imp_res_tac cs_extends_emit_inst >> imp_res_tac cs_extends_new_block >>
     metis_tac[cs_extends_trans]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`compile_word_copy_loop _ _ _ _ _ _ _ = _`, `fresh_var _ = _`,
     `emit_inst ASSIGN [Lit _] _ _ = _`,
     `emit_void _ _ _ = _`, `emit_inst ASSIGN _ _ _ = _`] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op ADD _ _ = _` kall_tac) >>
  qpat_x_assum `emit_op MUL _ _ = _` kall_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _` kall_tac >>
  goal_assum (drule_at (Pat `emitted_insts _ _ = [mk_inst _ ASSIGN _ _]`)) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  goal_assum (drule_at (Pat `emitted_insts _ _ = [_;_;_;_;_;_;_]`)) >>
  simp[ALL_DISTINCT] >> metis_tac[]
QED

Theorem topcopy_code_at[local]:
  !sa sb func code.
    fn_has_code sa sb func /\ same_blocks sa sb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb = code ==>
    ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
      !j. j < LENGTH code ==>
        get_instruction bb (LENGTH sa.cs_current_insts+j) = SOME (EL j code)
Proof
  rpt strip_tac >> irule fn_has_code_same_block >>
  gvs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  qexists_tac `sb` >> simp[DROP_LENGTH_APPEND]
QED

Theorem topcopy_code_certificate:
  !loc src dst n sa u sb func.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
    fn_has_code sa sb func ==>
    ?hdr loop_body exit cv tv mv sv vv dv nv ei hi bi ebb hbb bbb.
      ALL_DISTINCT [cv;tv;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dv;nv]) /\
      lookup_block sa.cs_current_bb func.fn_blocks = SOME ebb /\
      (!j. j < 2 ==> get_instruction ebb (LENGTH sa.cs_current_insts+j) =
        SOME (EL j [mk_inst ei ASSIGN [Lit 0w] [cv];
                    mk_inst (ei+1) JMP [Label hdr] []])) /\
      lookup_block hdr func.fn_blocks = SOME hbb /\
      (!j. j < 2 ==> get_instruction hbb j =
        SOME (EL j [mk_inst hi EQ [Var cv;Lit (n2w n)] [tv];
                    mk_inst (hi+1) JNZ [Var tv;Label exit;Label loop_body] []])) /\
      lookup_block loop_body func.fn_blocks = SOME bbb /\
      (!j. j < 8 ==> get_instruction bbb j =
        SOME (EL j
          [mk_inst bi MUL [Var cv;Lit 32w] [mv];
           mk_inst (bi+1) ADD [src;Var mv] [sv];
           mk_inst (bi+2) MLOAD [Var sv] [vv];
           mk_inst (bi+3) ADD [dst;Var cv] [dv];
           mk_inst (bi+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] [];
           mk_inst (bi+5) ADD [Var cv;Lit 1w] [nv];
           mk_inst (bi+6) ASSIGN [Var nv] [cv];
           mk_inst (bi+7) JMP [Label hdr] []])) /\
      sb.cs_current_bb = exit /\ sb.cs_current_insts = []
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all topcopy_compile_certificate >> strip_tac >>
  `fn_has_code sa s0 func /\ fn_has_code s0 sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all frag_exec_loop_layout >> strip_tac >>
  `?ebb. lookup_block sa.cs_current_bb func.fn_blocks = SOME ebb /\
     !j. j < 1 ==> get_instruction ebb (LENGTH sa.cs_current_insts+j) =
       SOME (EL j [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]])` by
    (qpat_assum `emitted_insts sa s0 = _`
       (mp_then (Pat `emitted_insts _ _ = _`) mp_tac topcopy_code_at) >>
     disch_then (qspec_then `func` mp_tac) >> simp[]) >>
  `?hbb. lookup_block sth.cs_current_bb func.fn_blocks = SOME hbb /\
     !j. j < 1 ==> get_instruction hbb (LENGTH sth.cs_current_insts+j) =
       SOME (EL j [mk_inst sth.cs_next_id EQ [Var cv;Lit (n2w n)] [tv]])` by
    (qpat_assum `emitted_insts sth stj = _`
       (mp_then (Pat `emitted_insts _ _ = _`) mp_tac topcopy_code_at) >>
     disch_then (qspec_then `func` mp_tac) >> simp[]) >>
  qpat_assum `emitted_insts stb ste = _`
    (mp_then (Pat `emitted_insts _ _ = _`) mp_tac topcopy_code_at) >>
  disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `bbb` strip_assume_tac) >>
  map_every (fn q => rpt (qpat_x_assum q kall_tac))
    [`emit_inst _ _ _ _ = _`, `new_block _ _ = _`, `emit_op _ _ _ = _`,
     `compile_word_copy_loop _ _ _ _ _ _ _ = _`, `cs_extends _ _`, `fn_has_code _ _ _`] >>
  qexistsl_tac [`hdr`, `loop_body`, `exit`, `cv`, `tv`, `mv`, `sv`, `vv`, `dv`, `nv`,
    `sa.cs_next_id`, `sth.cs_next_id`, `stb.cs_next_id`, `ebb`, `hbb`, `bbb`] >>
  gvs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
  rpt conj_tac >> rpt strip_tac >>
  `j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6 \/ j=7` by decide_tac >>
  fs[]
QED
