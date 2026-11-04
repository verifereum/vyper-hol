(* Actual storage/transient copy prefixes and their linear-memory footprints. *)
Theory bodyStorageCopyMemory
Ancestors
  bodyAllocMemory exprSimStorageCopy storageDecodeMemory fragExecMem instMemFrontier
  context compileEnv emitHelper emitHelperProps fragExec exprLoweringProps
  venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map
Libs
  monadsyntax

Theorem body_storage_singleton_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand dst s = SOME (n2w b : bytes32) /\
  (!x. dst = Var x ==> x <> v) /\
  b + 32 < dimword (:256) /\ b + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [v];
     mk_inst (id+1) MSTORE [dst; Var v] []] s
Proof
  strip_tac >> (rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> gvs[mk_inst_def]) >>
  gvs[step_inst_base_def, exec_read1_def, mk_inst_def] >>
  Cases_on `eval_operand src s` >> simp[] >>
  simp[run_inst_seq_mem_ok_last, GSYM mk_inst_def, below_frontier_MSTORE] >>
  Cases_on `dst` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[])
QED

Theorem body_storage_iteration_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand dst s = SOME (n2w b : bytes32) /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
  (!x. src = Var x \/ dst = Var x ==>
       ~MEM x [cv; sv; vv; mv; dv; nv]) /\
  b + 32*(k+1) < dimword (:256) /\
  b + 32*(k+1) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s
Proof
  strip_tac >> (
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  Cases_on `eval_operand src s`
  >- simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  `step_inst_base (mk_inst id ADD [src; Var cv] [sv]) s =
     OK (update_var sv (x + n2w k) s)` by (irule step_ADD >> simp[]) >>
  simp[] >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[Once step_inst_base_def, exec_read1_def, mk_inst_def,
       eval_operand_update_var] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s2` >>
  `eval_operand dst s2 = SOME (n2w b) /\
   eval_operand (Var cv) s2 = SOME (n2w k) /\
   s2.vs_alloca_next = s.vs_alloca_next` by
    (Cases_on `dst` >>
     gvs[Abbr `s2`, ALL_DISTINCT, eval_operand_def,
         lookup_var_update_var, update_var_def]) >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base (mk_inst (id+2) MUL [Var cv; Lit 32w] [mv]) s2 =
     OK (update_var mv (n2w k * 32w) s2)` by
    (irule step_MUL >> simp[eval_operand_lit]) >>
  simp[] >>
  `eval_operand dst (update_var mv (n2w k * 32w) s2) = SOME (n2w b)` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base (mk_inst (id+3) ADD [dst; Var mv] [dv])
      (update_var mv (n2w k * 32w) s2) =
     OK (update_var dv (n2w b + n2w k * 32w)
           (update_var mv (n2w k * 32w) s2))` by
    (irule step_ADD >> simp[eval_operand_update_var]) >>
  simp[] >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (simp[below_frontier_MSTORE, eval_operand_update_var, update_var_def] >>
      `b + k * 32 < dimword (:256)` by decide_tac >>
      simp[word_mul_n2w, word_add_n2w, w2n_n2w] >>
      decide_tac) >>
  Cases_on `step_inst_base (mk_inst (id+4) MSTORE [Var dv; Var vv] [])
    (update_var dv (n2w b + n2w k * 32w)
      (update_var mv (n2w k * 32w) s2))` >> simp[] >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  Cases_on `step_inst_base (mk_inst (id+5) ADD [Var cv; Lit 1w] [nv]) v` >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def])
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_STORAGE_COPY_MEMORY_AUDIT OK\n"
     else raise Fail "storage copy inherited admission"
  end) [body_storage_singleton_mem_ok, body_storage_iteration_mem_ok];

(* Resolve the shared execution interface here, without duplicating it. *)
val () = (List.app (fn _ => ())
  [storage_copy_source_run_effect, storage_copy_destination_run_effect,
   storage_copy_increment_run_effect, storage_copy_body_run,
   storage_copy_body_run_effect];
  print "BODY_STORAGE_COPY_EXECUTION_EXPORTS OK\n");

(* Compiler-only boundaries for the memory consumer. *)
Theorem body_storage_copy_layout[local]:
  !loc src dst n.
    (loc = LocStorage \/ loc = LocTransient) ==>
    compile_word_copy_loop src dst n loc LocMemory F =
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
      src_off <- emit_op ADD [src; Var counter];
      value <- compile_ptr_load F NONE loc src_off;
      dst_off <- (do
        scaled <- emit_op MUL [Var counter; Lit 32w];
        emit_op ADD [dst; scaled]
      od);
      emit_void MSTORE [dst_off; value];
      next <- emit_op ADD [Var counter; Lit 1w];
      emit_inst ASSIGN [next] [counter];
      emit_inst JMP [Label hdr] [];
      new_block exit
    od
Proof
  rpt strip_tac >> gvs[compile_word_copy_loop_def, word_scale_def,
                        compile_ptr_store_def]
QED

Theorem body_storage_copy_bind_eq[local]:
  comp_bind m f s = (u,t) <=>
  ?v s1. m s = (v,s1) /\ f v s1 = (u,t)
Proof
  Cases_on `m s` >> simp[comp_bind_def]
QED

Theorem body_storage_copy_boundaries[local]:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) ==>
    ?hdr body exit cv test so value scaled dest next old0 oldh
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
      emit_op ADD [src; Var cv] stb = (so,s5) /\
      compile_ptr_load F NONE loc so s5 = (value,s6) /\
      emit_op MUL [Var cv; Lit 32w] s6 = (scaled,s7) /\
      emit_op ADD [dst; scaled] s7 = (dest,s8) /\
      emit_void MSTORE [dest; value] s8 = ((),s9) /\
      emit_op ADD [Var cv; Lit 1w] s9 = (next,s10) /\
      emit_inst ASSIGN [next] [cv] s10 = ((),ste) /\
      emit_inst JMP [Label hdr] [] ste = ((),st3) /\
      new_block exit st3 = (u,sb)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[body_storage_copy_layout, comp_ignore_bind_def,
      comp_bind_assoc, body_storage_copy_bind_eq]
QED

Theorem body_storage_copy_body_layout[local]:
  !loc src dst cv so value scaled dest next stb s1 s2 s3 s4 s5 s6 ste.
    (loc = LocStorage \/ loc = LocTransient) /\
    emit_op ADD [src; Var cv] stb = (so,s1) /\
    compile_ptr_load F NONE loc so s1 = (value,s2) /\
    emit_op MUL [Var cv; Lit 32w] s2 = (scaled,s3) /\
    emit_op ADD [dst; scaled] s3 = (dest,s4) /\
    emit_void MSTORE [dest; value] s4 = ((),s5) /\
    emit_op ADD [Var cv; Lit 1w] s5 = (next,s6) /\
    emit_inst ASSIGN [next] [cv] s6 = ((),ste) ==>
    ?sv vv mv dv nv.
      so = Var sv /\ value = Var vv /\ scaled = Var mv /\
      dest = Var dv /\ next = Var nv /\
      ALL_DISTINCT [sv; vv; mv; dv; nv] /\
      (!x. not_fresh_at stb x ==> ~MEM x [sv; vv; mv; dv; nv]) /\
      same_blocks stb ste /\
      isPREFIX stb.cs_current_insts ste.cs_current_insts /\
      ste.cs_next_var = stb.cs_next_var + 5 /\
      emitted_insts stb ste =
       [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
        mk_inst (stb.cs_next_id+1)
          (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
        mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
        mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_ptr_load_def, emit_op_def, emit_void_def, emit_inst_def,
      comp_ignore_bind_def, comp_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND,
       DROP_LENGTH_APPEND, GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem body_storage_copy_header_layout[local]:
  !cv n sth test stj.
    emit_op EQ [Var cv; Lit (n2w n)] sth = (test,stj) ==>
    ?tv. test = Var tv /\
      (!x. not_fresh_at sth x ==> x <> tv) /\
      same_blocks sth stj /\
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

Theorem body_storage_copy_init_layout[local]:
  !sa hdr body exit cv tv s1 s2 s3 s4 s0 sj sth stj n old.
    fresh_label "wcopy_cond" sa = (hdr,s1) /\
    fresh_label "wcopy_body" s1 = (body,s2) /\
    fresh_label "wcopy_exit" s2 = (exit,s3) /\
    fresh_var s3 = (cv,s4) /\
    emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0) /\
    emit_inst JMP [Label hdr] [] s0 = ((),sj) /\
    new_block hdr sj = (old,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) ==>
    cv <> tv /\ same_blocks sa s0 /\
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

Theorem body_storage_copy_prefix_freshness[local]:
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

Theorem body_storage_copy_certificate:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) ==>
    ?s0 sj sth stj st2 stb ste st3 hdr loop_body exit cv tv sv vv mv dv nv old0 oldh.
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
       [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
        mk_inst (stb.cs_next_id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
        mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
        mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
        mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
        mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
        mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
      cs_extends sa s0 /\ cs_extends s0 sb /\
      cs_extends sth stj /\ cs_extends stb ste /\
      ALL_DISTINCT [cv;tv;sv;vv;mv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;sv;vv;mv;dv;nv])
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule_all body_storage_copy_boundaries >> strip_tac >>
  drule body_storage_copy_header_layout >> strip_tac >> gnvs[] >>
  drule_all body_storage_copy_init_layout >> strip_tac >>
  drule_all body_storage_copy_prefix_freshness >> strip_tac >>
  rename1 `emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0)` >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj)` >>
  rename1 `emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2)` >>
  rename1 `new_block loop_body st2 = (oldh,stb)` >>
  drule_all body_storage_copy_body_layout >> strip_tac >> gnvs[] >>
  rename1 `emit_inst ASSIGN [Var nv] [cv] s10 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `emit_op ADD [src; Var cv] stb = (Var sv,s5)` >>
  rename1 `compile_ptr_load F NONE loc (Var sv) s5 = (Var vv,s6)` >>
  rename1 `emit_op MUL [Var cv; Lit 32w] s6 = (Var mv,s7)` >>
  rename1 `emit_op ADD [dst; Var mv] s7 = (Var dv,s8)` >>
  `cs_extends sa s0 /\ cs_extends sth stj /\ cs_extends stb ste` by
    (rpt conj_tac >> irule cs_extends_same_block >> gvs[same_blocks_def]) >>
  `cs_extends s0 sb` by
    (imp_res_tac cs_extends_emit_inst >> imp_res_tac cs_extends_new_block >>
     metis_tac[cs_extends_trans]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`compile_word_copy_loop _ _ _ _ _ _ _ = _`, `fresh_var _ = _`,
     `emit_inst ASSIGN [Lit _] _ _ = _`, `compile_ptr_load _ _ _ _ _ = _`,
     `emit_void _ _ _ = _`, `emit_inst ASSIGN _ _ _ = _`] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op ADD _ _ = _` kall_tac) >>
  qpat_x_assum `emit_op MUL _ _ = _` kall_tac >>
  goal_assum (drule_at (Pat `emitted_insts _ _ = [mk_inst _ ASSIGN _ _]`)) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  goal_assum (drule_at (Pat `emitted_insts _ _ = [_;_;_;_;_;_;_]`)) >>
  simp[ALL_DISTINCT] >> metis_tac[]
QED

Theorem body_storage_copy_word_layout:
  !opc src dst sa u sb.
    do v <- emit_op opc [src]; emit_void MSTORE [dst; v] od sa = (u,sb) ==>
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id opc [src] [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id + 1) MSTORE
         [dst; Var (STRING #"%" (toString sa.cs_next_var))] []] /\
    (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var))
Proof
  rpt strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      emitted_insts_def, same_blocks_def, not_fresh_at_def] >>
  simp[DROP_APPEND1] >> rewrite_tac[GSYM APPEND_ASSOC] >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_STORAGE_COPY_LAYOUT_AUDIT OK\n"
     else raise Fail "storage copy layout inherited admission"
  end) [body_storage_copy_certificate, body_storage_copy_word_layout];
