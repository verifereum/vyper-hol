(*
 * Statement simulation: copying a value from memory into storage or
 * transient storage (#637)
 *
 * compile_store_storage (and its transient twin in compile_assign_value),
 * for a value held in more than one word, runs compile_word_copy_loop from
 * the value's memory buffer to its slot: word i of the buffer (MLOAD at
 * buf + 32 * i) is stored at slot + i (SSTORE or TSTORE), for i from 0
 * to word_count - 1, in that order.  The loop reaches its exit block with
 * those stores done and nothing else changed but its own fresh variables.
 * Python: context.py _store_memory_to_storage, _store_memory_to_transient.
 *
 * TOP-LEVEL:
 *   compile_store_copy_frag — the copy loop runs to its exit, having done
 *                             the word_count stores in order
 *)

Theory stmtSimStoreCopy
Ancestors
  list rich_list finite_map pred_set
  fragExec loweringSlice
  emitHelper emitHelperProps exprLoweringProps
  context compileEnv
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* Compiler boundary facts: byte offsets at the source, slot offsets at
   the destination. *)
Theorem compile_store_copy_layout[local]:
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

Theorem store_copy_bind_eq[local]:
  comp_bind m f s = (u,t) <=>
  ?v s1. m s = (v,s1) /\ f v s1 = (u,t)
Proof
  Cases_on `m s` >> simp[comp_bind_def]
QED

Theorem compile_store_copy_boundaries[local]:
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
  gvs[compile_store_copy_layout, comp_ignore_bind_def,
      comp_bind_assoc, store_copy_bind_eq]
QED

Theorem store_copy_body_layout[local]:
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

Theorem store_copy_header_layout[local]:
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

Theorem store_copy_init_layout[local]:
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

Theorem store_copy_prefix_freshness[local]:
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

Theorem compile_store_copy_certificate[local]:
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
      cs_extends sa s0 /\ cs_extends s0 sb /\
      cs_extends sth stj /\ cs_extends stb ste /\
      ALL_DISTINCT [cv;tv;mv;sv;vv;dv;nv] /\
      (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dv;nv])
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule_all compile_store_copy_boundaries >> strip_tac >>
  drule store_copy_header_layout >> strip_tac >> gnvs[] >>
  drule_all store_copy_init_layout >> strip_tac >>
  drule_all store_copy_prefix_freshness >> strip_tac >>
  rename1 `emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0)` >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj)` >>
  rename1 `emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2)` >>
  rename1 `new_block loop_body st2 = (oldh,stb)` >>
  drule_all store_copy_body_layout >> strip_tac >> gnvs[] >>
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

(* Restore exactly the fields ignored by the frozen postcondition. *)
Definition store_copy_normalize_def:
  store_copy_normalize sbase s =
    s with <| vs_vars := sbase.vs_vars;
              vs_current_bb := sbase.vs_current_bb;
              vs_inst_idx := sbase.vs_inst_idx;
              vs_prev_bb := sbase.vs_prev_bb |>
End

Definition store_copy_prefix_def:
  store_copy_prefix loc (b:bytes32) k sbase i =
    FOLDL (\t j. (if loc = LocStorage then sstore else tstore)
                   (k + n2w j) (mload (w2n (b + n2w j * 32w)) sbase) t)
          sbase (COUNT_LIST i)
End

Definition store_copy_frame_def:
  store_copy_frame sa loc b k sbase i s <=>
    (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
    store_copy_normalize sbase s = store_copy_prefix loc b k sbase i
End

Theorem store_copy_prefix_zero[local,simp]:
  store_copy_prefix loc b k sbase 0 = sbase
Proof
  simp[store_copy_prefix_def, COUNT_LIST_def]
QED

Theorem store_copy_prefix_suc[local]:
  store_copy_prefix loc b k sbase (SUC i) =
    (if loc = LocStorage then sstore else tstore)
      (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase)
      (store_copy_prefix loc b k sbase i)
Proof
  simp[store_copy_prefix_def, COUNT_LIST_SNOC, FOLDL_SNOC]
QED

Theorem store_copy_prefix_memory[local,simp]:
  (store_copy_prefix loc b k sbase i).vs_memory = sbase.vs_memory /\
  (store_copy_prefix loc b k sbase i).vs_labels = sbase.vs_labels
Proof
  Induct_on `i` >> simp[store_copy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem store_copy_normalize_jump[local,simp]:
  store_copy_normalize sbase (jump_to l s) = store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def, jump_to_def]
QED

Theorem store_copy_normalize_idx[local,simp]:
  store_copy_normalize sbase (s with vs_inst_idx := idx) =
    store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def]
QED

Theorem store_copy_normalize_update[local,simp]:
  store_copy_normalize sbase (update_var v w s) = store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def, update_var_def]
QED

Theorem store_copy_normalize_store[local]:
  store_copy_normalize sbase
    ((if loc = LocStorage then sstore else tstore) key value s) =
  (if loc = LocStorage then sstore else tstore) key value
    (store_copy_normalize sbase s)
Proof
  Cases_on `loc = LocStorage` >>
  simp[store_copy_normalize_def, sstore_def, tstore_def]
QED

Theorem store_copy_frame_base[local,simp]:
  store_copy_frame sa loc b k sbase 0 sbase
Proof
  simp[store_copy_frame_def, store_copy_normalize_def]
QED

Theorem store_copy_frame_jump[local,simp]:
  store_copy_frame sa loc b k sbase i (jump_to l s) =
  store_copy_frame sa loc b k sbase i s
Proof
  simp[store_copy_frame_def, jump_to_def, store_copy_normalize_def, lookup_var_def]
QED

Theorem store_copy_frame_idx[local,simp]:
  store_copy_frame sa loc b k sbase i (s with vs_inst_idx := idx) =
  store_copy_frame sa loc b k sbase i s
Proof
  simp[store_copy_frame_def, lookup_var_def]
QED

Theorem store_copy_frame_update[local]:
  store_copy_frame sa loc b k sbase i s /\
  (!x. not_fresh_at sa x ==> x <> v) ==>
  store_copy_frame sa loc b k sbase i (update_var v w s)
Proof
  simp[store_copy_frame_def, lookup_var_update_var] >> metis_tac[]
QED

Theorem store_copy_frame_memory[local]:
  store_copy_frame sa loc b k sbase i s ==>
  s.vs_memory = sbase.vs_memory /\ s.vs_labels = sbase.vs_labels
Proof
  strip_tac >> fs[store_copy_frame_def] >> conj_tac
  >- (qpat_x_assum `store_copy_normalize _ _ = _`
        (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >>
      simp[store_copy_normalize_def]) >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
  simp[store_copy_normalize_def]
QED

Theorem store_copy_frame_operand[local]:
  store_copy_frame sa loc b k sbase i s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op sbase = SOME w ==>
  eval_operand op s = SOME w
Proof
  strip_tac >> drule store_copy_frame_memory >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def, store_copy_frame_def] >>
  metis_tac[]
QED

Theorem store_copy_frame_load[local]:
  store_copy_frame sa loc b k sbase i s ==>
  mload addr s = mload addr sbase
Proof
  strip_tac >> drule store_copy_frame_memory >> simp[mload_def]
QED

Theorem store_copy_frame_store[local]:
  store_copy_frame sa loc b k sbase i s ==>
  store_copy_frame sa loc b k sbase (SUC i)
    ((if loc = LocStorage then sstore else tstore)
      (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase) s)
Proof
  simp[store_copy_frame_def, store_copy_prefix_suc,
       store_copy_normalize_store] >> strip_tac >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def, lookup_var_def]
QED

(* Exact straight-line source computation. All register writes are fresh. *)
Theorem store_copy_source_run[local]:
  !sa loc b k sbase i s src cv mv sv vv id.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand src sbase = SOME b /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    ALL_DISTINCT [cv;mv;sv;vv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [mv;sv;vv]) ==>
    ?t. run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+1) ADD [src; Var mv] [sv];
       mk_inst (id+2) MLOAD [Var sv] [vv]] s = OK t /\
      store_copy_frame sa loc b k sbase i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      eval_operand (Var vv) t =
        SOME (mload (w2n (b + n2w i * 32w)) sbase) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var mv (n2w i * 32w) s` >>
  `store_copy_frame sa loc b k sbase i s1` by
    (simp[Abbr `s1`] >> irule store_copy_frame_update >> gvs[] >> metis_tac[]) >>
  `eval_operand src s1 = SOME b` by
    (irule store_copy_frame_operand >> metis_tac[]) >>
  `store_copy_frame sa loc b k sbase i
      (update_var sv (b + n2w i * 32w) s1)` by
    (irule store_copy_frame_update >> gvs[] >> metis_tac[]) >>
  `mload (w2n (b + n2w i * 32w))
      (update_var sv (b + n2w i * 32w) s1) =
    mload (w2n (b + n2w i * 32w)) sbase` by
    (drule_all store_copy_frame_load >> simp[]) >>
  qexists_tac `update_var vv (mload (w2n (b + n2w i * 32w)) sbase)
                (update_var sv (b + n2w i * 32w) s1)` >>
  conj_tac
  >- (`step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [mv]) s = OK s1` by
        (simp[Abbr `s1`] >> irule step_MUL >> simp[eval_operand_lit]) >>
      `step_inst_base (mk_inst (id+1) ADD [src; Var mv] [sv]) s1 =
         OK (update_var sv (b + n2w i * 32w) s1)` by
        (irule step_ADD >> simp[Abbr `s1`, eval_operand_update_var]) >>
      `step_inst_base (mk_inst (id+2) MLOAD [Var sv] [vv])
         (update_var sv (b + n2w i * 32w) s1) =
       OK (update_var vv (mload (w2n (b + n2w i * 32w)) sbase)
             (update_var sv (b + n2w i * 32w) s1))` by
        simp[step_inst_base_def, mk_inst_def, exec_read1_def,
             eval_operand_update_var] >>
      simp[run_inst_seq_def]) >>
  conj_tac
  >- (irule store_copy_frame_update >> gvs[] >> metis_tac[]) >>
  gvs[eval_operand_def, lookup_var_update_var, ALL_DISTINCT,
      update_var_def, Abbr `s1`]
QED

Theorem store_copy_destination_run[local]:
  !sa loc b k sbase i s dst cv vv dv id.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand dst sbase = SOME k /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    eval_operand (Var vv) s = SOME (mload (w2n (b + n2w i * 32w)) sbase) /\
    ALL_DISTINCT [cv;vv;dv] /\
    (!x. not_fresh_at sa x ==> x <> dv) ==>
    ?t. run_inst_seq
      [mk_inst id ADD [dst; Var cv] [dv];
       mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
         [Var dv; Var vv] []] s = OK t /\
      store_copy_frame sa loc b k sbase (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand dst s = SOME k` by
    (drule_all store_copy_frame_operand >> simp[]) >>
  qabbrev_tac `s1 = update_var dv (k + n2w i) s` >>
  `store_copy_frame sa loc b k sbase i s1` by
    (simp[Abbr `s1`] >> irule store_copy_frame_update >> metis_tac[]) >>
  qexists_tac `(if loc = LocStorage then sstore else tstore)
    (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase) s1` >>
  conj_tac
  >- (`step_inst_base (mk_inst id ADD [dst; Var cv] [dv]) s = OK s1` by
        (simp[Abbr `s1`] >> irule step_ADD >> simp[]) >>
      simp[run_inst_seq_def] >>
      fs[ALL_DISTINCT, eval_operand_def] >> Cases_on `loc = LocStorage` >>
      simp[step_inst_base_def, mk_inst_def, exec_write2_def,
           eval_operand_def, lookup_var_update_var, Abbr `s1`]) >>
  conj_tac >- (irule store_copy_frame_store >> simp[]) >>
  Cases_on `loc = LocStorage` >>
  gvs[sstore_def, tstore_def, eval_operand_def, lookup_var_def,
      update_var_def, Abbr `s1`, ALL_DISTINCT, FLOOKUP_UPDATE]
QED

Theorem store_copy_increment_run[local]:
  !sa loc b k sbase i s cv nv id.
    store_copy_frame sa loc b k sbase (SUC i) s /\
    eval_operand (Var cv) s = SOME (n2w i) /\ cv <> nv /\
    (!x. not_fresh_at sa x ==> x <> cv /\ x <> nv) ==>
    ?t. run_inst_seq
      [mk_inst id ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+1) ASSIGN [Var nv] [cv]] s = OK t /\
      store_copy_frame sa loc b k sbase (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s1 = update_var nv (n2w i + 1w) s` >>
  `store_copy_frame sa loc b k sbase (SUC i) s1` by
    (simp[Abbr `s1`] >> irule store_copy_frame_update >> metis_tac[]) >>
  qexists_tac `update_var cv (n2w i + 1w) s1` >> conj_tac
  >- (`step_inst_base (mk_inst id ADD [Var cv; Lit 1w] [nv]) s = OK s1` by
        (simp[Abbr `s1`] >> irule step_ADD >> simp[eval_operand_lit]) >>
      simp[run_inst_seq_def, step_inst_base_def, mk_inst_def,
           eval_operand_update_var, Abbr `s1`]) >>
  conj_tac >- (irule store_copy_frame_update >> metis_tac[]) >>
  simp[eval_operand_update_var, update_var_def, Abbr `s1`,
       arithmeticTheory.ADD1, wordsTheory.word_add_n2w]
QED

Theorem store_copy_body_run[local]:
  !sa loc b k sbase i s src dst cv mv sv vv dv nv id.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) ==>
    ?t. run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+1) ADD [src; Var mv] [sv];
       mk_inst (id+2) MLOAD [Var sv] [vv];
       mk_inst (id+3) ADD [dst; Var cv] [dv];
       mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv; Var vv] [];
       mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t /\
      store_copy_frame sa loc b k sbase (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT [cv;mv;sv;vv] /\ ALL_DISTINCT [cv;vv;dv] /\ cv <> nv` by
    gvs[ALL_DISTINCT] >>
  `(!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. dst = Var x ==> not_fresh_at sa x) /\
   (!x. not_fresh_at sa x ==> ~MEM x [mv;sv;vv]) /\
   (!x. not_fresh_at sa x ==> x <> dv) /\
   (!x. not_fresh_at sa x ==> x <> cv /\ x <> nv)` by
    (gvs[] >> metis_tac[]) >>
  drule_all store_copy_source_run >>
  disch_then (qspec_then `id` (qx_choose_then `s1` strip_assume_tac)) >>
  drule_all store_copy_destination_run >>
  disch_then (qspec_then `id+3` (qx_choose_then `s2` strip_assume_tac)) >>
  drule_all store_copy_increment_run >>
  disch_then (qspec_then `id+5` (qx_choose_then `t` strip_assume_tac)) >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `run_inst_seq _ s = OK s1`
    (assume_tac o SRULE [] o MATCH_MP run_inst_seq_append) >>
  qpat_x_assum `run_inst_seq _ s1 = OK s2`
    (assume_tac o SRULE [arithmeticTheory.ADD_ASSOC] o MATCH_MP run_inst_seq_append) >>
  gvs[arithmeticTheory.ADD_ASSOC]
QED

Theorem store_copy_body_frag[local]:
  !ctx sa loc b k sbase i src dst cv mv sv vv dv nv stb ste R.
    same_blocks stb ste /\ isPREFIX stb.cs_current_insts ste.cs_current_insts /\
    emitted_insts stb ste =
      [mk_inst stb.cs_next_id MUL [Var cv; Lit 32w] [mv];
       mk_inst (stb.cs_next_id+1) ADD [src; Var mv] [sv];
       mk_inst (stb.cs_next_id+2) MLOAD [Var sv] [vv];
       mk_inst (stb.cs_next_id+3) ADD [dst; Var cv] [dv];
       mk_inst (stb.cs_next_id+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv; Var vv] [];
       mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
    eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) ==>
    frag_exec ctx stb ste
      (\s. store_copy_frame sa loc b k sbase i s /\
           eval_operand (Var cv) s = SOME (n2w i))
      (\s. store_copy_frame sa loc b k sbase (SUC i) s /\
           eval_operand (Var cv) s = SOME (n2w (SUC i))) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, Excl "ALL_DISTINCT", Excl "MEM"] >>
  Cases_on `loc = LocStorage` >>
  simp[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  drule_at (Pat `ALL_DISTINCT`) store_copy_body_run >>
  disch_then (drule_all o SRULE []) >>
  disch_then (qspec_then `stb.cs_next_id` (qx_choose_then `t` strip_assume_tac)) >>
  disj1_tac >> qexists_tac `t` >>
  gvs[mk_inst_def, eval_operand_def, lookup_var_def]
QED

Theorem store_copy_init_frag[local]:
  !ctx sa s0 cv loc b k sbase R.
    same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
    emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
    (!x. not_fresh_at sa x ==> x <> cv) ==>
    frag_exec ctx sa s0 (\s. s = sbase)
      (\s. store_copy_frame sa loc b k sbase 0 s /\
           eval_operand (Var cv) s = SOME 0w) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  qexists_tac `update_var cv 0w sbase` >> conj_tac
  >- simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, eval_operand_lit] >>
  conj_tac >- (irule store_copy_frame_update >> simp[] >> metis_tac[]) >>
  simp[eval_operand_def, lookup_var_update_var, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE]
QED

Theorem store_copy_header_frag[local]:
  !ctx sa loc b k sbase i cv tv n sth stj R.
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) ==>
    frag_exec ctx sth stj
      (\s. store_copy_frame sa loc b k sbase i s /\
           eval_operand (Var cv) s = SOME (n2w i))
      (\s. store_copy_frame sa loc b k sbase i s /\
           eval_operand (Var cv) s = SOME (n2w i) /\
           eval_operand (Var tv) s = SOME (bool_to_word (n2w i = n2w n : bytes32))) R
Proof
  rpt gen_tac >> strip_tac >>
  drule store_copy_header_layout >> strip_tac >> gvs[] >>
  irule frag_exec_run_inst_seq >> fs[same_blocks_def] >>
  simp[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  disj1_tac >>
  qexists_tac `update_var tv (bool_to_word (n2w i = n2w n : bytes32)) s` >>
  conj_tac
  >- (`step_inst_base
         (mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]) s =
       OK (update_var tv (bool_to_word (n2w i = n2w n : bytes32)) s)` by
        (irule step_EQ >> simp[eval_operand_lit]) >>
      gvs[run_inst_seq_def, mk_inst_def]) >>
  conj_tac >- (irule store_copy_frame_update >> metis_tac[]) >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem store_copy_test[local]:
  !i n. i <= n /\ n < dimword (:256) ==>
    (bool_to_word (n2w i = n2w n : bytes32) = 0w <=> i < n)
Proof
  rpt strip_tac >>
  `i < dimword (:256)` by decide_tac >>
  simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD, bool_to_word_def] >>
  decide_tac
QED

Theorem store_copy_loop[local]:
  !ctx sa loc b k sbase st0 sj sth stj st2 stb ste st3 sb hdr body exit cv tv n
   old0 oldh u R.
    emit_inst JMP [Label hdr] [] st0 = ((),sj) /\
    new_block hdr sj = (old0,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    emit_inst JNZ [Var tv; Label exit; Label body] [] stj = ((),st2) /\
    new_block body st2 = (oldh,stb) /\
    emit_inst JMP [Label hdr] [] ste = ((),st3) /\
    new_block exit st3 = (u,sb) /\
    cs_extends sth stj /\ cs_extends stb ste /\
    cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
    n < dimword (:256) /\
    (!i. i < n ==> frag_exec ctx stb ste
      (\s. store_copy_frame sa loc b k sbase i s /\ eval_operand (Var cv) s = SOME (n2w i))
      (\s. store_copy_frame sa loc b k sbase (SUC i) s /\
           eval_operand (Var cv) s = SOME (n2w (SUC i))) R) ==>
    frag_exec ctx st0 sb
      (\s. store_copy_frame sa loc b k sbase 0 s /\ eval_operand (Var cv) s = SOME 0w)
      (\s. store_copy_frame sa loc b k sbase n s /\
           eval_operand (Var cv) s = SOME (n2w n) /\ eval_operand (Var tv) s = SOME 1w) R
Proof
  rpt gen_tac >> strip_tac >>
  (let
     val th = SPEC_ALL frag_exec_loop
     val vs = free_vars (concl th)
     fun v name = valOf (List.find (fn x => #1 (dest_var x) = name) vs)
   in
     irule (SRULE [] (BETA_RULE (INST
       [v "I" |-> ``\i s. store_copy_frame sa loc b k sbase i s /\
                     eval_operand (Var cv) s = SOME (n2w i)``,
        v "J" |-> ``\i s. store_copy_frame sa loc b k sbase i s /\
                     eval_operand (Var cv) s = SOME (n2w i) /\
                     eval_operand (Var tv) s =
                       SOME (bool_to_word (n2w i = n2w n : bytes32))``,
        v "N" |-> ``n:num``] th)))
   end) >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, jump_to_def] >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, jump_to_def] >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac
  >- (rpt strip_tac >> simp[] >> metis_tac[store_copy_test]) >>
  conj_tac
  >- (rpt strip_tac >> rename1 `i < n` >> irule frag_exec_conseq >>
      first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
      disch_then (irule_at Any) >> simp[]) >>
  rpt strip_tac >> irule (SRULE [] store_copy_header_frag) >> simp[] >> metis_tac[]
QED

(* The loop from buffer buf (value b) to slot (value k): the state at its
   exit is sbase after the word_count stores, in order, of the buffer's
   words, except for the loop's own variables and the position.  Stores do
   not change memory, so every word is read from sbase's memory.
   word_count < dimword (:256): the loop compares its counter against
   n2w word_count. *)
Theorem compile_store_copy_frag:
  !ctx loc src dst n sa u sb sbase b k R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
    n < dimword (:256) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s with <| vs_vars := sbase.vs_vars;
                     vs_current_bb := sbase.vs_current_bb;
                     vs_inst_idx := sbase.vs_inst_idx;
                     vs_prev_bb := sbase.vs_prev_bb |> =
           FOLDL (\t i. (if loc = LocStorage then sstore else tstore)
                          (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase) t)
                 sbase (COUNT_LIST n)) R
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all compile_store_copy_certificate >> strip_tac >>
  `!i. i < n ==> frag_exec ctx stb ste
      (\s. store_copy_frame sa loc b k sbase i s /\ eval_operand (Var cv) s = SOME (n2w i))
      (\s. store_copy_frame sa loc b k sbase (SUC i) s /\
           eval_operand (Var cv) s = SOME (n2w (SUC i))) R` by
    (rpt strip_tac >> irule store_copy_body_frag >> conj_tac
     >- (goal_assum (drule_at (Pat `emitted_insts _ _ = [_;_;_;_;_;_;_]`)) >>
         fs[ALL_DISTINCT, MEM] >> metis_tac[]) >> simp[]) >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT, MEM] >> metis_tac[]) >>
  drule_all store_copy_loop >> strip_tac >>
  irule frag_exec_conseq >>
  irule_at Any frag_exec_seq >>
  goal_assum (drule_at (Pat `frag_exec ctx s0 sb _ _ R`)) >>
  irule_at Any store_copy_init_frag >>
  goal_assum (drule_at (Pat `emitted_insts sa s0 = _`)) >>
  simp[store_copy_frame_def, store_copy_normalize_def, store_copy_prefix_def] >>
  fs[MEM] >> metis_tac[]
QED

(* Check the complete dependency closure, not just the final proof text. *)
val _ =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag compile_store_copy_frag)
  in
    if null axioms andalso List.all (fn s => s = "DISK_THM") oracles
    then print "compile_store_copy_frag: kernel dependency audit passed\n"
    else raise Fail "compile_store_copy_frag has oracle or axiom dependencies"
  end;
