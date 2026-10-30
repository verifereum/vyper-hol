(*
 * Expression simulation: copying a value out of storage or transient
 * storage into memory is defined (#637)
 *
 * compile_ensure_in_memory, for a pointer into storage or transient
 * storage, allocates a buffer and copies the value's words into it: an
 * SLOAD or TLOAD and an MSTORE for one word, compile_word_copy_loop
 * otherwise.  Every instruction it emits runs with defined operands and
 * the loop's counter runs from 0 until it equals n2w word_count, so the
 * copy ends at the start of its exit block with the buffer's operand
 * defined and the variables handed out before it unchanged, whatever
 * storage holds.  Nothing is said about the bytes copied.
 *
 * TOP-LEVEL:
 *   compile_storage_copy_defined_frag  — the copy loop runs to its exit
 *   ensure_storage_memory_layout       — compile_ensure_in_memory's code
 *                                        for storage and transient storage
 *   ensure_storage_memory_defined_frag — that code runs with its result
 *                                        operand defined
 *   storage_copy_alloc_layout          — compile_alloc_buffer's code
 *
 * Helper: storage_copy_frame, the frame the loop invariant keeps, and the
 *   layout, step and loop lemmas for the copy's blocks.
 *)

Theory exprSimStorageCopy
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim exprSimUnwrap exprSimHyps exprSimWordBuiltins loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  context compileEnv moduleLoweringProps
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* Storage copies use slot offsets at the source and byte offsets at the
   destination.  Keep the location dispatch outside the loop proofs. *)
Theorem compile_storage_copy_layout[local]:
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
      value <- compile_ptr_load F loc src_off;
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

Theorem compile_storage_copy_appends[local]:
  !loc src dst n.
    (loc = LocStorage \/ loc = LocTransient) ==>
    cs_appends (compile_word_copy_loop src dst n loc LocMemory F)
Proof
  rpt strip_tac >>
  simp[compile_storage_copy_layout] >>
  gvs[compile_ptr_load_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_prims, cs_appends_emit_helpers]) >>
  rw[cs_appends_prims, cs_appends_emit_helpers]
QED

Theorem compile_storage_copy_extends[local]:
  !loc src dst n sa u sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u, sb) ==>
    cs_extends sa sb
Proof
  rpt gen_tac >> strip_tac >>
  `cs_appends (compile_word_copy_loop src dst n loc LocMemory F)` by
    (irule compile_storage_copy_appends >> simp[]) >>
  gvs[cs_appends_def] >> first_x_assum drule >> simp[]
QED

(* Expose compiler boundaries without expanding compile_state records. *)
Theorem storage_copy_bind_eq[local]:
  comp_bind m f s = (u,t) <=>
  ?v s1. m s = (v,s1) /\ f v s1 = (u,t)
Proof
  Cases_on `m s` >> simp[comp_bind_def]
QED

Theorem compile_storage_copy_boundaries[local]:
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
      compile_ptr_load F loc so s5 = (value,s6) /\
      emit_op MUL [Var cv; Lit 32w] s6 = (scaled,s7) /\
      emit_op ADD [dst; scaled] s7 = (dest,s8) /\
      emit_void MSTORE [dest; value] s8 = ((),s9) /\
      emit_op ADD [Var cv; Lit 1w] s9 = (next,s10) /\
      emit_inst ASSIGN [next] [cv] s10 = ((),ste) /\
      emit_inst JMP [Label hdr] [] ste = ((),st3) /\
      new_block exit st3 = (u,sb)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_storage_copy_layout, comp_ignore_bind_def,
      comp_bind_assoc, storage_copy_bind_eq]
QED

Theorem storage_copy_body_layout[local]:
  !loc src dst cv so value scaled dest next stb s1 s2 s3 s4 s5 s6 ste.
    (loc = LocStorage \/ loc = LocTransient) /\
    emit_op ADD [src; Var cv] stb = (so,s1) /\
    compile_ptr_load F loc so s1 = (value,s2) /\
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

Theorem storage_copy_header_layout[local]:
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

Theorem storage_copy_init_layout[local]:
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

Theorem storage_copy_prefix_freshness[local]:
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

Theorem compile_storage_copy_certificate[local]:
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
  drule_all compile_storage_copy_boundaries >> strip_tac >>
  drule storage_copy_header_layout >> strip_tac >> gnvs[] >>
  drule_all storage_copy_init_layout >> strip_tac >>
  drule_all storage_copy_prefix_freshness >> strip_tac >>
  rename1 `emit_inst ASSIGN [Lit 0w] [cv] s4 = ((),s0)` >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj)` >>
  rename1 `emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2)` >>
  rename1 `new_block loop_body st2 = (oldh,stb)` >>
  drule_all storage_copy_body_layout >> strip_tac >> gnvs[] >>
  rename1 `emit_inst ASSIGN [Var nv] [cv] s10 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `emit_op ADD [src; Var cv] stb = (Var sv,s5)` >>
  rename1 `compile_ptr_load F loc (Var sv) s5 = (Var vv,s6)` >>
  rename1 `emit_op MUL [Var cv; Lit 32w] s6 = (Var mv,s7)` >>
  rename1 `emit_op ADD [dst; Var mv] s7 = (Var dv,s8)` >>
  `cs_extends sa s0 /\ cs_extends sth stj /\ cs_extends stb ste` by
    (rpt conj_tac >> irule cs_extends_same_block >> gvs[same_blocks_def]) >>
  `cs_extends s0 sb` by
    (imp_res_tac cs_extends_emit_inst >> imp_res_tac cs_extends_new_block >>
     metis_tac[cs_extends_trans]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`compile_word_copy_loop _ _ _ _ _ _ _ = _`, `fresh_var _ = _`,
     `emit_inst ASSIGN [Lit _] _ _ = _`, `compile_ptr_load _ _ _ _ = _`,
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

(* Both slot spaces are total reads, independent of the stored contents. *)
Theorem storage_copy_load_step[local]:
  !opc op v id out s.
    (opc = SLOAD \/ opc = TLOAD) /\ eval_operand op s = SOME v ==>
    ?t. step_inst_base (mk_inst id opc [op] [out]) s = OK t /\
        (?w. lookup_var out t = SOME w) /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\
        t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  gvs[step_inst_base_def, exec_read1_def, mk_inst_def] >>
  simp[lookup_var_update_var, update_var_def] >> metis_tac[]
QED

(* An operand depends only on its register (if any) and the label map. *)
Theorem storage_copy_operand_frame[local]:
  !op ds s t w.
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> ~MEM x ds) /\
    (!x. ~MEM x ds ==> lookup_var x t = lookup_var x s) /\
    t.vs_labels = s.vs_labels ==>
    eval_operand op t = SOME w
Proof
  Cases >> simp[eval_operand_def] >> metis_tac[]
QED

(* The invariant deliberately ignores position and memory. *)
Definition storage_copy_frame_def:
  storage_copy_frame ds sbase s <=>
    (!x. ~MEM x ds ==> lookup_var x s = lookup_var x sbase) /\
    s.vs_labels = sbase.vs_labels
End

Theorem storage_copy_frame_jump[local,simp]:
  storage_copy_frame ds sbase (jump_to l s) = storage_copy_frame ds sbase s
Proof
  simp[storage_copy_frame_def, jump_to_def, lookup_var_def]
QED

Theorem storage_copy_frame_idx[local,simp]:
  storage_copy_frame ds sbase (s with vs_inst_idx := i) =
  storage_copy_frame ds sbase s
Proof
  simp[storage_copy_frame_def, lookup_var_def]
QED

Theorem storage_copy_frame_step[local]:
  storage_copy_frame ds sbase s /\
  (!x. ~MEM x ds ==> lookup_var x t = lookup_var x s) /\
  t.vs_labels = s.vs_labels ==>
  storage_copy_frame ds sbase t
Proof
  rw[storage_copy_frame_def] >> metis_tac[]
QED

Theorem storage_copy_eq_step[local]:
  !cv tv k n id s.
    eval_operand (Var cv) s = SOME k ==>
    ?t. step_inst_base (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) s = OK t /\
        eval_operand (Var tv) t = SOME (bool_to_word (k = n2w n)) /\
        (!x. x <> tv ==> lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  qexists_tac `update_var tv (bool_to_word (k = n2w n)) s` >> conj_tac
  >- (irule step_EQ >> simp[eval_operand_def]) >>
  simp[eval_operand_update_var, lookup_var_update_var, update_var_def]
QED

Theorem storage_copy_header_frag[local]:
  !ctx cv tv n sth stj ds sbase k R.
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    cv <> tv /\ MEM tv ds ==>
    frag_exec ctx sth stj
      (\s. eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s)
      (\s. eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s /\
           eval_operand (Var tv) s = SOME (bool_to_word (k = n2w n))) R
Proof
  rpt gen_tac >> strip_tac >>
  drule storage_copy_header_layout >> strip_tac >> gvs[] >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >>
  simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  drule storage_copy_eq_step >>
  disch_then (qspecl_then [`tv`, `n`, `sth.cs_next_id`] mp_tac) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  disj1_tac >> qexists_tac `t` >> simp[run_inst_seq_def] >>
  conj_tac
  >- gvs[mk_inst_def] >>
  conj_tac
  >- (gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[] >> irule storage_copy_frame_step >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem storage_copy_binary_step[local]:
  !opc op1 op2 a b id out s.
    (opc = ADD \/ opc = MUL) /\
    eval_operand op1 s = SOME a /\ eval_operand op2 s = SOME b ==>
    ?t. step_inst_base (mk_inst id opc [op1; op2] [out]) s = OK t /\
        eval_operand (Var out) t =
          SOME (if opc = ADD then a + b else a * b) /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >> gvs[]
  >- (qexists_tac `update_var out (a + b) s` >> conj_tac
      >- (irule step_ADD >> simp[]) >>
      simp[eval_operand_update_var, lookup_var_update_var, update_var_def]) >>
  qexists_tac `update_var out (a * b) s` >> conj_tac
  >- (irule step_MUL >> simp[]) >>
  simp[eval_operand_update_var, lookup_var_update_var, update_var_def]
QED

Theorem storage_copy_assign_step[local]:
  !op w id out s.
    eval_operand op s = SOME w ==>
    ?t. step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK t /\
        eval_operand (Var out) t = SOME w /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, mk_inst_def] >>
  simp[eval_operand_update_var, lookup_var_update_var, update_var_def]
QED

Theorem storage_copy_init_frag[local]:
  !ctx sa s0 cv ds sbase R.
    same_blocks sa s0 /\ isPREFIX sa.cs_current_insts s0.cs_current_insts /\
    emitted_insts sa s0 = [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]] /\
    MEM cv ds ==>
    frag_exec ctx sa s0 (\s. s = sbase)
      (\s. eval_operand (Var cv) s = SOME 0w /\ storage_copy_frame ds sbase s) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  qexists_tac `update_var cv 0w sbase` >>
  simp[run_inst_seq_def, step_inst_base_def, eval_operand_def,
       eval_operand_update_var, storage_copy_frame_def,
       lookup_var_update_var, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem storage_copy_store_step[local]:
  !op1 op2 a b id s.
    eval_operand op1 s = SOME a /\ eval_operand op2 s = SOME b ==>
    ?t. step_inst_base (mk_inst id MSTORE [op1; op2] []) s = OK t /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  rpt strip_tac >> qexists_tac `mstore (w2n a) b s` >> conj_tac
  >- (irule step_MSTORE >> simp[]) >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem storage_copy_source_run[local]:
  !opc src a cv sv vv id s k.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand (Var cv) s = SOME k /\
    ALL_DISTINCT [cv; sv; vv] /\
    (!x. src = Var x ==> ~MEM x [sv; vv]) ==>
    ?t. run_inst_seq
      [mk_inst id ADD [src; Var cv] [sv];
       mk_inst (id+1) opc [Var sv] [vv]] s = OK t /\
      (?w. eval_operand (Var vv) t = SOME w) /\
      eval_operand (Var cv) t = SOME k /\ eval_operand src t = SOME a /\
      (!x. ~MEM x [sv; vv] ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  `?s1. step_inst_base (mk_inst id ADD [src; Var cv] [sv]) s = OK s1 /\
        eval_operand (Var sv) s1 = SOME (a + k) /\
        (!x. x <> sv ==> lookup_var x s1 = lookup_var x s) /\
        s1.vs_current_bb = s.vs_current_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\
        s1.vs_halted = s.vs_halted /\ s1.vs_labels = s.vs_labels` by
    (irule (SRULE [] (Q.SPEC `ADD` storage_copy_binary_step)) >> simp[]) >>
  drule_at (Pat `eval_operand _ _ = SOME _`) storage_copy_load_step >>
  disch_then (qspecl_then [`opc`, `id+1`, `vv`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  qexists_tac `s2` >> simp[run_inst_seq_def] >>
  gvs[ALL_DISTINCT, eval_operand_def, lookup_var_update_var] >>
  irule storage_copy_operand_frame >>
  qexistsl [`[sv; vv]`, `s`] >> simp[] >> metis_tac[]
QED

Theorem storage_copy_destination_run[local]:
  !dst b cv vv mv dv id s k v.
    eval_operand dst s = SOME b /\ eval_operand (Var cv) s = SOME k /\
    eval_operand (Var vv) s = SOME v /\
    ALL_DISTINCT [cv; vv; mv; dv] /\
    (!x. dst = Var x ==> ~MEM x [mv; dv]) ==>
    ?t. run_inst_seq
      [mk_inst id MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+1) ADD [dst; Var mv] [dv];
       mk_inst (id+2) MSTORE [Var dv; Var vv] []] s = OK t /\
      (!x. ~MEM x [mv; dv] ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  `?s1. step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [mv]) s = OK s1 /\
        eval_operand (Var mv) s1 = SOME (k * 32w) /\
        (!x. x <> mv ==> lookup_var x s1 = lookup_var x s) /\
        s1.vs_current_bb = s.vs_current_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\
        s1.vs_halted = s.vs_halted /\ s1.vs_labels = s.vs_labels` by
    (irule (SRULE [] (Q.SPEC `MUL` storage_copy_binary_step)) >>
     simp[eval_operand_lit]) >>
  `eval_operand dst s1 = SOME b` by
    (irule storage_copy_operand_frame >> qexistsl [`[mv]`, `s`] >>
     gvs[] >> metis_tac[]) >>
  `?s2. step_inst_base (mk_inst (id+1) ADD [dst; Var mv] [dv]) s1 = OK s2 /\
        eval_operand (Var dv) s2 = SOME (b + k * 32w) /\
        (!x. x <> dv ==> lookup_var x s2 = lookup_var x s1) /\
        s2.vs_current_bb = s1.vs_current_bb /\
        s2.vs_inst_idx = s1.vs_inst_idx /\
        s2.vs_halted = s1.vs_halted /\ s2.vs_labels = s1.vs_labels` by
    (irule (SRULE [] (Q.SPEC `ADD` storage_copy_binary_step)) >> simp[]) >>
  `eval_operand (Var vv) s2 = SOME v` by
    (gvs[ALL_DISTINCT, eval_operand_def] >> metis_tac[]) >>
  `?t. step_inst_base (mk_inst (id+2) MSTORE [Var dv; Var vv] []) s2 = OK t /\
       (!x. lookup_var x t = lookup_var x s2) /\
       t.vs_current_bb = s2.vs_current_bb /\
       t.vs_inst_idx = s2.vs_inst_idx /\
       t.vs_halted = s2.vs_halted /\ t.vs_labels = s2.vs_labels` by
    (irule storage_copy_store_step >> simp[]) >>
  qexists_tac `t` >> simp[run_inst_seq_def] >> metis_tac[]
QED

Theorem storage_copy_increment_run[local]:
  !cv nv id s k.
    cv <> nv /\ eval_operand (Var cv) s = SOME k ==>
    ?t. run_inst_seq
      [mk_inst id ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+1) ASSIGN [Var nv] [cv]] s = OK t /\
      eval_operand (Var cv) t = SOME (k + 1w) /\
      (!x. ~MEM x [cv; nv] ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  `?s1. step_inst_base (mk_inst id ADD [Var cv; Lit 1w] [nv]) s = OK s1 /\
        eval_operand (Var nv) s1 = SOME (k + 1w) /\
        (!x. x <> nv ==> lookup_var x s1 = lookup_var x s) /\
        s1.vs_current_bb = s.vs_current_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\
        s1.vs_halted = s.vs_halted /\ s1.vs_labels = s.vs_labels` by
    (irule (SRULE [] (Q.SPEC `ADD` storage_copy_binary_step)) >>
     simp[eval_operand_lit]) >>
  drule storage_copy_assign_step >>
  disch_then (qspecl_then [`id+1`, `cv`] mp_tac) >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  qexists_tac `s2` >> simp[run_inst_seq_def] >> metis_tac[]
QED

Theorem storage_copy_body_run[local]:
  !opc src dst a b cv sv vv mv dv nv id s k.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    eval_operand (Var cv) s = SOME k /\
    ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
    (!x. src = Var x \/ dst = Var x ==>
         ~MEM x [cv; sv; vv; mv; dv; nv]) ==>
    ?t. run_inst_seq
      [mk_inst id ADD [src; Var cv] [sv];
       mk_inst (id+1) opc [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (id+3) ADD [dst; Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t /\
      eval_operand (Var cv) t = SOME (k + 1w) /\
      eval_operand src t = SOME a /\ eval_operand dst t = SOME b /\
      (!x. ~MEM x [cv; sv; vv; mv; dv; nv] ==>
           lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >> (
  `?s1. run_inst_seq [mk_inst id ADD [src; Var cv] [sv];
          mk_inst (id+1) opc [Var sv] [vv]] s = OK s1 /\
        (?w. eval_operand (Var vv) s1 = SOME w) /\
        eval_operand (Var cv) s1 = SOME k /\ eval_operand src s1 = SOME a /\
        (!x. ~MEM x [sv; vv] ==> lookup_var x s1 = lookup_var x s) /\
        s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx /\
        s1.vs_halted = s.vs_halted /\ s1.vs_labels = s.vs_labels` by
    (irule storage_copy_source_run >> gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand dst s1 = SOME b` by
    (irule storage_copy_operand_frame >> qexistsl [`[sv; vv]`, `s`] >>
     gvs[] >> metis_tac[]) >>
  `?s2. run_inst_seq [mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
          mk_inst ((id+2)+1) ADD [dst; Var mv] [dv];
          mk_inst ((id+2)+2) MSTORE [Var dv; Var vv] []] s1 = OK s2 /\
        (!x. ~MEM x [mv; dv] ==> lookup_var x s2 = lookup_var x s1) /\
        s2.vs_current_bb = s1.vs_current_bb /\ s2.vs_inst_idx = s1.vs_inst_idx /\
        s2.vs_halted = s1.vs_halted /\ s2.vs_labels = s1.vs_labels` by
    (irule storage_copy_destination_run >> gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand (Var cv) s2 = SOME k` by
    (gvs[eval_operand_def, ALL_DISTINCT] >> metis_tac[]) >>
  drule_at (Pat `eval_operand _ _ = SOME _`) storage_copy_increment_run >>
  disch_then (qspecl_then [`nv`, `id+5`] mp_tac) >>
  (impl_tac >- gvs[ALL_DISTINCT]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `!x. ~MEM x [cv; sv; vv; mv; dv; nv] ==>
        lookup_var x t = lookup_var x s` by (gvs[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (qpat_x_assum `run_inst_seq _ s = OK s1`
        (assume_tac o SRULE [] o MATCH_MP run_inst_seq_append) >>
      qpat_x_assum `run_inst_seq _ s1 = OK s2`
        (assume_tac o SRULE [arithmeticTheory.ADD_ASSOC] o MATCH_MP run_inst_seq_append) >>
      gvs[arithmeticTheory.ADD_ASSOC]) >>
  conj_tac >> irule storage_copy_operand_frame >>
  qexistsl [`[cv; sv; vv; mv; dv; nv]`, `s`] >> gvs[] >> metis_tac[])
QED

Theorem storage_copy_body_frag[local]:
  !ctx loc src dst cv sv vv mv dv nv stb ste ds sbase a b k R.
    (loc = LocStorage \/ loc = LocTransient) /\
    same_blocks stb ste /\ isPREFIX stb.cs_current_insts ste.cs_current_insts /\
    emitted_insts stb ste =
      [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
       mk_inst (stb.cs_next_id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
       mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]] /\
    ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
    (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv; sv; vv; mv; dv; nv]) /\
    (!x. MEM x [cv; sv; vv; mv; dv; nv] ==> MEM x ds) ==>
    frag_exec ctx stb ste
      (\s. eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
           eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s)
      (\s. eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
           eval_operand (Var cv) s = SOME (k+1w) /\ storage_copy_frame ds sbase s) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  `?t. run_inst_seq
      [mk_inst stb.cs_next_id ADD [src; Var cv] [sv];
       mk_inst (stb.cs_next_id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (stb.cs_next_id+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (stb.cs_next_id+3) ADD [dst; Var mv] [dv];
       mk_inst (stb.cs_next_id+4) MSTORE [Var dv; Var vv] [];
       mk_inst (stb.cs_next_id+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (stb.cs_next_id+6) ASSIGN [Var nv] [cv]] s = OK t /\
      eval_operand (Var cv) t = SOME (k+1w) /\
      eval_operand src t = SOME a /\ eval_operand dst t = SOME b /\
      (!x. ~MEM x [cv; sv; vv; mv; dv; nv] ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels` by
    (irule storage_copy_body_run >> simp[] >> metis_tac[]) >>
  disj1_tac >> qexists_tac `t` >>
  gvs[GSYM mk_inst_def, control_moves_keep_vars] >>
  irule storage_copy_frame_step >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem storage_copy_body_frame_frag[local]:
  !ctx stb ste src dst a b cv ds sbase k R.
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b /\
    (!x. src = Var x \/ dst = Var x ==> ~MEM x ds) /\
    frag_exec ctx stb ste
      (\s. eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
           eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s)
      (\s. eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
           eval_operand (Var cv) s = SOME (k+1w) /\ storage_copy_frame ds sbase s) R ==>
    frag_exec ctx stb ste
      (\s. eval_operand (Var cv) s = SOME k /\ storage_copy_frame ds sbase s)
      (\s. eval_operand (Var cv) s = SOME (k+1w) /\ storage_copy_frame ds sbase s) R
Proof
  rpt gen_tac >> strip_tac >> irule frag_exec_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  irule storage_copy_operand_frame >> qexistsl [`ds`, `sbase`] >>
  gvs[storage_copy_frame_def] >> metis_tac[]
QED

Theorem storage_copy_loop[local]:
  !ctx st0 st1 sth stj st2 stb ste st3 stx hdr loop_body exit cv tv n
   x0 x1 x2 x3 x4 x5 ds sbase R.
    emit_inst JMP [Label hdr] [] st0 = (x0,st1) /\
    new_block hdr st1 = (x1,sth) /\
    emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj) /\
    emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = (x2,st2) /\
    new_block loop_body st2 = (x3,stb) /\
    emit_inst JMP [Label hdr] [] ste = (x4,st3) /\
    new_block exit st3 = (x5,stx) /\
    cs_extends stb ste /\ cv <> tv /\ MEM tv ds /\
    (!k. k < w2n (n2w n : bytes32) ==>
      frag_exec ctx stb ste
        (\s. eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s)
        (\s. eval_operand (Var cv) s = SOME (n2w (k+1)) /\ storage_copy_frame ds sbase s) R) ==>
    frag_exec ctx st0 stx
      (\s. eval_operand (Var cv) s = SOME 0w /\ storage_copy_frame ds sbase s)
      (\s. eval_operand (Var cv) s = SOME (n2w n) /\ storage_copy_frame ds sbase s /\
           eval_operand (Var tv) s = SOME 1w) R
Proof
  rpt gen_tac >> strip_tac >>
  (let
     val th = SPEC_ALL frag_exec_loop
     val vs = free_vars (concl th)
     fun v name = valOf (List.find (fn x => #1 (dest_var x) = name) vs)
   in
     irule (SRULE [wordsTheory.n2w_w2n] (BETA_RULE (INST
       [v "I" |-> ``\(k:num) (s:venom_state).
          eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s``,
        v "J" |-> ``\(k:num) (s:venom_state).
          eval_operand (Var cv) s = SOME (n2w k) /\ storage_copy_frame ds sbase s /\
          eval_operand (Var tv) s = SOME (bool_to_word (k = w2n (n2w n : bytes32)))``,
        v "N" |-> ``w2n (n2w n : bytes32)``] th)))
   end) >>
  Cases_on `x0` >> Cases_on `x2` >> Cases_on `x4` >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac
  >- (rpt strip_tac >> qexists_tac `bool_to_word (k = n MOD dimword (:256))` >>
      simp[bool_to_word_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> irule frag_exec_conseq >>
      first_x_assum (qspec_then `k` mp_tac) >>
      simp[wordsTheory.w2n_n2w, arithmeticTheory.ADD1] >>
      disch_then (irule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      irule frag_exec_conseq >> irule_at Any storage_copy_header_frag >>
      goal_assum (drule_at (Pat `emit_op EQ _ _ = _`)) >>
      qexistsl_tac [`sbase`, `n2w k : bytes32`, `ds`, `R`] >> simp[] >>
      rpt strip_tac >> AP_TERM_TAC >>
      `k < dimword (:256)` by
        (qspec_then `n2w n : bytes32`
           (assume_tac o PURE_REWRITE_RULE [wordsTheory.w2n_n2w]) wordsTheory.w2n_lt >>
         decide_tac) >>
      simp[arithmeticTheory.LESS_MOD]) >>
  irule cs_extends_same_block >>
  drule storage_copy_header_layout >> simp[same_blocks_def]
QED

Theorem compile_storage_copy_defined_frag:
  !ctx loc src dst n sa u sb sbase a b R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all compile_storage_copy_certificate >> strip_tac >>
  rename1 `emit_op EQ [Var cv; Lit (n2w n)] sth = (Var tv,stj)` >>
  rename1 `emitted_insts sa s0 = [mk_inst _ ASSIGN _ _]` >>
  rename1 `emitted_insts stb ste = [mk_inst _ ADD _ [sv]; _; _; _; _; _; _]` >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT ds` >>
  `MEM cv ds /\ MEM tv ds /\ cv <> tv /\
   (!x. src = Var x \/ dst = Var x ==> ~MEM x ds)` by
    (gvs[Abbr `ds`, ALL_DISTINCT] >> metis_tac[]) >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s. eval_operand (Var cv) s = SOME 0w /\
                    storage_copy_frame ds sbase s`, `s0`] >> simp[] >>
  conj_tac >- (irule storage_copy_init_frag >> simp[]) >>
  irule frag_exec_conseq >>
  qexistsl_tac
    [`\s. eval_operand (Var cv) s = SOME 0w /\ storage_copy_frame ds sbase s`,
     `\s. eval_operand (Var cv) s = SOME (n2w n) /\ storage_copy_frame ds sbase s /\
           eval_operand (Var tv) s = SOME 1w`, `R`] >> simp[] >>
  conj_tac >- (rw[storage_copy_frame_def] >> metis_tac[]) >>
  irule storage_copy_loop >> simp[] >>
  goal_assum (drule_at (Pat `emit_op EQ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  rpt (goal_assum (drule_at (Pat `new_block _ _ = _`))) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> qx_gen_tac `i` >> strip_tac >>
  irule (SRULE [wordsTheory.word_add_n2w]
    (Q.INST [`k` |-> `n2w (i:num) : bytes32`] (SPEC_ALL storage_copy_body_frame_frag))) >>
  qexistsl_tac [`a`, `b`, `dst`, `src`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule (SRULE [wordsTheory.word_add_n2w]
    (Q.INST [`k` |-> `n2w (i:num) : bytes32`] (SPEC_ALL storage_copy_body_frag))) >>
  reverse conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `emitted_insts _ _ = _`)) >>
  gvs[Abbr `ds`, ALL_DISTINCT] >> metis_tac[]
QED

Theorem storage_copy_alloc_layout:
  !n sa buf sb.
    compile_alloc_buffer n sa = (buf,sb) ==>
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]] /\
    buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
    sb.cs_next_var = sa.cs_next_var + 1 /\
    (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x)
Proof
  rpt strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      emitted_insts_def, same_blocks_def, not_fresh_at_def] >>
  simp[DROP_APPEND1]
QED

Theorem storage_copy_alloc_frag[local]:
  !ctx n sa buf sb sbase R.
    compile_alloc_buffer n sa = (buf,sb) ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand buf.buf_operand s = SOME w) /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  rpt strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[] >>
  qspecl_then [`sa.cs_next_id`, `n2w n`, `STRING #"%" (toString sa.cs_next_var)`, `sbase`]
    strip_assume_tac loweringHaltTheory.step_alloca_frame >>
  rename1 `step_inst_base _ sbase = OK t` >>
  disj1_tac >> qexists_tac `t` >>
  gvs[run_inst_seq_def, GSYM mk_inst_def, control_moves_keep_vars,
      eval_operand_def] >> metis_tac[]
QED

Theorem storage_copy_word_layout[local]:
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

Theorem storage_copy_word_frag[local]:
  !ctx opc src dst sa u sb sbase a b R.
    (opc = SLOAD \/ opc = TLOAD) /\
    do v <- emit_op opc [src]; emit_void MSTORE [dst; v] od sa = (u,sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\ eval_operand dst sbase = SOME b ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule storage_copy_word_layout >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >> simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  mp_tac (Q.SPECL [`opc`, `src`, `a`] storage_copy_load_step) >>
  simp[] >>
  disch_then (qspecl_then [`sa.cs_next_id`, `STRING #"%" (toString sa.cs_next_var)`, `sbase`]
    mp_tac) >> simp[] >> strip_tac >>
  rename1 `step_inst_base _ sbase = OK t` >>
  `eval_operand dst t = SOME b` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `?w. eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) t = SOME w` by
    simp[eval_operand_def] >>
  rename1 `eval_operand (Var _) t = SOME loaded` >>
  mp_tac (Q.SPECL [`dst`, `Var (STRING #"%" (toString sa.cs_next_var))`,
    `b`, `loaded`] storage_copy_store_step) >>
  disch_then (qspecl_then [`sa.cs_next_id + 1`, `t`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `step_inst_base _ t = OK t1` >>
  disj1_tac >> qexists_tac `t1` >>
  gvs[run_inst_seq_def, GSYM mk_inst_def, control_moves_keep_vars] >> metis_tac[]
QED

Theorem ensure_storage_memory_layout:
  !loc src nb n ctor.
    (loc = LocStorage \/ loc = LocTransient) ==>
    compile_ensure_in_memory src loc nb n ctor =
    do buf <- compile_alloc_buffer nb;
       (if n = 1 then
          do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
             emit_void MSTORE [buf.buf_operand; v] od
        else do compile_word_copy_loop src buf.buf_operand n loc LocMemory F;
                return () od);
       return buf.buf_operand
    od
Proof
  rpt strip_tac >>
  gvs[compile_ensure_in_memory_def, compile_storage_to_memory_def,
      compile_transient_to_memory_def, FUN_EQ_THM, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ensure_storage_memory_defined_frag:
  !ctx loc src nb n ctor sa op sb sbase a R.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_ensure_in_memory src loc nb n ctor sa = (op,sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a ==>
    frag_exec ctx sa sb (\s. s = sbase)
      (\s. (?w. eval_operand op s = SOME w) /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ = _` mp_tac >>
  drule ensure_storage_memory_layout >>
  disch_then (qspecl_then [`src`, `nb`, `n`, `ctor`] SUBST1_TAC) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gnvs[] >> rename1 `compile_alloc_buffer nb sa = (buf,sm)` >>
  rename1 `_ sm = (_,sb)` >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `cs_extends sa sm` by
    (gvs[cs_extends_def, same_blocks_def] >> qexists_tac `[]` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    simp[not_fresh_at_def] >>
  `frag_exec ctx sa sm (\s. s = sbase)
    (\s. (?w. eval_operand buf.buf_operand s = SOME w) /\
         (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
         s.vs_labels = sbase.vs_labels) R` by
    (irule storage_copy_alloc_frag >> qexists_tac `nb` >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> simp[] >>
  reverse conj_tac
  >- (Cases_on `n = 1` >> gnvs[]
      >- (drule storage_copy_word_layout >>
          simp[cs_extends_def, same_blocks_def] >> strip_tac >>
          qexists_tac `[]` >> simp[]) >>
      gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[] >> irule compile_storage_copy_extends >>
      goal_assum (drule_at Any) >> simp[]) >>
  qx_gen_tac `t` >> strip_tac >>
  `eval_operand src t = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `frag_exec ctx sm sb (\s. s = t)
    (\s. (!x. not_fresh_at sm x ==> lookup_var x s = lookup_var x t) /\
         s.vs_labels = t.vs_labels) R` by
    (qpat_x_assum `t.vs_labels = _` kall_tac >>
     Cases_on `n = 1` >> gnvs[]
     >- (irule storage_copy_word_frag >>
         goal_assum (drule_at (Pat `comp_bind _ _ _ = _`)) >>
         simp[] >> metis_tac[]) >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> irule compile_storage_copy_defined_frag >>
     goal_assum (drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  drule frag_exec_weaken >> disch_then irule >> simp[] >>
  rpt strip_tac >> simp[] >>
  Cases_on `buf.buf_operand` >> gvs[eval_operand_def] >> metis_tac[]
QED
