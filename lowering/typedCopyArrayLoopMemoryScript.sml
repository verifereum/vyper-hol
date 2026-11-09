(* Finite typed-array traversal, including the final exit test. *)
Theory typedCopyArrayLoopMemory
Ancestors typedCopyArrayStepMemory typedCopyLoopPathMemory typedMemoryCopy
  finiteIterationMemory fragGasPathMem venomExecSemantics venomState
  words list finite_map arithmetic

Theorem typed_copy_array_exit_path_mem[local]:
  typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 N s /\
  ci_mono sa a /\ not_fresh_at a ctr /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at a x) /\
  ~not_fresh_at a lt /\ ~not_fresh_at a done /\
  N < dimword (:256) /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME test /\
  test.bb_instructions =
    [mk_inst hid LT [Var ctr; Lit (n2w N)] [lt];
     mk_inst (hid+1) ISZERO [Var lt] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 N t /\
    t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `lookup_var ctr s = SOME (n2w N)` by gvs[typed_copy_index_inv_def] >>
  `N <= N` by simp[] >>
  drule_all typed_copy_loop_header_path_mem >> simp[] >> strip_tac >>
  qabbrev_tac `t = jump_to exit (update_var done 1w (update_var lt 0w s))` >>
  `typed_copy_state_frame a 0 0 s t` by
    (unabbrev_all_tac >> irule typed_copy_control_pair_frame >> simp[]) >>
  `t.vs_memory = s.vs_memory` by
    simp[Abbr `t`, jump_to_def, update_var_def] >>
  `typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 N t` by
    (irule typed_copy_index_inv_preserve >> goal_assum (drule_at Any) >>
     qexistsl_tac [`a`, `0`, `0`] >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[Abbr `t`, jump_to_def, update_var_def] >>
  metis_tac[]
QED

Theorem typed_copy_array_loop_path_mem:
  typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k s /\
  ci_mono sa a /\ not_fresh_at a ctr /\
  ~not_fresh_at sa ctr /\ ~not_fresh_at sa tmp /\ ctr <> tmp /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at a x) /\
  (!x. MEM x [lt; done; so; doff; sp; dp] ==> ~not_fresh_at a x) /\
  ALL_DISTINCT [ctr; so; doff; sp; dp] /\
  k <= N /\ N < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = header /\ s.vs_inst_idx = 0 /\
  (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  lookup_block header func.fn_blocks = SOME test /\
  test.bb_instructions =
    [mk_inst hid LT [Var ctr; Lit (n2w N)] [lt];
     mk_inst (hid+1) ISZERO [Var lt] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  lookup_block body_lbl func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst aid MUL [Var ctr; Lit (n2w (type_memory_size stv))] [so];
     mk_inst (aid+1) MUL [Var ctr; Lit (n2w (type_memory_size dtv))] [doff];
     mk_inst (aid+2) ADD [src; Var so] [sp];
     mk_inst (aid+3) ADD [dst; Var doff] [dp]] bb.bb_instructions /\
  lookup_block end_lbl func.fn_blocks = SOME back /\
  back.bb_instructions = pre ++
    [mk_inst bid ADD [Var ctr; Lit 1w] [tmp];
     mk_inst (bid+1) ASSIGN [Var tmp] [ctr];
     mk_inst (bid+2) JMP [Label header] []] /\
  (!j u. j < N /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 j u /\
    eval_operand (Var sp) u = SOME (sw + n2w (j * type_memory_size stv)) /\
    eval_operand (Var dp) u = SOME (dw + n2w (j * type_memory_size dtv)) /\
    u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 4 /\ ~u.vs_halted ==>
    ?v. gas_path_mem ctx func u 0 (OK v) /\
      typed_copy_state_frame a (w2n dw + j * type_memory_size dtv)
        (type_memory_size dtv) u v /\
      val_in_memory dtv (f j) (w2n dw + j * type_memory_size dtv) v.vs_memory /\
      v.vs_current_bb = end_lbl /\ v.vs_inst_idx = LENGTH pre /\ ~v.vs_halted) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 N t /\
    t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `Inv = \j u.
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 j u /\
    u.vs_current_bb = header /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    u.vs_alloca_next = s.vs_alloca_next` >>
  ho_match_mp_tac gas_path_mem_finite_iteration_exit >>
  conj_tac
  >- (simp[Abbr `Inv`] >> rpt strip_tac >>
      qpat_x_assum `!j u. _` (qspec_then `i` mp_tac) >>
      simp[] >> disch_tac >>
      drule_all typed_copy_array_step_path_mem >>
      strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- simp[Abbr `Inv`] >>
  conj_tac
  >- (simp[Abbr `Inv`] >> rpt strip_tac >>
      `~not_fresh_at a lt /\ ~not_fresh_at a done` by
        (conj_tac >> first_x_assum irule >> simp[]) >>
      `lookup_block u.vs_current_bb func.fn_blocks = SOME test` by simp[] >>
      drule_all typed_copy_array_exit_path_mem >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[Abbr `Inv`]
QED
