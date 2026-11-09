(* Memory-safe execution of the typed-copy array increment and backedge. *)
Theory typedCopyArrayStepMemory
Ancestors
  typedCopyLoopPathMemory typedCopyArrayControlMemory typedCopyRuntimeStepMemory typedMemoryCopy
  stmtForRangeMemoryParts fragGasSeqMem fragGasPathMem fragExecMem
  exprLoweringProps venomExecSemantics venomInst venomState instMemFrontier
  words list rich_list finite_map arithmetic memSafeRun

Theorem typed_copy_array_step_path_mem:
  typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k s /\
  ci_mono sa a /\ not_fresh_at a ctr /\
  ~not_fresh_at sa ctr /\ ~not_fresh_at sa tmp /\ ctr <> tmp /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at a x) /\
  (!x. MEM x [lt; done; so; doff; sp; dp] ==> ~not_fresh_at a x) /\
  ALL_DISTINCT [ctr; so; doff; sp; dp] /\
  k < N /\ N < dimword (:256) /\ ~s.vs_halted /\
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
  (!u. typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k u /\
    eval_operand (Var sp) u = SOME (sw + n2w (k * type_memory_size stv)) /\
    eval_operand (Var dp) u = SOME (dw + n2w (k * type_memory_size dtv)) /\
    u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 4 /\ ~u.vs_halted ==>
    ?v. gas_path_mem ctx func u 0 (OK v) /\
      typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
        (type_memory_size dtv) u v /\
      val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) v.vs_memory /\
      v.vs_current_bb = end_lbl /\ v.vs_inst_idx = LENGTH pre /\ ~v.vs_halted) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 (SUC k) t /\
    t.vs_current_bb = header /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`bound` |-> `Lit (n2w N)`] typed_copy_runtime_array_step_path_mem) >>
  (impl_tac >- (simp[eval_operand_def] >> metis_tac[])) >> metis_tac[]
QED
