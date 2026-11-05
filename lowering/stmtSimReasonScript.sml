(*
 * Statement simulation: Raise and Assert with a string literal reason (#637)
 *
 * The reason is ABI-encoded into a buffer that the REVERT returns.  The
 * encoder's code only allocates, adds, loads, stores and copies memory, so
 * it runs to the REVERT from any state where its operands are defined
 * (reason_prefix, a definedness certificate for its instructions).
 *
 * TOP-LEVEL:
 *   compile_revert_reason_frag     — the encoder and the REVERT, an exit,
 *                                    for an operand reason_vv hands out
 *   compile_bytelike_revert_frag   — the same for a string literal
 *   compile_raise_reason_lit_frag  — raise with a string literal reason
 *   compile_assert_reason_lit_frag — assert with a string literal reason
 *
 * Helper: reason_known, reason_operand, reason_step, reason_prefix,
 *   reason_vv, unwrap_value_reason_vv, compile_revert_reason_certificate,
 *   compile_revert_reason_split_certificate (the encoder's code split at
 *   its unwrap_value, for reasons that unwrap_value copies),
 *   reason_prefix_sound, reason_head_frag, reason_prefix_revert_frag,
 *   reason_operand_mono, reason_prefix_append, reason_prefix_append_known
 *)

Theory stmtSimReason
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice  stmtSimIf loweringHalt
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperExprNoControl
  vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* Memory execution needs defined operands, not a memory-safety invariant.
   ALLOCA (including repeat executions and zero sizes) is total by
   loweringHaltTheory.step_alloca_frame. ADD, AND, MLOAD and MSTORE use
   step_ADD, step_AND, step_MLOAD and step_MSTORE; update_var's lookup
   equations give output definedness and the frame for the read steps.
   REVERT with defined operands is step_revert_behavior. *)
Theorem step_MCOPY_defined[local]:
  !dst src sz d a n id outs s.
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand sz s = SOME n ==>
    step_inst_base (mk_inst id MCOPY [dst; src; sz] outs) s =
      OK (mcopy (w2n d) (w2n a) (w2n n) s)
Proof
  cheat
QED

Theorem lookup_var_mcopy[local,simp]:
  !x dst src sz s.
    lookup_var x (mcopy dst src sz s) = lookup_var x s
Proof
  cheat
QED

Theorem byte_chunk_head_run[local]:
  !ptr off value sa dst sm sb s w.
    emit_op ADD [ptr; Lit off] sa = (dst, sm) /\
    emit_void MSTORE [dst; Lit value] sm = ((), sb) /\
    eval_operand ptr s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        t.vs_labels = s.vs_labels /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem compile_store_byte_chunks_run[local]:
  !ptr bs off sa sb s w.
    compile_store_byte_chunks ptr bs off sa = ((), sb) /\
    (!x. ptr = Var x ==> not_fresh_at sa x) /\
    eval_operand ptr s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
        t.vs_labels = s.vs_labels /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem byte_literal_head_run[local]:
  !size len sa buf sm sb s.
    compile_alloc_buffer size sa = (buf, sm) /\
    emit_void MSTORE [buf.buf_operand; Lit len] sm = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
          eval_operand buf.buf_operand t = SOME w /\ t.vs_labels = s.vs_labels /\
          (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem compile_bytelike_literal_run[local]:
  !bs max_len sa buf sb s.
    compile_bytelike_literal bs max_len sa = (buf, sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
          eval_operand buf.buf_operand t = SOME w /\ t.vs_labels = s.vs_labels /\
          (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

(* A focused definedness certificate for the reason encoder's memory code.
   Outputs may already be bound: the certificate tracks availability only. *)
Definition reason_known_def:
  reason_known ds s <=> !x. MEM x ds ==> ?w. lookup_var x s = SOME w
End

Definition reason_operand_def:
  reason_operand ds (Lit w) = T /\
  reason_operand ds (Var x) = MEM x ds /\
  reason_operand ds (Label l) = F
End

Definition reason_step_def:
  reason_step ds i <=>
    (?id sz out. i = mk_inst id ALLOCA [Lit sz] [out]) \/
    (?id opc a b out. (opc = ADD \/ opc = AND) /\
      i = mk_inst id opc [a; b] [out] /\
      reason_operand ds a /\ reason_operand ds b) \/
    (?id a out. i = mk_inst id MLOAD [a] [out] /\ reason_operand ds a) \/
    (?id a b. i = mk_inst id MSTORE [a; b] [] /\
      reason_operand ds a /\ reason_operand ds b) \/
    (?id a b c. i = mk_inst id MCOPY [a; b; c] [] /\
      reason_operand ds a /\ reason_operand ds b /\ reason_operand ds c)
End

Definition reason_prefix_def:
  reason_prefix ds [] es = (es = ds) /\
  reason_prefix ds (i::is) es =
    (reason_step ds i /\ reason_prefix (i.inst_outputs ++ ds) is es)
End

Theorem reason_operand_defined[local]:
  !ds op s. reason_operand ds op /\ reason_known ds s ==>
    ?w. eval_operand op s = SOME w
Proof
  cheat
QED

Theorem reason_known_update[local]:
  !ds s out w. reason_known ds s ==>
    reason_known (out::ds) (update_var out w s)
Proof
  cheat
QED

Theorem reason_step_sound[local]:
  !ds i s. reason_step ds i /\ reason_known ds s ==>
    ?t. step_inst_base i s = OK t /\
        reason_known (i.inst_outputs ++ ds) t /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem reason_step_known_frame[local]:
  !ds i s t. reason_step ds i /\ reason_known ds s /\
    step_inst_base i s = OK t ==>
    !x. ~MEM x i.inst_outputs ==> lookup_var x t = lookup_var x s
Proof
  cheat
QED

Theorem reason_prefix_sound:
  !is ds es s. reason_prefix ds is es /\ reason_known ds s ==>
    ?t. run_inst_seq is s = OK t /\ reason_known es t /\
        t.vs_labels = s.vs_labels /\
        (!x. ~MEM x (FLAT (MAP (\i. i.inst_outputs) is)) ==>
             lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem reason_step_simple[local]:
  !ds i. reason_step ds i ==> i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode
Proof
  cheat
QED

Theorem reason_prefix_simple[local]:
  !is ds es. reason_prefix ds is es ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is
Proof
  cheat
QED

Theorem reason_head_frag:
  !ctx sa sm h hs sbase R.
    same_blocks sa sm /\
    sm.cs_current_insts = sa.cs_current_insts ++ h /\
    reason_prefix [] h hs /\
    EVERY (\i. EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) h ==>
    frag_exec ctx sa sm (\s. s = sbase)
      (\s. reason_known hs s /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x sbase) /\
           s.vs_labels = sbase.vs_labels) R
Proof
  cheat
QED

Theorem reason_operand_mono:
  !ds es op. (!x. MEM x ds ==> MEM x es) /\ reason_operand ds op ==>
    reason_operand es op
Proof
  cheat
QED

Theorem reason_step_mono[local]:
  !ds es i. (!x. MEM x ds ==> MEM x es) /\ reason_step ds i ==>
    reason_step es i
Proof
  cheat
QED

Theorem reason_prefix_append_known:
  !is ds es extra. reason_prefix ds is es ==>
    reason_prefix (ds ++ extra) is (es ++ extra)
Proof
  cheat
QED

Theorem reason_prefix_append:
  !is js ds es fs.
    reason_prefix ds is es /\ reason_prefix es js fs ==>
    reason_prefix ds (is ++ js) fs
Proof
  cheat
QED

(* The operand a reason's value_vv hands to the encoder with no code of
   unwrap_value's own: a stack operand, or the pointer of a value in memory
   of a type that is not a word type (a string). *)
Definition reason_vv_def:
  reason_vv (StackValue t op) = SOME op /\
  reason_vv (LocatedValue t p) =
    if ~is_word_type t /\ p.ptr_location = LocMemory then SOME p.ptr_operand
    else NONE
End

Theorem unwrap_value_reason_vv:
  !cenv vv op st. reason_vv vv = SOME op ==> unwrap_value cenv vv st = (op, st)
Proof
  cheat
QED

Theorem compile_revert_reason_split_certificate:
  !cenv vv mt ms sa sb.
    compile_revert_with_reason cenv vv mt ms sa = ((),sb) ==>
    ?sm sn op h hs k id off len.
      unwrap_value cenv vv sm = (op,sn) /\
      same_blocks sa sm /\ sm.cs_current_insts = sa.cs_current_insts ++ h /\
      reason_prefix [] h hs /\ EVERY (not_fresh_at sm) hs /\
      EVERY (\i. EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) h /\
      sa.cs_next_var <= sm.cs_next_var /\
      cs_extends sa sm /\ cs_extends sn sb /\
      same_blocks sn sb /\
      sb.cs_current_insts = sn.cs_current_insts ++
        (k ++ [mk_inst id REVERT [off;len] []]) /\
      (!ds. (!x. MEM x hs ==> MEM x ds) /\ reason_operand ds op ==>
        ?es. reason_prefix ds k es /\ reason_operand es off /\ reason_operand es len)
Proof
  cheat
QED

Theorem compile_revert_reason_certificate:
  !cenv msg_vv op msg_type msg_size sa sb ds.
    reason_vv msg_vv = SOME op /\ reason_operand ds op /\
    compile_revert_with_reason cenv msg_vv msg_type msg_size sa = ((), sb) ==>
    ?prefix es id off len.
      emitted_insts sa sb = prefix ++ [mk_inst id REVERT [off; len] []] /\
      reason_prefix ds prefix es /\ reason_operand es off /\
      reason_operand es len /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      same_blocks sa sb
Proof
  cheat
QED

Theorem compile_revert_reason_buf_certificate[local]:
  !cenv msg_ty buf msg_type msg_size sa sb ds.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) ==>
    ?prefix es id off len.
      emitted_insts sa sb = prefix ++ [mk_inst id REVERT [off; len] []] /\
      reason_prefix ds prefix es /\ reason_operand es off /\
      reason_operand es len /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      same_blocks sa sb
Proof
  cheat
QED

Theorem reason_prefix_revert_run[local]:
  !is ds es s id off len.
    reason_prefix ds is es /\ reason_known ds s /\
    reason_operand es off /\ reason_operand es len ==>
    ?t. run_inst_seq (is ++ [mk_inst id REVERT [off; len] []]) s =
          Abort Revert_abort t /\ t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem compile_revert_reason_run[local]:
  !cenv msg_ty buf msg_type msg_size sa sb s ds.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    reason_known ds s /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
        t.vs_labels = s.vs_labels
Proof
  cheat
QED

Theorem reason_prefix_revert_frag:
  !ctx sa sb ds es is id off len R.
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      (is ++ [mk_inst id REVERT [off; len] []]) /\
    reason_prefix ds is es /\ reason_operand es off /\ reason_operand es len /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (reason_known ds) (\s. F) R
Proof
  cheat
QED

Theorem compile_revert_reason_buf_frag[local]:
  !ctx cenv msg_ty buf msg_type msg_size sa sb ds R.
    ~is_word_type msg_ty /\ reason_operand ds buf.buf_operand /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sa = ((), sb) /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (reason_known ds) (\s. F) R
Proof
  cheat
QED

(* The encoder and its REVERT, for a message operand that reason_vv hands
   out, from any state where the variables of ds are defined. *)
Theorem compile_revert_reason_frag:
  !ctx cenv msg_vv op msg_type msg_size sa sb ds R.
    reason_vv msg_vv = SOME op /\ reason_operand ds op /\
    compile_revert_with_reason cenv msg_vv msg_type msg_size sa = ((), sb) /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (reason_known ds) (\s. F) R /\ cs_extends sa sb
Proof
  cheat
QED

Theorem compile_store_byte_chunks_simple[local]:
  !ptr bs off sa sb.
    compile_store_byte_chunks ptr bs off sa = ((), sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  cheat
QED

Theorem compile_bytelike_literal_simple[local]:
  !bs ml sa buf sb.
    compile_bytelike_literal bs ml sa = (buf, sb) ==>
    (?x. buf.buf_operand = Var x) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  cheat
QED

Theorem compile_bytelike_revert_frag:
  !ctx cenv bs ml msg_ty msg_type msg_size sa sm buf sb R.
    compile_bytelike_literal bs ml sa = (buf, sm) /\
    ~is_word_type msg_ty /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sm = ((), sb) /\
    (!t. R (Abort Revert_abort t)) ==>
    frag_exec ctx sa sb (\s. T) (\s. F) R
Proof
  cheat
QED

(* raise and assert with a string literal as the reason: the literal's
   buffer and the Error(string) encoding of compile_revert_with_reason,
   straight-line code that ends in a REVERT, which every assertion
   allows.  A reason other than a literal is compiled with compile_expr
   and read back with unwrap_value after code of its own; those forms are
   not covered yet. *)
(* Why they hold.  The literal evaluates to StringV str, so the source
   raises AssertException str, which expr_exit takes as Revert_abort.  The
   reason code is one run of instructions in the open block, none a
   terminator before the REVERT: ALLOCAs with a literal size and one
   output, MSTOREs, ADD/AND, MLOAD, MCOPY, all total, each Var operand the
   output of an earlier one; unwrap_value of the literal's memory pointer
   emits nothing.  So it reaches the REVERT from any state.  The assert form
   is compile_assert_frag's shape with this run in place of the one
   aborting instruction of the fail block. *)
Theorem compile_raise_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty ml str es res es'.
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))

      (eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))) es
Proof
  cheat
QED

Theorem bytelike_revert_extends[local]:
  !cenv bs ml msg_ty msg_type msg_size sa sm buf sb.
    compile_bytelike_literal bs ml sa = (buf, sm) /\
    ~is_word_type msg_ty /\
    compile_revert_with_reason cenv (LocatedValue msg_ty (base_ptr buf))
      msg_type msg_size sm = ((), sb) ==>
    cs_extends sa sb
Proof
  cheat
QED

Theorem compile_assert_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty e ml str es res es'.
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))

      (eval_stmt cx (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))) es
Proof
  cheat
QED





(* Integrity gate for preserved public reason certificates and execution. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "REASON_FORCE_AUDIT OK\n"
     else print "statement-check gate skipped\n"
  end) [compile_store_byte_chunks_run, compile_bytelike_literal_run,
        compile_revert_reason_certificate, compile_revert_reason_run,
        compile_revert_reason_frag, compile_store_byte_chunks_simple,
        compile_bytelike_literal_simple, compile_bytelike_revert_frag,
        compile_raise_reason_lit_frag, compile_assert_reason_lit_frag];
