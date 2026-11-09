(* Finite traversal of the generated typed-copy condition block. *)
Theory typedCopyLoopPathMemory
Ancestors
  stmtForRangeMemoryParts fragGasSeqMem fragGasPathMem fragExecMem
  finiteIterationMemory typedCopyRuntimeHeaderMemory
  exprLoweringProps venomExecSemantics venomInst venomState instMemFrontier
  words list rich_list finite_map arithmetic memSafeRun

Theorem typed_copy_loop_header_path_mem:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id LT [Var ctr; Lit (n2w N)] [lt];
     mk_inst (id+1) ISZERO [Var lt] [done];
     mk_inst (id+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  lookup_var ctr s = SOME (n2w k) /\ k <= N /\ N < dimword (:256) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to (if k < N then body_lbl else exit)
      (update_var done (bool_to_word (~(k < N)))
        (update_var lt (bool_to_word (k < N)) s))))
Proof
  strip_tac >> irule typed_copy_runtime_loop_header_path_mem >>
  simp[] >> qexistsl_tac [`Lit (n2w N)`, `ctr`, `id`] >>
  simp[eval_operand_def]
QED
