(* Return-boundary diagnostics, not counterexamples to the frozen seam. *)
Theory bodyIntCallReturnProbe
Ancestors
  compileVyper compileEnv exprLowering exprLoweringProps intCallCallee
  stmtLowering context vyperCompiler moduleLowering words

(* A successful memory-return body can require only one fresh word of
   allocation credit.  No DALLOCA forces the independent FMP margin. *)
Theorem empty_string_return_allocation_probe[local]:
  let ty = BaseT (StringT 0) in
  let body = [Return (SOME (Literal ty (StringL "")))] in
  let tops = [FunctionDecl Internal Pure F F "callee" [] [] ty body] in
  let ce = build_compile_env tops Internal Pure "callee" [] ty body F in
  let st = SND (compile_internal_function ce [] T F 0 F F F 0 body
      (SOME ty) (initial_compile_state "callee")) in
  let insts = st.cs_current_insts ++
      FLAT (MAP (\b. b.bb_instructions) st.cs_blocks) in
    MAP alloca_lit_size (FILTER (\i. i.inst_opcode = ALLOCA) insts) = [32] /\
    ~EXISTS (\i. i.inst_opcode = DALLOCA \/ i.inst_opcode = INVOKE) insts
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Theorem return_copy_margin_numeric_probe[local]:
  let frontier = dimword (:256) - 33 in
  let rb = frontier - 32 in
    rb + 32 <= frontier /\
    frontier + 32 < dimword (:256) /\
    ~(rb + 32 + 64 < dimword (:256))
Proof
  simp[dimword_def]
QED
