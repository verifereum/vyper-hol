(* Counted checked execution of the folded selector's four instructions. *)
Theory bodyPtrEnvBuiltinsFoldedCounted
Ancestors bodyPtrEnvBuiltinsMethodFolded bodyPtrEnvBuiltinsSelectorBytes
  bodyPtrEnvBuiltinsSelectorCounted bodyPtrDefs exprLoweringProps exprSimHash
  fragExec compileEnv venomState venomInst ptrDiscipline words list

Theorem folded_selector_counted:
  LENGTH (bs:word8 list) = 4 /\
  compile_bytelike_literal bs 4 sa = (buf,sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ghost_inv d cenv cx es G' tn' (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept cenv es sa G tn s G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) buf.buf_operand G' tn'
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args)
      buf.buf_operand G' (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all folded_selector_code >> strip_tac >> gvs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    (irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]) >>
  `~not_fresh_at sa (STRING #"%" (toString sa.cs_next_var)) /\
   ~not_fresh_at sa (STRING #"%" (toString (sa.cs_next_var+1)))` by
    (simp[not_fresh_at_def]) >>
  `TAKE 4 (word_to_bytes (word_of_bytes T (0w:256 word)
     (TAKE 32 (bs ++ REPLICATE 31 (0w:word8)))) T) = bs` by
    simp[selector_padded_word_bytes] >>
  qpat_assum `s.vs_inst_idx = _` (fn idx =>
  drule_all (selector_suffix_counted |> SPEC_ALL |> Q.INST
    [`p` |-> `STRING #"%" (toString sa.cs_next_var)`,
     `q` |-> `STRING #"%" (toString (sa.cs_next_var+1))`,
     `w` |-> `word_of_bytes T (0w:256 word)
       (TAKE 32 (bs ++ REPLICATE 31 (0w:word8)))`,
     `value` |-> `Lit (word_of_bytes T (0w:256 word)
       (TAKE 32 (bs ++ REPLICATE 31 (0w:word8))))`]
    |> SRULE [idx] |> GEN_ALL |> SRULE [eval_operand_def, op_taint_def])) >>
  disch_then (qspecl_then [`args`, `PG`, `D`] ACCEPT_TAC)
QED
