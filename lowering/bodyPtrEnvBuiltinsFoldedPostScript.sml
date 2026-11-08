(* Ordinary folded-selector execution and post, before ghost decoration. *)
Theory bodyPtrEnvBuiltinsFoldedPost
Ancestors bodyPtrEnvBuiltinsMethodFolded bodyPtrEnvBuiltinsSelectorBytes
  bodyPtrEnvBuiltinsSelectorRun bodyPtrEnvBuiltinsSelectorPost
  exprLoweringProps exprSimAlloc exprSimLiteralBuffer compileEnv emitHelper
  context fragExec loweringPosts venomState venomInst words list

Theorem folded_selector_run_post:
  LENGTH (bs:word8 list) = 4 /\
  compile_bytelike_literal bs 4 sa = (buf,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb fn ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args)
      es sa sb s es (Value (BytesV bs))
      (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf))
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all folded_selector_code >> strip_tac >>
  gvs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    (irule exprSimHashTheory.hash_emitted_inst_mem >>
     goal_assum (drule_at Any) >> simp[]) >>
  `~not_fresh_at sa (STRING #"%" (toString (sa.cs_next_var+1)))` by
    (simp[not_fresh_at_def] >> qexists_tac `sa.cs_next_var+1` >> simp[]) >>
  drule_all (selector_buffer_run_frame |> SPEC_ALL |> Q.INST
    [`p` |-> `STRING #"%" (toString sa.cs_next_var)`,
     `q` |-> `STRING #"%" (toString (sa.cs_next_var+1))`,
     `value` |-> `Lit (word_of_bytes T 0w
       (TAKE 32 (bs ++ REPLICATE 31 (0w:word8))))`]
    |> GEN_ALL |> SRULE [eval_operand_def]) >>
  disch_then (qspecl_then [`sa.cs_next_id+3`, `sa.cs_next_id+2`,
    `sa.cs_next_id+1`, `bs`] mp_tac) >>
  simp[eval_operand_def, selector_padded_word_bytes] >>
  strip_tac >> qexists_tac `t` >> conj_tac
  >- (gvs[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  irule (SRULE [] selector_buffer_vv_post) >>
  goal_assum (drule_at Any) >> simp[eval_operand_def] >>
  conj_tac >- (first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED
