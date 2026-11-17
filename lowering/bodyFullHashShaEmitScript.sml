(* The compiler's emitted SHA tail has the complete bounded frame. *)
Theory bodyFullHashShaEmit
Ancestors
  bodyFullHashShaTail bodyPtrHashBuiltinsShaEmit
  bodyPtrHashBuiltinsShaTailSteps bodyPtrDefs exprSimHash
  builtinHashing emitHelperProps emitHelper compileEnv exprLoweringProps
  venomState venomInst ptrDiscipline finite_map pred_set ASCIInumbers

Theorem sha_emit_tail_frame_at:
  !D lo d cenv cx es G tn s ctx fn sa sg sc sh sb gas_op success_op op p len q w n r bs outcome rest t Gf tf.
    emit_op GAS [] sa = (gas_op,sg) /\
    emit_op STATICCALL [gas_op;Lit 2w;Var p;len;Var q;Lit 32w] sg = (success_op,sc) /\
    emit_void ASSERT [success_op] sc = ((),sh) /\
    emit_op MLOAD [Var q] sh = (op,sb) /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    (!x. x = p \/ len = Var x \/ x = q ==> not_fresh_at sa x) /\
    mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
    s.vs_outcomes = outcome::rest /\ outcome.co_success /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    ghost_inv_at D lo d cenv cx es G tn s /\ stmt_state_rel H ctx fn cenv cx es s /\
    local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!name b k. local_region cenv es.scopes s name b k ==>
      b+k <= w2n r \/ w2n r+32 <= b) /\ lo <= w2n r /\
    Gf = DRESTRICT G (COMPL {STRING #"%" (toString sa.cs_next_var);
      STRING #"%" (toString (sa.cs_next_var+1)); STRING #"%" (toString (sa.cs_next_var+2))}) /\
    tf = tn with <|t_var := tn.t_var |+
      (STRING #"%" (toString sa.cs_next_var),{}) |+
      (STRING #"%" (toString (sa.cs_next_var+1)),{}) |+
      (STRING #"%" (toString (sa.cs_next_var+2)),{});
      t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|> ==>
    ghost_inv_at D lo d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+4) /\
    ghost_kept_at lo cenv es sa G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emitted_insts_sha256_tail >> strip_tac >> gvs[] >>
  irule (SRULE [] sha_tail_success_frame_at) >>
  simp[] >> gvs[mk_inst_def] >> metis_tac[hash_sha256_emit_fresh]
QED
