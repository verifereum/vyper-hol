(* Emission transports the shared counted SHA tail without replaying its edges. *)
Theory bodyPtrHashBuiltinsShaEmit
Ancestors bodyPtrHashBuiltinsShaTail bodyPtrHashBuiltinsShaTailFrame
  bodyPtrHashBuiltinsGhostFrame exprSimHash bodyPtrDefs compileEnv
  exprLowering emitHelperProps venomState ptrDiscipline words finite_map
  ASCIInumbers venomInst

Theorem hash_sha256_emit_fresh:
  !sa x.
    not_fresh_at sa x ==>
    x <> STRING #"%" (toString sa.cs_next_var) /\
    x <> STRING #"%" (toString (sa.cs_next_var+1)) /\
    x <> STRING #"%" (toString (sa.cs_next_var+2))
Proof
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED

Theorem hash_emit_sha256_tail_abort_path:
  !D ctx fn PG G tn s bb sa sg sc sh sb gas_op success_op op p len q w n r.
    emit_op GAS [] sa = (gas_op,sg) /\
    emit_op STATICCALL [gas_op;Lit 2w;Var p;len;Var q;Lit 32w] sg = (success_op,sc) /\
    emit_void ASSERT [success_op] sc = ((),sh) /\
    emit_op MLOAD [Var q] sh = (op,sb) /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    ptr_covers G tn p s (w2n n) /\ ptr_covers G tn q s 32 /\
    op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    (!x. x = p \/ len = Var x \/ x = q ==> not_fresh_at sa x) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
    ?t j Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
      gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
        (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emitted_insts_sha256_tail >> strip_tac >>
  qrefinel [`_`, `_`, `DRESTRICT G (COMPL {gv;sv})`,
    `tn with t_var := tn.t_var |+ (gv,{}) |+ (sv,{})`] >>
  irule hash_sha256_tail_abort_path >>
  gvs[mk_inst_def] >> metis_tac[hash_sha256_emit_fresh]
QED

Theorem hash_emit_sha256_tail_success_path:
  !D ctx fn PG G tn s bb sa sg sc sh sb gas_op success_op op p len q w n r bs outcome rest.
    emit_op GAS [] sa = (gas_op,sg) /\
    emit_op STATICCALL [gas_op;Lit 2w;Var p;len;Var q;Lit 32w] sg = (success_op,sc) /\
    emit_void ASSERT [success_op] sc = ((),sh) /\
    emit_op MLOAD [Var q] sh = (op,sb) /\
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    ptr_covers G tn p s (w2n n) /\ ptr_covers G tn q s 32 /\
    op_taint tn len = {} /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    (!x. x = p \/ len = Var x \/ x = q ==> not_fresh_at sa x) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
    s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
    ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = OK t /\
      gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
        (OK (t with vs_inst_idx := s.vs_inst_idx+4)) /\
      eval_operand op t = SOME (SHA_256_bytes bs) /\
      Gf = DRESTRICT G (COMPL {STRING #"%" (toString sa.cs_next_var);
        STRING #"%" (toString (sa.cs_next_var+1)); STRING #"%" (toString (sa.cs_next_var+2))}) /\
      tf = tn with <|t_var := tn.t_var |+
        (STRING #"%" (toString sa.cs_next_var),{}) |+
        (STRING #"%" (toString (sa.cs_next_var+1)),{}) |+
        (STRING #"%" (toString (sa.cs_next_var+2)),{});
        t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|>
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emitted_insts_sha256_tail >> strip_tac >>
  qrefinel [`_`, `DRESTRICT G (COMPL {gv;sv;ov})`,
    `tn with <|t_var := tn.t_var |+ (gv,{}) |+ (sv,{}) |+ (ov,{});
      t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|>`] >>
  gvs[] >> irule (SRULE [] hash_sha256_tail_success_path) >>
  gvs[mk_inst_def] >> metis_tac[hash_sha256_emit_fresh]
QED

Theorem hash_emit_sha256_tail_frame:
  !d cenv cx es G tn s ctx fn sa sg sc sh sb gas_op success_op op p len q w n r bs outcome rest t Gf tf.
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
    ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
    local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!name b k. local_region cenv es.scopes s name b k ==>
      b+k <= w2n r \/ w2n r+32 <= b) /\
    Gf = DRESTRICT G (COMPL {STRING #"%" (toString sa.cs_next_var);
      STRING #"%" (toString (sa.cs_next_var+1)); STRING #"%" (toString (sa.cs_next_var+2))}) /\
    tf = tn with <|t_var := tn.t_var |+
      (STRING #"%" (toString sa.cs_next_var),{}) |+
      (STRING #"%" (toString (sa.cs_next_var+1)),{}) |+
      (STRING #"%" (toString (sa.cs_next_var+2)),{});
      t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|> ==>
    ghost_inv d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+4) /\
    ghost_kept cenv es sa G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emitted_insts_sha256_tail >> strip_tac >> gvs[] >>
  irule (SRULE [] hash_sha256_tail_success_frame) >>
  simp[] >> gvs[mk_inst_def] >> metis_tac[hash_sha256_emit_fresh]
QED
