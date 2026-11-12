(* Word staging for the single-argument ABI encoder. *)
Theory abiEncodeSinglePtrWord
Ancestors
  bodyPtrHashBuiltinsShaFixed abiStaticAggregateProps exprSimProps
  exprSimUnopProps bodyPtrDefs valueEncodingProps byte bodyPtrBopInMachineMemory

Theorem abi_encode_word_source_stage:
  compile_alloc_buffer 32 sa = (buf,sl) /\
  emit_void MSTORE [buf.buf_operand;value] sl = ((),sm) /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME (typed_val_to_w256 tv v) /\ op_taint tn value = {} /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ ghost_inv d ce cx es G tn s /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?a p w H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK a) /\
    stmt_state_rel ctx fn ce cx es a /\ ghost_inv d ce cx es H un a /\
    ghost_kept ce es sa G tn s H un /\ buf.buf_operand = Var p /\
    eval_operand (Var p) a = SOME w /\ ptr_covers H un p a 32 /\
    (!mem. mem_agree_outside un.t_mem a.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
    ~a.vs_halted /\ a.vs_current_bb = s.vs_current_bb /\
    a.vs_inst_idx = s.vs_inst_idx+2 /\
    sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
    sm.cs_next_id = sa.cs_next_id+2 /\
    not_fresh_at sm p /\ local_ptrs_reserved ce sm
Proof
  strip_tac >>
  `32 <= 32` by decide_tac >>
  drule_all hash_fixed_prepare_endpoint >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  strip_tac >>
  qexistsl [`a`, `p`, `w`, `G2`, `tn2`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at (w2n w) 32 a.vs_memory = word_to_bytes_be (typed_val_to_w256 tv v)` by
        (first_x_assum irule >> simp[length_word_to_bytes_be]) >>
      `mem_agree_outside tn2.t_mem a.vs_memory mem` by gvs[] >>
      `mem_bytes_at (w2n w) 32 a.vs_memory = mem_bytes_at (w2n w) 32 mem` by
        (irule mem_agree_outside_window >> metis_tac[]) >>
      drule_all val_in_memory_word >> disch_then (qspecl_then [`w2n w`, `mem`] mp_tac) >>
      gvs[mem_word_at_bytes] >>
      simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_word_to_bytes]) >>
  drule_all hash_fixed_prepare_emission >> strip_tac >>
  irule bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb >>
  goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]
QED
