(* Robust immutable loads remain checked at every compiler cursor.
   General ptr_inst_ok cursor equivalence is false: access_ok may use
   in_revert_forward.  This boundary instead uses actual source coverage. *)
Theory immutableSeqCursorPtr
Ancestors
  immutableLoadPtr ghostPcTransportPtr payloadLoadStorePtr
  ptrDiscipline contextCodegenRel codegenRel venomInst venomState
  exprSimCopy immutableCopyExecution context compileEnv emitHelper
  exprLoweringProps finite_map storageCopyBodyPtr fragGasSeqPtr
  ptrSafeRun venomExecSemantics emitHelperProps

Theorem immutable_load_checked_uniform:
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  (ctor ==> ?p. op = Var p /\ ptr_covers G tn p s 32) /\
  ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if ctor then ILOAD else DLOAD) [op] [out]]
    (s with vs_inst_idx := k)
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+
      (out,if ctor then mem_word_taint tn.t_mem (w2n a) else {}))
Proof
  rpt strip_tac >> irule immutable_load_checked >> simp[] >>
  Cases_on `ctor`
  >- (gvs[] >>
      irule (SRULE [] (Q.INST [`ctor` |-> `T`] immutable_load_access)) >>
      qexists_tac `tn` >> simp[]) >>
  simp[access_ok_def, mk_inst_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem emit_immutable_load_checked:
  emit_op (if ctor then ILOAD else DLOAD) [op] sa = (r,sb) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  (ctor ==> ?p. op = Var p /\ ptr_covers G tn p s 32) /\
  ~ctx_has_dalloca ctx ==>
  ?out tf.
    r = Var out /\
    copy_runtime_frame sa s sb
      (update_var out (immutable_copy_read ctor a s) s) /\
    copy_old_operand sb r /\
    eval_operand r (update_var out (immutable_copy_read ctor a s) s) =
      SOME (immutable_copy_read ctor a s) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) (DRESTRICT G (COMPL {out})) tf) /\
    op_prov (DRESTRICT G (COMPL {out})) r = NONE /\
    op_taint tf r = (if ctor then mem_word_taint tn.t_mem (w2n a) else {}) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP (DRESTRICT G (COMPL {out})) x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all emit_immutable_load_runtime_frame >> strip_tac >>
  qexistsl [`out`, `tn with t_var := tn.t_var |+
      (out,if ctor then mem_word_taint tn.t_mem (w2n a) else {})`] >>
  simp[copy_old_operand_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, op_prov_def, FLOOKUP_DRESTRICT] >>
  conj_tac
  >- (irule immutable_load_checked_uniform >> simp[]) >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >> simp[]
QED

Theorem compile_imm_load_word_direct_checked:
  compile_imm_load_word ctor imm op sa = (r,sb) /\
  (ctor ==> imm = NONE) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  (ctor ==> ?p. op = Var p /\ ptr_covers G tn p s 32) /\
  ~ctx_has_dalloca ctx ==>
  ?out tf.
    r = Var out /\
    copy_runtime_frame sa s sb
      (update_var out (immutable_copy_read ctor a s) s) /\
    copy_old_operand sb r /\
    eval_operand r (update_var out (immutable_copy_read ctor a s) s) =
      SOME (immutable_copy_read ctor a s) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) (DRESTRICT G (COMPL {out})) tf) /\
    op_prov (DRESTRICT G (COMPL {out})) r = NONE /\
    op_taint tf r = (if ctor then mem_word_taint tn.t_mem (w2n a) else {}) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP (DRESTRICT G (COMPL {out})) x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `emit_op (if ctor then ILOAD else DLOAD) [op] sa = (r,sb)` by
    (Cases_on `ctor` >> gvs[compile_imm_load_word_def]) >>
  irule emit_immutable_load_checked >> simp[] >> qexists_tac `op` >> simp[]
QED

Theorem emit_mstore_payload_checked_uniform:
  emit_void MSTORE [Var p;v] sa = ((),sb) /\
  copy_old_operand sa (Var p) /\ copy_old_operand sa v /\
  eval_operand (Var p) s = SOME addr /\ eval_operand v s = SOME value /\
  ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx ==>
  copy_runtime_frame sa s sb (mstore (w2n addr) value s) /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) G
    (tn with t_mem :=
      (tn.t_mem DIFF {i | w2n addr <= i /\ i < w2n addr + 32}) UNION
      {w2n addr + j | j IN op_taint tn v}))
Proof
  strip_tac >> conj_tac
  >- (irule copy_runtime_store >> qexistsl [`Var p`,`v`] >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >> simp[] >> gen_tac >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var p;v] [])
      (s with vs_inst_idx := k) =
    OK (mstore (w2n addr) value (s with vs_inst_idx := k))` by
    simp[storage_copy_store_step] >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_mstore_payload >> simp[]) >>
  `mstore (w2n addr) value (s with vs_inst_idx := k) =
   (mstore (w2n addr) value s) with vs_inst_idx := k` by
    simp[mstore_def] >>
  simp[storage_copy_store_ghost]
QED
