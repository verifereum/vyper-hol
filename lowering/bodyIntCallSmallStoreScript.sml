(* Tight runtime copy footprints, including empty bytestring payloads. *)
Theory bodyIntCallSmallStore
Ancestors
  context compileEnv exprSimBufferStore valueCopy vyperMisc venomState
  venomExecSemantics

Theorem intcall_bytestring_store_footprint:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n w) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  32 + 32 * word_size len <= bound ==>
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
    q.vs_memory =
      (mcopy (w2n d) (w2n w) (32 + 32 * word_size len) s).vs_memory /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (!a k. a + k <= w2n d \/ w2n d + bound <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> drule_all buffer_store_bytestring_run >> strip_tac >>
  qexists_tac `q` >> simp[] >> rpt strip_tac >>
  irule buffer_mcopy_exterior >> simp[]
QED

Theorem intcall_zero_raw_store:
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  type_memory_bytes ce ty = 0 ==>
  compile_store_memory ce src dst ty ty sa = ((),sa)
Proof
  simp[compile_store_memory_def, compile_copy_memory_def, comp_return_def]
QED

Theorem intcall_empty_bytestring_footprint[local]:
  32 + 32 * word_size 0 = 32
Proof
  EVAL_TAC
QED
