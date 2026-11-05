(* The length-load edge of compile_bytestring_hash. Coverage is explicit:
   payload-length bounds and transport across operands remain separate. *)
Theory bodyPtrBopHashProbe
Ancestors
  typedCopyPtr fragGasSeqPtr

Theorem bop_hash_length_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MLOAD [Var src] [tmp]) /\
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) u)
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id MLOAD [Var src] [tmp]) s` by
    (irule ptr_inst_ok_mload >> simp[]) >>
  `(mk_inst id MLOAD [Var src] [tmp]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id MLOAD [Var src] [tmp]).inst_opcode` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  drule_all straight_line_ptr_edge >> simp[venomInstTheory.mk_inst_def]
QED

Theorem bop_buffer_covers_prefix:
  ptr_buf_ok cenv e (Var p) G s /\
  op_taint tn (Var p) = {} /\ lookup_var p s = SOME w /\
  0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
  n <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ptr_covers G tn p s n
Proof
  rw[bodyPtrDefsTheory.ptr_buf_ok_def, bodyPtrDefsTheory.ptr_covers_def] >>
  first_x_assum (qspec_then `w` mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`w`, `b`, `sz`] >> simp[]
QED
