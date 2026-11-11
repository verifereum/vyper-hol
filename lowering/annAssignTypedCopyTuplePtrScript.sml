(* Tuple normalization: concrete offsets, recursive children, robust fields. *)
Theory annAssignTypedCopyTuplePtr
Ancestors
  annAssignTypedCopyInterfacePtr annAssignTypedCopyAtomsPtr
  assignBasePtrFieldOffsets bodyPtrPopNestedLiveAddressFrame
  context compileEnv typedMemoryCopy fragGasPathPtr venomState words
  valueEncodingDefs valueEncoding ptrDiscipline finite_map bodyPtrDefs

(* Unlike the older strict-offset adapter this also covers a zero-sized
   trailing field.  The immutable-taint frame is needed by declaration. *)
Theorem annassign_typed_field_offset_ambient_ptr:
  !root off sa op sb G tn s a total n fn ctx D PG.
    compile_with_byte_offset (Var root) off sa = (op,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s total /\ off+n <= total /\
    w2n a + off < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?p Gf tf u.
      op = Var p /\ not_fresh_at sb p /\
      lookup_var p u = SOME (n2w (w2n a+off)) /\
      ptr_covers Gf tf p u n /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_offset_extends >> strip_tac >> simp[] >>
  Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules] >>
      gvs[ptr_covers_def, venom_state_component_equality] >> decide_tac) >>
  `emit_op ADD [Var root; Lit (n2w off)] sa = (op,sb)` by
    gvs[compile_with_byte_offset_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all pop_emit_offset_endpoint_framed_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`out`, `H`, `tf`, `t`] >> simp[] >>
  qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
  simp[venom_state_component_equality]
QED
