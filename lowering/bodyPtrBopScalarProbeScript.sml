(* Counted scalar-edge interface probe; reuses the existing general
   ADD/AND instruction certificate rather than duplicating it. *)
Theory bodyPtrBopScalarProbe
Ancestors
  typedCopyPtr fragGasSeqPtr

Theorem bop_add_counted_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [left; right] [tmp]) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id ADD [left; right] [tmp]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [left; right] [tmp]) u)
    (step_taint (mk_inst id ADD [left; right] [tmp]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id ADD [left; right] [tmp]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  ` (mk_inst id ADD [left; right] [tmp]).inst_opcode <> INVOKE /\
    ~is_terminator (mk_inst id ADD [left; right] [tmp]).inst_opcode` by
    simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[venomInstTheory.mk_inst_def]
QED

Theorem bop_add_preserves_old_prov:
  x <> tmp ==>
  FLOOKUP (step_prov PG G (mk_inst id ADD [left; right] [tmp]) u) x =
  FLOOKUP G x
Proof
  strip_tac >>
  pure_rewrite_tac[ptrDisciplineTheory.step_prov_def] >>
  Cases_on `ptrDiscipline$out_prov PG G
    (mk_inst id ADD [left; right] [tmp]) u` >>
  simp[ptrDisciplineTheory.set_prov_def, venomInstTheory.mk_inst_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem bop_add_output_clean:
  FLOOKUP (step_taint (mk_inst id ADD [left; right] [tmp]) s u tn).t_var tmp =
  SOME {}
Proof
  simp[ptrDisciplineTheory.step_taint_def,
       ptrDisciplineTheory.set_var_taint_def,
       ptrDisciplineTheory.out_taint_def, venomInstTheory.mk_inst_def] >>
  Cases_on `eval_operand left s` >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED
