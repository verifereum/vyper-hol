(* The shape facts the per-function simulation proof threads through each
   rewrite step: fn_shape_ok without its return-PC
   conjuncts, inst_shape_ok without its PHI arity conjunct, and
   label_positions_ok without distinct JNZ targets.  The whole pass is shown
   to keep those separately (simplifyCfgPhi2,
   simplifyCfgJnzdist, o1ContractSimplifyCfgStep); an intermediate step
   need not. *)
Theory simplifyCfgShapeCore
Ancestors
  unitShapeDefs

Definition scfg_label_positions_def:
  scfg_label_positions inst <=>
    if inst.inst_opcode = JNZ then
      (case inst.inst_operands of
         [c; Label t; Label f] => ~is_label_operand c
       | ops => EVERY (\op. ~is_label_operand op) ops)
    else label_positions_ok inst
End

Theorem label_positions_ok_scfg_label_positions:
  label_positions_ok inst ==> scfg_label_positions inst
Proof
  strip_tac >> simp[scfg_label_positions_def] >> strip_tac >>
  qpat_x_assum `label_positions_ok _` mp_tac >>
  simp[label_positions_ok_def] >>
  namedCases_on `inst.inst_operands` ["", "c r1"] >> simp[] >>
  namedCases_on `r1` ["", "x r2"] >> simp[] >>
  namedCases_on `r2` ["", "y r3"] >> simp[] >>
  Cases_on `x` >> simp[] >> Cases_on `y` >> simp[] >>
  Cases_on `r3` >> simp[]
QED

Definition scfg_inst_shape_def:
  scfg_inst_shape inst <=>
    ~MEM inst.inst_opcode [DJMP; OFFSET] /\
    (is_read0_opcode inst.inst_opcode ==> inst.inst_operands = []) /\
    scfg_label_positions inst
End

Definition scfg_shape_def:
  scfg_shape fn <=>
    fn_entry_label fn = SOME fn.fn_name /\ opaque_use_ok fn /\
    EVERY (\bb. ~reserved_label bb.bb_label) fn.fn_blocks /\
    EVERY scfg_inst_shape (fn_insts fn)
End

Theorem fn_shape_ok_scfg_shape:
  fn_shape_ok fn ==> scfg_shape fn
Proof
  simp[fn_shape_ok_def, scfg_shape_def, scfg_inst_shape_def, inst_shape_ok_def,
       listTheory.EVERY_MEM] >>
  metis_tac[label_positions_ok_scfg_label_positions]
QED
