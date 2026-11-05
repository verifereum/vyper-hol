(* Operand provenance and shape preservation for guarded bypass. *)
Theory simplifyCfgBypassShape
Ancestors
  simplifyCfgShapeCore
  simplifyCfgBypassClosure simplifyCfgBypassPhi simplifyCfgDefs
  unitShapeDefs cfgTransform venomInst unitLabelMapIdentity list simplifyCfgLabelProps
  simplifyCfgShape
  simplifyCfgStruct

Theorem scfg_subst_label_inst_var[simp]:
  MEM (Var v) (subst_label_inst B target i).inst_operands <=>
  MEM (Var v) i.inst_operands
Proof
  simp[subst_label_inst_def, MEM_MAP] >>
  metis_tac[subst_label_op_var]
QED

Theorem scfg_bypass_term_var:
  MEM (Var v) (scfg_bypass_term B target i).inst_operands ==>
  MEM (Var v) i.inst_operands
Proof
  simp[scfg_bypass_term_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> drule canon_jnz_inst_var_subset >> simp[]
QED

Theorem scfg_bypass_image_var:
  MEM (Var v) (scfg_bypass_image A B target l i).inst_operands ==>
  MEM (Var v) i.inst_operands
Proof
  simp[scfg_bypass_image_def] >> rpt IF_CASES_TAC >>
  metis_tac[update_phi_bypass_var_subset, scfg_bypass_term_var]
QED

Theorem scfg_bypass_image_ordinary:
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI ==>
  scfg_bypass_image A B target l i = i
Proof
  simp[scfg_bypass_image_def, scfg_bypass_term_def, update_phi_bypass_def]
QED

Theorem scfg_bypass_inst_image:
  scfg_bypass_hyp fn a b fn' /\ MEM i' (fn_insts fn') ==>
  ?bb i. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
    i' = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i
Proof
  strip_tac >> fs[fn_insts_MEM] >>
  drule_all (iffLR scfg_bypass_mem) >> strip_tac >> gvs[] >>
  fs[scfg_bypass_block_def, MEM_MAP] >> gvs[] >> metis_tac[]
QED

Theorem scfg_canon_opcode:
  !i. (canon_jnz_inst i).inst_opcode = i.inst_opcode \/
  (canon_jnz_inst i).inst_opcode = JMP /\ i.inst_opcode = JNZ
Proof
  gen_tac >> Cases_on `canon_jnz_inst i = i` >- simp[] >>
  drule canon_jnz_inst_changed >> strip_tac >> simp[]
QED

Theorem scfg_bypass_term_opcode:
  (scfg_bypass_term B target i).inst_opcode = i.inst_opcode \/
  (scfg_bypass_term B target i).inst_opcode = JMP /\ i.inst_opcode = JNZ
Proof
  simp[scfg_bypass_term_def] >> IF_CASES_TAC >> simp[] >>
  qspec_then `subst_label_inst B target i` mp_tac scfg_canon_opcode >>
  simp[subst_label_inst_def]
QED

Theorem scfg_bypass_image_opcode:
  (scfg_bypass_image A B target l i).inst_opcode = i.inst_opcode \/
  (scfg_bypass_image A B target l i).inst_opcode = JMP /\ i.inst_opcode = JNZ
Proof
  simp[scfg_bypass_image_def] >> rpt IF_CASES_TAC >>
  simp[update_phi_bypass_shape, scfg_bypass_term_opcode]
QED

Theorem scfg_bypass_image_ordinary_inv:
  ~is_terminator (scfg_bypass_image A B target l i).inst_opcode /\
  (scfg_bypass_image A B target l i).inst_opcode <> PHI ==>
  scfg_bypass_image A B target l i = i
Proof
  strip_tac >> irule scfg_bypass_image_ordinary >>
  metis_tac[scfg_bypass_image_classes]
QED

Theorem scfg_bypass_copy_phi_var:
  scfg_bypass_hyp fn a b fn' /\ ~is_terminator origin /\ origin <> PHI /\
  copy_phi_var origin fn' x ==> copy_phi_var origin fn x
Proof
  `!origin f x. copy_phi_var origin f x ==>
    !fn a b. scfg_bypass_hyp fn a b f /\ ~is_terminator origin /\ origin <> PHI ==>
      copy_phi_var origin fn x` suffices_by metis_tac[] >>
  Induct_on `copy_phi_var` >> rpt strip_tac
  >- (drule_all scfg_bypass_inst_image >> strip_tac >> gvs[] >>
      `scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i = i` by
        (irule scfg_bypass_image_ordinary_inv >> simp[]) >>
      metis_tac[copy_phi_var_seed, fn_insts_MEM])
  >- (drule_all scfg_bypass_inst_image >> strip_tac >> gvs[] >>
      `scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i = i` by
        (irule scfg_bypass_image_ordinary_inv >>
         simp[Excl "scfg_bypass_image_classes", is_terminator_def]) >>
      metis_tac[copy_phi_var_assign, fn_insts_MEM]) >>
  drule_all scfg_bypass_inst_image >> strip_tac >> gvs[] >>
  irule copy_phi_var_phi >> qexists_tac `i` >>
  metis_tac[fn_insts_MEM, scfg_bypass_image_var, scfg_bypass_image_fields,
    scfg_bypass_image_classes]
QED

Theorem scfg_bypass_opaque_vars:
  scfg_bypass_hyp fn a b fn' ==>
  (!x. gas_var fn' x ==> gas_var fn x) /\
  (!x. retpc_var fn' x ==> retpc_var fn x)
Proof
  simp[gas_var_def, retpc_var_def] >> strip_tac >> conj_tac >>
  rpt strip_tac >> irule scfg_bypass_copy_phi_var >>
  simp[is_terminator_def] >> metis_tac[]
QED

Theorem scfg_canon_non_jnz:
  i.inst_opcode <> JNZ ==> canon_jnz_inst i = i
Proof
  metis_tac[canon_jnz_inst_changed]
QED

Theorem scfg_bypass_image_opaque_use:
  (gas_use_ok i x ==> gas_use_ok (scfg_bypass_image A B target l i) x) /\
  (retpc_use_ok i x ==> retpc_use_ok (scfg_bypass_image A B target l i) x)
Proof
  Cases_on `i.inst_opcode = PHI`
  >- simp[gas_use_ok_def, retpc_use_ok_def] >>
  Cases_on `i.inst_opcode = ASSIGN`
  >- (`scfg_bypass_image A B target l i = i` by
        (irule scfg_bypass_image_ordinary >> simp[is_terminator_def]) >> simp[]) >>
  conj_tac
  >- (simp[gas_use_ok_def] >> rpt strip_tac >>
      `scfg_bypass_image A B target l i = i` by
        (irule scfg_bypass_image_ordinary >> simp[is_terminator_def]) >> simp[]) >>
  simp[retpc_use_ok_def] >> rpt strip_tac >>
  `!B target. canon_jnz_inst (subst_label_inst B target i) = subst_label_inst B target i` by
    (rpt gen_tac >> irule scfg_canon_non_jnz >> simp[subst_label_inst_def]) >>
  simp[scfg_bypass_image_def, scfg_bypass_term_def, is_terminator_def] >>
  rpt IF_CASES_TAC >>
  simp[update_phi_bypass_def, canon_jnz_inst_def, subst_label_inst_def,
       retpc_use_ok_def, MAP_APPEND, subst_label_op_def] >>
  simp[MEM_MAP] >> metis_tac[subst_label_op_var]
QED

Theorem scfg_bypass_opaque_use:
  scfg_bypass_hyp fn a b fn' /\ opaque_use_ok fn ==> opaque_use_ok fn'
Proof
  strip_tac >> simp[opaque_use_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all scfg_bypass_inst_image >> strip_tac >> gvs[] >>
  drule scfg_bypass_image_var >> strip_tac >>
  `MEM i (fn_insts fn)` by metis_tac[fn_insts_MEM] >>
  drule scfg_bypass_opaque_vars >> strip_tac >>
  metis_tac[opaque_use_ok_retpc_use,
    scfg_bypass_image_opaque_use]
QED

Theorem scfg_subst_nonlabel:
  ~is_label_operand op ==> subst_label_op B target op = op
Proof
  Cases_on `op` >> simp[stackPlanTypesTheory.is_label_operand_def, subst_label_op_def]
QED

Theorem scfg_subst_nonlabels:
  EVERY (\op. ~is_label_operand op) ops ==>
  MAP (subst_label_op B target) ops = ops
Proof
  Induct_on `ops` >> simp[] >> metis_tac[scfg_subst_nonlabel]
QED

Theorem scfg_update_phi_bypass_shape:
  scfg_inst_shape i ==> scfg_inst_shape (update_phi_bypass A B i)
Proof
  Cases_on `i.inst_opcode = PHI`
  >- (simp[scfg_inst_shape_def, update_phi_bypass_shape,
           is_read0_opcode_def, scfg_label_positions_def, label_positions_ok_def]) >>
  simp[update_phi_bypass_def]
QED

(* Pending term-shape attempt: needs a compact label-position boundary before
   unfolding scfg_inst_shape. Kept for inspection, not a proved theorem.
Theorem scfg_bypass_term_shape:
  scfg_inst_shape i ==> scfg_inst_shape (scfg_bypass_term B target i)
Proof
  Cases_on `is_terminator i.inst_opcode`
  >- (strip_tac >> Cases_on `i.inst_opcode` >> gvs[is_terminator_def] >>
      gvs[scfg_bypass_term_def, scfg_inst_shape_def, is_read0_opcode_def,
          scfg_label_positions_def, label_positions_ok_def, scfg_canon_non_jnz] >> FAIL_TAC "term shape") >>
  simp[scfg_bypass_term_def]
QED
*)

Theorem scfg_jmp_label_positions:
  i.inst_opcode = JMP ==>
  (scfg_label_positions i <=>
    EVERY (\op. ~is_label_operand op) i.inst_operands \/
    ?l. i.inst_operands = [Label l])
Proof
  strip_tac >> simp[scfg_label_positions_def, label_positions_ok_def] >>
  namedCases_on `i.inst_operands` ["", "x rest"] >> simp[] >>
  Cases_on `x` >> simp[stackPlanTypesTheory.is_label_operand_def] >>
  Cases_on `rest` >> simp[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem scfg_jnz_label_positions:
  i.inst_opcode = JNZ ==>
  (scfg_label_positions i <=>
    EVERY (\op. ~is_label_operand op) i.inst_operands \/
    ?c t f. i.inst_operands = [c; Label t; Label f] /\ ~is_label_operand c)
Proof
  strip_tac >> simp[scfg_label_positions_def, label_positions_ok_def] >>
  namedCases_on `i.inst_operands` ["", "c r1"] >> simp[] >>
  namedCases_on `r1` ["", "x r2"] >> simp[] >> namedCases_on `r2` ["", "y r3"]
  >- (Cases_on `x` >> simp[stackPlanTypesTheory.is_label_operand_def]) >>
  Cases_on `r3` >> simp[] >>
  Cases_on `x` >> Cases_on `y` >>
  simp[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem scfg_other_term_nonlabels:
  is_terminator i.inst_opcode /\ i.inst_opcode <> JMP /\
  i.inst_opcode <> JNZ /\ scfg_label_positions i ==>
  EVERY (\op. ~is_label_operand op) i.inst_operands
Proof
  Cases_on `i.inst_opcode` >> simp[is_terminator_def] >>
  simp[scfg_label_positions_def, label_positions_ok_def]
QED

Theorem scfg_other_term_identity:
  is_terminator i.inst_opcode /\ i.inst_opcode <> JMP /\
  i.inst_opcode <> JNZ /\ scfg_inst_shape i ==>
  scfg_bypass_term B target i = i
Proof
  strip_tac >>
  `EVERY (\op. ~is_label_operand op) i.inst_operands` by
    (irule scfg_other_term_nonlabels >> gvs[scfg_inst_shape_def]) >>
  `subst_label_inst B target i = i` by
    simp[subst_label_inst_def, scfg_subst_nonlabels] >>
  simp[scfg_bypass_term_def, scfg_canon_non_jnz]
QED

Theorem scfg_jmp_term_shape:
  i.inst_opcode = JMP /\ scfg_inst_shape i ==>
  scfg_inst_shape (scfg_bypass_term B target i)
Proof
  strip_tac >>
  `scfg_label_positions i` by fs[scfg_inst_shape_def] >>
  drule scfg_jmp_label_positions >> simp[] >> strip_tac
  >- (`subst_label_inst B target i = i` by
        simp[subst_label_inst_def, scfg_subst_nonlabels] >>
      simp[scfg_bypass_term_def, is_terminator_def, scfg_canon_non_jnz]) >>
  simp[scfg_bypass_term_def, is_terminator_def, subst_label_inst_def,
       subst_label_op_def, scfg_canon_non_jnz, scfg_inst_shape_def,
       is_read0_opcode_def, scfg_label_positions_def, label_positions_ok_def] >>
  IF_CASES_TAC >> simp[scfg_label_positions_def, label_positions_ok_def]
QED

Theorem scfg_jnz_nonlabels_canon_shape:
  i.inst_opcode = JNZ /\ scfg_inst_shape i /\
  EVERY (\op. ~is_label_operand op) i.inst_operands ==>
  scfg_inst_shape (canon_jnz_inst i)
Proof
  strip_tac >> simp[canon_jnz_inst_def] >>
  namedCases_on `i.inst_operands` ["", "c r1"] >> gvs[] >>
  namedCases_on `r1` ["", "x r2"] >> gvs[] >>
  namedCases_on `r2` ["", "y r3"] >> gvs[] >>
  Cases_on `r3` >> gvs[] >> IF_CASES_TAC >>
  simp[scfg_inst_shape_def, is_read0_opcode_def, scfg_label_positions_def, label_positions_ok_def] >>
  Cases_on `x` >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem scfg_jnz_term_shape:
  i.inst_opcode = JNZ /\ scfg_inst_shape i ==>
  scfg_inst_shape (scfg_bypass_term B target i)
Proof
  strip_tac >>
  `scfg_label_positions i` by fs[scfg_inst_shape_def] >>
  drule scfg_jnz_label_positions >> simp[] >> strip_tac
  >- (`subst_label_inst B target i = i` by
        simp[subst_label_inst_def, scfg_subst_nonlabels] >>
      simp[scfg_bypass_term_def, is_terminator_def] >>
      irule scfg_jnz_nonlabels_canon_shape >> simp[]) >>
  `subst_label_op B target c = c` by metis_tac[scfg_subst_nonlabel] >>
  simp[scfg_bypass_term_def, is_terminator_def, subst_label_inst_def,
       subst_label_op_def] >> rpt IF_CASES_TAC >>
  simp[canon_jnz_inst_def] >> rpt IF_CASES_TAC >>
  simp[scfg_inst_shape_def, is_read0_opcode_def, scfg_label_positions_def, label_positions_ok_def]
QED

Theorem scfg_bypass_term_shape:
  scfg_inst_shape i ==> scfg_inst_shape (scfg_bypass_term B target i)
Proof
  strip_tac >> Cases_on `is_terminator i.inst_opcode`
  >- (Cases_on `i.inst_opcode = JMP` >- metis_tac[scfg_jmp_term_shape] >>
      Cases_on `i.inst_opcode = JNZ` >- metis_tac[scfg_jnz_term_shape] >>
      `scfg_bypass_term B target i = i` by
        (irule scfg_other_term_identity >> simp[]) >> simp[]) >>
  simp[scfg_bypass_term_def]
QED

Theorem scfg_bypass_image_shape:
  scfg_inst_shape i ==> scfg_inst_shape (scfg_bypass_image A B target l i)
Proof
  strip_tac >> simp[scfg_bypass_image_def] >> rpt IF_CASES_TAC >>
  metis_tac[scfg_bypass_term_shape, scfg_update_phi_bypass_shape]
QED

Theorem scfg_bypass_fn_shape:
  scfg_bypass_hyp fn a b fn' /\ scfg_shape fn ==> scfg_shape fn'
Proof
  strip_tac >>
  `fn'.fn_name = fn.fn_name` by
    (fs[scfg_bypass_hyp_def] >> drule do_merge_jump_metadata >>
     simp[fn_identity_metadata_eq_def]) >>
  drule scfg_bypass_entry_eq >> strip_tac >>
  drule scfg_bypass_blocks_eq >> strip_tac >>
  simp[scfg_shape_def] >> conj_tac
  >- fs[scfg_shape_def] >>
  conj_tac >- metis_tac[scfg_bypass_opaque_use, scfg_shape_def] >>
  conj_tac
  >- (fs[scfg_shape_def] >> simp[EVERY_MEM, MEM_MAP, MEM_FILTER] >>
      rpt strip_tac >> gvs[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all scfg_bypass_inst_image >> strip_tac >> gvs[] >>
  irule scfg_bypass_image_shape >>
  fs[scfg_shape_def, EVERY_MEM] >> metis_tac[fn_insts_MEM]
QED
