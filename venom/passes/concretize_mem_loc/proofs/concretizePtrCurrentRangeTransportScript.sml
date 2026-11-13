Theory concretizePtrCurrentRangeTransport
Ancestors
  concretizePtrObservationInterface concretizePtrWritePurity
  concretizePtrOpaqueRetpc concretizePtrOwnershipErasure
  ptrDiscipline memLocDefs pointerConfinedDefs
  contextCodegenRel codegenRel venomInst venomState
  list finite_map pred_set

Theorem ptr_read_max_size_not_pointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  mem_read_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop ==>
  !v. sizeop = Var v ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `fn_ptr_ok P fn` kall_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[mem_read_ops_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- metis_tac[MEM_REVERSE, MEM] >>
  `inst.inst_operands = REVERSE (Var v::Var v::v10::v11)` by
    metis_tac[REVERSE_REVERSE] >>
  gvs[FILTER_REVERSE, FILTER_APPEND_DISTRIB] >>
  qpat_x_assum `_ ++ _ = [_]` mp_tac >>
  disch_then (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
  simp[]
QED

Theorem ptr_read_max_size_untainted:
  taint_ok fn tn inst s /\ mem_read_ops inst = SOME ops /\
  ops.iao_max_size = SOME sizeop ==> op_taint tn sizeop = {}
Proof
  Cases_on `inst.inst_opcode` >>
  simp[mem_read_ops_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[taint_ok_def] >>
  simp[op_taint_def] >> metis_tac[op_taint_def, MEM_REVERSE, MEM]
QED

val load_tac =
  rpt strip_tac >>
  Cases_on `eval_operand src' tgt` >> gvs[] >>
  `?x. eval_operand src' src = SOME x` by
    metis_tac[optionTheory.IS_SOME_DEF, optionTheory.option_CASES] >>
  simp[];

val range_tac =
  rpt strip_tac >>
  gvs[memory_range_of_operands_def] >>
  qmatch_goalsub_rename_tac `eval_operand a src = SOME _` >>
  Cases_on `eval_operand a tgt` >> gvs[] >>
  `?x. eval_operand a src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand sz tgt` >> gvs[];

val copy_tac =
  rpt strip_tac >>
  Cases_on `eval_operand v2 tgt` >> gvs[] >>
  `?z. eval_operand v2 src = SOME z` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand src' tgt` >> gvs[] >>
  `?x. eval_operand src' src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand sz tgt` >> gvs[];

val call_tac =
  rpt strip_tac >>
  gvs[memory_range_of_operands_def, sized_source_write_range_def] >>
  qpat_x_assum `inst.inst_operands = _` kall_tac >>
  rpt (qmatch_asmsub_rename_tac
         `MEM _ (case eval_operand gate tgt of NONE => [] | SOME v => _)` >>
       Cases_on `eval_operand gate tgt` >> gvs[] >>
       `?z. eval_operand gate src = SOME z` by
         metis_tac[optionTheory.IS_SOME_EXISTS] >> gvs[] >>
       qpat_x_assum `eval_operand gate tgt = SOME _` kall_tac >>
       qpat_x_assum `eval_operand gate src = SOME _` kall_tac) >>
  qmatch_goalsub_rename_tac `eval_operand a src = SOME _` >>
  rename1 `eval_operand szop src = eval_operand szop tgt` >>
  Cases_on `eval_operand a tgt` >> gvs[] >>
  `?x. eval_operand a src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand szop tgt` >> gvs[] >>
  Cases_on `eval_operand v10 tgt` >> gvs[] >>
  `?z. eval_operand v10 src = SOME z` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >> simp[];

val fixed_tac =
  rpt strip_tac >>
  gvs[fixed_source_write_range_def] >>
  Cases_on `eval_operand dst tgt` >> gvs[] >>
  `?x. eval_operand dst src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand v6 tgt` >> gvs[] >>
  `?z. eval_operand v6 src = SOME z` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >> simp[];

val sized_tac =
  rpt strip_tac >>
  gvs[sized_source_write_range_def] >>
  Cases_on `eval_operand dst tgt` >> gvs[] >>
  `?x. eval_operand dst src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand v6 tgt` >> gvs[] >>
  `?z. eval_operand v6 src = SOME z` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand sz tgt` >> gvs[];

Theorem ptr_current_descriptor_range_reflection[local]:
  inst.inst_opcode <> DRET /\ inst.inst_opcode <> LOG /\
  ((mops = mem_read_ops inst /\
    ranges_s = source_memory_read_ranges inst src /\
    ranges_t = source_memory_read_ranges inst tgt) \/
   (mops = mem_write_ops inst /\
    ranges_s = source_memory_write_ranges inst src /\
    ranges_t = source_memory_write_ranges inst tgt)) /\
  (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)) /\
  (!ops sizeop. mops = SOME ops /\ ops.iao_max_size = SOME sizeop ==>
    eval_operand sizeop src = eval_operand sizeop tgt) /\
  MEM (off,len) ranges_t ==>
  ?ops x y. mops = SOME ops /\
    eval_operand ops.iao_ofst src = SOME x /\
    eval_operand ops.iao_ofst tgt = SOME y /\
    off = w2n y /\ MEM (w2n x,len) ranges_s
Proof
  strip_tac >>
  qpat_x_assum `MEM _ ranges_t` mp_tac >>
  simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
       AllCaseEqs()] >>
  Cases_on `inst.inst_opcode` >> simp[] >> strip_tac >>
  gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()] >>
  all_tac
  >~ [`inst.inst_opcode = MLOAD`] >- load_tac
  >~ [`inst.inst_opcode = ILOAD`] >- load_tac
  >~ [`inst.inst_opcode = MCOPY`] >- copy_tac
  >~ [`inst.inst_opcode = RETURN`] >- range_tac
  >~ [`inst.inst_opcode = REVERT`] >- range_tac
  >~ [`inst.inst_opcode = SHA3`] >- range_tac
  >~ [`inst.inst_opcode = CALL`] >- call_tac
  >~ [`inst.inst_opcode = CALL`] >- call_tac
  >~ [`inst.inst_opcode = STATICCALL`] >- call_tac
  >~ [`inst.inst_opcode = STATICCALL`] >- call_tac
  >~ [`inst.inst_opcode = DELEGATECALL`] >- call_tac
  >~ [`inst.inst_opcode = DELEGATECALL`] >- call_tac
  >~ [`inst.inst_opcode = CREATE`] >- call_tac
  >~ [`inst.inst_opcode = CREATE2`] >- call_tac
  >~ [`inst.inst_opcode = EXTCODECOPY`] >- call_tac
  >~ [`inst.inst_opcode = MSTORE`] >- fixed_tac
  >~ [`inst.inst_opcode = ISTORE`] >- fixed_tac
  >~ [`inst.inst_opcode = MSTORE8`] >- fixed_tac
  >> sized_tac
QED

Theorem ptr_current_eval_operands_presence[local]:
  (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)) ==>
  !ops. IS_SOME (eval_operands ops src) = IS_SOME (eval_operands ops tgt)
Proof
  strip_tac >> Induct >- simp[eval_operands_def] >>
  gen_tac >> first_assum (qspec_then `h` mp_tac) >>
  Cases_on `eval_operand h src` >> Cases_on `eval_operand h tgt` >>
  simp[eval_operands_def] >>
  Cases_on `eval_operands ops src` >>
  Cases_on `eval_operands ops tgt` >> gvs[]
QED

Theorem ptr_current_log_range_reflection[local]:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc::rest /\
  REVERSE rest = addr::sz::topics /\
  (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)) /\
  eval_operand sz src = eval_operand sz tgt /\
  MEM (off,len) (source_memory_read_ranges inst tgt) ==>
  ?x y. eval_operand addr src = SOME x /\
    eval_operand addr tgt = SOME y /\ off = w2n y /\
    MEM (w2n x,len) (source_memory_read_ranges inst src)
Proof
  strip_tac >>
  `IS_SOME (eval_operands topics src) = IS_SOME (eval_operands topics tgt)` by
    metis_tac[ptr_current_eval_operands_presence] >>
  gvs[source_memory_read_ranges_def] >>
  Cases_on `eval_operands topics tgt` >> gvs[] >>
  `?zs. eval_operands topics src = SOME zs` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  gvs[memory_range_of_operands_def] >>
  Cases_on `eval_operand addr tgt` >> gvs[] >>
  `?x. eval_operand addr src = SOME x` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  Cases_on `eval_operand sz tgt` >> gvs[] >>
  Cases_on `LENGTH rest = w2n tc + 2` >> gvs[]
QED

Theorem ptr_current_range_transport:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  opaque_use_ok fn /\ label_positions_ok inst /\
  ptr_ledger_erases births TG G /\ FDOM G SUBSET fn_pv P fn /\
  ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels /\ taint_ok fn tn inst src /\
  ((mops = mem_read_ops inst /\
    ranges_s = source_memory_read_ranges inst src /\
    ranges_t = source_memory_read_ranges inst tgt) \/
   (mops = mem_write_ops inst /\
    ranges_s = source_memory_write_ranges inst src /\
    ranges_t = source_memory_write_ranges inst tgt)) /\
  MEM (off,len) ranges_t ==>
  ?off_s. MEM (off_s,len) ranges_s /\
    ((off = off_s /\
      ~(?ops. mops = SOME ops /\ op_prov G ops.iao_ofst <> NONE)) \/
     (?ops x y. mops = SOME ops /\
       eval_operand ops.iao_ofst src = SOME x /\
       eval_operand ops.iao_ofst tgt = SOME y /\
       off_s = w2n x /\ off = w2n y /\
       ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
         (SOME x) (SOME y)))
Proof
  strip_tac >>
  `inst.inst_opcode <> DRET` by (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (strip_tac >> gvs[source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> metis_tac[]) >>
  `!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)` by
    (drule_all ptr_mixed_vars_eval_presence >> simp[]) >>
  `!ops sizeop. mops = SOME ops /\ ops.iao_max_size = SOME sizeop ==>
     eval_operand sizeop src = eval_operand sizeop tgt` by
    (rpt strip_tac >>
     `op_taint tn sizeop = {}` by
       metis_tac[ptr_read_max_size_untainted, ptr_write_max_size_untainted] >>
     `!v. sizeop = Var v ==> v NOTIN fn_pv P fn` by
       metis_tac[ptr_read_max_size_not_pointer, ptr_write_max_size_not_pointer] >>
     `op_prov G sizeop = NONE` by
       (Cases_on `sizeop` >> gvs[op_prov_def] >>
        metis_tac[flookup_thm, SUBSET_DEF]) >>
     `MEM sizeop inst.inst_operands \/ (?w. sizeop = Lit w)` by
       (Cases_on `inst.inst_opcode` >>
        gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()] >>
        metis_tac[MEM_REVERSE, MEM]) >>
     `ptr_nonopaque_operand fn sizeop` by
       metis_tac[EVERY_MEM, ptr_nonopaque_operand_def] >>
     drule_all ptr_mixed_scalar_eval >> simp[]) >>
  Cases_on `inst.inst_opcode = LOG` >>
  TRY (qpat_assum `inst.inst_opcode = LOG` assume_tac >>
       gvs[source_memory_write_ranges_def] >> suspend "log" >> NO_TAC) >>
  `?ops x y. mops = SOME ops /\
    eval_operand ops.iao_ofst src = SOME x /\
    eval_operand ops.iao_ofst tgt = SOME y /\
    off = w2n y /\ MEM (w2n x,len) ranges_s` by
    (irule ptr_current_descriptor_range_reflection >> metis_tac[]) >>
  `MEM ops.iao_ofst inst.inst_operands` by
    (Cases_on `inst.inst_opcode` >>
     gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()]) >>
  `ptr_nonopaque_operand fn ops.iao_ofst` by metis_tac[EVERY_MEM] >>
  `op_taint tn ops.iao_ofst = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     Cases_on `inst.inst_opcode` >>
     gvs[mem_read_ops_def, mem_write_ops_def, AllCaseEqs()] >>
     simp[taint_ok_def] >> metis_tac[]) >>
  drule_all ptr_mixed_vars_eval >> simp[] >> strip_tac >>
  qexists_tac `w2n x` >> simp[] >> metis_tac[]
QED

Resume ptr_current_range_transport[log]:
  gvs[venomWfTheory.inst_wf_def] >>
  `LENGTH (REVERSE rest) = w2n tc + 2` by simp[] >>
  Cases_on `REVERSE rest` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1 `REVERSE rest = addr::sz::topics` >>
  `MEM addr rest /\ MEM sz rest` by metis_tac[MEM_REVERSE, MEM] >>
  `ptr_nonopaque_operand fn addr /\ ptr_nonopaque_operand fn sz` by
    metis_tac[EVERY_MEM] >>
  `op_taint tn addr = {} /\ op_taint tn sz = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `mem_read_ops inst = SOME
     <|iao_ofst := addr; iao_size := SOME sz; iao_max_size := SOME sz|>` by
    (simp[mem_read_ops_def] >> Cases_on `topics` >> simp[]) >>
  `eval_operand sz src = eval_operand sz tgt` by
    (qpat_x_assum `!ops sizeop. _`
       (qspec_then `<|iao_ofst := addr; iao_size := SOME sz;
                      iao_max_size := SOME sz|>` mp_tac) >> simp[]) >>
  `?x y. eval_operand addr src = SOME x /\
    eval_operand addr tgt = SOME y /\ off = w2n y /\
    MEM (w2n x,len) (source_memory_read_ranges inst src)` by
    (irule ptr_current_log_range_reflection >> metis_tac[]) >>
  qpat_x_assum `ptr_nonopaque_operand fn sz` kall_tac >>
  drule_all ptr_mixed_vars_eval >> simp[] >> strip_tac >>
  qexists_tac `w2n x` >> simp[]
QED

Finalise ptr_current_range_transport
