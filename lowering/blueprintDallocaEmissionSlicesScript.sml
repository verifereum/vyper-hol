Theory blueprintDallocaEmissionSlices
Ancestors
  context emitHelperProps exprLoweringProps venomInst list rich_list

(* Cancel prefixes on instruction lists, without expanding compiler states. *)
Triviality blueprint_dalloca_projection_slices:
  sm.cs_current_insts = sa.cs_current_insts ++ [a] /\
  sn.cs_current_insts = sm.cs_current_insts ++ [b] /\
  sc.cs_current_insts = sn.cs_current_insts ++ insns /\
  sd.cs_current_insts = sc.cs_current_insts ++ [e] /\
  emitted_insts sa sd = sum :: alloc :: (middle ++ [effect]) ==>
  alloc = b /\ alloc :: middle = emitted_insts sm sc /\
  [effect] = emitted_insts sc sd /\ effect = e
Proof
  strip_tac >>
  `emitted_insts sm sc = b :: insns` by
    (qpat_x_assum `sm.cs_current_insts = _` kall_tac >>
     pure_asm_rewrite_tac[emitted_insts_def, GSYM APPEND_ASSOC,
                          APPEND, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  `emitted_insts sc sd = [e]` by
    (qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
     pure_asm_rewrite_tac[emitted_insts_def, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  qpat_x_assum `emitted_insts sa sd = _` mp_tac >>
  pure_asm_rewrite_tac[emitted_insts_def, GSYM APPEND_ASSOC,
                       APPEND, DROP_LENGTH_APPEND] >>
  simp[GSYM SNOC_APPEND]
QED

Theorem blueprint_dalloca_emission_slices:
  emit_op ADD [code;args_len] sa = (size_op,sm) /\
  compile_alloc_dynamic size_op sm = (alloc_ptr,sn) /\
  (?insns. sc.cs_current_insts = sn.cs_current_insts ++ insns) /\
  (case salt of NONE => emit_op CREATE [value;alloc_ptr;size_op]
   | SOME q => emit_op CREATE2 [value;alloc_ptr;size_op;q]) sc = (created,sd) /\
  emitted_insts sa sd = sum :: alloc :: (middle ++ [effect]) ==>
  alloc.inst_operands = [size_op] /\
  alloc :: middle = emitted_insts sm sc /\
  [effect] = emitted_insts sc sd /\
  (case salt of NONE => effect.inst_opcode = CREATE /\ effect.inst_operands = [value;alloc_ptr;size_op]
   | SOME q => effect.inst_opcode = CREATE2 /\ effect.inst_operands = [value;alloc_ptr;size_op;q])
Proof
  Cases_on `salt` >> simp[compile_alloc_dynamic_def] >> strip_tac >>
  ntac 3 (dxrule emitted_insts_emit_op >> strip_tac) >>
  drule_all blueprint_dalloca_projection_slices >> strip_tac >>
  simp[mk_inst_def]
QED
