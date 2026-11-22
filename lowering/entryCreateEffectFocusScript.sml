(* Ownership of the effect suffix is independent of the source effect:
   its own native visits cannot stand for a CREATE in an earlier operand. *)
Theory entryCreateEffectFocus
Ancestors
  entryCreateFocusSpec entryCreatePathScope entryCreatePendingScope entryCreateBodyCut
  createSizeCutRegion createSizeCutCode createSizePrefixReplay
  bodySim exprSimAbiGasBridge exprLoweringProps builtinSystem emitHelper compileEnv fragExec
  fragGasOrigin venomExecSemantics venomInst list rich_list pred_set

Theorem create_effect_suffix_cut:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} sm sb /\ fn_has_code sm sb func /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sm sb) ==>
  create_operand_cut sm sb explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> rw[create_operand_cut_def] >>
  `create_cut_region sm sb s` by
    (drule_all create_cut_region_rules >> strip_tac >>
     fs[create_interior_visit_def, create_operand_at_def]) >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region sm sb u` by metis_tac[create_expr_prefix_cut_region] >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_operand_fetch_def, create_operand_at_def, EVERY_MEM] >>
  `MEM inst (frag_code sm sb)` by metis_tac[] >>
  gvs[create_body_cut_def, venomRunBoundedTheory.inst_create_size_ok_def]
QED

Theorem selfdestruct_effect_code:
  compile_selfdestruct op sm = ((),sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sm sb)
Proof
  simp[compile_selfdestruct_def] >> strip_tac >> conj_tac
  >- (`create_cut_code {} sm (SND (emit_void SELFDESTRUCT [op] sm))` by
         simp[create_cut_code_emit_void, create_cut_targets_def] >>
       pop_assum mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  fs[emit_void_def, comp_ignore_bind_def, comp_bind_def, comp_return_def,
     fresh_id_def, emit_def, frag_code_def, emitted_insts_def,
     emitted_blocks_def, mk_inst_def, DROP_LENGTH_APPEND] >>
  gvs[DROP_LENGTH_APPEND]
QED

Theorem raw_revert_effect_code:
  compile_raw_revert op sm = ((),sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sm sb)
Proof
  strip_tac >> conj_tac
  >- (`create_cut_code {} sm (SND (compile_raw_revert op sm))` by
        (simp[NoAsms, compile_raw_revert_def] >> irule create_cut_code_bind >>
         simp[create_cut_code_emit_op, create_cut_targets_def] >>
         irule create_cut_code_bind >>
         simp[create_cut_code_emit_op, create_cut_code_emit_inst, create_cut_targets_def]) >>
      pop_assum mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `compile_raw_revert _ _ = _` mp_tac >>
  simp[compile_raw_revert_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def, frag_code_def,
      emitted_blocks_def, emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC,
      mk_inst_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED

Theorem create_terminal_effect_cut:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\ fn_has_code sm sb func /\
  (compile_raw_revert op sm = ((),sb) \/ compile_selfdestruct op sm = ((),sb)) ==>
  create_operand_cut sm sb explicit ctx func tops cx st0 source (es,s)
Proof
  rpt strip_tac >> irule create_effect_suffix_cut >>
  metis_tac[raw_revert_effect_code, selfdestruct_effect_code]
QED
