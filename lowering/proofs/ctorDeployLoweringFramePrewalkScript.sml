(* Entry-local opcode boundary for the first O1 prewalk pass.
   This does not establish preservation by the mapped-stage runner. *)
Theory ctorDeployLoweringFramePrewalk
Ancestors
  simplifyCfgInvariant venomInst list

Theorem simplify_cfg_entry_call_free:
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])
    (fn_insts fn) ==>
  EVERY (\i. ~MEM i.inst_opcode
    [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])
    (fn_insts (FST (simplify_cfg_fn_with_labels fn)))
Proof
  strip_tac >> ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> simp[]
QED
