(* Open-body boundaries, parameterized by the consumed helper contracts. *)
Theory ctorCallFreeBodies
Ancestors
  list pair compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  ctorCallFreeRules ctorCallFreeCallbacks exprBopLowering
  ctorCallFreeExprBody ctorCallFreeBuiltinBody ctorCallFreeTypeBuiltinBody

Theorem every_state_insts_addmod_names:
  (!ty name st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_name_vv cenv ty name st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) /\
  (!a b m st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_addmod a b m st)))) ==>
  !aty a bty b mty m rty st. EVERY P (state_insts st) ==>
    EVERY P (state_insts
      (SND (compile_addmod_names cenv rty aty a bty b mty m st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_addmod_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[as_stack_val_pair] >> metis_tac[SND]
QED

Theorem every_state_insts_mulmod_names:
  (!ty name st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_name_vv cenv ty name st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) /\
  (!a b m st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_mulmod a b m st)))) ==>
  !aty a bty b mty m rty st. EVERY P (state_insts st) ==>
    EVERY P (state_insts
      (SND (compile_mulmod_names cenv rty aty a bty b mty m st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_mulmod_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[as_stack_val_pair] >> metis_tac[SND]
QED

Theorem every_state_insts_powmod256_names:
  (!ty name st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_name_vv cenv ty name st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) /\
  (!a b st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_pow_mod256 a b st)))) ==>
  !aty a bty b rty st. EVERY P (state_insts st) ==>
    EVERY P (state_insts
      (SND (compile_powmod256_names cenv rty aty a bty b st)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_powmod256_names_def, as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[as_stack_val_pair] >> metis_tac[SND]
QED
