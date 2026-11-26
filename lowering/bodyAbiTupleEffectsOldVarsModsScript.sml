(* Compose the observations of old variables and scalar taint across a row cut. *)
Theory bodyAbiTupleEffectsOldVarsMods
Ancestors
  bodyAbiTupleBufferStateMods exprLoweringProps freshWrites

Theorem abi_tuple_effects_old_vars_trans_mods:
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu c z Gz tz ==>
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    c z Gz tz e q Ge tq ==>
  (!x. not_fresh_at a x ==>
    (!w. lookup_var x u = SOME w ==> lookup_var x q = SOME w) /\
    FLOOKUP Ge x = FLOOKUP Gu x /\ op_taint tq (Var x) = op_taint tu (Var x)) /\
  tq.t_stor = tu.t_stor /\ tq.t_trans = tu.t_trans /\ tq.t_imm = tu.t_imm
Proof
  pure_rewrite_tac[abi_tuple_row_effects_mods_def] >>
  ntac 2 (disch_then strip_assume_tac) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `not_fresh_at c x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists `a` >> fs[ci_mono_def]) >>
      qpat_assum `!x. not_fresh_at a x ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!x. not_fresh_at c x ==> _` (drule_then strip_assume_tac) >>
      metis_tac[]) >>
  simp[]
QED
