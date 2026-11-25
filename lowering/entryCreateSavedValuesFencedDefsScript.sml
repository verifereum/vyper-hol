(* Cursor geometry for the guarded saved-values encoder path relation. *)
Theory entryCreateSavedValuesFencedDefs
Ancestors
  entryCreatePathScope exprLoweringProps abiEncoderProps compileEnv
  venomState venomInst list pred_set arithmetic

Definition abi_saved_values_exit_fence_def:
  abi_saved_values_exit_fence func b <=>
    !bb j. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH b.cs_current_insts) = SOME j ==>
      b.cs_next_id <= j.inst_id
End

Definition abi_saved_values_fenced_scope_def:
  abi_saved_values_fenced_scope explicit ctx func a b v z <=>
    (a = b /\ v = z) \/
    (abi_saved_values_exit_fence func a /\
      (abi_saved_values_exit_fence func b ==>
        create_operand_full_scope a b explicit ctx func v [] (OK z)))
End

Theorem abi_saved_values_exit_fence_excludes_frag_ids:
  ci_mono b c /\ abi_saved_values_exit_fence func c /\
  lookup_block c.cs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH c.cs_current_insts) = SOME j ==>
  j.inst_id NOTIN frag_ids a b
Proof
  simp[abi_saved_values_exit_fence_def,ci_mono_def,frag_ids_def] >>
  strip_tac >> res_tac >> decide_tac
QED

Theorem abi_saved_values_fenced_scope_refl:
  !explicit ctx func a v.
    abi_saved_values_fenced_scope explicit ctx func a a v v
Proof
  simp[abi_saved_values_fenced_scope_def]
QED

Theorem abi_saved_values_fenced_scope_trans:
  !explicit ctx func a b c u v z.
    ci_mono a b /\ ci_mono b c /\
    abi_saved_values_fenced_scope explicit ctx func a b u v /\
    abi_saved_values_fenced_scope explicit ctx func b c v z ==>
    abi_saved_values_fenced_scope explicit ctx func a c u z
Proof
  rw[abi_saved_values_fenced_scope_def] >> gvs[] >>
  strip_tac >> disj2_tac >>
  irule (SIMP_RULE bool_ss [APPEND]
    (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
      create_operand_full_scope_prepend)) >>
  qexistsl_tac [`b`,`v`] >>
  metis_tac[ci_mono_def,abi_saved_values_exit_fence_excludes_frag_ids]
QED
