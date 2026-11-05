Theory bodyPtrBytestringBuiltinsPtrFrame
Ancestors
  bodyPtrBytestringBuiltinsPtrRun bodyPtrBytestringBuiltinsSourceFrame
  bodyPtrBytestringBuiltinsOrderRun vyperTypeInvariants bodySim

(* A single-local typing environment for the compatible PtrVar fixture. *)
Definition order_ptr_tenv_def:
  order_ptr_tenv = <|
    current_src := NONE;
    var_types := FEMPTY |+ ("arr", ArrayT (BaseT AddressT) (Dynamic 2));
    var_assignable := FEMPTY |+ ("arr", T);
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
    fn_sigs := FEMPTY; flag_members := FEMPTY; event_fields := FEMPTY |>
End

Theorem order_ptr_frame_body_inv:
  body_inv [] order_frame_unit.cu_context order_ptr_env order_frame_cx
Proof
  mp_tac order_frame_body_inv >>
  simp[bodySimTheory.body_inv_def, order_ptr_env_def] >>
  metis_tac[]
QED

Theorem order_ptr_frame_local_bindings:
  (!id ty. FLOOKUP order_ptr_tenv.var_types id = SOME ty ==>
    ?p sz. FLOOKUP order_ptr_env.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  (!id ty. FLOOKUP order_ptr_tenv.var_types id = SOME ty ==>
    order_ptr_env.ce_var_type id = SOME ty)
Proof
  simp[order_ptr_tenv_def, order_ptr_env_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> EVAL_TAC
QED

Theorem order_ptr_frame_scopes:
  env_scopes_consistent order_ptr_tenv order_frame_cx
    (st with scopes := bodyPtrBytestringBuiltinsOrderProbe$order_probe_scopes)
Proof
  simp[env_scopes_consistent_def, order_ptr_tenv_def,
       bodyPtrBytestringBuiltinsOrderProbeTheory.order_probe_scopes_def,
       vyperStateTheory.lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> EVAL_TAC >> simp[wordsTheory.dimword_def]
QED
