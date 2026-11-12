(* Encoding metadata over the source context's actual type environment. *)
Theory exprExtRequestPlanEntry
Ancestors
  exprExtRequestAbiPlan exprSimHyps exprSimHypsDefs finite_map

Theorem extrequest_encoding_plan:
  expr_sim_inv cenv cx env es /\
  assignable_type (get_tenv cx) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  abi_enc_plan (get_tenv cx) ty
    (type_to_abi_enc_info cenv.ce_struct_fields cenv ty)
Proof
  strip_tac >> irule abi_encode_translated_plan >>
  simp[] >>
  conj_tac >- fs[expr_sim_inv_def] >>
  qexists_tac `get_tenv cx` >> simp[] >>
  conj_tac >- metis_tac[expr_sim_inv_memory_size] >>
  fs[expr_sim_inv_def]
QED
