(* Source write layout at the post-RHS state, not the original struct value. *)
Theory augAssignPtrFieldWriteSource
Ancestors
  augAssignPtrFieldSource stmtSimAugAssignAttr stmtSimAssignStore
  exprSimDefs exprSimProps vyperState vyperLookup valueEncoding
  exprSimSource stmtSimAssignAttr stmtSimDeclStore finite_map

Theorem augassign_attr_write_all_obs_ptr:
  write_place cx (MemoryPlace id [AttrSubscript fld]) v ee = (res,ff) /\
  (!m. res <> INR (Error (TypeError m))) /\
  expr_sim_inv cenv cx env ee /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (ty,fsz) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  res = INL () /\
  ?pre env1 entry rest fs vals.
    find_containing_scope id ee.scopes = SOME (pre,env1,entry,rest) /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP fs fld = SOME tv /\
    store_lays_out tv tv v /\
    !obs. write_place cx (MemoryPlace id [AttrSubscript fld]) v
      (ee with gas_obs := obs) =
      (INL (),ee with <|scopes := pre ++
        (env1 |+ (id,entry with <|value := StructV (AFUPDKEY fld (K v) vals);
          popped := []|>)) :: rest; gas_obs := obs|>)
Proof
  strip_tac >> drule_all write_attr_local_typed >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule store_lays_out_typed >> simp[] >>
      qexistsl [`ty`, `get_tenv cx`] >> simp[]) >>
  drule write_attr_local_gas_obs_ptr >> simp[]
QED
