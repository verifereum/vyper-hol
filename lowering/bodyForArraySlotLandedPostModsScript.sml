(* Observations of the storage item copy relative to the body landing. *)
Theory bodyForArraySlotLandedPostMods
Ancestors
  fragGasOriginPtrLoop slotCopyExecution loweringStateRelDefs
  vyperStorageFootprint vyperState venomState ptrDiscipline finite_map words

Theorem for_array_slot_landed_post_mods:
  lookup_var idx sh = SOME (n2w k) /\
  lookup_var idx u = lookup_var idx sh /\
  FLOOKUP Gu idx = FLOOKUP Gh idx /\
  op_taint tu (Var idx) = op_taint th (Var idx) /\
  eval_operand base_op u = eval_operand base_op sh /\
  eval_operand len_op u = eval_operand len_op sh /\
  (!q. not_fresh_at saL q ==>
    FLOOKUP Gu q = FLOOKUP Gh q /\ op_taint tu (Var q) = op_taint th (Var q)) /\
  slot_copy_external saCopy (Var idx) /\
  slot_copy_external saCopy base_op /\
  slot_copy_external saCopy len_op /\
  (!q. not_fresh_at saL q ==> slot_copy_external saCopy (Var q)) /\
  (!op. slot_copy_external saCopy op ==>
    eval_operand op z = eval_operand op u /\ op_prov Gf op = op_prov Gu op /\
    op_taint tf op = op_taint tu op) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (sh,Gh,th) [] (OK u,Gu,tu)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gf,tf)) ==>
  lookup_var idx z = SOME (n2w k) /\
  FLOOKUP Gf idx = FLOOKUP Gh idx /\ op_taint tf (Var idx) = op_taint th (Var idx) /\
  eval_operand base_op z = eval_operand base_op sh /\
  eval_operand len_op z = eval_operand len_op sh /\
  (!q. not_fresh_at saL q ==>
    FLOOKUP Gf q = FLOOKUP Gh q /\ op_taint tf (Var q) = op_taint th (Var q)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (sh,Gh,th) [] (OK z,Gf,tf))
Proof
  strip_tac >>
  qpat_assum `!op. slot_copy_external saCopy op ==> _`
    (qspec_then `Var idx` (drule_then strip_assume_tac)) >>
  qpat_assum `!op. slot_copy_external saCopy op ==> _`
    (qspec_then `base_op` (drule_then strip_assume_tac)) >>
  qpat_assum `!op. slot_copy_external saCopy op ==> _`
    (qspec_then `len_op` (drule_then strip_assume_tac)) >>
  fs[eval_operand_def,op_prov_def] >>
  conj_tac
  >- (qx_gen_tac `q` >> strip_tac >>
      `slot_copy_external saCopy (Var q)` by simp[] >>
      qpat_assum `!op. slot_copy_external saCopy op ==> _`
        (qspec_then `Var q` (drule_then strip_assume_tac)) >>
      fs[op_prov_def]) >>
  rpt strip_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl [`Gu`,`u`,`tu`] >> simp[]
QED
