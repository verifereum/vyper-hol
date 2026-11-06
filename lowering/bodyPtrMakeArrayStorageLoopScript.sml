(* Control-edge transport and counted CFG iteration for storage copies. *)
Theory bodyPtrMakeArrayStorageLoop
Ancestors
  bodyPtrMakeArrayStorageSuccessor bodyPtrMakeArrayStorageEndpoints
  bodyPtrMakeArrayStorageControl exprSimStorageCopy ptrDiscipline
  bodyPtrDefs venomState finite_map pred_set words

Theorem storage_loop_test_inv:
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s /\
  tv IN writes /\ tv <> cv /\ dst NOTIN writes /\
  (!x. src = Var x ==> x NOTIN writes) ==>
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (jump_to lbl (update_var tv w s))
Proof
  strip_tac >>
  `dst <> tv /\ (!x. src = Var x ==> x <> tv)` by metis_tac[] >>
  `copy_prefix loc a b n sbase k (jump_to lbl (update_var tv w s))` by
    (simp[copy_prefix_jump, copy_prefix_update_var] >>
     metis_tac[storage_body_inv_prefix]) >>
  Cases_on `src` >>
  gvs[storage_body_inv_def, storage_body_frame_def, ptr_covers_def,
    copy_static_def, jump_to_def, update_var_def, lookup_var_def,
    op_prov_def, op_taint_def, eval_operand_def, FLOOKUP_DRESTRICT,
    FLOOKUP_UPDATE, allocas_from_def] >> metis_tac[]
QED

Theorem storage_loop_jump_inv:
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn (jump_to lbl s)
Proof
  Cases_on `src` >> strip_tac >>
  gvs[storage_body_inv_def, storage_body_frame_def, copy_prefix_def, copy_static_def,
    jump_to_def, lookup_var_def, eval_operand_def, ptr_covers_def,
    allocas_from_def] >> first_assum ACCEPT_TAC
QED
