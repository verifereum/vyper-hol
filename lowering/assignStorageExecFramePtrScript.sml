(* Storage-copy frame composition keeps all noncontrol machine fields. *)
Theory assignStorageExecFramePtr
Ancestors
  assignStorageBlockFramePtr assignBasePtrStorageLoop placeDynStorageEffect
  stateFrame venomState venomExecSemantics words arithmetic

Theorem store_copy_prefix_execution_frame:
  !n loc b k s t.
    execution_frame s = execution_frame t ==>
    execution_frame (store_copy_prefix loc b k s n) =
    execution_frame (store_copy_prefix loc b k t n)
Proof
  Induct >- simp[assign_base_store_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!loc b k s t. _`
    (qspecl_then [`loc`,`b`,`k`,`s`,`t`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `loc = LocStorage` >>
  gvs[assign_base_store_prefix_suc,execution_frame_def,sstore_def,tstore_def,
    mload_def,assign_base_store_prefix_frame]
QED

Theorem store_copy_block_execution_frame:
  execution_frame s = execution_frame (store_copy_prefix loc b k s0 i) /\
  execution_frame u = execution_frame
    (store_copy_prefix loc (b+n2w i*32w) (k+n2w i) s j) ==>
  execution_frame u = execution_frame (store_copy_prefix loc b k s0 (i+j))
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`j`,`loc`,`b+n2w i*32w`,`k+n2w i`,
    `s`,`store_copy_prefix loc b k s0 i`] store_copy_prefix_execution_frame) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  metis_tac[place_store_prefix_append]
QED
