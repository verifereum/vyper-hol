(* Direct immutable stores need only the value's meaningful footprint. *)
Theory immutableDeployMeaningfulTransfer
Ancestors
  immutableDeployAssignBytes immutableDeployAssignRanges immutableDeployAssignAdmissible
  exprSimMemoryTransport valueCopyBytes vyperTypeValues
  valueTypingMemoryProps abiCanonicalHeadSize list

Theorem immutable_direct_meaningful_transfer:
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  (sty = dty \/ (is_bytestring_type sty /\ is_bytestring_type dty)) /\
  val_in_memory stv v p mem /\
  val_footprint stv v <= n /\
  mem_bytes_at off n mem' = mem_bytes_at p n mem ==>
  val_in_memory dtv v off mem' /\
  immutable_value_bytes_rel dtv v
    (mem_bytes_at off (type_memory_size dtv) mem')
Proof
  strip_tac >>
  `mem_bytes_at off (val_footprint stv v) mem' =
   mem_bytes_at p (val_footprint stv v) mem` by
    (`!a m. TAKE (val_footprint stv v) (mem_bytes_at a n m) =
        mem_bytes_at a (val_footprint stv v) m` by
       metis_tac[mem_bytes_at_window, arithmeticTheory.ADD_CLAUSES, DROP_0] >>
     metis_tac[]) >>
  `val_wf stv v` by metis_tac[value_has_type_memory_wf] >>
  `val_in_memory stv v off mem'` by
    metis_tac[val_in_memory_relocate_footprint] >>
  `val_in_memory dtv v off mem'` by
    metis_tac[bytestring_val_in_memory_transfer, optionTheory.SOME_11] >>
  simp[] >> irule immutable_memory_bytes >> simp[] >>
  metis_tac[evaluated_immutable_admissible, evaluate_type_well_formed_type_value]
QED
