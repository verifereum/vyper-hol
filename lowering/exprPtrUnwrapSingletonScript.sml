(* Singleton copies retain the loaded slot's possibly nonempty taint. *)
Theory exprPtrUnwrapSingleton
Ancestors
  exprPtrUnwrapLoadSegment exprPtrUnwrapStoreSegment exprPtrUnwrapFrames
  ghostPcTransportPtr slotCopyExecution fragGasSeqPtr fragExec bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map
  exprLoweringProps instIdxIndep list valueEncodingProps exprSimStorageCopy
  venomMemProps valueEncoding

Theorem copy_singleton_execution:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand src s = SOME key /\
  root <> out /\ lookup_var root s = SOME addr ==>
  run_inst_seq [mk_inst id load [src] [out];
    mk_inst (id+1) MSTORE [Var root;Var out] []] s =
  OK (mstore (w2n addr) (slot_copy_word load s key)
      (update_var out (slot_copy_word load s key) s))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id load [src] [out]) s =
     OK (update_var out (slot_copy_word load s key) s)` by
    (gvs[] >> simp[step_inst_base_def, mk_inst_def, exec_read1_def,
                   slot_copy_word_def]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var root;Var out] [])
     (update_var out (slot_copy_word load s key) s) =
     OK (mstore (w2n addr) (slot_copy_word load s key)
       (update_var out (slot_copy_word load s key) s))` by
    simp[step_inst_base_def, mk_inst_def, exec_write2_def, eval_operand_def,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[] >> simp[run_inst_seq_def]
QED

