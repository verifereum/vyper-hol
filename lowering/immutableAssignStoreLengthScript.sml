(* Optional-buffer store sequences never shrink memory. *)
Theory immutableAssignStoreLength
Ancestors
  immutableDeployStoreLength immutableDeployAssignExecution context compileEnv
  venomState

Theorem immutable_assign_store_words_memory_length:
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule immutable_store_words_insts >> strip_tac >>
  drule_all immutable_store_seq_memory_length >> simp[]
QED
