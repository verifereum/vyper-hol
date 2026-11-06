(* Diagnostic representation tests for the checked variable-buffer return.
   These are not a universal child judgment or a body-frame counterexample. *)
Theory bodyPtrStructLitVariableRobust
Ancestors bodyPtrStructLitVariableReturn bodyPtrStructLitInitialization
  representationCleanPtr valueEncoding valueEncodingProps list venomState

Theorem structlit_variable_return_headers:
  mem_word_at 64 (structlit_variable_state 14).vs_memory = 0w /\
  mem_word_at 160 (structlit_variable_state 14).vs_memory = 0w
Proof
  mp_tac structlit_variable_copy_run >>
  Cases_on `run_inst_seq
    (TAKE 14 (SND structlit_variable_compiled).cs_current_insts)
    structlit_variable_initial` >>
  simp[structlit_variable_state_def] >> strip_tac >>
  `mem_bytes_at 64 160 v.vs_memory = mem_bytes_at 64 160 []` by
    (gvs[read_memory_def, mem_bytes_at_def]) >>
  `mem_bytes_at (64+0) 32 v.vs_memory = mem_bytes_at (64+0) 32 [] /\
   mem_bytes_at (64+96) 32 v.vs_memory = mem_bytes_at (64+96) 32 []` by
    (conj_tac >> irule mem_bytes_at_translated_window >>
     qexists_tac `160` >> simp[]) >>
  gvs[mem_word_at_def, GSYM mem_bytes_at_def] >> EVAL_TAC >> simp[]
QED

Theorem structlit_variable_declared_robust:
  !mem. mem_agree_outside (structlit_variable_taint 14).t_mem
    (structlit_variable_state 14).vs_memory mem ==>
    val_in_memory
      (TupleTV [BaseTV (BytesT (Dynamic 33));
                ArrayTV (BaseTV BoolT) (Dynamic 1)])
      (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 64 mem
Proof
  match_mp_tac structlit_return_robust_representation_boundary >>
  simp[structlit_variable_return_headers] >>
  simp[structlit_variable_memory_14] >> rpt strip_tac >> decide_tac
QED

Theorem structlit_variable_narrow_not_robust:
  ~(!mem. mem_agree_outside (structlit_variable_taint 14).t_mem
      (structlit_variable_state 14).vs_memory mem ==>
    val_in_memory
      (TupleTV [BaseTV (BytesT (Dynamic 1));
                ArrayTV (BaseTV BoolT) (Dynamic 1)])
      (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 64 mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside (structlit_variable_taint 14).t_mem
      (structlit_variable_state 14).vs_memory mem ==>
    mem_word_at 128 mem = 0w` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[val_in_memory_def, type_memory_size_def, mem_bytes_at_def] >>
     EVAL_TAC >> simp[]) >>
  drule robust_mem_word_at_clean >>
  disch_then (qspec_then `128` mp_tac) >>
  simp[structlit_variable_memory_14]
QED
