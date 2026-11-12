Theory runtimeSymSrcDataExpr
Ancestors
  runtimeSymSrcDataFrame exprLowering context abiEncoder compileEnv emitHelper

Theorem runtime_data_frame_cond[simp]:
  runtime_data_frame (if b then m else n) <=>
  (if b then runtime_data_frame m else runtime_data_frame n)
Proof
  Cases_on `b` >> simp[]
QED

Theorem runtime_data_frame_imm_load[simp]:
  runtime_data_frame (compile_imm_load_word ctor imm off)
Proof
  Cases_on `imm` >> simp[compile_imm_load_word_def]
QED

Theorem runtime_data_frame_ptr_load[simp]:
  runtime_data_frame (compile_ptr_load ctor imm loc off)
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def]
QED

Theorem runtime_data_frame_imm_store[simp]:
  runtime_data_frame (compile_imm_store_word imm off v)
Proof
  Cases_on `imm` >> simp[compile_imm_store_word_def]
QED

Theorem runtime_data_frame_ptr_store[simp]:
  runtime_data_frame (compile_ptr_store ctor imm loc off v)
Proof
  Cases_on `loc` >> simp[compile_ptr_store_def]
QED

Theorem runtime_data_frame_word_copy_base[simp]:
  runtime_data_frame (compile_word_copy_loop_base src dst n l s ctor imm)
Proof
  simp[compile_word_copy_loop_base_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_alloc_buffer[simp]:
  runtime_data_frame (compile_alloc_buffer n)
Proof
  simp[compile_alloc_buffer_def]
QED

Theorem runtime_data_frame_alloc_dynamic[simp]:
  runtime_data_frame (compile_alloc_dynamic n)
Proof
  simp[compile_alloc_dynamic_def]
QED
