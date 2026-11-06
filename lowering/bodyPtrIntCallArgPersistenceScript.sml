Theory bodyPtrIntCallArgPersistence
Ancestors bodyPtrDefs ptrDiscipline venomInst finite_map

Theorem intcall_ptr_buf_transport:
  ptr_buf_ok cenv e op G s /\
  eval_operand op t = eval_operand op s /\ op_prov H op = op_prov G op ==>
  ptr_buf_ok cenv e op H t
Proof
  Cases_on `op` >> simp[ptr_buf_ok_def, op_prov_def] >> metis_tac[]
QED

Theorem intcall_ptr_word_transport:
  is_word_type ty /\ ptr_val_ok cx ty v op G tn s /\
  op_taint un op = op_taint tn op /\ op_prov H op = op_prov G op ==>
  ptr_val_ok cx ty v' op H un t
Proof
  simp[ptr_val_ok_def]
QED
