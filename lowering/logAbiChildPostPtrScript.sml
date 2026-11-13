(* Pure post transport: instruction cursors affect neither values nor memory. *)
Theory logAbiChildPostPtr
Ancestors
  logAbiEncodePtr logTopicScalarPtr venomState venomExecSemantics words

Theorem abi_child_post_inst_idx:
  lookup_var lv w = SOME (n2w len) /\
  op_taint tm (Var lv) = {} /\ op_prov H (Var lv) = NONE /\
  (!i. (h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
       (p <= i /\ i < p+32) ==> i NOTIN tm.t_mem) /\
  (!i. ~((h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
         (p <= i /\ i < p+32)) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> lookup_var x w = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  mload h w = n2w r /\ mload p w = n2w r + n2w len /\
  mem_agree_outside
    {i | (h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
         (p <= i /\ i < p+32)} w.vs_memory s.vs_memory ==>
  eval_operand (Var lv) (w with vs_inst_idx := k) = SOME (n2w len) /\
  op_taint tm (Var lv) = {} /\ op_prov H (Var lv) = NONE /\
  (!i. (h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
       (p <= i /\ i < p+32) ==> i NOTIN tm.t_mem) /\
  (!i. ~((h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
         (p <= i /\ i < p+32)) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> lookup_var x (w with vs_inst_idx := k) = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  mload h (w with vs_inst_idx := k) = n2w r /\
  mload p (w with vs_inst_idx := k) = n2w (r+len) /\
  mem_agree_outside
    {i | (h <= i /\ i < h+32) \/ (dest <= i /\ i < dest+len) \/
         (p <= i /\ i < p+32)} (w with vs_inst_idx := k).vs_memory s.vs_memory
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!q. mload q (w with vs_inst_idx := k) = mload q w` by simp[mload_def] >>
  asm_simp_tac bool_ss [eval_operand_def, lookup_var_def, venom_state_accfupds] >>
  fs[lookup_var_def, GSYM word_add_n2w] >> metis_tac[]
QED
