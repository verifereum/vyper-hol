(* Memory and pointer-check interfaces shared by CALL and STATICCALL. *)
Theory callReadinessPtr
Ancestors
  oracleCallStepPtr valueEncoding venomInst venomState bodyPtrDefs stmtSimReturn exprSimTypedAlloc

Theorem mem_bytes_at_read_memory:
  mem_bytes_at off len s.vs_memory = bs ==>
  read_memory off len s = bs
Proof
  simp[venomStateTheory.read_memory_def, valueEncodingTheory.mem_bytes_at_def]
QED

Theorem mem_bytes_at_read_memory_words:
  off < dimword(:256) /\ len < dimword(:256) /\
  mem_bytes_at off len s.vs_memory = bs ==>
  read_memory (w2n (n2w off:bytes32)) (w2n (n2w len:bytes32)) s = bs
Proof
  simp[wordsTheory.w2n_n2w, mem_bytes_at_read_memory]
QED

Theorem canonical_call_access_ok_ptr:
  inst = mk_inst iid (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;ao;az;Var rp;rz]
     else [gas;addr;value;ao;az;Var rp;rz]) outs /\
  eval_operand ao s = SOME aw /\ eval_operand az s = SOME an /\
  eval_operand (Var rp) s = SOME rw /\ eval_operand rz s = SOME rn /\
  (an <> 0w ==> ?p b sz. ao = Var p /\ FLOOKUP G p = SOME (b,sz) /\
    b <= w2n aw /\ w2n aw + w2n an <= b + sz) /\
  ptr_covers G tn rp s (w2n rn) ==>
  access_ok 0 G fn inst s
Proof
  strip_tac >> irule call_access_ok_ptr >>
  Cases_on `stat` >>
  gvs[venomInstTheory.mk_inst_def, bodyPtrDefsTheory.ptr_covers_def,
      venomStateTheory.eval_operand_def] >> metis_tac[]
QED

Theorem canonical_call_taint_ok_ptr:
  inst = mk_inst iid (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;ao;az;ro;rz]
     else [gas;addr;value;ao;az;ro;rz]) outs /\
  EVERY (\op. op_taint tn op = {})
    (if stat then [gas;addr;ao;az;ro;rz]
     else [gas;addr;value;ao;az;ro;rz]) /\
  eval_operand ao s = SOME aw /\ eval_operand az s = SOME an /\
  (!i. w2n aw <= i /\ i < w2n aw + w2n an ==> i NOTIN tn.t_mem) ==>
  taint_ok fn tn inst s
Proof
  strip_tac >> irule call_taint_ok_ptr >>
  Cases_on `stat` >>
  gvs[venomInstTheory.mk_inst_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      memLocDefsTheory.mem_read_ops_def,
      contextCodegenRelTheory.memory_range_of_operands_def,
      AllCaseEqs()] >>
  Cases_on `eval_operand gas s` >> gvs[] >>
  Cases_on `eval_operand addr s` >> gvs[] >>
  Cases_on `eval_operand value s` >> gvs[] >>
  Cases_on `eval_operand ro s` >> gvs[] >>
  Cases_on `eval_operand rz s` >> gvs[] >> metis_tac[]
QED

(* The prefix's placement witness, not its G-site interval alone, supplies
   the nonwrapping address and length domain for a bytes payload. *)
Theorem placed_bytes_payload_word_bounds:
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ~is_word_type ty /\ eval_operand op s = SOME (n2w b) /\
  b < dimword(:256) ==>
  b + 32 + LENGTH bs < dimword(:256) /\
  b + 32 < dimword(:256) /\ LENGTH bs < dimword(:256)
Proof
  strip_tac >> drule_all expr_val_at_bound >>
  simp[loweringPostsTheory.val_footprint_def] >> decide_tac
QED
