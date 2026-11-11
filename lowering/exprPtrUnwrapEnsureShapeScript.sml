Theory exprPtrUnwrapEnsureShape
Ancestors
  exprSimStorageCopy exprSimAlloc copyExecution fragExec context
  venomInst compileEnv loweringHalt

(* Singleton copies have no generated loop. *)
Theorem ensure_slot_memory_split:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) ==>
  ?buf sm.
    compile_alloc_buffer nb sa = (buf,sm) /\ op = buf.buf_operand /\
    (if n = 1 then
       (do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
           emit_void MSTORE [buf.buf_operand; v] od) sm = ((),sb)
     else ?lab. compile_slot_to_memory src buf.buf_operand n loc sm = (lab,sb))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `n=1` >>
  gvs[compile_ensure_in_memory_def, compile_storage_to_memory_def,
      compile_transient_to_memory_def, compile_slot_to_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Theorem ensure_slot_memory_loop_code:
  (loc = LocStorage \/ loc = LocTransient) /\ n <> 1 /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?buf sm lab.
    compile_alloc_buffer nb sa = (buf,sm) /\ op = buf.buf_operand /\
    compile_slot_to_memory src buf.buf_operand n loc sm = (lab,sb) /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all ensure_slot_memory_split >> simp[] >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl [`buf`, `sm`, `lab`] >> simp[] >>
  irule buffer_alloc_code >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ensure_slot_memory_single_code:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?buf sm.
    compile_alloc_buffer nb sa = (buf,sm) /\ op = buf.buf_operand /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    emitted_insts sm sb =
      [mk_inst sm.cs_next_id (if loc=LocStorage then SLOAD else TLOAD) [src]
         [STRING #"%" (toString sm.cs_next_var)];
       mk_inst (sm.cs_next_id+1) MSTORE
         [buf.buf_operand; Var (STRING #"%" (toString sm.cs_next_var))] []] /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all ensure_slot_memory_split >> simp[] >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  `cs_extends sm sb` by
    (irule storage_copy_suffix_extends >>
     qexistsl [`buf.buf_operand`, `loc`, `1`, `src`, `()`] >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl [`buf`, `sm`] >> simp[] >> conj_tac
  >- (drule storage_copy_word_layout >> simp[]) >>
  irule buffer_alloc_code >> goal_assum (drule_at Any) >> simp[]
QED
