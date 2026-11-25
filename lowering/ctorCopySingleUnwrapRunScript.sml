(* The singleton slot-copy endpoint is one installed straight run. *)
Theory ctorCopySingleUnwrapRun
Ancestors
  exprPtrUnwrapEnsureShape abiBufferAllocationCode entryDecodeStructure
  slotCopyExecution bufferAllocationExecution
  abiDecodeStaticProps compileEnv venomInst emitHelperProps exprLoweringProps
  exprSimStorageCopy venomExecSemantics venomState finite_map list rich_list
  loweringStateRelDefs

Theorem ctor_single_unwrap_straight_free:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) ==>
  dec_straight sa sb /\
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all ensure_slot_memory_split >> simp[] >> strip_tac >>
  qpat_x_assum `_ sm = ((),sb)` mp_tac >> simp[comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule compile_alloc_buffer_straight >> strip_tac >>
  drule compile_alloc_buffer_code >> strip_tac >>
  Cases_on `loc = LocStorage` >> gvs[] >>
  drule dec_straight_emit_op >> simp[is_terminator_def] >> strip_tac >>
  drule dec_straight_emit_void >> simp[is_terminator_def] >> strip_tac >>
  conj_tac >- metis_tac[dec_straight_trans] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  fs[dec_straight_def,inst_extends_def] >>
  gvs[emitted_insts_def, DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def,
      arithmeticTheory.SUB_EQ_0, arithmeticTheory.SUB_PLUS]
QED

(* Evaluate just the three known instructions at the semantic endpoint of
   the singleton producer. The intermediate index is supplied by ALLOCA. *)
Theorem ctor_single_unwrap_endpoint_run:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\
  compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
  d = n2w (buffer_allocation_base s sa.cs_next_id) /\
  u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := SUC s.vs_inst_idx /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ eval_operand src s = SOME key /\
  t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a key)
        (update_var (STRING #"%" (toString sm.cs_next_var))
          (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a key) a)
            with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  ?raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\
        t = raw with vs_inst_idx := LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all ensure_slot_memory_single_code >>
  disch_then (qx_choosel_then [`b1`,`m1`] strip_assume_tac) >>
  qpat_x_assum `compile_alloc_buffer nb sa = (b1,m1)` mp_tac >> simp[] >>
  disch_then (CONJUNCTS_THEN SUBST_ALL_TAC) >>
  drule_all ensure_slot_memory_split >> simp[] >> strip_tac >>
  rename1 `compile_alloc_buffer nb sa = (buf,sm)` >>
  drule storage_copy_word_layout >> strip_tac >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> conj_tac >- simp[] >>
     qpat_x_assum `isPREFIX _ _` (mp_tac o REWRITE_RULE [prefix_drop_equiv]) >>
     pure_rewrite_tac[emitted_insts_def] >> disch_then ACCEPT_TAC) >>
  `eval_operand src u = SOME key /\ lookup_var root u = SOME d` by
    (Cases_on `src` >>
     gvs[not_fresh_at_def,eval_operand_def,lookup_var_def,update_var_def,
         FLOOKUP_UPDATE,buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> gvs[]) >>
  `root <> STRING #"%" (toString sm.cs_next_var)` by
    (qpat_assum `buf.buf_operand = Var root` mp_tac >>
     simp[] >> disch_then (SUBST1_TAC o SYM) >>
     simp[ASCIInumbersTheory.toString_inj]) >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  Cases_on `loc = LocStorage` >>
  gvs[run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,
      exec_read1_def,exec_write2_def,slot_copy_word_def,eval_operand_def,
      lookup_var_def,update_var_def,FLOOKUP_UPDATE,sload_def,tload_def,
      contract_storage_def,contract_transient_def,
      mstore_def,write_memory_with_expansion_def]
QED
