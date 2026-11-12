(* Immutable word loads retain payload taint and erase payload provenance. *)
Theory immutableLoadPtr
Ancestors
  immutableOffsetPtr payloadLoadStorePtr exprSimCopy exprSimStorageCopy
  immutableCopyExecution
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  stmtAppendStorageRunPtr fragGasSeqPtr ptrDiscipline venomExecSemantics
  venomInst venomState finite_map words list memLocDefs bodyPtrDefs
  codegenRel contextCodegenRel

Theorem immutable_load_step:
  eval_operand op s = SOME a ==>
  step_inst_base (mk_inst id (if ctor then ILOAD else DLOAD) [op] [out]) s =
    OK (update_var out (immutable_copy_read ctor a s) s)
Proof
  strip_tac >> Cases_on `ctor` >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, immutable_copy_read_def]
QED

Theorem immutable_load_checked:
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  ~ctx_has_dalloca ctx /\
  access_ok 0 G fn (mk_inst id (if ctor then ILOAD else DLOAD) [op] [out]) s ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if ctor then ILOAD else DLOAD) [op] [out]] s
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+
      (out,if ctor then mem_word_taint tn.t_mem (w2n a) else {}))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id (if ctor then ILOAD else DLOAD) [op] [out]) s =
    OK (update_var out (immutable_copy_read ctor a s) s)` by
    simp[immutable_load_step] >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (irule ptr_inst_ok_immutable_load_payload >>
      simp[] >> goal_assum (drule_at Any) >> simp[update_var_def]) >>
  conj_tac
  >- (Cases_on `ctor` >>
      simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def]) >>
  sym_tac >> irule immutable_load_payload_taint >> simp[update_var_def]
QED

Theorem emit_immutable_load_runtime_frame:
  emit_op (if ctor then ILOAD else DLOAD) [op] sa = (r,sb) /\
  eval_operand op s = SOME a ==>
  ?out.
    r = Var out /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id (if ctor then ILOAD else DLOAD) [op] [out]] /\
    not_fresh_at sb out /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    copy_runtime_frame sa s sb
      (update_var out (immutable_copy_read ctor a s) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >> simp[] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_blocks = sa.cs_blocks /\
   sb.cs_next_var = sa.cs_next_var + 1` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  simp[not_fresh_at_def] >>
  `step_inst_base (mk_inst sa.cs_next_id (if ctor then ILOAD else DLOAD)
      [op] [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (immutable_copy_read ctor a s) s)` by simp[immutable_load_step] >>
  simp[copy_runtime_frame_def, same_blocks_def,
       run_inst_seq_def, copy_static_def, update_var_def] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[]) >>
  simp[lookup_var_def, FLOOKUP_UPDATE]
QED

