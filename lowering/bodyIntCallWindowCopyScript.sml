(* Immutable copy snapshots independent of prior fresh-variable bindings. *)
Theory bodyIntCallWindowCopy
Ancestors
  bodyIntCallForcingCodeRun exprSimCopy immutableCopyExecution
  valueCopy valueEncoding valueEncodingDefs venomExecSemantics venomState compileEnv loweringStateRelDefs
  fragExec emitHelperProps words exprLoweringProps exprLowering
  context

Theorem optional_immutable_copy_snapshot:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. ctor /\ imm = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  0 < n /\
  a+off+32*n < dimword (:256) /\ b+off+32*n < dimword (:256) /\
  (ctor ==> regions_disjoint (a+off) (32*n) (b+off) (32*n)) ==>
  ?t. copy_runtime_frame sa s sb t /\
    t.vs_memory = (write_memory_with_expansion (b+off)
      (mem_bytes_at (a+off) (32*n)
        (if ctor then s.vs_memory else s.vs_data_section)) s).vs_memory
Proof
  strip_tac >> Cases_on `ctor` >> gvs[]
  >- (drule copy_ctor_run >> disch_then (qspec_then `s` mp_tac) >>
      simp[] >> strip_tac >>
      ` (immutable_transfers F T (n2w a) (n2w b) n off s).vs_memory =
          (mcopy (b+off) (a+off) (32*n) s).vs_memory` by
        (irule immutable_memory_transfers_snapshot >> fs[regions_disjoint_def]) >>
      qexists_tac `zz` >> fs[mcopy_def, read_memory_def, GSYM mem_bytes_at_def]) >>
  drule_all copy_runtime_run >> strip_tac >>
  `immutable_transfers F F (n2w a) (n2w b) n off s =
   write_memory_with_expansion (b+off)
     (mem_bytes_at (a+off) (32*n) s.vs_data_section) s` by
    (simp[mem_bytes_at_def] >> irule immutable_runtime_transfers_snapshot >> simp[]) >>
  qexists_tac `s'` >> gvs[]
QED

Theorem optional_immutable_copy_run:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. ctor /\ imm = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  a+off+32*n < dimword (:256) /\ b+off+32*n < dimword (:256) /\
  (ctor ==> regions_disjoint (a+off) (32*n) (b+off) (32*n)) ==>
  ?t. copy_runtime_frame sa s sb t /\
    t.vs_memory = if n = 0 then s.vs_memory else
      (write_memory_with_expansion (b+off)
        (mem_bytes_at (a+off) (32*n)
          (if ctor then s.vs_memory else s.vs_data_section)) s).vs_memory
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_imm_copy_to_memory_def, comp_return_def] >>
      qexists_tac `s` >>
      simp[copy_runtime_frame_def, emitted_insts_def, run_inst_seq_def,
           same_blocks_def]) >>
  `0 < n` by decide_tac >>
  drule_all optional_immutable_copy_snapshot >> simp[]
QED
