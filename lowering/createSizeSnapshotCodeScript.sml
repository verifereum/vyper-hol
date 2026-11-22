(* Caller-branch closure of the production snapshot actions. *)
Theory createSizeSnapshotCode
Ancestors
  createSizeCutCode exprLowering context emitHelper compileEnv venomInst

(* Discharge primitive steps, leaving the recursive copies opaque. *)
fun snapshot_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ [LET_DEF, create_cut_code_emit_inst,
                  create_cut_code_emit_op, create_cut_code_emit_void,
                  create_cut_targets_def])),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              conj_tac]);

Theorem create_bytecode_snapshot_case:
  (!src dst n loc a. create_cut_code {} a
    (SND (compile_slot_to_memory src dst n loc a))) /\
  (!ctor imm src dst n off a. create_cut_code {} a
    (SND (compile_imm_copy_to_memory ctor imm src dst n off a))) ==>
  !a. create_cut_code {} a (SND (compile_create_snapshot ce vv ty a))
Proof
  strip_tac >> gen_tac >> simp[compile_create_snapshot_def] >>
  irule create_cut_code_bind >> conj_tac
  >- snapshot_steps [compile_alloc_buffer_def] >>
  simp[] >> irule create_cut_code_ignore_bind >> simp[] >>
  Cases_on `vv_location vv` >> simp[]
  >- snapshot_steps [compile_copy_memory_dynamic_def] >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >>
  snapshot_steps [compile_copy_memory_dynamic_def]
QED

Theorem create_vv_snapshot_case:
  (!ce vv a. create_cut_code {} a (SND (unwrap_value ce vv a))) /\
  (!ce src dst ty ty' a. create_cut_code {} a
    (SND (compile_store_memory ce src dst ty ty' a))) ==>
  !a. create_cut_code {} a (SND (compile_snapshot_vv ce copy vv a))
Proof
  strip_tac >> gen_tac >> simp[compile_snapshot_vv_def] >>
  IF_CASES_TAC >- snapshot_steps [] >>
  IF_CASES_TAC >> snapshot_steps [compile_materialize_vv_def,
                                  compile_alloc_buffer_def]
QED
