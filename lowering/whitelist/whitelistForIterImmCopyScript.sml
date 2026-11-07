(* Location boundary for the immutable For element preparation.  The boolean
   constructor flag remains explicit: runtime uses DLOAD; constructors ILOAD. *)
Theory whitelistForIterImmCopy
Ancestors
  stmtLowering context compileEnv exprSimTopLevelImmutable exprSimCopy
  immutableCopyExecution
Libs
  monadsyntax

Theorem immutable_iter_small_copy:
  elem_size <= 32 ==>
  compile_iter_elem_copy cenv src dst elem_size LocCode F target_ty elem_ty =
    do v <- compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca src;
       emit_void MSTORE [dst; v]
    od
Proof
  simp[compile_iter_elem_copy_def, compile_ptr_load_def]
QED

Theorem immutable_iter_large_copy:
  32 < elem_size ==>
  compile_iter_elem_copy cenv src dst elem_size LocCode F target_ty elem_ty =
    compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca
      src dst ((elem_size + 31) DIV 32) 0
Proof
  simp[compile_iter_elem_copy_def]
QED

(* Execution, not merely compiler shape: the frame records all old registers
   and static state, while the memory equation retains the constructor read. *)
Theorem immutable_iter_large_run:
  32 < bytes /\
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      z.vs_memory =
        (immutable_transfers F cenv.ce_is_ctor a b ((bytes + 31) DIV 32) 0 s).vs_memory
Proof
  strip_tac >> gvs[immutable_iter_large_copy] >>
  Cases_on `cenv.ce_is_ctor` >> gvs[]
  >- (drule_all copy_ctor_run >> simp[]) >>
  drule_all copy_runtime_run >> simp[]
QED

Theorem immutable_iter_load_run[local]:
  compile_imm_load_word ctor imm src sa = (value,mid) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  (!region. ctor /\ imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?u. copy_runtime_frame sa s mid u /\ copy_old_operand mid value /\
      eval_operand value u = SOME (immutable_copy_read ctor a s) /\
      u.vs_memory = s.vs_memory
Proof
  Cases_on `ctor` >> simp[] >> strip_tac
  >- (drule_all copy_ctor_load >> simp[]) >>
  drule_all copy_runtime_load >> simp[]
QED

Theorem immutable_iter_small_run:
  bytes <= 32 /\
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      z.vs_memory = (mstore (w2n b) (immutable_copy_read cenv.ce_is_ctor a s) s).vs_memory
Proof
  strip_tac >> gvs[immutable_iter_small_copy, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_imm_load_word _ _ _ sa = (value,mid)` >>
  drule_all immutable_iter_load_run >> strip_tac >>
  `copy_old_operand mid dst` by
    (fs[copy_runtime_frame_def] >> metis_tac[copy_old_operand_mono]) >>
  `eval_operand dst u = SOME b` by metis_tac[copy_runtime_frame_operand] >>
  drule_all copy_runtime_store >> strip_tac >>
  qexists_tac `mstore (w2n b) (immutable_copy_read cenv.ce_is_ctor a s) u` >>
  conj_tac >- metis_tac[copy_runtime_frame_trans] >>
  simp[venomStateTheory.mstore_def]
QED

Theorem immutable_iter_copy_run:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      z.vs_memory =
        (if bytes <= 32 then
           mstore (w2n b) (immutable_copy_read cenv.ce_is_ctor a s) s
         else immutable_transfers F cenv.ce_is_ctor a b ((bytes + 31) DIV 32) 0 s).vs_memory
Proof
  strip_tac >> Cases_on `bytes <= 32` >> simp[]
  >- (drule_all immutable_iter_small_run >> simp[]) >>
  `32 < bytes` by decide_tac >>
  drule_all immutable_iter_large_run >> simp[]
QED
