(* Location boundary for the immutable For element preparation.  The boolean
   constructor flag remains explicit: runtime uses DLOAD; constructors ILOAD. *)
Theory whitelistForIterImmCopy
Ancestors
  stmtLowering context compileEnv exprSimTopLevelImmutable exprSimCopy
  immutableCopyExecution vyperValue valueEncodingProps
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

(* A well-evaluated array rules out the zero-sized element case, even though
   assignable_type by itself is not a positive-size predicate. *)
Theorem immutable_array_element_size_positive:
  evaluate_type tenv (ArrayT ty bd) = SOME (ArrayTV tv bd) ==>
  0 < type_memory_size tv
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[valueEncodingPropsTheory.type_memory_size_slots]
QED

Theorem immutable_iter_transfer_size[local]:
  0 < type_memory_size tv ==>
  (if type_memory_size tv <= 32 then
     mstore (w2n b) (immutable_copy_read ctor a s) s
   else immutable_transfers F ctor a b ((type_memory_size tv + 31) DIV 32) 0 s) =
  immutable_transfers F ctor a b (type_slot_size tv) 0 s
Proof
  simp[type_memory_size_slots] >> strip_tac >>
  Cases_on `type_slot_size tv <= 1`
  >- (`type_slot_size tv = 1` by decide_tac >>
      simp[] >>
      pure_once_rewrite_tac[numLib.num_CONV ``1:num``] >>
      pure_rewrite_tac[immutable_transfers_def, immutable_word_transfer_def] >>
      simp[wordsTheory.WORD_ADD_0]) >>
  simp[arithmeticTheory.ADD_DIV_ADD_DIV]
QED

Theorem immutable_iter_copy_typed_run:
  compile_iter_elem_copy cenv src dst bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func cenv cx es s /\
  immutable_holds cenv cx ty (Value v) a es s /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  w2n b + bytes < dimword (:256) /\
  (cenv.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n b) bytes) /\
  (!region. cenv.ce_is_ctor /\ cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n b) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n b \/ w2n b + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> gvs[] >>
  drule_all immutable_iter_copy_run >> strip_tac >>
  drule immutable_iter_transfer_size >> strip_tac >> gvs[] >>
  drule_all immutable_holds_bounds >> strip_tac >>
  qexists_tac `z` >> simp[] >>
  Cases_on `cenv.ce_is_ctor` >> gvs[]
  >- (drule copy_ctor_contents >> simp[] >> metis_tac[]) >>
  conj_tac >- (drule copy_runtime_contents >> simp[] >> metis_tac[]) >>
  conj_tac >- (drule copy_runtime_contents >> simp[] >> metis_tac[]) >>
  drule_at (Pos (el 3)) runtime_code_copy_memory_frame >> simp[] >> metis_tac[]
QED

Theorem immutable_iter_copy_static_frame:
  copy_runtime_frame sa s sb z ==> copy_static z = copy_static s
Proof
  simp[copy_runtime_frame_def]
QED
