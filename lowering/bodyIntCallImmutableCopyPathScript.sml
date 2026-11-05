(* Protected prefixes along the actual emitted immutable-copy family. *)
Theory bodyIntCallImmutableCopyPath
Ancestors
  exprSimCopy immutableMemoryFrame immutableCopyExecution

Theorem immutable_word_transfer_prefix:
  cap <= LENGTH s.vs_memory /\ cap <= w2n b + off /\
  w2n b + off + 32 < dimword (:256) ==>
  TAKE cap (immutable_word_transfer F mode a b off s).vs_memory =
    TAKE cap s.vs_memory /\
  cap <= LENGTH (immutable_word_transfer F mode a b off s).vs_memory
Proof
  strip_tac >>
  `w2n (b + n2w off) = w2n b + off` by
    (`off < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  simp[immutable_word_transfer_def] >>
  conj_tac >- (irule immutable_mstore_prefix >> simp[]) >>
  simp[immutable_mstore_as_write, immutable_write_memory_capacity,
       arithmeticTheory.MAX_DEF]
QED

Theorem immutable_transfers_prefix:
  !n off s.
    cap <= LENGTH s.vs_memory /\ cap <= w2n b + off /\
    w2n b + off + 32*n < dimword (:256) ==>
    TAKE cap (immutable_transfers F mode a b n off s).vs_memory =
      TAKE cap s.vs_memory /\
    cap <= LENGTH (immutable_transfers F mode a b n off s).vs_memory
Proof
  Induct_on `n` >- simp[immutable_transfers_def] >>
  rpt gen_tac >> strip_tac >>
  `TAKE cap (immutable_word_transfer F mode a b off s).vs_memory =
     TAKE cap s.vs_memory /\
   cap <= LENGTH (immutable_word_transfer F mode a b off s).vs_memory` by
    (irule immutable_word_transfer_prefix >> simp[] >> decide_tac) >>
  simp[immutable_transfers_def] >>
  first_x_assum irule >> simp[] >> decide_tac
QED

Theorem compile_imm_copy_prefix_frame:
  compile_imm_copy_to_memory mode imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  cap <= LENGTH s.vs_memory /\ cap <= w2n b + off /\
  w2n b + off + 32*n < dimword (:256) /\
  (mode ==> !region. imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?t. copy_runtime_frame sa s sb t /\
      TAKE cap t.vs_memory = TAKE cap s.vs_memory /\
      cap <= LENGTH t.vs_memory
Proof
  strip_tac >>
  `?t. copy_runtime_frame sa s sb t /\
       t.vs_memory = (immutable_transfers F mode a b n off s).vs_memory` by
    (Cases_on `mode` >> gvs[] >-
       (drule_all copy_ctor_run >> simp[]) >>
     drule_all copy_runtime_run >> simp[]) >>
  qexists `t` >> simp[] >> irule immutable_transfers_prefix >> simp[]
QED

Theorem compile_imm_copy_prefix_run:
  compile_imm_copy_to_memory mode imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  cap <= LENGTH s.vs_memory /\ cap <= w2n b + off /\
  w2n b + off + 32*n < dimword (:256) /\
  (mode ==> !region. imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  copy_runtime_frame sa s sb t /\
  TAKE cap t.vs_memory = TAKE cap s.vs_memory /\
  cap <= LENGTH t.vs_memory
Proof
  strip_tac >> drule_all compile_imm_copy_prefix_frame >>
  strip_tac >> gvs[copy_runtime_frame_def]
QED

Theorem immutable_word_transfer_window:
  off0 + len <= LENGTH s.vs_memory /\
  regions_disjoint off0 len (w2n b + off) 32 /\
  w2n b + off + 32 < dimword (:256) ==>
  mem_bytes_at off0 len (immutable_word_transfer F mode a b off s).vs_memory =
    mem_bytes_at off0 len s.vs_memory /\
  LENGTH s.vs_memory <=
    LENGTH (immutable_word_transfer F mode a b off s).vs_memory
Proof
  strip_tac >>
  `w2n (b + n2w off) = w2n b + off` by
    (`off < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  simp[immutable_word_transfer_def, immutable_mstore_as_write] >>
  conj_tac
  >- (simp[valueEncodingTheory.mem_bytes_at_def,
           listTheory.TAKE_APPEND1, listTheory.LENGTH_DROP,
           immutable_write_memory_capacity,
           byteTheory.LENGTH_word_to_bytes,
           arithmeticTheory.MAX_DEF] >>
      irule immutable_write_memory_disjoint >>
      gvs[compileEnvTheory.regions_disjoint_def,
          byteTheory.LENGTH_word_to_bytes] >> decide_tac) >>
  simp[immutable_write_memory_capacity, arithmeticTheory.MAX_DEF]
QED

Theorem immutable_transfers_window:
  !n off s.
    off0 + len <= LENGTH s.vs_memory /\
    regions_disjoint off0 len (w2n b + off) (32*n) /\
    w2n b + off + 32*n < dimword (:256) ==>
    mem_bytes_at off0 len (immutable_transfers F mode a b n off s).vs_memory =
      mem_bytes_at off0 len s.vs_memory /\
    LENGTH s.vs_memory <=
      LENGTH (immutable_transfers F mode a b n off s).vs_memory
Proof
  Induct_on `n` >- simp[immutable_transfers_def] >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at off0 len (immutable_word_transfer F mode a b off s).vs_memory =
     mem_bytes_at off0 len s.vs_memory /\
   LENGTH s.vs_memory <=
     LENGTH (immutable_word_transfer F mode a b off s).vs_memory` by
    (irule immutable_word_transfer_window >>
     gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  simp[immutable_transfers_def] >>
  first_x_assum (qspecl_then
    [`off+32`, `immutable_word_transfer F mode a b off s`] mp_tac) >>
  impl_tac
  >- (gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  strip_tac >> simp[] >> decide_tac
QED

Theorem compile_imm_copy_window_frame:
  compile_imm_copy_to_memory mode imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  off0 + len <= LENGTH s.vs_memory /\
  regions_disjoint off0 len (w2n b + off) (32*n) /\
  w2n b + off + 32*n < dimword (:256) /\
  (mode ==> !region. imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) ==>
  ?t. copy_runtime_frame sa s sb t /\
      mem_bytes_at off0 len t.vs_memory = mem_bytes_at off0 len s.vs_memory /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  `?t. copy_runtime_frame sa s sb t /\
       t.vs_memory = (immutable_transfers F mode a b n off s).vs_memory` by
    (Cases_on `mode` >> gvs[] >-
       (drule_all copy_ctor_run >> simp[]) >>
     drule_all copy_runtime_run >> simp[]) >>
  qexists `t` >> simp[] >> irule immutable_transfers_window >> simp[]
QED

Theorem compile_imm_copy_window_run:
  compile_imm_copy_to_memory mode imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  off0 + len <= LENGTH s.vs_memory /\
  regions_disjoint off0 len (w2n b + off) (32*n) /\
  w2n b + off + 32*n < dimword (:256) /\
  (mode ==> !region. imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  copy_runtime_frame sa s sb t /\
  mem_bytes_at off0 len t.vs_memory = mem_bytes_at off0 len s.vs_memory /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule_all compile_imm_copy_window_frame >>
  strip_tac >> gvs[copy_runtime_frame_def]
QED
