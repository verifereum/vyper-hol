Theory createSizeRawImmutableFootprint
Ancestors
  exprSimCopy immutableCopyExecution exprLowering exprLoweringProps
  loweringStateRelDefs venomState venomExecSemantics venomMemProps
  exprSimStorageCopy valueEncodingProps words arithmetic

(* The choice of immutable read changes the value, not the store address. *)
Theorem raw_immutable_word_exterior[local]:
  w2n b + off + 32 < dimword (:256) /\
  (at + len <= w2n b + off \/ w2n b + off + 32 <= at) ==>
  mem_bytes_at at len (immutable_word_transfer F ctor a b off s).vs_memory =
  mem_bytes_at at len s.vs_memory
Proof
  strip_tac >>
  `w2n (b + n2w off) = w2n b + off` by
    (Cases_on `b` >> fs[word_add_n2w]) >>
  simp[immutable_word_transfer_def, mstore_mem_bytes_at_disjoint]
QED

Theorem raw_immutable_transfers_exterior[local]:
  !n off s.
    w2n b + off + 32*n < dimword (:256) ==>
    !at len. at + len <= w2n b + off \/ w2n b + off + 32*n <= at ==>
    mem_bytes_at at len (immutable_transfers F ctor a b n off s).vs_memory =
    mem_bytes_at at len s.vs_memory
Proof
  Induct >- simp[immutable_transfers_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once immutable_transfers_def] >>
  `w2n b + (off + 32) + 32*n < dimword (:256) /\
   (at + len <= w2n b + (off + 32) \/ w2n b + (off + 32) + 32*n <= at)` by
    (fs[MULT_SUC] >> decide_tac) >>
  irule raw_immutable_word_exterior >> fs[MULT_SUC] >> decide_tac
QED

Theorem create_raw_immutable_copy_frame:
  compile_imm_copy_to_memory ctor imm src dst n 0 m = ((),b) /\
  copy_old_operand m src /\ copy_old_operand m dst /\
  eval_operand src y = SOME p /\ eval_operand dst y = SOME d /\
  (ctor ==> !op. imm = SOME op ==>
     copy_old_operand m op /\ eval_operand op y = SOME 0w) /\
  w2n d + 32*n < dimword (:256) /\
  run_inst_seq (emitted_insts m b) y = OK (z with vs_inst_idx := y.vs_inst_idx) ==>
  copy_static z = copy_static y /\ LENGTH y.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at m x ==> lookup_var x z = lookup_var x y) /\
  (!off k. off + k <= w2n d \/ w2n d + 32*n <= off ==>
    mem_bytes_at off k z.vs_memory = mem_bytes_at off k y.vs_memory)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH y.vs_memory <= LENGTH z.vs_memory` by
    (drule run_inst_seq_memory_length >> simp[]) >>
  `?t. copy_runtime_frame m y b t /\
       t.vs_memory = (immutable_transfers F ctor p d n 0 y).vs_memory` by
    (Cases_on `ctor` >> gvs[]
     >- (irule copy_ctor_run >> simp[] >> metis_tac[]) >>
     irule copy_runtime_run >> simp[] >> metis_tac[]) >>
  fs[copy_runtime_frame_def] >>
  `t = z with vs_inst_idx := y.vs_inst_idx` by metis_tac[] >>
  gvs[copy_static_def, lookup_var_def] >>
  rpt strip_tac >> irule raw_immutable_transfers_exterior >> simp[]
QED
