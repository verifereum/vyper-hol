Theory bodyFullExtCallEncoderWindows
Ancestors
  allocationGrowth abiDecodeStaticProps abiEncoderRegisteredEffect
  exprSimAbiEncodeCallerFrame exprSimAbiEncodeFrameTransfer
  loweringStateRelDefs ptrDiscipline venomMemDefs venomState venomInst
  arithmetic finite_map list pred_set

(* Separate the caller window from the final registered write rows before
   applying the byte and taint frames at the same encoder exit. *)
Theorem extcall_encoder_caller_window:
  allocation_growth q t /\ alloca_inv t /\
  FLOOKUP q.vs_allocas shared = SOME (p,n) /\
  p <= dst /\ dst + m <= p + n /\
  cut <= shared /\ (!i. i IN ids ==> cut <= i) /\
  abi_encoder_registered_effect ids [(dst,m)] q t /\
  (!j. (j < dst \/ dst + m <= j) /\
       (!i r sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (r,sz) ==>
          j < r \/ r + sz <= j) ==>
       (j IN tf.t_mem <=> j IN tq.t_mem)) /\
  ((?old. old < cut /\ FLOOKUP q.vs_allocas old = SOME (b,k)) \/
   (?ptr. local_backed func ptr q b k /\ b + k <= q.vs_alloca_next /\
      (!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN (shared INSERT ids))) \/
   (b + k <= q.vs_alloca_next /\
    (!i r sz. i IN (shared INSERT ids) /\ FLOOKUP q.vs_allocas i = SOME (r,sz) ==>
       b + k <= r \/ r + sz <= b))) ==>
  mem_bytes_at b k t.vs_memory = mem_bytes_at b k q.vs_memory /\
  (!j. b <= j /\ j < b + k /\ j IN tf.t_mem ==> j IN tq.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i r. FLOOKUP q.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r`
    by (rpt strip_tac >> drule_all allocation_growth_old >> simp[]) >>
  `!i r sz. FLOOKUP t.vs_allocas i = SOME (r,sz) /\
      FLOOKUP q.vs_allocas i = NONE ==> q.vs_alloca_next <= r`
    by (rpt strip_tac >> drule_all allocation_growth_new >> simp[]) >>
  `!i r sz. i IN (shared INSERT ids) /\ FLOOKUP t.vs_allocas i = SOME (r,sz) ==>
      b + k <= r \/ r + sz <= b` by
    (qpat_x_assum `(?old. _) \/ _` strip_assume_tac
     >- (rpt gen_tac >> strip_tac >>
         `cut <= i` by (gvs[] >> metis_tac[]) >>
         `old <> i` by decide_tac >>
         `FLOOKUP t.vs_allocas old = SOME (b,k)` by simp[] >>
         qpat_x_assum `alloca_inv t` mp_tac >>
         simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >>
         strip_tac >> metis_tac[])
     >- (rename1 `local_backed func lp q b k` >> rpt gen_tac >> strip_tac >>
         irule abi_encode_initial_local_separation >>
         qexistsl [`t`, `func`, `i`, `shared INSERT ids`, `q`, `lp`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC)
     >> rpt gen_tac >> strip_tac >>
        irule abi_encode_initial_region_separation >>
        qexistsl [`t`, `i`, `shared INSERT ids`, `q`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(?old. _) \/ _` kall_tac >>
  `EVERY (\(r,sz). b + k <= r \/ r + sz <= b) [(dst,m)]` by
    (`b + k <= p \/ p + n <= b` by
       (first_x_assum irule >> qexists `shared` >> simp[]) >>
     simp[] >> decide_tac) >>
  `!i r sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (r,sz) ==>
      b + k <= r \/ r + sz <= b` by
    (rpt gen_tac >> strip_tac >> first_x_assum irule >> qexists `i` >> simp[]) >>
  conj_tac
  >- (irule mem_bytes_at_bytewise >> rpt strip_tac >>
      irule abi_encode_registered_protected_byte >>
      qexistsl [`ids`, `b`, `k`, `[(dst,m)]`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `j < dst \/ dst + m <= j` by
    (qpat_x_assum `EVERY _ [(dst,m)]` mp_tac >> simp[] >> decide_tac) >>
  `!i r sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (r,sz) ==>
      j < r \/ r + sz <= j` by
    (rpt gen_tac >> strip_tac >> first_x_assum drule_all >> decide_tac) >>
  metis_tac[]
QED
