Theory concretizePtrDallocaHistoricalRead
Ancestors
  concretizePtrDallocaHistoricalMemory concretizePtrDallocaReadChannels
  concretizePtrDallocaCopyRead concretizePtrPairedPrefix
  concretizePtrPairedFields list rich_list arithmetic finite_map words pred_set

(* Each read uses the recorded departure snapshot. Recursive memory
   assumptions range only over source indices strictly before i. *)
Theorem ptr_dalloca_historical_demanded_reflection:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG0 v = SOME (token,aid) /\
  FLOOKUP (EL i h).po_prov v = SOME (b,sz) /\
  FLOOKUP bw0 (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward (EL i h).po_fn (EL i h).po_state /\
  (EL i h).po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) (EL i h).po_inst.inst_operands /\
  (inst_read_op (EL i h).po_inst = SOME (Var v) \/ (EL i h).po_inst.inst_opcode = INVOKE) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k IN (EL q ht).po_taint.t_mem ==> b+k IN (EL i h).po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  drule ptr_paired_memory_samples >> strip_tac >>
  `i < LENGTH h /\ q < LENGTH ht /\ LENGTH H = LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  `EL (EL q done) H = (ts0,rw0,bw0,PT0,TG0,sv0,en0)` by metis_tac[] >>
  drule_all ptr_dalloca_memory_departure_cut >> strip_tac >>
  mp_tac (Q.INST
    [`h` |-> `TAKE (SUC i) h`, `endpoint` |-> `EL i h`,
     `ht` |-> `TAKE (SUC q) ht`, `at` |-> `EL q ht`,
     `done` |-> `TAKE q done`, `tokens` |-> `ts0`, `registry` |-> `rw0`,
     `births` |-> `bw0`, `PT` |-> `PT0`, `TG` |-> `TG0`,
     `saved` |-> `sv0`, `entries` |-> `en0`,
     `H` |-> `TAKE (SUC i) H`,
     `ws` |-> `FILTER (\(n,j,rho). j < q) ws`]
    ptr_dalloca_demanded_reflection_memory) >>
  impl_tac
  >- (simp[LENGTH_TAKE, EL_TAKE] >> rpt conj_tac >>
      rpt strip_tac >> gvs[EL_TAKE] >> first_x_assum irule >> simp[]
      >> (fn g =>
        if is_exists (snd g) then
          (rename1 `FLOOKUP bw (tok,id) = SOME (read_base,read_size)` >>
           qexistsl [`id`,`pos`,`read_size`,`tok`,`u`] >> simp[]) g
        else decide_tac g)) >>
  simp[]
QED

Theorem ptr_dalloca_historical_mload_read_mask:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (EL i h).po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' (EL q ht) zt ==>
  ?op x y. (EL i h).po_inst.inst_operands = [op] /\
    eval_operand op (EL i h).po_state = SOME x /\
    eval_operand op (EL q ht).po_state = SOME y /\
    mem_word_taint (EL q ht).po_taint.t_mem (w2n y) SUBSET
      mem_word_taint (EL i h).po_taint.t_mem (w2n x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_memory_samples >> strip_tac >>
  `i < LENGTH h /\ q < LENGTH ht /\ LENGTH H = LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  `EL (EL q done) H = (ts0,rw0,bw0,PT0,TG0,sv0,en0)` by metis_tac[] >>
  drule_all ptr_dalloca_memory_departure_cut >> strip_tac >>
  mp_tac (Q.INST
    [`h` |-> `TAKE (SUC i) h`, `endpoint` |-> `EL i h`,
     `ht` |-> `TAKE (SUC q) ht`, `at` |-> `EL q ht`,
     `done` |-> `TAKE q done`, `tokens` |-> `ts0`, `registry` |-> `rw0`,
     `births` |-> `bw0`, `PT` |-> `PT0`, `TG` |-> `TG0`,
     `saved` |-> `sv0`, `entries` |-> `en0`,
     `H` |-> `TAKE (SUC i) H`,
     `ws` |-> `FILTER (\(n,j,rho). j < q) ws`]
    ptr_dalloca_mload_read_mask_memory) >>
  impl_tac
  >- (simp[LENGTH_TAKE, EL_TAKE] >> rpt conj_tac >>
      rpt strip_tac >> gvs[EL_TAKE] >> first_x_assum irule >> simp[]
      >> (fn g =>
        if is_exists (snd g) then
          (rename1 `FLOOKUP bw (tok,id) = SOME (read_base,read_size)` >>
           qexistsl [`id`,`pos`,`read_size`,`tok`,`u`] >> simp[]) g
        else decide_tac g)) >>
  simp[]
QED

Theorem ptr_dalloca_historical_mcopy_read_mask:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  q < LENGTH done /\ i = EL q done /\
  EL i H = (ts0,rw0,bw0,PT0,TG0,sv0,en0) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL i h).po_taint.t_mem) /\
  (EL i h).po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' (EL q ht) zt ==>
  ?dop sop nop d r dt rt n.
    (EL i h).po_inst.inst_operands = [dop;sop;nop] /\
    eval_operand dop (EL i h).po_state = SOME d /\
    eval_operand sop (EL i h).po_state = SOME r /\
    eval_operand nop (EL i h).po_state = SOME n /\
    eval_operand dop (EL q ht).po_state = SOME dt /\
    eval_operand sop (EL q ht).po_state = SOME rt /\
    eval_operand nop (EL q ht).po_state = SOME n /\
    (!k. k < w2n n ==> w2n rt+k IN (EL q ht).po_taint.t_mem ==>
      w2n r+k IN (EL i h).po_taint.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_memory_samples >> strip_tac >>
  `i < LENGTH h /\ q < LENGTH ht /\ LENGTH H = LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  `EL (EL q done) H = (ts0,rw0,bw0,PT0,TG0,sv0,en0)` by metis_tac[] >>
  drule_all ptr_dalloca_memory_departure_cut >> strip_tac >>
  mp_tac (Q.INST
    [`h` |-> `TAKE (SUC i) h`, `endpoint` |-> `EL i h`,
     `ht` |-> `TAKE (SUC q) ht`, `at` |-> `EL q ht`,
     `done` |-> `TAKE q done`, `tokens` |-> `ts0`, `registry` |-> `rw0`,
     `births` |-> `bw0`, `PT` |-> `PT0`, `TG` |-> `TG0`,
     `saved` |-> `sv0`, `entries` |-> `en0`,
     `H` |-> `TAKE (SUC i) H`,
     `ws` |-> `FILTER (\(n,j,rho). j < q) ws`]
    ptr_dalloca_mcopy_read_mask_memory) >>
  impl_tac
  >- (simp[LENGTH_TAKE, EL_TAKE] >> rpt conj_tac >>
      rpt strip_tac >> gvs[EL_TAKE] >> first_x_assum irule >> simp[]
      >> (fn g =>
        if is_exists (snd g) then
          (rename1 `FLOOKUP bw (tok,id) = SOME (read_base,read_size)` >>
           qexistsl [`id`,`pos`,`read_size`,`tok`,`u`] >> simp[]) g
        else decide_tac g)) >>
  simp[]
QED
