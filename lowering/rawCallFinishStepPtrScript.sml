(* One emitted oracle CALL edge, shared by every raw-call result shape. *)
Theory rawCallFinishStepPtr
Ancestors
  rawCallFinishCodePtr rawCallFinishBridgePtr rawCallOracleProofPtr
  rawCallFinishSuffixPtr

Theorem raw_call_emit_checked_full:
  (if stat then emit_op STATICCALL [gas_op;addr_op;ao_op;az_op;ro_op;rz_op]
   else emit_op CALL [gas_op;addr_op;value_op;ao_op;az_op;ro_op;rz_op]) sa = (Var out,sc) /\
  fn_has_code sa sc func /\
  inst = mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas_op;addr_op;ao_op;az_op;ro_op;rz_op]
     else [gas_op;addr_op;value_op;ao_op;az_op;ro_op;rz_op]) [out] /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr_op s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand ao_op s = SOME ao /\ eval_operand az_op s = SOME az /\
  eval_operand ro_op s = SOME ro /\ eval_operand rz_op s = SOME rz /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME n => n) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  access_ok 0 G func inst s /\ taint_ok func tn inst s /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\ not_local_ptr cenv es.scopes out /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv protected /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x. not_fresh_at protected x ==> x <> out) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint (w2n ro) (w2n rz) a len) /\
  (!aid a len. aid < protected.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n ro) (w2n rz) a len) ==>
  ?s' t H un u.
    exec_ext_call inst s gas aw (if stat then 0w else vw) ao az ro rz stat = OK t /\
    t = update_var out (if outcome.co_success then 1w else 0w) s' /\
    s'.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
    s'.vs_returndata = outcome.co_returnData /\
    H = step_prov PG G inst t /\ un = step_taint inst s t tn /\
    u = t with vs_inst_idx := LENGTH sc.cs_current_insts /\
    gas_path_ptr_edge (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK u) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
    ghost_inv d cenv cx (SND (adopt_call_outcome rq outcome es1)) H un u /\
    ghost_kept cenv es protected G tn s H un /\
    wb_frame cenv es (SND (adopt_call_outcome rq outcome es1)) protected s u /\
    op_taint un (Var out) = {} /\ op_prov H (Var out) = NONE /\
    u.vs_allocas = s.vs_allocas /\
    u.vs_vars = s.vs_vars |+ (out,if outcome.co_success then 1w else 0w) /\
    u.vs_fmp = s.vs_fmp /\
    u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    LENGTH sc.cs_current_insts = SUC s.vs_inst_idx /\ sc.cs_current_bb = s.vs_current_bb` by
    (Cases_on `stat` >> gvs[] >> drule_all raw_call_emit_code >>
     strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]) >>
  mp_tac (oracle_call_checked_full |> Q.INST [`sa` |-> `protected`]) >>
  impl_tac >- (Cases_on `stat` >> gvs[venomInstTheory.mk_inst_def] >> metis_tac[]) >> strip_tac >>
  qexistsl_tac [`s'`, `t`, `H`, `un`, `t with vs_inst_idx := LENGTH sc.cs_current_insts`] >>
  gvs[]
QED

(* Readiness is consumed from the one CALL post, not from a second execution. *)
Theorem raw_call_emit_suffix_ready:
  inst = mk_inst iid (if stat then STATICCALL else CALL)
    (if stat then [gas_op;addr_op;ao_op;az_op;ro_op;rz_op]
     else [gas_op;addr_op;value_op;ao_op;az_op;ro_op;rz_op]) [out] /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr_op s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand ao_op s = SOME ao /\ eval_operand az_op s = SOME az /\
  eval_operand ro_op s = SOME ro /\ eval_operand rz_op s = SOME rz /\
  w2n ro = w2n a+32 /\ w2n rz = cap /\ src <> out /\
  t.vs_vars = s.vs_vars |+ (out,if flag then 1w else 0w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) s).vs_memory /\
  t.vs_returndata = rd /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
  FLOOKUP s.vs_allocas aid = SOME (off,len) /\
  H = step_prov PG G inst t /\ un = step_taint inst s t tn /\
  u = t with vs_inst_idx := LENGTH sc.cs_current_insts ==>
  lookup_var src u = SOME a /\ ptr_covers H un src u capacity /\
  FLOOKUP u.vs_allocas aid = SOME (off,len) /\
  mem_bytes_at (w2n a+32) (LENGTH (TAKE cap rd)) u.vs_memory = TAKE cap rd /\
  (!i. w2n a+32 <= i /\ i < w2n a+32+LENGTH (TAKE cap rd) ==> i NOTIN un.t_mem) /\
  eval_operand (Var out) u = SOME (val_to_w256 (BoolV flag)) /\
  u.vs_returndata = rd
Proof
  strip_tac >>
  mp_tac (oracle_call_suffix_ready |> Q.INST
    [`pc` |-> `LENGTH sc.cs_current_insts`, `result` |-> `if flag then 1w else 0w`]) >>
  impl_tac >- (Cases_on `stat` >> gvs[venomInstTheory.mk_inst_def,
    codegenRelTheory.source_memory_write_ranges_def,
    contextCodegenRelTheory.memory_range_of_operands_def]) >>
  gvs[valueEncodingTheory.val_to_w256_def]
QED

(* Extraction presents a calltype case.  Normalize it once here, keeping
   instruction construction out of the consumer's witness bookkeeping. *)
Theorem raw_call_extracted_checked_full:
  (case (if stat then StaticCall else RegularCall) of
     RegularCall => emit_op CALL [gas_op;addr;value_op;dp;dl;op;rz_op]
   | DelegateCall => emit_op DELEGATECALL [gas_op;addr;dp;dl;op;rz_op]
   | StaticCall => emit_op STATICCALL [gas_op;addr;dp;dl;op;rz_op]) sa = (Var out,sc) /\
  fn_has_code sa sc func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand rz_op s = SOME rz /\
  w2w aw = target /\ w2n (if stat then 0w else vw) =
    (case value_opt of NONE => 0 | SOME n => n) /\ stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  access_ok 0 G func (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas_op;addr;dp;dl;op;rz_op]
     else [gas_op;addr;value_op;dp;dl;op;rz_op]) [out]) s /\
  taint_ok func tn (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas_op;addr;dp;dl;op;rz_op]
     else [gas_op;addr;value_op;dp;dl;op;rz_op]) [out]) s /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ ~cenv.ce_is_ctor /\ not_local_ptr cenv es.scopes out /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv protected /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at protected x) /\
  (!x. not_fresh_at protected x ==> x <> out) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint (w2n ro) (w2n rz) a len) /\
  (!aid a len. aid < protected.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    regions_disjoint (w2n ro) (w2n rz) a len) ==>
  ?s' t H un u.
    exec_ext_call (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;rz_op]
       else [gas_op;addr;value_op;dp;dl;op;rz_op]) [out])
      s gas aw (if stat then 0w else vw) ao az ro rz stat = OK t /\
    t = update_var out (if outcome.co_success then 1w else 0w) s' /\
    s'.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
    s'.vs_returndata = outcome.co_returnData /\
    H = step_prov PG G (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;rz_op]
       else [gas_op;addr;value_op;dp;dl;op;rz_op]) [out]) t /\
    un = step_taint (mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr;dp;dl;op;rz_op]
       else [gas_op;addr;value_op;dp;dl;op;rz_op]) [out]) s t tn /\
    u = t with vs_inst_idx := LENGTH sc.cs_current_insts /\
    gas_path_ptr_edge (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK u) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
    ghost_inv d cenv cx (SND (adopt_call_outcome rq outcome es1)) H un u /\
    ghost_kept cenv es protected G tn s H un /\
    wb_frame cenv es (SND (adopt_call_outcome rq outcome es1)) protected s u /\
    op_taint un (Var out) = {} /\ op_prov H (Var out) = NONE /\
    u.vs_allocas = s.vs_allocas /\
    u.vs_vars = s.vs_vars |+ (out,if outcome.co_success then 1w else 0w) /\
    u.vs_fmp = s.vs_fmp /\
    u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted
Proof
  strip_tac >>
  mp_tac (raw_call_emit_checked_full |> Q.INST
    [`inst` |-> `mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
      (if stat then [gas_op;addr_op;ao_op;az_op;ro_op;rz_op]
       else [gas_op;addr_op;value_op;ao_op;az_op;ro_op;rz_op]) [out]`]
    |> Q.INST [`addr_op` |-> `addr`, `ao_op` |-> `dp`, `az_op` |-> `dl`, `ro_op` |-> `op`]) >>
  impl_tac >- (Cases_on `stat` >> fs[] >> metis_tac[]) >>
  simp[]

QED

val _ = if List.all (null o hyp)
  [raw_call_emit_checked_full, raw_call_emit_suffix_ready,
   raw_call_extracted_checked_full] then ()
  else raise Fail "emitted oracle adapters have kernel hypotheses";

(* The header and CALL output address refer to the same allocation witness.
   Capacity is the whole allocated buffer, not just its returned prefix. *)
Theorem raw_call_allocated_suffix_ready:
  inst = mk_inst iid (if stat then STATICCALL else CALL)
    (if stat then [gas_op;addr_op;ao_op;az_op;ro_op;rz_op]
     else [gas_op;addr_op;value_op;ao_op;az_op;ro_op;rz_op]) [out] /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr_op s = SOME aw /\
  (~stat ==> eval_operand value_op s = SOME vw) /\
  eval_operand ao_op s = SOME ao /\ eval_operand az_op s = SOME az /\
  eval_operand ro_op s = SOME (n2w (ob+32)) /\
  eval_operand rz_op s = SOME (n2w cap) /\
  ob+capacity < dimword(:256) /\ 32 <= capacity /\ cap < dimword(:256) /\
  src <> out /\ lookup_var src s = SOME (n2w ob) /\
  ptr_covers G tn src s capacity /\
  FLOOKUP s.vs_allocas aid = SOME (ob,capacity) /\ aid < sa.cs_next_id /\
  ci_mono protected sa /\ ci_mono sa sc /\ not_fresh_at sa src /\
  not_fresh_at sc out /\
  t.vs_vars = s.vs_vars |+ (out,if flag then 1w else 0w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_memory = (write_memory_with_expansion (ob+32) (TAKE cap rd) s).vs_memory /\
  t.vs_returndata = rd /\ H = step_prov PG G inst t /\
  un = step_taint inst s t tn /\ u = t with vs_inst_idx := LENGTH sc.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv protected /\
  wb_frame cenv es es' protected s u /\ ee.scopes = es.scopes /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint ob capacity a len) /\
  (!id a len. id < protected.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (a,len) ==>
    regions_disjoint ob capacity a len) ==>
  lookup_var src u = SOME (n2w ob) /\ ptr_covers H un src u capacity /\
  local_ptrs_reserved cenv protected /\ ci_mono protected sc /\
  not_fresh_at sc src /\ not_fresh_at sc out /\
  FLOOKUP u.vs_allocas aid = SOME (ob,capacity) /\ aid < sc.cs_next_id /\
  ob <= w2n (n2w ob : bytes32) /\ w2n (n2w ob : bytes32)+capacity <= ob+capacity /\
  32 <= capacity /\ ob+capacity < dimword(:256) /\
  mem_bytes_at (ob+32) (LENGTH (TAKE cap rd)) u.vs_memory = TAKE cap rd /\
  (!i. ob+32 <= i /\ i < ob+32+LENGTH (TAKE cap rd) ==> i NOTIN un.t_mem) /\
  eval_operand (Var out) u = SOME (val_to_w256 (BoolV flag)) /\ u.vs_returndata = rd /\
  (!name a len. local_region cenv ee.scopes u name a len ==>
    regions_disjoint ob capacity a len) /\
  (!id a len. id < protected.cs_next_id /\ FLOOKUP u.vs_allocas id = SOME (a,len) ==>
    regions_disjoint ob capacity a len) /\
  (!name a len. local_region cenv ee.scopes u name a len ==>
    regions_disjoint ob 32 a len) /\
  (!id a len. id < protected.cs_next_id /\ FLOOKUP u.vs_allocas id = SOME (a,len) ==>
    regions_disjoint ob 32 a len)
Proof
  strip_tac >>
  `ob < dimword(:256) /\ ob+32 < dimword(:256)` by decide_tac >>
  mp_tac (raw_call_emit_suffix_ready |> Q.INST
    [`a` |-> `n2w ob`, `ro` |-> `n2w (ob+32)`, `rz` |-> `n2w cap`,
     `off` |-> `ob`, `len` |-> `capacity`]) >>
  impl_tac >- simp[wordsTheory.w2n_n2w] >> strip_tac >>
  `!name a len. local_region cenv es.scopes s name a len <=>
    local_region cenv ee.scopes u name a len` by
    (irule wordArgsPtrTheory.wb_frame_local_regions >> simp[] >> metis_tac[]) >>
  `ci_mono protected sc /\ not_fresh_at sc src /\ aid < sc.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     conj_tac >- metis_tac[compileEnvTheory.cs_extends_trans] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  gvs[wordsTheory.w2n_n2w] >> rpt strip_tac >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> res_tac >> decide_tac
QED
