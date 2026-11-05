Theory bodyPtrIntCallMaterializeList
Ancestors
  bodyPtrIntCallMaterialize intCallCallee moduleLowering emitHelper words fragExec venomState venomExecSemantics
  finite_map list bodyPtrDefs valueEncoding context compileEnv loweringHalt ptrDiscipline

(* Only completed source bindings are quantified here.  The compile environment
   may still contain MemLoc declarations for all pending parameters. *)
Definition intcall_local_value_def:
  intcall_local_value entry p sz G tn (s:venom_state) <=>
    val_wf entry.type entry.value /\ ptr_covers G tn p s sz /\
    ?w. lookup_var p s = SOME w /\
        w2n w + val_footprint entry.type entry.value <= s.vs_alloca_next /\
        !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
            val_in_memory entry.type entry.value (w2n w) m
End

Definition intcall_completed_def:
  intcall_completed env cenv G tn s <=>
    !name entry. FLOOKUP env name = SOME entry ==>
      ?p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
             intcall_local_value entry p sz G tn s
End

Definition intcall_pending_def:
  intcall_pending env cenv caps G tn (s:venom_state) <=>
    EVERY (\(name,stack,op).
      ?entry off sz w.
        FLOOKUP env name = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) /\
        val_wf entry.type entry.value /\
        type_memory_size entry.type <= sz /\
        eval_operand op s = SOME w /\ op_taint tn op = {} /\
        if stack then
          32 <= sz /\
          (!b m. mem_word_at b m = w ==> val_in_memory entry.type entry.value b m)
        else
          ?p. op = Var p /\ intcall_local_value entry p sz G tn s) caps
End

Theorem intcall_materialize_empty:
  intcall_completed FEMPTY cenv G tn s /\
  intcall_pending env cenv [] G tn s
Proof
  simp[intcall_completed_def, intcall_pending_def]
QED

Theorem intcall_completed_bind:
  intcall_completed env cenv G tn s /\
  intcall_local_value entry p sz G tn s ==>
  intcall_completed (env |+ (name,entry))
    (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var p) sz)) G tn s
Proof
  rw[intcall_completed_def, FLOOKUP_UPDATE] >>
  Cases_on `name' = name` >> gvs[] >> metis_tac[]
QED

Theorem intcall_pending_drop_bind:
  intcall_pending src cenv caps G tn s /\
  EVERY (\(nm,stack,op). nm <> name) caps ==>
  intcall_pending src
    (cenv with ce_vars := cenv.ce_vars |+ (name,loc)) caps G tn s
Proof
  simp[intcall_pending_def, EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `e` >> gvs[] >>
  first_x_assum (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE] >>
  first_x_assum (qspec_then `(e0,e1,e2)` mp_tac) >> simp[]
QED

Theorem intcall_materialize_memory_bind:
  intcall_completed done cenv G tn s /\
  intcall_pending src cenv ((name,F,Var p)::caps) G tn s /\
  EVERY (\(nm,stack,op). nm <> name) caps /\
  FLOOKUP src name = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) ==>
  intcall_completed (done |+ (name,entry))
    (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var p) sz)) G tn s /\
  intcall_pending src
    (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var p) sz)) caps G tn s
Proof
  rpt strip_tac
  >- (irule intcall_completed_bind >>
      gvs[intcall_pending_def] >> metis_tac[]) >>
  irule intcall_pending_drop_bind >> gvs[intcall_pending_def]
QED

Theorem intcall_materialize_memory_computation:
  FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) ==>
  materialize_internal_params cenv [(name,F,Var p)] cs =
    (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var p) sz),cs)
Proof
  simp[materialize_internal_params_def, comp_return_def, compile_env_component_equality]
QED

Theorem intcall_completed_ghost_inv:
  intcall_completed env cenv G tn s /\
  (!name. lookup_scopes name es.scopes = FLOOKUP env name) /\
  return_buf_ptr d cenv G tn s /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> op_taint tn (Var x) = {}) /\
  stor_taint_ok cx tn s ==>
  ghost_inv d cenv cx es G tn s
Proof
  rw[ghost_inv_def] >>
  fs[intcall_completed_def] >>
  first_x_assum drule >> strip_tac >>
  gvs[intcall_local_value_def] >> metis_tac[]
QED

(* Exact endpoint of the two-instruction scalar block, without its path.
   Keeping this interface separate lets both actual and auxiliary PG use
   the same preservation proof, never a safety-transfer argument. *)
Definition intcall_materialize_end_def:
  intcall_materialize_end id n out word s s1 G tn t G' tn' <=>
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\ 32 <= n /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    t = (mstore s.vs_alloca_next word s1 with vs_inst_idx := s.vs_inst_idx + 2) /\
    G' = G |+ (out,(s.vs_alloca_next,n)) /\
    tn'.t_var = tn.t_var |+ (out,{}) /\
    tn'.t_mem = (tn.t_mem UNION {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+n})
      DIFF {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
End

Theorem intcall_materialize_end_vars:
  intcall_materialize_end id n out word s s1 G tn t G' tn' ==>
  !x. x <> out ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)
Proof
  rpt gen_tac >> strip_tac >> fs[intcall_materialize_end_def] >>
  match_mp_tac (Q.INST [`j` |-> `s.vs_inst_idx + 2`] intcall_materialize_old_vars) >> simp[]
QED

Theorem intcall_materialize_end_frontier:
  intcall_materialize_end id n out word s s1 G tn t G' tn' ==>
  t.vs_alloca_next = s.vs_alloca_next + n
Proof
  simp[intcall_materialize_end_def] >> rpt strip_tac >>
  drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
  simp[mstore_def, update_var_def]
QED

Theorem intcall_materialize_end_local:
  intcall_materialize_end id n out word s s1 G tn t G' tn' /\
  intcall_local_value entry p sz G tn s /\ p <> out ==>
  intcall_local_value entry p sz G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  drule intcall_materialize_end_vars >> disch_then (qspec_then `p` mp_tac) >>
  simp[] >> strip_tac >>
  drule intcall_materialize_end_frontier >> strip_tac >>
  fs[intcall_local_value_def] >>
  conj_tac >- gvs[ptr_covers_def] >>
  match_mp_tac (Q.INST [`j` |-> `s.vs_inst_idx + 2`] intcall_materialize_old_robust) >>
  fs[intcall_materialize_end_def] >> metis_tac[]
QED

Theorem intcall_materialize_end_completed:
  intcall_materialize_end id n out word s s1 G tn t G' tn' /\
  intcall_completed env cenv G tn s /\
  (!name p sz. FLOOKUP env name <> NONE /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) ==>
  intcall_completed env cenv G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  fs[intcall_completed_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  `p <> out` by (strip_tac >> gvs[] >> first_x_assum drule >> simp[]) >>
  qexistsl_tac [`p`,`sz`] >> simp[] >>
  irule intcall_materialize_end_local >> metis_tac[]
QED

Theorem intcall_materialize_end_operand:
  intcall_materialize_end id n out word s s1 G tn t G' tn' /\ op <> Var out ==>
  eval_operand op t = eval_operand op s /\ op_taint tn' op = op_taint tn op
Proof
  rpt gen_tac >> strip_tac >>
  drule intcall_materialize_end_vars >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def, op_taint_def] >>
  fs[intcall_materialize_end_def] >>
  drule_all step_alloca_fresh >> disch_then (qspec_then `out` mp_tac) >>
  simp[mstore_def, update_var_def]
QED

Theorem intcall_materialize_end_pending:
  intcall_materialize_end id n out word s s1 G tn t G' tn' /\
  intcall_pending src cenv caps G tn s /\
  EVERY (\(name,stack,op). op <> Var out) caps ==>
  intcall_pending src cenv caps G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  fs[intcall_pending_def, EVERY_MEM] >>
  qx_gen_tac `cap` >> strip_tac >> PairCases_on `cap` >>
  first_x_assum (qspec_then `(cap0,cap1,cap2)` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `(cap0,cap1,cap2)` mp_tac) >> simp[] >> strip_tac >>
  `eval_operand cap2 t = eval_operand cap2 s /\ op_taint tn' cap2 = op_taint tn cap2` by
    (irule intcall_materialize_end_operand >> metis_tac[]) >>
  qexistsl_tac [`entry`,`off`,`sz`,`w`] >> simp[] >>
  Cases_on `cap1` >> gvs[] >>
  irule intcall_materialize_end_local >> metis_tac[]
QED

Theorem intcall_materialize_end_extend:
  intcall_materialize_end id n out word s s1 G tn t G' tn' /\
  intcall_completed done cenv G tn s /\
  (!name p sz. FLOOKUP done name <> NONE /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  intcall_pending src cenv caps G tn s /\
  EVERY (\(nm,stack,op). nm <> name /\ op <> Var out) caps /\
  intcall_local_value entry out n G' tn' t ==>
  intcall_completed (done |+ (name,entry))
    (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var out) n)) G' tn' t /\
  intcall_pending src
    (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var out) n)) caps G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  `intcall_completed done cenv G' tn' t` by
    (irule intcall_materialize_end_completed >> metis_tac[]) >>
  `EVERY (\(nm,stack,op). op <> Var out) caps /\
   EVERY (\(nm,stack,op). nm <> name) caps` by
    (fs[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
     first_x_assum drule >> simp[]) >>
  `intcall_pending src cenv caps G' tn' t` by
    (irule intcall_materialize_end_pending >> metis_tac[]) >>
  conj_tac >- (irule intcall_completed_bind >> simp[]) >>
  irule intcall_pending_drop_bind >> simp[]
QED

Theorem intcall_materialize_end_new_local:
  intcall_materialize_end id n out word s s1 G tn t G' tn' /\
  s.vs_alloca_next < dimword (:256) /\
  val_wf entry.type entry.value /\ val_footprint entry.type entry.value <= n /\
  ptr_covers G' tn' out t n /\
  (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
       val_in_memory entry.type entry.value s.vs_alloca_next m) ==>
  intcall_local_value entry out n G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  drule intcall_materialize_end_frontier >> strip_tac >>
  `lookup_var out t = SOME (n2w s.vs_alloca_next)` by
    (fs[intcall_materialize_end_def] >>
     mp_tac (Q.SPECL [`id`,`n`,`out`,`s`] step_alloca_fresh) >> simp[] >>
     strip_tac >> gvs[mstore_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[intcall_local_value_def, w2n_n2w]
QED

Theorem intcall_materialize_end_metadata:
  intcall_materialize_end id n out word s s1 G tn t G' tn' /\
  (!k. cenv.ce_return_buf <> SOME (PtrVar (Var out) k)) /\
  (!k. cenv.ce_return_pc <> SOME (PtrVar (Var out) k)) /\
  return_buf_ptr d cenv G tn s /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn (Var x) = {}) /\
  stor_taint_ok cx tn s ==>
  return_buf_ptr d cenv G' tn' t /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> op_taint tn' (Var x) = {}) /\
  stor_taint_ok cx tn' t
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST [`j` |-> `s.vs_inst_idx + 2`] intcall_materialize_metadata) >>
  fs[intcall_materialize_end_def] >> metis_tac[]
QED

Theorem intcall_scalar_materialize_extend_path:
  FLOOKUP s.vs_allocas id = NONE /\
  s.vs_alloca_next + n < dimword (:256) /\ 32 <= n /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  op <> Var out /\ eval_operand op s = SOME word /\ op_taint tn op = {} /\
  (!b m. mem_word_at b m = word ==> val_in_memory entry.type entry.value b m) /\
  val_wf entry.type entry.value /\ val_footprint entry.type entry.value <= n /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit (n2w n)] [out];
            mk_inst (id+1) MSTORE [Var out;op] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  intcall_completed done cenv G tn s /\
  (!nm p sz. FLOOKUP done nm <> NONE /\
     FLOOKUP cenv.ce_vars nm = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  intcall_pending src cenv caps G tn s /\
  EVERY (\(nm,stack,op). nm <> name /\ op <> Var out) caps ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    intcall_materialize_end id n out word s s1 G tn t G' tn' /\
    intcall_completed (done |+ (name,entry))
      (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var out) n)) G' tn' t /\
    intcall_pending src
      (cenv with ce_vars := cenv.ce_vars |+ (name,PtrVar (Var out) n)) caps G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_scalar_materialize_path >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `intcall_materialize_end id n out word s s1 G tn t G' tn'` by
    (simp[intcall_materialize_end_def] >> decide_tac) >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  `intcall_local_value entry out n G' tn' t` by
    (irule intcall_materialize_end_new_local >> metis_tac[]) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> simp[] >>
  irule intcall_materialize_end_extend >> metis_tac[]
QED
