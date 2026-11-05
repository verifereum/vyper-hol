(* The fresh single-slot run: intermediate states are private to this proof. *)
Theory bodyPtrStructLitSingleSlotRun
Ancestors
  bodyPtrStructLitSingleSlotMaterialize fragExecPtr allocationPtr fragGasPathPtr
  bodyPtrStructLitFieldStore ptrDiscipline venomState venomInst
  venomExecSemantics finite_map pred_set contextCodegenRel exprSimProps

Theorem single_slot_materialize_run:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit 32w] [out]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) (if tr then TLOAD else SLOAD) [src] [tmp]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) =
    SOME (mk_inst (id+2) MSTORE [Var out; Var tmp] []) /\
  FLOOKUP s.vs_allocas id = NONE /\ s.vs_alloca_next + 32 < dimword (:256) /\
  out <> tmp /\ ~not_fresh_at sa out /\ ~not_fresh_at sa tmp /\
  (!r. src = Var r ==> not_fresh_at sa r) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  ghost_kept cenv es sa G0 tn0 initial G tn /\
  (!aid b sz. FLOOKUP initial.vs_allocas aid = SOME (b,sz) ==>
    b + sz <= s.vs_alloca_next) /\
  (!name b sz. local_region cenv es.scopes initial name b sz ==>
    b + sz <= s.vs_alloca_next) ==>
  ?G' tn' s'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK s') /\
    ghost_inv d cenv cx es G' tn' s' /\
    ghost_kept cenv es sa G0 tn0 initial G' tn' /\
    ptr_covers G' tn' out s' 32 /\
    lookup_var out s' = SOME (n2w s.vs_alloca_next) /\
    (!i. s.vs_alloca_next <= i /\ i < s.vs_alloca_next + 32 ==> i NOTIN tn'.t_mem) /\
    s'.vs_memory = (mstore s.vs_alloca_next
      (if tr then tload a s else sload a s) s).vs_memory /\
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_current_bb = s.vs_current_bb /\ s'.vs_inst_idx = s.vs_inst_idx + 3 /\
    ~s'.vs_halted /\ s'.vs_alloca_next = s.vs_alloca_next + 32 /\
    s'.vs_allocas = s.vs_allocas |+ (id,(s.vs_alloca_next,32)) /\
    (!r. not_fresh_at sa r ==> lookup_var r s' = lookup_var r s) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  qabbrev_tac `ua = update_var out (n2w s.vs_alloca_next)
    (s with <| vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,32));
               vs_alloca_next := s.vs_alloca_next + 32 |>)` >>
  qabbrev_tac `ga = step_prov PG G (mk_inst id ALLOCA [Lit 32w] [out]) ua` >>
  qabbrev_tac `ta = step_taint (mk_inst id ALLOCA [Lit 32w] [out]) s ua tn` >>
  qabbrev_tac `sa1 = (ua with vs_inst_idx := SUC s.vs_inst_idx)` >>
  qabbrev_tac `word = (if tr then tload a s else sload a s)` >>
  qabbrev_tac `ul = update_var tmp word sa1` >>
  qabbrev_tac `gl = step_prov PG ga
    (mk_inst (id+1) (if tr then TLOAD else SLOAD) [src] [tmp]) ul` >>
  qabbrev_tac `tl = step_taint
    (mk_inst (id+1) (if tr then TLOAD else SLOAD) [src] [tmp]) sa1 ul ta` >>
  qabbrev_tac `sl = (ul with vs_inst_idx := SUC sa1.vs_inst_idx)` >>
  qabbrev_tac `tf = step_taint (mk_inst (id+2) MSTORE [Var out; Var tmp] [])
    sl (mstore (w2n (n2w s.vs_alloca_next : bytes32)) word sl) tl` >>
  qabbrev_tac `sf = (mstore (w2n (n2w s.vs_alloca_next : bytes32)) word sl with
    vs_inst_idx := SUC sl.vs_inst_idx)` >>
  `step_inst_base (mk_inst id ALLOCA [Lit 32w] [out]) s = OK ua` by
    (simp[Abbr `ua`, Once step_inst_base_def, mk_inst_def, exec_alloca_def]) >>
  `ga = G |+ (out,(s.vs_alloca_next,32)) /\
   ta = tn with <| t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + 32};
      t_var := tn.t_var |+ (out,{}) |>` by
    (`32 < dimword (:256)` by simp[] >>
     drule_all fresh_alloca_ghost >>
     disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >>
     simp[Abbr `ga`, Abbr `ta`]) >>
  qexistsl [`gl`, `tf`, `sf`] >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "inv" >>
  conj_tac >- suspend "kept" >>
  suspend "post"
QED

Resume single_slot_materialize_run[path]:
  `gas_path_ptr D 0 ctx fn PG G tn s 0 ga ta (OK sa1) /\
   ptr_covers ga ta out sa1 32 /\
   (!r sz. r <> out /\ ptr_covers G tn r s sz ==> ptr_covers ga ta r sa1 sz) /\
   sa1.vs_memory = s.vs_memory /\ sa1.vs_accounts = s.vs_accounts /\
   sa1.vs_transient = s.vs_transient /\ sa1.vs_call_ctx = s.vs_call_ctx /\
   ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm` by
    (irule fresh_buffer_counted >> simp[] >>
     qexists `id` >>
     simp[Abbr `sa1`, Abbr `ua`, Abbr `ga`, Abbr `ta`]) >>
  `eval_operand src sa1 = SOME a /\ op_taint ta src = {}` by
    (Cases_on `src` >> gvs[eval_operand_def, op_taint_def,
       Abbr `sa1`, Abbr `ua`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `lookup_var out sa1 = SOME (n2w s.vs_alloca_next) /\
   sa1.vs_current_bb = s.vs_current_bb /\
   sa1.vs_inst_idx = SUC s.vs_inst_idx /\ ~sa1.vs_halted` by
    simp[Abbr `sa1`, Abbr `ua`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `gas_path_ptr D 0 ctx fn PG ga ta sa1 0 gl tf (OK sf)` by
    (qunabbrev_tac `tf` >> qunabbrev_tac `sf` >>
     `id+2 = (id+1)+1` by decide_tac >>
     qpat_x_assum `id+2 = _` (fn th => pure_rewrite_tac[th]) >>
     irule slot_load_store_counted >> simp[] >>
     qexistsl [`a`, `src`, `tr`] >>
     simp[Abbr `word`, Abbr `gl`, Abbr `tl`, Abbr `sl`,
       tload_def, sload_def, contract_storage_def, contract_transient_def] >>
     metis_tac[]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Resume single_slot_materialize_run[kept]:
  irule ghost_kept_taint_above_frontier >>
  qexistsl [`G`, `s.vs_alloca_next`, `tn`] >> simp[] >>
  qpat_x_assum `Abbrev (sf = _)` kall_tac >>
  qpat_x_assum `Abbrev (ga = _)` kall_tac >>
  qpat_x_assum `Abbrev (ta = _)` kall_tac >>
  Cases_on `tr` >>
  simp[Abbr `gl`, step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
    FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  simp[Abbr `tf`, Abbr `tl`, Abbr `sl`, Abbr `ul`,
    Abbr `sa1`, Abbr `ua`, Abbr `word`, step_prov_def, step_taint_def,
    mk_inst_def, set_var_taint_def, store_taint_def, adopt_reset_def,
    imm_taint_def, op_taint_def, FLOOKUP_UPDATE, lookup_var_def,
    update_var_def, mem_taint_def, set_prov_def, out_prov_def, FLOOKUP_DRESTRICT,
    mstore_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
