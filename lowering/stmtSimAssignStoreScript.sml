(*
 * Statement simulation: a store into a live local (#637)
 *
 * An assignment to a local (Assign, AugAssign) writes the value of a local
 * that is already in scope: write_place on MemoryPlace id [] replaces the
 * entry's value in the scope that holds id, and the lowering stores into
 * the region at the local's pointer, which compile_get_target_ptr hands out
 * without emitting code.  Unlike a declaration (stmtSimDeclStore) the local
 * may sit in any scope, and its region is backed however local_ptrs_rel
 * says; it misses every other live local's region by local_ptrs_rel itself.
 *
 * TOP-LEVEL:
 *   compile_get_target_ptr_local     — a local's target pointer is its
 *                                      pointer operand, and no code
 *   write_place_local                — write_place on a local, on any
 *                                      outcome but a type error
 *   stmt_state_rel_write_local       — rewriting a live local's region with
 *                                      a value laid out at its type relates
 *                                      the scopes write_place leaves
 *   stmt_state_rel_write_local_word  — the same for one MSTORE at the
 *                                      local's base
 *   stmt_state_rel_write_local_store — the same for the typed word of a
 *                                      value the store lays out
 *   assign_local_store_run           — running that MSTORE into a local
 *)

Theory stmtSimAssignStore
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps loweringSlice exprSim stmtSimDeclStore stmtSimDecl
  exprLowering stmtLowering exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperLookup
  venomExecSemantics venomExecProofs venomInst venomState emitHelperProps

Theorem compile_get_target_ptr_local:
  !cenv id op sz st.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar op sz) ==>
    compile_get_target_ptr cenv (NameTarget id) st =
      ((op, SOME LocMemory, OPTION_MAP ValPT (cenv.ce_var_type id)), st)
Proof
  simp[compile_get_target_ptr_def, comp_return_def]
QED

(* write_place on a local: unless it fails with a type error (not in
   scope, not assignable), it replaces the value of id in the scope that
   holds it, and clears the entry's pop history. *)
Theorem write_place_local:
  !cx id v es res es'.
    write_place cx (MemoryPlace id []) v es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?pre env entry rest.
      find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
      entry.assignable /\ res = INL () /\
      es' = es with scopes :=
              pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
              rest
Proof
  rpt gen_tac >>
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       replace_memory_entry_def, evaluate_subscripts_def,
       assign_subscripts_def, set_scopes_def, return_def, raise_def] >>
  Cases_on `find_containing_scope id es.scopes` >>
  simp[raise_def, return_def] >>
  rename1 `SOME q` >> PairCases_on `q` >> Cases_on `q2.assignable` >>
  gvs[assert_def, ignore_bind_def, bind_def, return_def, raise_def,
      set_scopes_def]
QED

(* The local id, held at p in the scope find_containing_scope finds,
   rewritten in t: t is s up to its variables and memory, keeps the
   pointers of live locals, and keeps memory outside the bytes the local's
   type lays out at its base, where it lays out v.  Then t is related to
   the scopes write_place leaves. *)
Theorem stmt_state_rel_write_local:
  !func cenv cx es s t id p sz w pre env entry rest v.
    stmt_state_rel func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q t = lookup_var q s) /\
    (!b n. b + n <= w2n w \/ w2n w + type_memory_size entry.type <= b ==>
           mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t /\
    val_wf entry.type v /\ val_in_memory entry.type v (w2n w) t.vs_memory ==>
    stmt_state_rel func cenv cx
      (es with scopes :=
         pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
      t
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `entry' = entry with <|value := v; popped := []|>` >>
  qabbrev_tac `scs' = pre ++ (env |+ (id, entry')) :: rest` >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
   t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
   t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
   t.vs_immutables = s.vs_immutables /\
   t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_backed func p s (w2n w) sz /\ w2n w + sz <= s.vs_alloca_next /\
   type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
             regions_disjoint (w2n w) sz b sz'` by
    (rpt strip_tac >> fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `lookup_scopes id scs' = SOME entry' /\
   !n. n <> id ==> lookup_scopes n scs' = lookup_scopes n es.scopes` by
    (`es.scopes = pre ++ env :: rest /\ lookup_scopes id pre = NONE` by
       metis_tac[find_containing_scope_structure,
                 find_containing_scope_pre_none] >>
     simp[Abbr `scs'`, lookup_scopes_update] >>
     rpt strip_tac >> simp[lookup_scopes_update_other]) >>
  `!n e q sq. lookup_scopes n scs' = SOME e /\
       FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >>
     qpat_x_assum `!q. ~not_local_ptr _ _ q ==> _` irule >>
     simp[not_local_ptr_def] >>
     Cases_on `n = id` >> gvs[] >> metis_tac[]) >>
  `entry'.type = entry.type /\ entry'.value = v` by simp[Abbr `entry'`] >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
             mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `!n b sz'. n <> id /\ _ ==> regions_disjoint _ _ _ _`
       drule_all >>
     simp[regions_disjoint_def] >> strip_tac >> irule EQ_SYM >>
     qpat_x_assum `!b n. _ ==> mem_bytes_at b n t.vs_memory = _` irule >>
     decide_tac) >>
  `local_ptrs_rel func cenv scs' t` by
    (irule local_ptrs_rel_write_local >>
     qexistsl_tac [`entry'`, `id`, `p`, `es.scopes`, `s`, `sz`, `w`] >>
     rpt conj_tac >> asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  `state_rel func cenv cx (es with scopes := scs') t` by
    (irule state_rel_frame >> conj_tac >- simp[] >>
     qexists_tac `es` >> qexists_tac `s` >>
     simp[vyperStateTheory.evaluation_state_component_equality] >>
     fs[stmt_state_rel_def]) >>
  `alloca_inv t` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_room func t` by
    (irule alloca_room_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  `immutable_alloca_sep func cenv cx (es with scopes := scs') t` by
    (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> reverse conj_tac >- fs[stmt_state_rel_def] >>
     rpt strip_tac >> qexists_tac `id'` >>
     gvs[local_region_def] >>
     qpat_x_assum `!n e q sq. _ ==> lookup_var q t = _` drule_all >>
     strip_tac >> Cases_on `id' = id` >> gvs[] >> metis_tac[]) >>
  fs[stmt_state_rel_def] >> metis_tac[]
QED

(* One MSTORE of a word inside a local's region. *)
Theorem local_mstore_immutables_at:
  stmt_state_rel func cenv cx es s /\
  local_region cenv es.scopes s id b sz /\ k + 32 <= sz ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (mstore (b + k) wd s)
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists_tac `s` >>
  conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
          arithmeticTheory.MAX_DEF] >>
  conj_tac >- simp[mstore_def] >>
  reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >>
     strip_tac >> qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >> metis_tac[]) >>
  irule mstore_mem_bytes_at_disjoint >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

(* One MSTORE of a word that lays v out at the local's base. *)
Theorem local_mstore_immutables[local]:
  stmt_state_rel func cenv cx es s /\
  local_region cenv es.scopes s id b sz /\ 32 <= sz ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (mstore b wd s)
Proof
  strip_tac >>
  qspecl_then [`b`, `0`] mp_tac
    (Q.GENL [`b`, `k`] local_mstore_immutables_at) >>
  simp[] >> disch_then irule >> metis_tac[]
QED

Theorem stmt_state_rel_write_local_word:
  !func cenv cx es s id p sz w pre env entry rest v wd.
    stmt_state_rel func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    type_memory_size entry.type = 32 /\ val_wf entry.type v /\
    val_in_memory entry.type v (w2n w) (mstore (w2n w) wd s).vs_memory ==>
    stmt_state_rel func cenv cx
      (es with scopes :=
         pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
      (mstore (w2n w) wd s)
Proof
  rpt strip_tac >>
  `(mstore (w2n w) wd s with <|vs_vars := s.vs_vars;
                               vs_memory := s.vs_memory|>) = s` by
    simp[mstore_def, LET_THM, venom_state_component_equality] >>
  `!q. ~not_local_ptr cenv es.scopes q ==>
       lookup_var q (mstore (w2n w) wd s) = lookup_var q s` by
    simp[mstore_def, LET_THM, lookup_var_def] >>
  `!b n. b + n <= w2n w \/ w2n w + type_memory_size entry.type <= b ==>
         mem_bytes_at b n (mstore (w2n w) wd s).vs_memory =
         mem_bytes_at b n s.vs_memory` by
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> gvs[]) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `32 <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mstore (w2n w) wd s)` by (drule_all local_mstore_immutables >> simp[]) >>
  irule stmt_state_rel_write_local >> asm_rewrite_tac[] >>
  qexistsl_tac [`p`, `s`, `sz`, `w`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

(* The typed word of a value of the local's type that the store lays out
   (store_lays_out: a word_value, or an address or bytesN of that type). *)
Theorem stmt_state_rel_write_local_store:
  !func cenv cx es s id p sz w pre env entry rest v etv.
    stmt_state_rel func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ store_lays_out etv entry.type v ==>
    stmt_state_rel func cenv cx
      (es with scopes :=
         pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest)
      (mstore (w2n w) (typed_val_to_w256 etv v) s)
Proof
  rw[store_lays_out_def] >> irule stmt_state_rel_write_local_word >>
  simp[] >> metis_tac[]
QED

(* The MSTORE of the typed word of v at a live local's pointer, run: it
   reaches its end related at the scopes write_place leaves, with every
   variable and allocation kept. *)
Theorem assign_local_store_run_framed:
  !ctx func cenv cx es s id p sz pre env entry rest v etv op st st'.
    emit_void MSTORE [Var p; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME (typed_val_to_w256 etv v) /\
    stmt_state_rel func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    store_lays_out etv entry.type v ==>
    ?dw t. lookup_var p s = SOME dw /\
        stmt_state_rel func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        (!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
           mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel func cenv cx es1` >>
  `stmt_state_rel func cenv cx es1
     (mstore (w2n w) (typed_val_to_w256 etv v) s)` by
    (simp[Abbr `es1`] >> irule stmt_state_rel_write_local_store >>
     metis_tac[]) >>
  `frag_exec ctx st st' (\t. t = s)
     (\t. stmt_state_rel func cenv cx es1 t /\
          (!x. lookup_var x t = lookup_var x s) /\
          (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          (!a len. a + len <= w2n w \/ w2n w + 32 <= a ==>
             mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory))
     (\r. F)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     drule emit_void_extends >> strip_tac >>
     `step_inst_base (mk_inst st.cs_next_id MSTORE [Var p; op] []) s =
        OK (mstore (w2n w) (typed_val_to_w256 etv v) s)` by
       (irule step_MSTORE >> simp[eval_operand_def]) >>
     `!a len. a + len <= w2n w \/ w2n w + 32 <= a ==>
        mem_bytes_at a len (mstore (w2n w) (typed_val_to_w256 etv v) s).vs_memory =
        mem_bytes_at a len s.vs_memory` by
       (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
     irule frag_exec_run_inst_seq >>
     fs[same_blocks_def, IS_PREFIX_APPEND3] >>
     simp[run_inst_seq_def, stmt_state_rel_inst_idx] >>
     gvs[mstore_def, LET_THM, lookup_var_def, is_terminator_def] >>
     first_assum ACCEPT_TAC) >>
  drule frag_exec_no_exit_run >> disch_then drule >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists `t` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem assign_local_store_run:
  !ctx func cenv cx es s id p sz pre env entry rest v etv op st st'.
    emit_void MSTORE [Var p; op] st = ((), st') /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME (typed_val_to_w256 etv v) /\
    stmt_state_rel func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    store_lays_out etv entry.type v ==>
    ?t. stmt_state_rel func cenv cx
          (es with scopes :=
             pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) ::
             rest) t /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt strip_tac >> drule_all assign_local_store_run_framed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> qexists `fuel` >> simp[]
QED
