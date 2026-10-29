(*
 * Statement simulation: a declared local's store, for any one-word value
 * (#637)
 *
 * loweringSlice's stmt_state_rel_declare_word stores val_to_w256 v of a
 * word_value v; a local of an address or bytesN type stores its typed word
 * typed_val_to_w256 instead, which val_in_memory lays out the same way.
 * stmt_state_rel_declare_store takes the stored word and the value's
 * layout as premises, so both kinds of locals use it.
 *
 * TOP-LEVEL:
 *   store_lays_out               — the stored word lays out the value
 *   store_lays_out_word_value, store_lays_out_typed — its two sources
 *   stmt_state_rel_declare_store — a store into a new local's region binds
 *                                  it, for a word laying out the value
 *   typed_word_store             — a typed value of a word type is laid out
 *                                  by its typed word, and well formed
 *   stmt_state_rel_declare_memory — copying a value into a new local's
 *                                  buffer binds the local
 *)

Theory stmtSimDeclStore
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps venomMemDefs loweringSlice exprSim
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperTyping
  venomExecSemantics venomInst venomState

Theorem stmt_state_rel_declare_memory:
  !func cenv cx es s t id p sz w inst v tyv sc rest a.
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
    (!q. q = p \/ ~not_local_ptr cenv es.scopes q ==>
         lookup_var q t = lookup_var q s) /\
    (!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
         mem_bytes_at b sz' s.vs_memory = mem_bytes_at b sz' t.vs_memory) /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel func cenv cx
      (es with scopes :=
         (sc |+ (id, <| assignable := a; type := tyv; value := v; popped := [] |>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >> gs[] >>
  qabbrev_tac `entry = <| assignable := a; type := tyv; value := v; popped := [] |>` >>
  qabbrev_tac `scs' = (sc |+ (id, entry)) :: rest` >>
  `local_ptrs_rel func cenv (sc :: rest) s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!n b sz'. n <> id /\ local_region cenv (sc :: rest) s n b sz' ==>
             regions_disjoint (w2n w) sz b sz'` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `sc :: rest`, `s`] >> simp[]) >>
  `w2n w + sz <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> res_tac >> fs[]) >>
  `lookup_scopes id scs' = SOME entry /\
   !n. n <> id ==> lookup_scopes n scs' = lookup_scopes n (sc :: rest)` by
    simp[Abbr `scs'`, lookup_scopes_def, FLOOKUP_UPDATE] >>
  `local_backed func p s (w2n w) sz` by
    (simp[local_backed_def] >> disj1_tac >> qexists_tac `inst` >> simp[]) >>
  `!n e q sq. lookup_scopes n scs' = SOME e /\
       FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) ==>
       lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> Cases_on `n = id` >- (gvs[] >> metis_tac[]) >>
     `lookup_scopes n (sc :: rest) = SOME e` by metis_tac[] >>
     `~not_local_ptr cenv (sc :: rest) q` by
       (simp[not_local_ptr_def] >> metis_tac[]) >>
     first_x_assum irule >> simp[]) >>
  `local_ptrs_rel func cenv scs' t` by
    (irule local_ptrs_rel_write_local >>
     qexistsl_tac [`entry`, `id`, `p`, `sc :: rest`, `s`, `sz`, `w`] >>
     simp[Abbr `entry`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> gvs[]) >>
  `state_rel func cenv cx (es with scopes := scs') t` by
    (irule state_rel_frame >> conj_tac >- simp[] >>
     qexists_tac `es` >> qexists_tac `s` >>
     simp[vyperStateTheory.evaluation_state_component_equality] >>
     fs[stmt_state_rel_def]) >>
  `alloca_inv t` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_room func t` by
    (irule alloca_room_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  fs[stmt_state_rel_def] >> metis_tac[]
QED

(* Storing a word that lays out v into a new local's region, whose ALLOCA
   ran, binds the local to v in the innermost scope. *)
Theorem stmt_state_rel_declare_store:
  !func cenv cx es s id p sz w inst v tyv sc rest a x.
    stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    32 <= sz /\ type_memory_size tyv = 32 /\
    val_in_memory tyv v (w2n w) (mstore (w2n w) x s).vs_memory /\
    val_wf tyv v ==>
    stmt_state_rel func cenv cx
      (es with scopes :=
         (sc |+ (id, <| assignable := a; type := tyv; value := v; popped := [] |>)) :: rest)
      (mstore (w2n w) x s)
Proof
  rpt strip_tac >>
  `!n b sz'. n <> id /\ local_region cenv es.scopes s n b sz' ==>
     mem_bytes_at b sz' s.vs_memory =
     mem_bytes_at b sz' (mstore (w2n w) x s).vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) sz b sz'` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`, `func`, `inst`, `n`, `p`, `es.scopes`, `s`] >>
        fs[stmt_state_rel_def, state_rel_def]) >>
     `b + sz' <= w2n w \/ w2n w + 32 <= b` by
       (fs[regions_disjoint_def] >> DECIDE_TAC) >>
     irule EQ_SYM >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[] >>
  qexistsl_tac [`inst`, `s`, `w`] >>
  fs[mstore_def, LET_THM, lookup_var_def] >> gs[] >> first_assum ACCEPT_TAC
QED

(* A value of a word type, of that type: its typed word lays it out, and
   it is well formed in one word. *)
Theorem typed_word_store:
  !tenv t tyv v off s.
    is_word_type t /\ evaluate_type tenv t = SOME tyv /\
    value_has_type tyv v ==>
    val_in_memory tyv v off
      (mstore off (typed_val_to_w256 tyv v) s).vs_memory /\
    val_wf tyv v /\ type_memory_size tyv = 32
Proof
  rpt gen_tac >> strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def,
      val_wf_def, type_memory_size_def, mstore_mem_word_at_same]
QED

(* The value v of a declared local of type tyv, from a right-hand side of
   type etv whose operand holds typed_val_to_w256 etv v: storing that word
   lays v out, in one word. *)
Definition store_lays_out_def:
  store_lays_out etv tyv v <=>
    val_wf tyv v /\ type_memory_size tyv = 32 /\
    !off s. val_in_memory tyv v off
              (mstore off (typed_val_to_w256 etv v) s).vs_memory
End

Theorem store_lays_out_word_value:
  !tenv t etv tyv v.
    word_value v /\ type_memory_size tyv = 32 /\
    is_word_type t /\ evaluate_type tenv t = SOME etv ==>
    store_lays_out etv tyv v
Proof
  rpt strip_tac >>
  `typed_val_to_w256 etv v = val_to_w256 v` by
    simp[typed_val_to_w256_word_value] >>
  simp[store_lays_out_def, word_value_in_memory, word_value_wf]
QED

Theorem store_lays_out_typed:
  !tenv t tyv v.
    is_word_type t /\ evaluate_type tenv t = SOME tyv /\
    value_has_type tyv v ==>
    store_lays_out tyv tyv v
Proof
  rpt strip_tac >> simp[store_lays_out_def] >>
  metis_tac[typed_word_store]
QED
