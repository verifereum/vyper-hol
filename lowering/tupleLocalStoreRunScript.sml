(*
 * The stores of a tuple's elements into locals, word or memory-backed,
 * against the source's writes; a store into x_i keeps the tuple's unread
 * elements.
 *
 * TOP-LEVEL:
 *   tuple_store_mixed_locals_run — the stores against the writes
 *)
Theory tupleLocalStoreRun
Ancestors
  tupleLocalStoreProps stmtSimAssignStore stmtSimAssignMem tupleMemoryFrame
  tupleMemoryLayout exprSim exprLoweringProps localPtrsProps compileEnv
  valueEncoding valueEncodingProps valueEncodingProofs vyperState vyperLookup
  list rich_list finite_map arithmetic venomState venomInst
  stmtSimDeclMem stmtLowering emitHelperProps emitHelper fragExec vyperInterpreter
  vyperTyping valueTypingMemoryProps freshWrites

(* Expose a destination's region and capacity without unfolding the state
   relation in every suffix-frame consumer. *)
Theorem tuple_store_destination_region:
  !func cenv cx es s id p dsz entry dw ctx.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
    lookup_var p s = SOME dw ==>
    local_region cenv es.scopes s id (w2n dw) dsz /\
    type_memory_size entry.type <= dsz
Proof
  rpt strip_tac
  >- (simp[local_region_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> simp[]
QED

(* This applies to either a 32-byte MSTORE or a runtime-sized memory
   copy. Only the unread suffix, not the already-consumed head, survives. *)
Theorem tuple_local_write_suffix:
  !func cenv cx es s id p dsz entry dw b sz addr elem vs tvs written mem' ctx.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
    lookup_var p s = SOME dw /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    b <= addr /\ addr + elem + type_memory_size_list tvs <= b + sz /\
    written <= elem /\ written <= type_memory_size entry.type /\
    (!a len. a + len <= w2n dw \/ w2n dw + written <= a ==>
       mem_bytes_at a len mem' = mem_bytes_at a len s.vs_memory) /\
    tuple_in_memory vs tvs (addr + elem) s.vs_memory /\
    tuple_val_wf vs tvs ==>
    tuple_in_memory vs tvs (addr + elem) mem'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `written <= dsz` by decide_tac >>
  drule_all (tuple_in_memory_unread_suffix |> SPEC_ALL
    |> Q.INST [`off` |-> `0`] |> GEN_ALL |> SRULE []) >> simp[]
QED

(* One execution interface for both representations; memory mode preserves
   old variables, while the word-only specialization preserves every variable. *)
Theorem tuple_local_store_head_run:
  !m ctx func cenv cx es s id p dsz pre env entry rest v tv ty vt op st st' w.
    (if is_word_type ty then emit_void MSTORE [Var p; op]
     else compile_store_memory cenv op (Var p) vt ty) st = ((), st') /\
    (~m ==> is_word_type ty) /\
    eval_operand op s = SOME w /\
    (if is_word_type ty then
       w = typed_val_to_w256 tv v /\ store_lays_out tv entry.type v
     else
       ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
       value_has_type entry.type v /\ val_wf entry.type v /\
       val_in_memory tv v (w2n w) s.vs_memory /\
       evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
       (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
       type_memory_bytes cenv vt = type_memory_size entry.type /\
       type_memory_size entry.type + 64 < dimword (:256)) /\
    (m ==> (!x. op = Var x ==> not_fresh_at st x) /\ local_ptrs_reserved cenv st) /\
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?dw t. lookup_var p s = SOME dw /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      (!x. (~m \/ not_fresh_at st x) ==> lookup_var x t = lookup_var x s) /\
      (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==>
                FLOOKUP t.vs_allocas aid = SOME bs) /\
      (!a len. a + len <= w2n dw \/
         w2n dw + (if is_word_type ty then 32
                   else MIN (type_memory_size tv) (type_memory_size entry.type)) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s = r
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type ty`
  >- (fs[] >> drule_all assign_local_store_run_framed >>
      strip_tac >>
      qexistsl [`dw`, `t`] >> simp[] >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
      rpt strip_tac >> first_x_assum irule >> simp[] >>
      qexists `fuel` >> simp[]) >>
  `m` by metis_tac[] >>
  gns[] >>
  qpat_x_assum `~is_word_type vt /\ _`
    (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(!x. op = Var x ==> _) /\ _`
    (map_every assume_tac o CONJUNCTS) >>
  drule_all (local_memory_store_run_framed |> SPEC_ALL
    |> Q.INST [`tyv` |-> `entry.type`] |> GEN_ALL
    |> PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >>
  strip_tac >>
  qexistsl [`dw`, `t`] >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> qexists `fuel` >> simp[]
QED

(* The typing condition for later targets depends only on scope-entry types. *)
Theorem tuple_store_layout_write_local:
  !cx cenv ids tys tvs vs sc pre env entry rest id v.
    find_containing_scope id sc = SOME (pre, env, entry, rest) /\
    (!i e. i < LENGTH ids /\ lookup_scopes (EL i ids) sc = SOME e ==>
       if is_word_type (EL i tys) then
         store_lays_out (EL i tvs) e.type (EL i vs)
       else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
                 evaluate_type (get_tenv cx) vt = SOME e.type /\
                 value_has_type e.type (EL i vs)) ==>
    !i e. i < LENGTH ids /\
      lookup_scopes (EL i ids)
        (pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) = SOME e ==>
      if is_word_type (EL i tys) then
        store_lays_out (EL i tvs) e.type (EL i vs)
      else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
                evaluate_type (get_tenv cx) vt = SOME e.type /\
                value_has_type e.type (EL i vs)
Proof
  rpt strip_tac >>
  drule_all lookup_scopes_write_local_type >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem tuple_store_operands_tail:
  !m st s t id ids ty tys tv tvs v vs op ops addr.
    LENGTH ops = LENGTH ids /\
    EVERY (\op. ?x. op = Var x) (op::ops) /\
    (m ==> EVERY (\op. !x. op = Var x ==> not_fresh_at st x) (op::ops)) /\
    (!x. (~m \/ not_fresh_at st x) ==> lookup_var x t = lookup_var x s) /\
    (!i. i < LENGTH (id::ids) ==>
       ?w. eval_operand (EL i (op::ops)) s = SOME w /\
         (if is_word_type (EL i (ty::tys)) then
            w = typed_val_to_w256 (EL i (tv::tvs)) (EL i (v::vs))
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i (tv::tvs))))) ==>
    !i. i < LENGTH ids ==>
      ?w. eval_operand (EL i ops) t = SOME w /\
        (if is_word_type (EL i tys) then
           w = typed_val_to_w256 (EL i tvs) (EL i vs)
         else w2n w = addr + type_memory_size tv +
                       SUM (MAP type_memory_size (TAKE i tvs)))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH (_::_) ==> _`
    (qspec_then `SUC i` mp_tac) >> asm_simp_tac (srw_ss()) [TAKE_def] >>
  strip_tac >> qexists `w` >>
  `?x. EL i ops = Var x` by
    (fs[EVERY_EL] >> first_x_assum irule >> simp[]) >>
  `lookup_var x t = lookup_var x s` by
    (first_x_assum irule >> Cases_on `m` >> gvs[EVERY_EL] >>
     metis_tac[]) >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `m ==> _` kall_tac >>
  qpat_x_assum `!x. _` kall_tac >>
  conj_tac
  >- (qpat_x_assum `eval_operand _ s = _` mp_tac >>
      asm_simp_tac (srw_ss()) [eval_operand_def]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  simp_tac (srw_ss()) [ADD_ASSOC]
QED

Theorem tuple_store_memory_tail:
  !func cenv cx es s t st scopes' id p dsz entry dw b sz addr tv tvs v vs written ctx.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
    lookup_var p s = SOME dw /\
    local_ptrs_reserved cenv st /\
    MAP FDOM es.scopes = MAP FDOM scopes' /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    b <= addr /\ addr + type_memory_size_list (tv::tvs) <= b + sz /\
    written <= type_memory_size tv /\ written <= type_memory_size entry.type /\
    (!a len. a + len <= w2n dw \/ w2n dw + written <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    tuple_in_memory (v::vs) (tv::tvs) addr s.vs_memory /\
    tuple_val_wf (v::vs) (tv::tvs) ==>
    b <= addr + type_memory_size tv /\
    addr + type_memory_size tv + type_memory_size_list tvs <= b + sz /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b, sz)) \/
     (?name. local_region cenv scopes' t name b sz)) /\
    tuple_in_memory vs tvs (addr + type_memory_size tv) t.vs_memory /\
    tuple_val_wf vs tvs
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `tuple_in_memory (_::_) _ _ _` mp_tac >>
  simp_tac (srw_ss()) [val_in_memory_def, LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `tuple_val_wf (_::_) _` mp_tac >>
  simp_tac (srw_ss()) [val_wf_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `addr + type_memory_size tv + type_memory_size_list tvs <= b + sz` by
    fs[type_memory_size_def] >>
  drule_all tuple_local_write_suffix >> disch_tac >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
          lookup_var x t = SOME w` by metis_tac[] >>
  drule_all tuple_container_transport >> disch_tac >>
  conj_tac >- decide_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem tuple_store_head_code_shape:
  !cenv ty vt p op st sm.
    (is_word_type vt = is_word_type ty) /\
    (~is_word_type ty ==> (vt = ty \/ is_bytestring_type vt) /\
                            0 < type_memory_bytes cenv vt) /\
    (if is_word_type ty then emit_void MSTORE [Var p; op]
     else compile_store_memory cenv op (Var p) vt ty) st = ((),sm) ==>
    cs_extends st sm /\ ~block_is_terminated sm
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type ty`
  >- (fs[] >> conj_tac
      >- metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
      drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  gns[] >>
  qpat_x_assum `(_ \/ _) /\ _` (map_every assume_tac o CONJUNCTS) >>
  `cs_appends (compile_store_memory cenv op (Var p) vt ty)` by
    (qspecl_then [`cenv`, `Var p`, `op`, `NONE`] mp_tac
       compile_assign_memory_widen_appends >>
     simp[compile_assign_value_def] >> disch_then irule >>
     metis_tac[]) >>
  conj_tac >- fs[cs_appends_def] >>
  qpat_assum `vt = ty \/ _` mp_tac >>
  once_rewrite_tac [EQ_SYM_EQ] >> disch_tac >>
  drule_all (compile_assign_value_memory_widen_open |> SPEC_ALL
    |> Q.INST [`loc` |-> `NONE`] |> GEN_ALL
    |> SRULE [compile_assign_value_def]) >> simp[]
QED

(* The single recursion used by both the all-word and memory-backed APIs. *)
Theorem tuple_store_mixed_locals_run:
  !ids m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops st = ((),st') /\
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es = (INL (),es') /\
    LENGTH ids = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    (~m ==> EVERY is_word_type tys) /\
    EVERY (\op. ?x. op = Var x) ops /\
    (m ==> EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops) /\
    (!i. i < LENGTH ids ==>
       ?w. eval_operand (EL i ops) s = SOME w /\
         (if is_word_type (EL i tys) then
            w = typed_val_to_w256 (EL i tvs) (EL i vs)
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    (!i. i < LENGTH ids ==>
       ?p dsz vt. FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) dsz) /\
         cenv.ce_var_type (EL i ids) = SOME vt /\
         (is_word_type vt = is_word_type (EL i tys)) /\
         (~is_word_type (EL i tys) ==>
           (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
           type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
           ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
                 type_memory_bytes cenv vt = type_memory_size vtv /\
                 0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256))) /\
    (!i entry. i < LENGTH ids /\ lookup_scopes (EL i ids) es.scopes = SOME entry ==>
       if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
       else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
                 evaluate_type (get_tenv cx) vt = SOME entry.type /\
                 value_has_type entry.type (EL i vs)) /\
    (m ==> local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
       (!i. i < LENGTH tys ==>
          evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
          (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
       b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
       ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
        (?name. local_region cenv es.scopes s name b sz)) /\
       tuple_in_memory vs tvs addr s.vs_memory) /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ stmt_state_rel ctx func cenv cx es s ==>
    (ids <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. (~m \/ not_fresh_at st x) ==> lookup_var x t = lookup_var x s) /\
        (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
        (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s = r)
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[compile_tuple_store_all_def, comp_return_def, Once evaluate_def,
          return_def] >> qexists `s` >> simp[] >>
      rpt strip_tac >> qexists `fuel` >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  suspend "cons"
QED

Resume tuple_store_mixed_locals_run[cons]:
  qpat_x_assum `!m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st'. _`
    (mk_asm "ih") >>
  drule assign_tuple_target_list_local_cons >> strip_tac >>
  rename1 `find_containing_scope id es.scopes = SOME (pre,env,entry,rest)` >>
  qpat_assum `!i. i < LENGTH (id::ids) ==> ?p dsz vt. _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `p` (qx_choose_then `dsz`
    (qx_choose_then `vt` (map_every assume_tac o CONJUNCTS)))) >>
  qpat_x_assum `compile_tuple_store_all cenv (ty::tys1) _ _ st = _`
    (assume_tac o SRULE [combinTheory.o_THM]) >>
  drule_all tuple_store_local_step >> strip_tac >>
  `~is_word_type ty ==> (vt = ty \/ is_bytestring_type vt) /\
     0 < type_memory_bytes cenv vt` by
    (strip_tac >> qpat_x_assum `~is_word_type ty ==> _` mp_tac >>
     simp[] >> metis_tac[]) >>
  drule_all tuple_store_head_code_shape >> strip_tac >>
  suspend "head_code"
QED

Resume tuple_store_mixed_locals_run[head_code]:
  `cs_extends sm st'` by
    (qpat_x_assum `ih :- _` kall_tac >>
     `LENGTH ids = LENGTH tys1 /\ LENGTH tys1 = LENGTH tvs1 /\
      LENGTH tvs1 = LENGTH vs1` by fs[] >>
     drule tuple_store_locals_extends >>
     impl_tac
     >- (rpt gen_tac >> strip_tac >>
         `i < LENGTH vs1` by metis_tac[] >>
         qpat_x_assum `!i. i < LENGTH (id::ids) ==> ?p dsz vt. _`
           (qspec_then `SUC i` mp_tac) >>
         asm_simp_tac (srw_ss()) [] >>
         disch_then (qx_choose_then `q` (qx_choose_then `n`
           (qx_choose_then `dty` (map_every assume_tac o CONJUNCTS)))) >>
         qexistsl [`q`, `n`, `dty`] >> simp[] >>
         metis_tac[]) >> simp[]) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    metis_tac[fn_has_code_split] >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  qpat_assum `!i. i < LENGTH (id::ids) ==> ?w. eval_operand _ _ = _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!i entry. i < LENGTH (id::ids) /\ _ ==> _`
    (qspecl_then [`0`, `entry`] mp_tac) >>
  simp_tac (srw_ss()) [] >>
  (impl_tac >- asm_rewrite_tac []) >> disch_tac >>
  suspend "head_execution"
QED

Resume tuple_store_mixed_locals_run[head_execution]:
  `(~m ==> is_word_type ty) /\
   (m ==> (!x. op = Var x ==> not_fresh_at st x) /\ local_ptrs_reserved cenv st)` by
    (qpat_x_assum `ih :- _` kall_tac >> fs[]) >>
  `if is_word_type ty then
     w = typed_val_to_w256 tv v /\ store_lays_out tv entry.type v
   else
     ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
     value_has_type entry.type v /\ val_wf entry.type v /\
     val_in_memory tv v (w2n w) s.vs_memory /\
     evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
     (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
     type_memory_bytes cenv vt = type_memory_size entry.type /\
     type_memory_size entry.type + 64 < dimword (:256)` by
    suspend "head_premises" >>
  drule_all tuple_local_store_head_run >>
  disch_then (qx_choose_then `dw` (qx_choose_then `s1`
    (map_every assume_tac o CONJUNCTS))) >>
  suspend "tail_execution"
QED

Resume tuple_store_mixed_locals_run[head_premises]:
  qpat_x_assum `ih :- _` kall_tac >>
  Cases_on `is_word_type ty` >- fs[] >>
  `m` by metis_tac[] >>
  qpat_x_assum `m ==> local_ptrs_reserved _ _ /\ _`
    mp_tac >> (impl_tac >- asm_rewrite_tac []) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!i. i < LENGTH (ty::tys1) ==> _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gns[value_has_type_def, val_in_memory_def] >>
  metis_tac[value_has_type_memory_wf]
QED

Resume tuple_store_mixed_locals_run[tail_execution]:
  asm_x "ih" drule >>
  disch_then drule >>
  disch_then (qspecl_then [`m`, `tvs1`, `addr + type_memory_size tv`, `b`] mp_tac) >>
  disch_then (qspecl_then [`sz`, `ctx`, `func`, `s1`] mp_tac) >>
  (impl_tac >- suspend "tail_premises") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "compose"
QED

Resume tuple_store_mixed_locals_run[tail_premises]:
  rpt conj_tac
  >- fs[] >- fs[] >- fs[] >- fs[] >- fs[] >- fs[]
  >- suspend "tail_fresh"
  >- suspend "tail_operands"
  >- suspend "tail_destinations"
  >- suspend "tail_layout"
  >- suspend "tail_memory"
  >> asm_rewrite_tac []
QED

Resume tuple_store_mixed_locals_run[tail_fresh]:
  strip_tac >>
  `EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops1` by fs[] >>
  qpat_x_assum `EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops1`
    mp_tac >>
  simp_tac (srw_ss()) [EVERY_MEM] >> disch_tac >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `st.cs_next_var <= sm.cs_next_var` by
    (Cases_on `is_word_type ty` >>
     qpat_x_assum `(if is_word_type ty then _ else _) st = _` mp_tac >>
     asm_rewrite_tac [] >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_def, ci_mono_emit_void, ci_mono_compile_store_memory, pairTheory.SND]) >>
  irule not_fresh_at_mono >> qexists `st` >> simp[] >>
  metis_tac[]
QED
Resume tuple_store_mixed_locals_run[tail_operands]:
  `LENGTH ops1 = LENGTH ids` by fs[] >>
  match_mp_tac (tuple_store_operands_tail
    |> INST_TYPE [alpha |-> ``:string``]
    |> SPEC_ALL
    |> Q.INST [`m` |-> `m`, `st` |-> `st`, `s` |-> `s`,
               `id` |-> `id`, `ty` |-> `ty`, `v` |-> `v`,
               `op` |-> `op`]) >>
  asm_rewrite_tac []
QED
Resume tuple_store_mixed_locals_run[tail_destinations]:
  gen_tac >> strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH (id::ids) ==> ?p dsz vt. _`
    (qspec_then `SUC i` mp_tac) >>
  simp [EL, TL]
QED
Resume tuple_store_mixed_locals_run[tail_layout]:
  qpat_x_assum `es1 = _` SUBST_ALL_TAC >>
  simp_tac (srw_ss()) [] >>
  match_mp_tac (tuple_store_layout_write_local |> SPEC_ALL
    |> Q.INST [`sc` |-> `es.scopes`, `entry` |-> `entry`,
               `id` |-> `id`, `v` |-> `v`]) >>
  conj_tac >- asm_rewrite_tac [] >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i entry. i < LENGTH (id::ids) /\ _ ==> _`
    (qspecl_then [`SUC i`, `e`] mp_tac) >>
  simp [EL, TL]
QED
Resume tuple_store_mixed_locals_run[tail_memory]:
  strip_tac >>
  qpat_x_assum `m ==> local_ptrs_reserved cenv st /\ _` mp_tac >>
  asm_rewrite_tac [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `st.cs_next_var <= sm.cs_next_var` by
    (Cases_on `is_word_type ty` >>
     qpat_x_assum `(if is_word_type ty then _ else _) st = _` mp_tac >>
     asm_rewrite_tac [] >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_def, ci_mono_emit_void, ci_mono_compile_store_memory, pairTheory.SND]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists `st` >> asm_rewrite_tac []) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (drule find_containing_scope_structure >>
     qpat_x_assum `es1 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `!x. not_fresh_at st x ==> lookup_var x s1 = lookup_var x s` by
    (rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac []) >>
  `(if is_word_type ty then 32 else MIN (type_memory_size tv) (type_memory_size entry.type)) <= type_memory_size tv /\
   (if is_word_type ty then 32 else MIN (type_memory_size tv) (type_memory_size entry.type)) <= type_memory_size entry.type` by
    (Cases_on `is_word_type ty` >-
       (qpat_x_assum `!i. _ ==> evaluate_type _ _ = _ /\ _`
          (qspec_then `0` mp_tac) >>
        qpat_x_assum `if is_word_type ty then store_lays_out _ _ _ else _` mp_tac >>
        simp[stmtSimDeclStoreTheory.store_lays_out_def]) >>
     simp[]) >>
  drule_all tuple_store_memory_tail >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `values_have_types tvs1 vs1` by
    (qpat_x_assum `values_have_types (_::_) (_::_)` mp_tac >>
     simp_tac (srw_ss()) [value_has_type_def]) >>
  qpat_x_assum `es1 = _` SUBST_ALL_TAC >>
  asm_simp_tac (srw_ss()) [] >>
  gen_tac >> strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. _ ==> evaluate_type _ _ = _ /\ _`
    (qspec_then `SUC i` mp_tac) >>
  simp[EL, TL]
QED
Resume tuple_store_mixed_locals_run[compose]:
  conj_tac >- (first_x_assum irule >> asm_rewrite_tac []) >>
  qpat_x_assum `?t. stmt_state_rel ctx _ _ _ _ _ /\ _` strip_assume_tac >>
  qexists `t` >>
  simp_tac (srw_ss()) [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "compose_vars" >>
  conj_tac >- suspend "compose_allocas" >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
    (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func s1 = r /\ _ ==> _`
    (qspec_then `fuel'` mp_tac) >> simp[]
QED
Resume tuple_store_mixed_locals_run[compose_vars]:
  rpt gen_tac >> disch_tac >>
  `st.cs_next_var <= sm.cs_next_var` by
    (Cases_on `is_word_type ty` >>
     qpat_x_assum `(if is_word_type ty then _ else _) st = _` mp_tac >>
     asm_rewrite_tac [] >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_def, ci_mono_emit_void, ci_mono_compile_store_memory, pairTheory.SND]) >>
  `~m \/ not_fresh_at sm x` by
    (qpat_x_assum `~m \/ _` mp_tac >>
     qpat_x_assum `st.cs_next_var <= sm.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[not_fresh_at_mono]) >>
  qpat_x_assum `!x. ~m \/ not_fresh_at sm x ==> _`
    (qspec_then `x` mp_tac) >>
  qpat_x_assum `!x. ~m \/ not_fresh_at st x ==> _`
    (qspec_then `x` mp_tac) >> simp[]
QED
Resume tuple_store_mixed_locals_run[compose_allocas]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> _` drule >>
  disch_tac >>
  qpat_x_assum `!aid bs. FLOOKUP s1.vs_allocas aid = SOME bs ==> _` drule >>
  simp[]
QED

Finalise tuple_store_mixed_locals_run
