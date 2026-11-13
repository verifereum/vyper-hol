(* Memory-checked stores for the existing-local tuple assignment suffix. *)
Theory bodyMemAssignTupleLocalsStores
Ancestors
  bodyMemAssignTupleLocalsFacts bodyDeclWordMemory bodyMemAssignLocalWord
  tupleLocalStoreRun stmtSimAssignStore stmtSimDeclStore
  fragGasMode fragGasPathMem fragExecMem emitHelperProps emitHelper
  stmtSimDefs exprLoweringProps localPtrsProps valueEncoding valueEncodingDefs valueEncodingProofs
  venomState venomInst vyperState vyperLookup finite_map list compileEnv loweringStateRelDefs
  valueEncodingProps valueCopy valueCopyBytes bodyDeclMemoryCore exprSimProps
  valueTypingMemoryProps bodyMemAssignLocalMem bodyDeclMemoryCounted
  stmtLowering vyperInterpreter fragGasPath tupleLocalStoreProps tupleMemoryFrame
  tupleMemoryLayout freshWrites fragExec vyperTyping

(* Word branch of S1 tuple_local_store_head_path, including the disjoint
   memory frame needed to retain the unread tuple suffix. *)
Theorem tuple_local_word_store_head_path_mem:
  emit_void MSTORE [Var p; op] st = ((), st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  store_lays_out tv entry.type v ==>
  ?dw t. lookup_var p s = SOME dw /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!x. lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\
    (!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `type_memory_size entry.type = 32` by fs[store_lays_out_def] >>
  `w2n dw + 32 <= s.vs_alloca_next` by
    (irule (tuple_local_destination_room |> cj 3) >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `entry`, `es`, `func`, `id`, `p`, `sz`] >>
     simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  drule_all annassign_word_mstore_path_mem >> strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb` by
    metis_tac[emit_void_same_blocks, same_blocks_def] >>
  `!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
     mem_bytes_at a len (mstore (w2n dw) (typed_val_to_w256 tv v) s).vs_memory =
     mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  qexistsl_tac [`dw`, `mstore (w2n dw) (typed_val_to_w256 tv v) s with
                              vs_inst_idx := LENGTH st'.cs_current_insts`] >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def] >>
  fs[mstore_def, lookup_var_def, LET_THM] >> first_assum ACCEPT_TAC
QED

(* Compatible nonword copy: S1's compatible-run normalization, retaining
   the smaller capacity frame for the tuple's unread suffix. *)
Theorem tuple_compatible_store_run_mem:
  !cenv src dst dty sty sa sb s tenv dtv stv v sw dw.
  compile_store_memory cenv src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  ~is_word_type dty /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  value_has_type dtv v /\ val_wf dtv v /\ value_has_type stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv + 64 < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!a len. a + len <= w2n dw \/
       w2n dw + MIN (type_memory_size stv) (type_memory_size dtv) <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb) /\
   val_in_memory dtv v (w2n sw) s.vs_memory /\
   val_store_size dtv v = val_store_size stv v /\
   (if is_bytestring_type dty then val_store_size dtv v
    else type_memory_size dtv) <= MIN (type_memory_size stv) (type_memory_size dtv)` by
    (Cases_on `dty = sty`
     >- (gvs[] >> drule val_store_size_le >>
         Cases_on `is_bytestring_type dty` >> simp[]) >>
     gvs[] >>
     `val_wf stv v` by metis_tac[value_has_type_memory_wf] >>
     `val_store_size dtv v = val_store_size stv v` by
       metis_tac[bytestring_val_store_size_eq] >>
     `val_store_size dtv v <= type_memory_size dtv /\
      val_store_size stv v <= type_memory_size stv` by
       metis_tac[val_store_size_le] >>
     conj_tac >- metis_tac[compile_store_memory_bytestring_src] >>
     conj_tac >- metis_tac[bytestring_val_in_memory_transfer] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_typed_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`dw`, `tenv`, `dtv`, `v`, `sw`] >> simp[] >>
     metis_tac[]) >>
  drule compile_store_memory_run_frame_with_capacity >>
  disch_then (qspecl_then [`s`, `tenv`, `dtv`, `v`, `sw`, `dw`,
     `MIN (type_memory_size stv) (type_memory_size dtv)`] mp_tac) >>
  (impl_tac >- (Cases_on `is_bytestring_type dty` >> gvs[])) >>
  strip_tac >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
  simp[venom_state_component_equality]
QED

Theorem tuple_local_nonword_store_head_path_mem:
  compile_store_memory cenv op (Var p) vt ty st = ((),st') /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  local_ptrs_reserved cenv st /\ eval_operand op s = SOME w /\
  ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
  value_has_type entry.type v /\ val_wf entry.type v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
  type_memory_bytes cenv vt = type_memory_size entry.type /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  w2n w + val_store_size tv v <= s.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?dw t. lookup_var p s = SOME dw /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\
    (!a len. a + len <= w2n dw \/
       w2n dw + MIN (type_memory_size tv) (type_memory_size entry.type) <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    gas_marked_path T ctx func s 0 (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw /\
        w2n dw + type_memory_size entry.type <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> metis_tac[]) >>
  `not_fresh_at st p` by
    (gns[local_ptrs_reserved_def] >> metis_tac[]) >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  drule tuple_compatible_store_run_mem >>
  disch_then (qspecl_then [`s`, `get_tenv cx`, `entry.type`, `tv`, `v`, `w`, `dw`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!a len. a + len <= w2n dw \/ w2n dw + type_memory_size entry.type <= a ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
     simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t` by
    (irule local_memory_write_frame >> simp[] >>
     qexistsl_tac [`s`, `st`, `dw`] >>
     simp[] >> conj_tac
     >- metis_tac[arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts st st')` by
    metis_tac[compile_store_memory_same_no_gas, compile_store_memory_bytestring_src] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `st` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl_tac [`s`, `st`] >> simp[]) >>
  qexistsl_tac [`dw`, `t with vs_inst_idx := LENGTH st'.cs_current_insts`] >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def, lookup_var_def] >>
  conj_tac >- fs[lookup_var_def] >> first_assum ACCEPT_TAC
QED

Theorem tuple_local_store_head_path_mem:
  (if is_word_type ty then emit_void MSTORE [Var p; op]
   else compile_store_memory cenv op (Var p) vt ty) st = ((),st') /\
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
     type_memory_size entry.type + 64 < dimword (:256) /\
     w2n w + val_store_size tv v <= s.vs_alloca_next) /\
  (!x. op = Var x ==> not_fresh_at st x) /\ local_ptrs_reserved cenv st /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?dw t. lookup_var p s = SOME dw /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\
    (!a len. a + len <= w2n dw \/
       w2n dw + (if is_word_type ty then 32
                  else MIN (type_memory_size tv) (type_memory_size entry.type)) <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    gas_marked_path T ctx func s 0 (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type ty`
  >- (gvs[] >> drule_all tuple_local_word_store_head_path_mem >>
      strip_tac >> goal_assum (drule_at Any) >> simp[] >>
      first_assum ACCEPT_TAC) >>
  gnvs[] >>
  qpat_x_assum `~is_word_type vt /\ _`
    (map_every assume_tac o CONJUNCTS) >>
  drule_all tuple_local_nonword_store_head_path_mem >>
  strip_tac >> goal_assum (drule_at Any) >> simp[] >> first_assum ACCEPT_TAC
QED

(* Memory-counted twin of S1 tuple_store_mixed_locals_path. *)
Theorem tuple_store_mixed_locals_path_mem:
  !ids tys tvs vs ops addr b sz ctx func cenv cx es es' s st st'.
    compile_tuple_store_all cenv tys (MAP (BaseTarget o NameTarget) ids) ops st = ((),st') /\
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs es = (INL (),es') /\
    LENGTH ids = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    EVERY (\op. ?x. op = Var x) ops /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
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
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH tys ==>
       evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
       (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
    b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    tuple_in_memory vs tvs addr s.vs_memory /\
    addr + type_memory_size_list tvs <= s.vs_alloca_next /\
    alloca_history func s /\ fn_inst_ids_distinct func /\
    fn_has_code st st' func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ stmt_state_rel ctx func cenv cx es s ==>
    (ids <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t. stmt_state_rel ctx func cenv cx es' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
        alloca_history func t /\ gas_marked_path T ctx func s 0 (OK t)
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[compile_tuple_store_all_def, comp_return_def, Once evaluate_def,
          return_def] >> qexists `s` >> simp[] >>
      gvs[Once evaluate_def, return_def] >>
      simp[gas_marked_path_def] >> irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  suspend "cons"
QED

Resume tuple_store_mixed_locals_path_mem[cons]:
  qpat_x_assum `!tys tvs vs ops addr b sz ctx func cenv cx es es' s st st'. _`
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
     simp[] >> strip_tac >> conj_tac >- gvs[] >> gvs[]) >>
  drule_all tuple_store_head_code_shape >> strip_tac >>
  suspend "head_code"
QED

Resume tuple_store_mixed_locals_path_mem[head_code]:
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
         qexistsl_tac [`q`, `n`, `dty`] >> simp[] >> metis_tac[]) >> simp[]) >>
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

Resume tuple_store_mixed_locals_path_mem[head_execution]:
  `(!x. op = Var x ==> not_fresh_at st x)` by fs[] >>
  `if is_word_type ty then
     w = typed_val_to_w256 tv v /\ store_lays_out tv entry.type v
   else
     ~is_word_type vt /\ evaluate_type (get_tenv cx) vt = SOME entry.type /\
     value_has_type entry.type v /\ val_wf entry.type v /\
     val_in_memory tv v (w2n w) s.vs_memory /\
     evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
     (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
     type_memory_bytes cenv vt = type_memory_size entry.type /\
     type_memory_size entry.type + 64 < dimword (:256) /\
     w2n w + val_store_size tv v <= s.vs_alloca_next` by
    suspend "head_premises" >>
  drule_all tuple_local_store_head_path_mem >>
  disch_then (qx_choose_then `dw` (qx_choose_then `s1`
    (map_every assume_tac o CONJUNCTS))) >>
  suspend "tail_execution"
QED

Resume tuple_store_mixed_locals_path_mem[head_premises]:
  qpat_x_assum `ih :- _` kall_tac >>
  Cases_on `is_word_type ty` >- fs[] >>
  qpat_x_assum `!i. i < LENGTH (ty::tys1) ==> _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gns[value_has_type_def, val_in_memory_def] >>
  `val_wf tv v /\ val_wf entry.type v` by
    metis_tac[value_has_type_memory_wf] >>
  `val_store_size tv v <= type_memory_size tv` by
    metis_tac[val_store_size_le] >>
  gns[type_memory_size_def] >> decide_tac
QED

Resume tuple_store_mixed_locals_path_mem[tail_execution]:
  asm_x "ih" drule >> disch_then drule >>
  disch_then (qspecl_then [`tvs1`, `addr + type_memory_size tv`, `b`,
                          `sz`, `ctx`, `func`, `s1`] mp_tac) >>
  (impl_tac >- suspend "tail_premises") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "compose"
QED

Resume tuple_store_mixed_locals_path_mem[tail_premises]:
  `st.cs_next_var <= sm.cs_next_var` by
    (Cases_on `is_word_type ty` >>
     qpat_x_assum `(if is_word_type ty then _ else _) st = _` mp_tac >>
     asm_rewrite_tac [] >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_def, ci_mono_emit_void, ci_mono_compile_store_memory, pairTheory.SND]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists `st` >> asm_rewrite_tac []) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (drule find_containing_scope_structure >>
     qpat_x_assum `es1 = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `(if is_word_type ty then 32 else MIN (type_memory_size tv) (type_memory_size entry.type)) <= type_memory_size tv /\
   (if is_word_type ty then 32 else MIN (type_memory_size tv) (type_memory_size entry.type)) <= type_memory_size entry.type` by
    (Cases_on `is_word_type ty` >-
       (qpat_x_assum `!i. _ ==> evaluate_type _ _ = _ /\ _`
          (qspec_then `0` mp_tac) >>
        qpat_x_assum `if is_word_type ty then store_lays_out _ _ _ else _` mp_tac >>
        simp[store_lays_out_def]) >> simp[]) >>
  `!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP s1.vs_allocas aid = SOME bs` by simp[] >>
  drule_all tuple_store_memory_tail >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac
  >- fs[] >- fs[] >- fs[] >- fs[] >- fs[]
  >- suspend "tail_fresh"
  >- suspend "tail_operands"
  >- suspend "tail_destinations"
  >- suspend "tail_layout"
  >- first_assum ACCEPT_TAC
  >- fs[value_has_type_def]
  >- fs[]
  >- suspend "tail_types"
  >- (fs[type_memory_size_def] >> decide_tac)
  >- fs[type_memory_size_def]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- fs[type_memory_size_def]
  >> asm_rewrite_tac []
QED

Resume tuple_store_mixed_locals_path_mem[tail_fresh]:
  fs[EVERY_MEM] >> rpt strip_tac >>
  irule not_fresh_at_mono >> qexists `st` >> simp[] >> metis_tac[]
QED

Resume tuple_store_mixed_locals_path_mem[tail_operands]:
  `LENGTH ops1 = LENGTH ids` by fs[] >>
  match_mp_tac (tuple_store_operands_tail |> SPEC_ALL
    |> Q.INST [`m` |-> `T`, `st` |-> `st`, `s` |-> `s`]) >>
  asm_rewrite_tac []
QED

Resume tuple_store_mixed_locals_path_mem[tail_destinations]:
  gen_tac >> strip_tac >> `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH (id::ids) ==> ?p dsz vt. _`
    (qspec_then `SUC i` mp_tac) >> simp[EL, TL]
QED

Resume tuple_store_mixed_locals_path_mem[tail_layout]:
  qpat_x_assum `es1 = _` SUBST_ALL_TAC >> simp_tac (srw_ss()) [] >>
  match_mp_tac (tuple_store_layout_write_local |> SPEC_ALL
    |> Q.INST [`sc` |-> `es.scopes`, `entry` |-> `entry`,
               `id` |-> `id`, `v` |-> `v`]) >>
  conj_tac >- asm_rewrite_tac [] >>
  rpt gen_tac >> strip_tac >> `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i entry. i < LENGTH (id::ids) /\ _ ==> _`
    (qspecl_then [`SUC i`, `e`] mp_tac) >> simp[EL, TL]
QED

Resume tuple_store_mixed_locals_path_mem[tail_types]:
  gen_tac >> strip_tac >> `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. _ ==> evaluate_type _ _ = _ /\ _`
    (qspec_then `SUC i` mp_tac) >> simp[EL, TL]
QED

Resume tuple_store_mixed_locals_path_mem[compose]:
  conj_tac >- (first_x_assum irule >> asm_rewrite_tac []) >>
  qpat_x_assum `?t. stmt_state_rel ctx _ _ _ _ _ /\ _` strip_assume_tac >>
  qexists `t` >> simp_tac (srw_ss()) [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "compose_vars" >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `gas_marked_path T ctx func s (0 + 0) (OK t)` by
    (irule gas_marked_path_then >> qexists `s1` >> simp[]) >> fs[]
QED

Resume tuple_store_mixed_locals_path_mem[compose_vars]:
  rpt gen_tac >> disch_tac >>
  `st.cs_next_var <= sm.cs_next_var` by
    (Cases_on `is_word_type ty` >>
     qpat_x_assum `(if is_word_type ty then _ else _) st = _` mp_tac >>
     asm_rewrite_tac [] >> POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_def, ci_mono_emit_void, ci_mono_compile_store_memory, pairTheory.SND]) >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
  qpat_x_assum `!x. not_fresh_at st x ==> _` (qspec_then `x` mp_tac) >> simp[]
QED

Finalise tuple_store_mixed_locals_path_mem
