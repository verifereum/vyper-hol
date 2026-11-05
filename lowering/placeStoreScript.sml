(*
 * Stores at an assignment place
 *
 * A place target's fragment (targetPlaceSim's target_post) leaves a pointer
 * w that place_ptr_rel relates to the source's place p: a local's region
 * offset in memory, or a slot in storage or transient storage.  The lowering
 * then stores the value there, and the source writes it with write_place.
 * These lemmas run the store from a state related at the source state
 * before the write to one related at the state after it.
 *
 * TOP-LEVEL:
 *   place_store_word_run  — one MSTORE, SSTORE or TSTORE of a word, as
 *                           compile_assign_value's word case, AugAssign
 *                           and a tuple's word element store it
 *   place_store_value_run — compile_assign_value at any location, the
 *                           value's type widening to the place's
 *   place_store_empty_run — the zero length word an empty value stores
 *)

Theory placeStore
Ancestors
  placeStoreMemory placeStoreStorage placeStoreDyn
  stmtSimDefs exprSimHypsDefs typedCopyDomain vyperStoragePlaceProvenance
  loweringPosts fragGasMode
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  venomState

(* One store of a word at the place: the store opcode of its location. *)
Theorem place_store_word_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op dty dtv v sa sb.
    emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                         | _ => MSTORE) [dst_op; op] sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    is_word_type dty /\ expr_val_rel cx dty v op s /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

(* compile_assign_value at the place: a word by one store, an aggregate
   by a typed copy into memory or a copy to (transient) storage, a DynArray
   to storage by its length and live elements.  A copy at one type or of
   a bytestring is one MCOPY, which reads its source before it writes, so
   only a typed copy (compile_store_memory_typed, element by element) from
   a source the lowering does not stage first needs that source outside
   the destination, or at it with the same layout (a copy in place). *)
Theorem place_store_value_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of
         ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes cenv et + 31) DIV 32,
                 type_memory_bytes cenv et)
       | _ => NONE)
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `loc <> LocMemory ==> loc = LocStorage \/ loc = LocTransient` by
    (Cases_on `p` >> gvs[place_ptr_rel_def] >>
     rename1 `slot_loc tr` >> Cases_on `tr` >> simp[slot_loc_def]) >>
  Cases_on `loc = LocMemory`
  >- (qspecl_then
      [`ctx`, `func`, `cenv`, `cx`, `env`, `ee`, `ff`, `s`, `p`, `w`, `loc`, `dst_op`,
       `op`, `src_loc`, `dty`, `sty`, `stv`, `v`, `sa`, `sb`]
      mp_tac place_store_value_memory_run >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
    simp[]) >>
  Cases_on `?et n. dty = ArrayT et (Dynamic n)`
  >- (qspecl_then
      [`ctx`, `func`, `cenv`, `cx`, `env`, `ee`, `ff`, `s`, `p`, `w`, `loc`, `dst_op`,
       `op`, `src_loc`, `dty`, `sty`, `stv`, `v`, `sa`, `sb`]
      mp_tac place_store_value_dyn_run >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
    simp[]) >>
  `!et n. dty <> ArrayT et (Dynamic n)` by fs[] >>
  (qspecl_then
      [`ctx`, `func`, `cenv`, `cx`, `env`, `ee`, `ff`, `s`, `p`, `w`, `loc`, `dst_op`,
       `op`, `src_loc`, `dty`, `sty`, `stv`, `v`, `sa`, `sb`]
      mp_tac place_store_value_storage_run >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
    simp[])
QED

(* An empty value at a type with a length word: a zero length word at the
   place's head. *)
Theorem place_store_empty_run:
  !ctx func cenv cx env ee ff s p w loc imm dst_op dty dtv sa sb.
    compile_store_at_loc imm dst_op (Lit 0w) (SOME loc) sa = ((), sb) /\
    loc <> LocCode /\ loc <> LocCalldata /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    has_length_word dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p (default_value dtv) ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
