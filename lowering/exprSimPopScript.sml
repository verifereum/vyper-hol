(*
 * Expression simulation: pop on a local dynamic array (#636, Places row 3)
 *
 * x.pop() on a local x of type DynArray[T, n] lowers to
 * compile_dynarray_pop on x's pointer variable p, in memory: an MLOAD of the
 * length word at p, an ASSERT that it is not 0, an MSTORE of the length less
 * one, and the address p + 32 + (len - 1) * type_memory_bytes T of the
 * popped element, handed out as a pointer into memory.  The source
 * (pop_place) shortens x's value, records the popped element in x's pop
 * history, and returns the place of the popped index, which reads back
 * through that history (pop_name_entry); it raises a runtime error on an
 * empty array, where the ASSERT aborts.  The lowering does not clear the
 * popped element, so it stays in x's region, past the new length, and the
 * pointer holds the value read from the place there; x's region holds the
 * shortened array, so the locals stay related (local_ptrs_rel_write_local).
 *
 * TOP-LEVEL:
 *   compile_pop_name_sim — expr_vv_sim of x.pop() on a local
 *
 * Helpers:
 *   pop_locals_kept — popping preserves the other live locals' regions
 *   elems_val_wf_EL, elems_val_wf_FRONT, elems_in_memory_FRONT,
 *     elems_in_memory_mstore_before — the array's layout
 *   lookup_scopes_set_other, eval_target_place_name, eval_pop_name,
 *     read_result_pop_name — the source side
 *   compile_expr_pop_name, dynarray_pop_mem_shape, dynarray_pop_mem_run_empty,
 *     dynarray_pop_mem_run — the lowering and its run
 *   pop_name_facts, pop_ptr_w2n, pop_elem_fits, pop_vv_post — the parts
 *     of the simulation
 *)

Theory exprSimPop
Ancestors
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map arithmetic words
  fragExec loweringSlice  exprSimHyps exprSimLeaves exprSimAggregateLayout
  exprSimAggregateEncoding exprLowering exprLoweringProps emitHelper
  emitHelperProps compileEnv localPtrsProps valueEncoding valueEncodingProps
  vyperAST vyperInterpreter vyperState vyperValue vyperValueOperation
  vyperLookup vyperTyping vyperTypeSystem vyperTypeInvariants vyperTypeEnv
  vyperTypeExprResult vyperTypeExprSoundness
  venomExecSemantics venomInst venomState
  gasOutcome gasSummary fragGasMode fragGasPath fragGasSeq fragGasSeqAbort
Libs
  pairLib

(* ===== The array's layout ===== *)

Theorem elems_val_wf_EL:
  !vs tv i. elems_val_wf vs tv /\ i < LENGTH vs ==> val_wf tv (EL i vs)
Proof
  cheat
QED

Theorem elems_val_wf_FRONT:
  !vs tv. elems_val_wf vs tv /\ vs <> [] ==> elems_val_wf (FRONT vs) tv
Proof
  cheat
QED

Theorem elems_in_memory_FRONT:
  !vs off tv mem.
    elems_in_memory vs off tv mem /\ vs <> [] ==>
    elems_in_memory (FRONT vs) off tv mem
Proof
  cheat
QED

(* A store below the elements leaves them in place. *)
Theorem elems_in_memory_mstore_before:
  !vs off tv s a w.
    elems_in_memory vs off tv s.vs_memory /\ elems_val_wf vs tv /\
    a + 32 <= off ==>
    elems_in_memory vs off tv (mstore a w s).vs_memory
Proof
  cheat
QED

(* ===== The source side ===== *)

(* Setting the entry find_containing_scope found leaves every other name. *)
Theorem lookup_scopes_set_other:
  !id sc pre env e rest v n.
    find_containing_scope id sc = SOME (pre, env, e, rest) /\ n <> id ==>
    lookup_scopes n (pre ++ env |+ (id, v) :: rest) = lookup_scopes n sc
Proof
  cheat
QED

Theorem eval_target_place_name:
  !cx id es.
    IS_SOME (lookup_scopes id es.scopes) ==>
    eval_target_place cx (NameTarget id) es = (INL (MemoryPlace id []), es)
Proof
  cheat
QED

(* The entry after a pop on the variable itself: the shortened array, and the
   popped element on top of its pop history. *)
Definition pop_name_entry_def:
  pop_name_entry entry vs =
    entry with <| value := ArrayV (DynArrayV (FRONT vs));
                  popped := ([ValueSubscript (IntV &(LENGTH vs - 1))], LAST vs)
                            :: entry.popped |>
End

Theorem eval_pop_name:
  !cx ann id es res es' entry vs.
    lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
    entry.value = ArrayV (DynArrayV vs) /\
    eval_expr cx (Pop ann (NameTarget id)) es = (res, es') ==>
    (vs = [] /\ res = INR (Error (RuntimeError "pop empty memory array"))) \/
    (vs <> [] /\
     res = INL (PlaceR (MemoryPlace id
                          [ValueSubscript (IntV &(LENGTH vs - 1))])) /\
     ?pre env rest.
       find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
       es' = es with scopes :=
         pre ++ env |+ (id, pop_name_entry entry vs) :: rest)
Proof
  cheat
QED

(* Reading the popped element's place after the pop: the shortened array
   has no element there, so the read falls back to the pop history. *)
Theorem read_result_pop_name:
  !cx id st entry vs etv n.
    lookup_scopes id st.scopes = SOME (pop_name_entry entry vs) /\
    entry.type = ArrayTV etv (Dynamic n) /\ vs <> [] /\ LENGTH vs <= n ==>
    read_result cx
      (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))])) st =
      (INL (LAST vs), st)
Proof
  cheat
QED

(* ===== The lowering ===== *)

Theorem compile_expr_pop_name:
  !cenv ty ann id p sz et bd sa.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (ArrayT et bd) ==>
    compile_expr cenv ty (Pop ann (NameTarget id)) sa =
      (LocatedValue ann
         (mk_ptr (FST (compile_dynarray_pop (Var p) 32
                         (type_memory_bytes cenv et)
                         cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory sa))
                 LocMemory),
       SND (compile_dynarray_pop (Var p) 32 (type_memory_bytes cenv et)
              cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory sa))
Proof
  cheat
QED

Theorem dynarray_pop_mem_shape:
  !p esz is_ctor imm sa r sb.
    compile_dynarray_pop (Var p) 32 esz is_ctor imm LocMemory sa = (r, sb) ==>
    ?x0 x1 x2 x3 x4 x5 x6.
      ALL_DISTINCT [x0; x1; x2; x3; x4; x5; x6] /\
      EVERY (\x. ~not_fresh_at sa x) [x0; x1; x2; x3; x4; x5; x6] /\
      r = Var x6 /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
      sb.cs_current_insts = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id MLOAD [Var p] [x0];
         mk_inst (sa.cs_next_id + 1) ISZERO [Var x0] [x1];
         mk_inst (sa.cs_next_id + 2) ISZERO [Var x1] [x2];
         mk_inst (sa.cs_next_id + 3) ASSERT [Var x2] [];
         mk_inst (sa.cs_next_id + 4) SUB [Var x0; Lit 1w] [x3];
         mk_inst (sa.cs_next_id + 5) MSTORE [Var p; Var x3] [];
         mk_inst (sa.cs_next_id + 6) ADD [Var p; Lit 32w] [x4];
         mk_inst (sa.cs_next_id + 7) MUL [Var x3; Lit (n2w esz)] [x5];
         mk_inst (sa.cs_next_id + 8) ADD [Var x4; Var x5] [x6]]
Proof
  cheat
QED

(* The pop's instructions on variable operands, as rewrites whose
   conditions name no other variable: simp unfolds no opcode case. *)
Theorem pop_step_MLOAD[local]:
  !id x out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id MLOAD [Var x] [out]) s =
      OK (update_var out (mload (w2n (THE (lookup_var x s))) s) s)
Proof
  cheat
QED

Theorem pop_step_ISZERO:
  !id x out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id ISZERO [Var x] [out]) s =
      OK (update_var out (bool_to_word (THE (lookup_var x s) = 0w)) s)
Proof
  cheat
QED

Theorem pop_step_ASSERT:
  !id x s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id ASSERT [Var x] []) s =
      if THE (lookup_var x s) = 0w
      then Abort Revert_abort (revert_state (set_returndata [] s))
      else OK s
Proof
  cheat
QED

Theorem pop_step_SUB_lit:
  !id x c out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id SUB [Var x; Lit c] [out]) s =
      OK (update_var out (THE (lookup_var x s) - c) s)
Proof
  cheat
QED

Theorem pop_step_ADD_lit[local]:
  !id x c out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id ADD [Var x; Lit c] [out]) s =
      OK (update_var out (THE (lookup_var x s) + c) s)
Proof
  cheat
QED

Theorem pop_step_MUL_lit:
  !id x c out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id MUL [Var x; Lit c] [out]) s =
      OK (update_var out (THE (lookup_var x s) * c) s)
Proof
  cheat
QED

Theorem pop_step_ADD_var:
  !id x y out s.
    IS_SOME (lookup_var x s) /\ IS_SOME (lookup_var y s) ==>
    step_inst_base (mk_inst id ADD [Var x; Var y] [out]) s =
      OK (update_var out (THE (lookup_var x s) + THE (lookup_var y s)) s)
Proof
  cheat
QED

Theorem pop_step_MSTORE[local]:
  !id x y s.
    IS_SOME (lookup_var x s) /\ IS_SOME (lookup_var y s) ==>
    step_inst_base (mk_inst id MSTORE [Var x; Var y] []) s =
      OK (mstore (w2n (THE (lookup_var x s))) (THE (lookup_var y s)) s)
Proof
  cheat
QED

Theorem mstore_vs_vars[local]:
  !a v s X. (mstore a v s).vs_vars = s.vs_vars /\
            mstore a v (s with vs_vars := X) = mstore a v s with vs_vars := X
Proof
  cheat
QED

val pop_run_simps =
  [run_inst_seq_def, pop_step_MLOAD, pop_step_ISZERO, pop_step_ASSERT,
   pop_step_SUB_lit, pop_step_ADD_lit, pop_step_MUL_lit, pop_step_ADD_var,
   pop_step_MSTORE, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
   mstore_vs_vars, bool_to_word_def];

(* The fresh names are distinct in the order later outputs are looked up
   past earlier ones (newest first), and none is p: FLOOKUP_UPDATE compares
   the newer key with the one looked up. *)
Theorem dynarray_pop_mem_run_empty:
  !p esz x0 x1 x2 x3 x4 x5 x6 id s w.
    ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0] /\
    lookup_var p s = SOME w /\ mload (w2n w) s = 0w ==>
    ?a s'. run_inst_seq
      [mk_inst id MLOAD [Var p] [x0];
       mk_inst (id + 1) ISZERO [Var x0] [x1];
       mk_inst (id + 2) ISZERO [Var x1] [x2];
       mk_inst (id + 3) ASSERT [Var x2] [];
       mk_inst (id + 4) SUB [Var x0; Lit 1w] [x3];
       mk_inst (id + 5) MSTORE [Var p; Var x3] [];
       mk_inst (id + 6) ADD [Var p; Lit 32w] [x4];
       mk_inst (id + 7) MUL [Var x3; Lit (n2w esz)] [x5];
       mk_inst (id + 8) ADD [Var x4; Var x5] [x6]] s = Abort a s'
Proof
  cheat
QED

Theorem dynarray_pop_mem_run:
  !p esz x0 x1 x2 x3 x4 x5 x6 id s w.
    ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0] /\
    EVERY (\x. x <> p) [x0; x1; x2; x3; x4; x5; x6] /\
    lookup_var p s = SOME w /\ mload (w2n w) s <> 0w ==>
    ?u. run_inst_seq
      [mk_inst id MLOAD [Var p] [x0];
       mk_inst (id + 1) ISZERO [Var x0] [x1];
       mk_inst (id + 2) ISZERO [Var x1] [x2];
       mk_inst (id + 3) ASSERT [Var x2] [];
       mk_inst (id + 4) SUB [Var x0; Lit 1w] [x3];
       mk_inst (id + 5) MSTORE [Var p; Var x3] [];
       mk_inst (id + 6) ADD [Var p; Lit 32w] [x4];
       mk_inst (id + 7) MUL [Var x3; Lit (n2w esz)] [x5];
       mk_inst (id + 8) ADD [Var x4; Var x5] [x6]] s = OK u /\
      u.vs_memory = (mstore (w2n w) (mload (w2n w) s - 1w) s).vs_memory /\
      u = s with <| vs_vars := u.vs_vars; vs_memory := u.vs_memory |> /\
      (!x. ~MEM x [x0; x1; x2; x3; x4; x5; x6] ==>
           lookup_var x u = lookup_var x s) /\
      lookup_var x6 u =
        SOME (w + 32w + (mload (w2n w) s - 1w) * n2w esz)
Proof
  cheat
QED

(* ===== The simulation ===== *)

Theorem pop_ptr_w2n:
  !w len esz.
    0 < len /\ w2n (w:bytes32) + 32 + len * esz < dimword (:256) ==>
    w2n (w + 32w + (n2w len - 1w) * n2w esz) = w2n w + 32 + (len - 1) * esz
Proof
  cheat
QED

(* The popped element's footprint lies in the local's region. *)
Theorem pop_elem_fits:
  !len n esz fp sz base.
    0 < len /\ len <= n /\ fp <= esz /\ 32 + n * esz <= sz ==>
    base + 32 + (len - 1) * esz + fp <= base + sz
Proof
  cheat
QED

Theorem value_has_type_dynarray[local]:
  !etv n v.
    value_has_type (ArrayTV etv (Dynamic n)) v ==>
    ?vs. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= n /\ all_have_type etv vs
Proof
  cheat
QED

(* What expr_sim_pre and stmt_state_rel give of the local popped from. *)
Theorem pop_name_facts:
  !cenv cx env ann id es func s0 ctx.
    expr_sim_pre cenv cx env (Pop ann (NameTarget id)) es /\
    stmt_state_rel ctx func cenv cx es s0 ==>
    ?n p sz entry etv vs w.
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME (ArrayT ann (Dynamic n)) /\
      lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
      evaluate_type (get_tenv cx) ann = SOME etv /\
      evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) =
        SOME (ArrayTV etv (Dynamic n)) /\
      entry.type = ArrayTV etv (Dynamic n) /\
      entry.value = ArrayV (DynArrayV vs) /\
      LENGTH vs <= n /\ n < dimword (:256) /\ elems_val_wf vs etv /\
      EVERY (value_has_type etv) vs /\
      type_memory_bytes cenv ann = type_memory_size etv /\
      lookup_var p s0 = SOME w /\ local_backed func p s0 (w2n w) sz /\
      w2n w + sz <= s0.vs_alloca_next /\
      32 + n * type_memory_size etv <= sz /\
      mem_word_at (w2n w) s0.vs_memory = n2w (LENGTH vs) /\
      elems_in_memory vs (w2n w + 32) etv s0.vs_memory
Proof
  cheat
QED

(* The local after the pop: its region holds the shortened array, and the
   other live locals' regions are untouched by the store of the length. *)
Theorem pop_local_ptrs_rel:
  !func cenv es s0 u id pre env entry rest p sz w etv n vs.
    local_ptrs_rel func cenv es.scopes s0 /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s0 = SOME w /\ local_backed func p s0 (w2n w) sz /\
    w2n w + sz <= s0.vs_alloca_next /\
    entry.type = ArrayTV etv (Dynamic n) /\ vs <> [] /\
    LENGTH vs <= n /\ elems_val_wf vs etv /\
    32 + n * type_memory_size etv <= sz /\
    elems_in_memory vs (w2n w + 32) etv s0.vs_memory /\
    u.vs_memory = (mstore (w2n w) (n2w (LENGTH vs) - 1w) s0).vs_memory /\
    u.vs_allocas = s0.vs_allocas /\ u.vs_alloca_next = s0.vs_alloca_next /\
    (!q n' sq. FLOOKUP cenv.ce_vars n' = SOME (PtrVar (Var q) sq) ==>
               lookup_var q u = lookup_var q s0) ==>
    local_ptrs_rel func cenv
      (pre ++ env |+ (id, pop_name_entry entry vs)
         :: rest) u
Proof
  cheat
QED

(* stmt_state_rel after the pop: the source changed only the scopes, Venom
   only variables and memory. *)
Theorem pop_stmt_state_rel:
  !func cenv cx es es' s0 u ctx.
    stmt_state_rel ctx func cenv cx es s0 /\
    local_ptrs_rel func cenv es'.scopes u /\
    es' = es with scopes := es'.scopes /\
    u = s0 with <| vs_vars := u.vs_vars; vs_memory := u.vs_memory |> /\
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es u /\
    (!id b sz. local_region cenv es'.scopes u id b sz ==>
       ?id0. local_region cenv es.scopes s0 id0 b sz) /\
    immutable_base_zero cenv u ==>
    stmt_state_rel ctx func cenv cx es' u
Proof
  cheat
QED

Theorem pop_stmt_state_rel_scopes:
  !func cenv cx es sc s0 u ctx.
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_rel func cenv sc u /\
    u = s0 with <| vs_vars := u.vs_vars; vs_memory := u.vs_memory |> /\
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es u /\
    (!id b sz. local_region cenv sc u id b sz ==>
       ?id0. local_region cenv es.scopes s0 id0 b sz) /\
    immutable_base_zero cenv u ==>
    stmt_state_rel ctx func cenv cx (es with scopes := sc) u
Proof
  cheat
QED

Theorem lookup_var_inst_idx[local]:
  !x s k. lookup_var x (s with vs_inst_idx := k) = lookup_var x s
Proof
  cheat
QED

(* The popped element, at its address in the local's region. *)
Theorem pop_elem_in_memory:
  !vs w etv esz s0 u.
    vs <> [] /\ esz = type_memory_size etv /\ elems_val_wf vs etv /\
    elems_in_memory vs (w2n w + 32) etv s0.vs_memory /\
    u.vs_memory = (mstore (w2n w) (n2w (LENGTH vs) - 1w) s0).vs_memory ==>
    val_in_memory etv (LAST vs) (w2n w + 32 + (LENGTH vs - 1) * esz)
      u.vs_memory
Proof
  cheat
QED

Theorem pop_regions_backwards[local]:
  find_containing_scope id es.scopes = SOME (pre,envs,entry,rest) /\
  (!q n sq. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) ==>
     lookup_var q u = lookup_var q s0) ==>
  !j b sz. local_region cenv
    (pre ++ envs |+ (id,pop_name_entry entry vs) :: rest) u j b sz ==>
    ?j0. local_region cenv es.scopes s0 j0 b sz
Proof
  cheat
QED

Theorem pop_local_mstore_immutables[local]:
  stmt_state_rel ctx func cenv cx es s0 /\
  local_region cenv es.scopes s0 id b sz /\ 32 <= sz /\
  u.vs_memory = (mstore b w s0).vs_memory /\
  u.vs_data_section = s0.vs_data_section ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es u
Proof
  cheat
QED

(* The store of the new length leaves the live locals' memory as
   locals_kept allows: the popped local is a dynamic array, whose length word
   is exempt, and the other locals' regions are disjoint from its region. *)
Theorem pop_locals_kept[local]:
  !func cenv es s0 u id entry p sz w et n v.
    local_ptrs_rel func cenv es.scopes s0 /\
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s0 = SOME w /\ 32 <= sz /\
    cenv.ce_var_type id = SOME (ArrayT et (Dynamic n)) /\
    u.vs_memory = (mstore (w2n w) v s0).vs_memory ==>
    locals_kept cenv es s0 u
Proof
  cheat
QED

Theorem pop_vv_post:
  !func cenv cx ann id es sa sb s0 u k pre envs entry rest p sz w etv n vs x6 ctx.
    stmt_state_rel ctx func cenv cx es s0 /\
    local_ptrs_rel func cenv es.scopes s0 /\
    find_containing_scope id es.scopes = SOME (pre, envs, entry, rest) /\
    cenv.ce_var_type id = SOME (ArrayT ann (Dynamic n)) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s0 = SOME w /\ local_backed func p s0 (w2n w) sz /\
    w2n w + sz <= s0.vs_alloca_next /\
    entry.type = ArrayTV etv (Dynamic n) /\ vs <> [] /\
    LENGTH vs <= n /\ elems_val_wf vs etv /\
    32 + n * type_memory_size etv <= sz /\
    elems_in_memory vs (w2n w + 32) etv s0.vs_memory /\
    u.vs_memory = (mstore (w2n w) (n2w (LENGTH vs) - 1w) s0).vs_memory /\
    u = s0 with <| vs_vars := u.vs_vars; vs_memory := u.vs_memory |> /\
    (!q n' sq. FLOOKUP cenv.ce_vars n' = SOME (PtrVar (Var q) sq) ==>
               lookup_var q u = lookup_var q s0) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0) /\
    (!q. cenv.ce_imm_alloca = SOME (Var q) ==>
         lookup_var q u = lookup_var q s0) /\
    lookup_var x6 u =
      SOME (w + 32w + (n2w (LENGTH vs) - 1w) * n2w (type_memory_size etv)) /\
    EVERY (value_has_type etv) vs /\
    evaluate_type (get_tenv cx) ann = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) =
      SOME (ArrayTV etv (Dynamic n)) ==>
    vv_post ctx func cenv cx (Pop ann (NameTarget id)) es sa sb s0
      (es with scopes :=
         pre ++ envs |+ (id, pop_name_entry entry vs)
           :: rest)
      (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))]))
      (LocatedValue ann (mk_ptr (Var x6) LocMemory))
      (u with vs_inst_idx := k)
Proof
  cheat
QED

(* The empty pop raises without touching the state. *)
Theorem eval_pop_name_empty[local]:
  !cx ann id es entry.
    lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
    entry.value = ArrayV (DynArrayV []) ==>
    eval_expr cx (Pop ann (NameTarget id)) es =
      (INR (Error (RuntimeError "pop empty memory array")), es)
Proof
  cheat
QED

Theorem eval_pop_name_ok[local]:
  !cx ann id es entry vs pre env rest.
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
    entry.value = ArrayV (DynArrayV vs) /\ vs <> [] ==>
    eval_expr cx (Pop ann (NameTarget id)) es =
      (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))])),
       es with scopes := pre ++ env |+ (id, pop_name_entry entry vs) :: rest)
Proof
  cheat
QED

(* TOP-LEVEL *)
Theorem compile_pop_name_sim:
  !ctx func cenv cx env ty ann id es.
    expr_sim_pre cenv cx env (Pop ann (NameTarget id)) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann (NameTarget id)) es
Proof
  cheat
QED
