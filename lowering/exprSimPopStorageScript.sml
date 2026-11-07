Theory exprSimPopStorage
Ancestors
  exprSimDefs exprSimProps loweringPosts
  exprSimPop exprSimLen exprSimLeaves accountsRelProps
  vyperInterpreter vyperState vyperValueOperation finite_map
  vyperTypeAssignContext vyperPlaceResultTyping vyperTypeEnv vyperTypeInvariants
  vyperStorageBackend vyperStorage
  exprLowering compileEnv vyperAST emitHelper
  exprSimHyps exprSimHypsDefs exprSimAttributeFields exprSimFieldLayout vfmState
  exprLoweringProps venomState vyperLookupStorage list
  emitHelperProps venomExecSemantics venomInst exprSimVVFrame
  gasOutcome gasSummary fragExec fragGasMode fragGasPath fragGasSeq fragGasSeqAbort
  exprSimTopLevelProps

(* Evaluation at a known declared dynamic-array slot, outside a static frame.
   This boundary does not assume that all top-level declarations are storage
   declarations. *)
Theorem eval_pop_storage:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (ArrayT et (Dynamic n)), name) /\
  lookup_var_slot_from_layout cx tr src name = SOME slot /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic n)) = SOME (ArrayTV tv (Dynamic n)) /\
  ~cx.txn.is_static ==>
  eval_expr cx (Pop ann (TopLevelNameTarget (src,id))) es =
    let len = w2n (lookup_storage (n2w slot) (get_storage cx es tr)) in
    if len = 0 then
      (INR (Error (RuntimeError "pop empty storage array")), es)
    else
      (INL (PlaceR (StoragePlace tr
        (n2w slot + n2w (1 + (len - 1) * type_slot_size tv)) tv)),
       set_storage cx es tr
         (apply_writes (n2w slot) [(0,n2w (len - 1))] (get_storage cx es tr)))
Proof
  cheat
QED

Theorem pop_storage_target_facts:
  well_typed_expr env (Pop ann (TopLevelNameTarget (src,id))) /\
  env_consistent env cx es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME d ==>
  ?n tr name slot tv.
    d = (StorageVarDecl tr (ArrayT ann (Dynamic n)), name) /\
    lookup_var_slot_from_layout cx tr src name = SOME slot /\
    evaluate_type (get_tenv cx) ann = SOME tv /\
    evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) =
      SOME (ArrayTV tv (Dynamic n))
Proof
  cheat
QED

Theorem compile_expr_pop_storage:
  FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (ArrayT et bd) ==>
  compile_expr cenv ty (Pop ann (TopLevelNameTarget (src,id))) sa =
    let loc = if tr then LocTransient else LocStorage in
    let result = compile_dynarray_pop (Lit slot) 1
      (elem_size_in_location cenv loc et)
      cenv.ce_is_ctor cenv.ce_imm_alloca loc sa in
    (LocatedValue ann (mk_ptr (FST result) loc), SND result)
Proof
  cheat
QED

Theorem pop_storage_compiler_facts:
  expr_sim_inv cenv cx env es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, name) ==>
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME typ
Proof
  cheat
QED

Theorem pop_storage_element_size:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  elem_size_in_location cenv (if tr then LocTransient else LocStorage) et =
    type_slot_size tv
Proof
  cheat
QED

(* Shortening the header preserves deadness if the element area is unchanged. *)
Theorem dead_bytes_dynarray_shorten:
  !st st' bs n tv.
  w2n (lookup_storage (n2w bs) st') <=
    w2n (lookup_storage (n2w bs) st) /\
  (!i. bs + 1 <= i /\ i < bs + 1 + n * type_slot_size tv ==>
       lookup_storage (n2w i) st' = lookup_storage (n2w i) st) ==>
  !j b. dead_bytes st bs (ArrayTV tv (Dynamic n)) j b ==>
        dead_bytes st' bs (ArrayTV tv (Dynamic n)) j b
Proof
  cheat
QED

Theorem dead_bytes_pop_header:
  !st (slot:bytes32) tv n.
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword (:256) ==>
  !j b. dead_bytes st (w2n slot) (ArrayTV tv (Dynamic n)) j b ==>
    dead_bytes
      (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
      (w2n slot) (ArrayTV tv (Dynamic n)) j b
Proof
  cheat
QED

Theorem storage_dead_pop_header:
  declared_storage_region cx mid name subs =
    SOME (tr, slot, ArrayTV tv (Dynamic n)) /\
  storage_dead cx tr st j b ==>
  storage_dead cx tr
    (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) j b
Proof
  cheat
QED

Theorem stmt_state_rel_pop_header:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs =
    SOME (tr, slot, ArrayTV tv (Dynamic n)) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr
      (update_storage slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1))
        (get_storage cx es tr)))
    (if tr then
       tstore slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1)) s
     else
       sstore slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1)) s)
Proof
  cheat
QED

Theorem storage_range_agree_dyn_last:
  storage_range_agree st st' w (ArrayTV tv (Dynamic n)) /\
  len = w2n (lookup_storage w st) /\ 0 < len /\ len <= n ==>
  storage_range_agree st st' (w + n2w (1 + (len - 1) * type_slot_size tv)) tv
Proof
  cheat
QED

Theorem storage_range_agree_frame:
  storage_range_agree st st' w tv /\
  (!i. w2n w <= i /\ i < w2n w + type_slot_size tv ==>
       lookup_storage (n2w i) su = lookup_storage (n2w i) st /\
       lookup_storage (n2w i) su' = lookup_storage (n2w i) st') ==>
  storage_range_agree su su' w tv
Proof
  cheat
QED

(* A header write cannot affect a non-wrapping element interval above it. *)
Theorem storage_pop_element_frame:
  storage_range_agree st st' elem tv /\
  (type_slot_size tv = 0 \/ w2n header < w2n elem) ==>
  storage_range_agree
    (apply_writes header [(0,v)] st)
    (apply_writes header [(0,v')] st') elem tv
Proof
  cheat
QED

Theorem pop_element_slots_frame:
  slots_in_range st (w2n elem) tv /\
  w2n elem + type_slot_size tv <= dimword(:256) /\
  (type_slot_size tv = 0 \/ w2n header < w2n elem) ==>
  slots_in_range (apply_writes header [(0,v)] st) (w2n elem) tv
Proof
  cheat
QED

Theorem pop_storage_holds:
  evaluate_type (get_tenv cx) ann = SOME tv /\
  well_formed_type_value tv /\
  slots_in_range (get_storage cx es tr) (w2n elem) tv /\
  storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) elem tv ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem es s
Proof
  cheat
QED

Theorem dynarray_pop_storage_shape:
  !slot tr esz is_ctor imm sa r sb.
    compile_dynarray_pop (Lit slot) 1 esz is_ctor imm
      (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
    ?x0 x1 x2 x3 x4 x5 x6.
      ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
      EVERY (\x. ~not_fresh_at sa x) [x0;x1;x2;x3;x4;x5;x6] /\
      r = Var x6 /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
      sb.cs_current_insts = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
         mk_inst (sa.cs_next_id + 1) ISZERO [Var x0] [x1];
         mk_inst (sa.cs_next_id + 2) ISZERO [Var x1] [x2];
         mk_inst (sa.cs_next_id + 3) ASSERT [Var x2] [];
         mk_inst (sa.cs_next_id + 4) SUB [Var x0; Lit 1w] [x3];
         mk_inst (sa.cs_next_id + 5) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
         mk_inst (sa.cs_next_id + 6) ADD [Lit slot; Lit 1w] [x4];
         mk_inst (sa.cs_next_id + 7) MUL [Var x3; Lit (n2w esz)] [x5];
         mk_inst (sa.cs_next_id + 8) ADD [Var x4; Var x5] [x6]]
Proof
  cheat
QED

Theorem storage_pop_step_load[local]:
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [out]) s =
    OK (update_var out (if tr then tload slot s else sload slot s) s)
Proof
  cheat
QED

Theorem storage_pop_step_store[local]:
  IS_SOME (lookup_var x s) /\ ~s.vs_call_ctx.cc_static ==>
  step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [Lit slot; Var x] []) s =
    OK (if tr then tstore slot (THE (lookup_var x s)) s
        else sstore slot (THE (lookup_var x s)) s)
Proof
  cheat
QED

Theorem storage_pop_step_add_literals[local]:
  step_inst_base (mk_inst id ADD [Lit a; Lit b] [out]) s =
    OK (update_var out (a+b) s)
Proof
  cheat
QED

Theorem storage_pop_vars[local]:
  (sstore a v s).vs_vars = s.vs_vars /\
  (tstore a v s).vs_vars = s.vs_vars /\
  sstore a v (s with vs_vars := X) = sstore a v s with vs_vars := X /\
  tstore a v (s with vs_vars := X) = tstore a v s with vs_vars := X
Proof
  cheat
QED

val storage_pop_run_simps =
  [run_inst_seq_def, storage_pop_step_load, storage_pop_step_store,
   storage_pop_step_add_literals, pop_step_ISZERO, pop_step_ASSERT,
   pop_step_SUB_lit, pop_step_MUL_lit, pop_step_ADD_var, storage_pop_vars, lookup_var_def, update_var_def,
   FLOOKUP_UPDATE, bool_to_word_def];

Theorem dynarray_pop_storage_run_empty:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  (if tr then tload slot s else sload slot s) = 0w ==>
  ?a s'. run_inst_seq
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] [];
     mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
     mk_inst (id+5) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
     mk_inst (id+6) ADD [Lit slot; Lit 1w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]] s = Abort a s'
Proof
  cheat
QED

Theorem dynarray_pop_storage_run:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\ ~s.vs_call_ctx.cc_static /\
  (if tr then tload slot s else sload slot s) <> 0w ==>
  ?u. run_inst_seq
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] [];
     mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
     mk_inst (id+5) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
     mk_inst (id+6) ADD [Lit slot; Lit 1w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]] s = OK u /\
    u = (if tr then tstore slot (tload slot s - 1w) s
         else sstore slot (sload slot s - 1w) s) with vs_vars := u.vs_vars /\
    (!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==> lookup_var x u = lookup_var x s) /\
    lookup_var x6 u = SOME (slot + 1w +
      ((if tr then tload slot s else sload slot s) - 1w) * n2w esz)
Proof
  cheat
QED

(* Postcondition packaging stays independent of the header-write proof. *)
Theorem pop_storage_vv_post:
  stmt_state_rel ctx func cenv cx es' u /\
  storage_holds cx tr ann tv slot es' u /\
  lookup_var x u = SOME slot /\
  u.vs_memory = s0.vs_memory /\ u.vs_allocas = s0.vs_allocas /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s0) ==>
  vv_post ctx func cenv cx (Pop ann tgt) es sa sb s0 es' tv
    (LocatedValue ann (mk_ptr (Var x) (if tr then LocTransient else LocStorage))) u
Proof
  cheat
QED

Theorem pop_declared_array_agree:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) ==>
  storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s)
    w (ArrayTV tv (Dynamic n))
Proof
  cheat
QED

Theorem pop_declared_array_slots:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) ==>
  slots_in_range (get_storage cx es tr) (w2n w) (ArrayTV tv (Dynamic n))
Proof
  cheat
QED

Theorem pop_declared_header_load:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) ==>
  (if tr then tload w s else sload w s) =
    lookup_storage w (get_storage cx es tr)
Proof
  cheat
QED

Theorem pop_array_length_bound:
  slots_in_range st (w2n w) (ArrayTV tv (Dynamic n)) ==>
  w2n (lookup_storage w st) <= n
Proof
  cheat
QED

Theorem pop_array_last_slots:
  slots_in_range st (w2n w) (ArrayTV tv (Dynamic n)) /\
  len = w2n (lookup_storage w st) /\ 0 < len ==>
  slots_in_range st
    (w2n (w + n2w (1 + (len - 1) * type_slot_size tv))) tv
Proof
  cheat
QED


Theorem pop_array_last_bounds:
  0 < len /\ len <= n /\
  w2n (w:bytes32) + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) ==>
  w2n (w + n2w (1 + (len - 1) * type_slot_size tv)) + type_slot_size tv <=
    dimword(:256) /\
  (type_slot_size tv = 0 \/
   w2n w < w2n (w + n2w (1 + (len - 1) * type_slot_size tv)))
Proof
  cheat
QED

Theorem pop_storage_updated_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) /\
  local_ptrs_reserved cenv sa /\
  u = (if tr then tstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1)) s
       else sstore w (n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1)) s)
        with vs_vars := u.vs_vars /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr
      (apply_writes w [(0,n2w (w2n (lookup_storage w (get_storage cx es tr)) - 1))]
        (get_storage cx es tr))) u
Proof
  cheat
QED

Theorem pop_storage_positive_holds:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid id [] = SOME (tr,w,ArrayTV tv (Dynamic n)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage w (get_storage cx es tr)) /\ 0 < len /\
  elem = w + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore w (n2w (len - 1)) s else sstore w (n2w (len - 1)) s)
        with vs_vars := u.vs_vars ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
    (set_storage cx es tr (apply_writes w [(0,n2w (len - 1))] (get_storage cx es tr))) u
Proof
  cheat
QED

Theorem pop_storage_gas_obs[local]:
  get_storage cx (es with gas_obs := g) tr = get_storage cx es tr /\
  set_storage cx (es with gas_obs := g) tr X =
    set_storage cx es tr X with gas_obs := g
Proof
  cheat
QED

Theorem pop_storage_holds_gas_obs[local]:
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tvv)) w es s ==>
  storage_holds cx tr t (PlaceR (StoragePlace tr' sl tvv)) w
    (es with gas_obs := g) s
Proof
  cheat
QED

Theorem pop_ssr_gas_obs[local]:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with gas_obs := g) s
Proof
  cheat
QED

Theorem compile_pop_storage_normalized_sim:
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (ArrayT ann (Dynamic n)), name) /\
  lookup_var_slot_from_layout cx tr src name = SOME slot /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) = SOME (ArrayTV tv (Dynamic n)) ==>
  expr_vv_sim ctx func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  cheat
QED



