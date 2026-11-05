(*
 * Expression simulation: pop on a nested target (x.a.pop(), x[i].pop(),
 * self.s.a.pop(), self.m[k].pop()).
 *
 * The lowering takes the array's pointer, location and type from
 * compile_get_target_ptr, as an assignment does, then runs
 * compile_dynarray_pop at that pointer.  The case lemmas take the target's
 * fragment judgment (pop_target_frag, which targetPlaceSimCases'
 * target_place_sim gives from target_sim) and split on the target's root:
 *
 *   pop_nested_storage_pure_sim — a storage or transient root with pure
 *                             indices: the header load and store and the
 *                             element's slots, as exprSimPopStorage's
 *                             compile_pop_storage_sim has them at a
 *                             declared variable's slot.
 *   pop_nested_storage_effectful_sim — RESIDUAL: a storage root with an
 *                             index that pops or calls, which can leave
 *                             the target's header dead.
 *   pop_nested_immutable_runtime_sim — an immutable or constant root at
 *                             runtime: such a target does not type
 *                             (bare_global_assignable is empty at runtime).
 *   pop_nested_immutable_deploy_sim — RESIDUAL: an immutable root in the
 *                             constructor, which Python accepts for a
 *                             member of a complex immutable.
 *   pop_nested_local_sim    — RESIDUAL: a memory local root, whose
 *                             nested length word locals_kept does not
 *                             exempt yet.
 *
 *   pop_nested_expr_target_frag — RESIDUAL: the target's fragment judgment
 *                             at the expression level; target_pre's
 *                             target_env_ok asks for every declaration's
 *                             metadata, where the target needs its root's.
 *)

Theory exprSimPopNested
Ancestors
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* The target's fragment, typed ty, evaluates to a place at the pointer
   (target_place_sim's conclusion, at every start). *)
Definition pop_target_frag_def:
  pop_target_frag ctx func cenv cx env bt es <=>
    !ty sa sb r res es' s0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      eval_target_place cx bt es = (res, es') /\
      ((?p. res = INL p) \/ (?m. res = INR (Error (RuntimeError m))) \/
       (?d. res = INR (Error (RevertData d))) \/
       (?str. res = INR (AssertException str))) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?p. res = INL p /\
                 target_post ctx func cenv cx es sa sb s0 es' (PlaceR p)
                   (Type ty) r s)
        (expr_exit res)
End

Theorem pop_target_frag_of_sim:
  !ctx func cenv cx env bt es.
    target_sim ctx func cenv cx env bt es ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  cheat
QED

Definition nested_pop_suffix_def[local]:
  nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 =
    [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] [];
     mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
     mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr; Var x3] [];
     mk_inst (id+6) ADD [hdr; Lit 1w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]]
End

Theorem nested_pop_suffix_shape[local]:
  !hdr tr esz is_ctor imm sa r sb.
    compile_dynarray_pop hdr 1 esz is_ctor imm
      (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
    ?x0 x1 x2 x3 x4 x5 x6.
      ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
      EVERY (\x. ~not_fresh_at sa x) [x0;x1;x2;x3;x4;x5;x6] /\
      r = Var x6 /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
      sb.cs_current_insts = sa.cs_current_insts ++
        nested_pop_suffix hdr tr sa.cs_next_id esz x0 x1 x2 x3 x4 x5 x6
Proof
  cheat
QED

Theorem nested_pop_step_load[local]:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]) s =
    OK (update_var out (if tr then tload (THE (eval_operand hdr s)) s
                       else sload (THE (eval_operand hdr s)) s) s)
Proof
  cheat
QED

Theorem nested_pop_step_store[local]:
  IS_SOME (eval_operand hdr s) /\ IS_SOME (lookup_var x s) ==>
  step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [hdr; Var x] []) s =
    OK (if tr then tstore (THE (eval_operand hdr s)) (THE (lookup_var x s)) s
        else sstore (THE (eval_operand hdr s)) (THE (lookup_var x s)) s)
Proof
  cheat
QED

Theorem nested_pop_step_add[local]:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id ADD [hdr; Lit 1w] [out]) s =
    OK (update_var out (THE (eval_operand hdr s) + 1w) s)
Proof
  cheat
QED


Theorem nested_pop_suffix_empty[local]:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME slot /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  (if tr then tload slot s else sload slot s) = 0w ==>
  ?a s'. run_inst_seq
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = Abort a s'
Proof
  cheat
QED

Theorem nested_pop_suffix_run[local]:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME slot /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  (if tr then tload slot s else sload slot s) <> 0w ==>
  ?u. run_inst_seq
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = OK u /\
    u = (if tr then tstore slot (tload slot s - 1w) s
         else sstore slot (sload slot s - 1w) s) with vs_vars := u.vs_vars /\
    (!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==> lookup_var x u = lookup_var x s) /\
    lookup_var x6 u = SOME (slot + 1w +
      ((if tr then tload slot s else sload slot s) - 1w) * n2w esz)
Proof
  cheat
QED

(* A storage or transient root whose indices are pure (no pop, no call).
   compile_get_target_ptr hands out the array's header slot with location
   storage (transient), and the source's pop_place pops the StoragePlace
   there, so the run is compile_pop_storage_sim's at that slot: the header
   load, the abort on zero, the store of the length less one, and the last
   element's slot.  The element is past the new length, so its slots are
   dead in the array; storage_holds asks for them to agree
   (storage_range_agree), before the pop by storage_rel and after it since
   only the header slot changed.  Pure indices leave the state alone, so
   the header the target points at stays live. *)
Theorem nested_pop_lookup_frame[local]:
  off + sz <= dimword (:256) /\
  (w2n slot < off \/ off + sz <= w2n slot) ==>
  !i. off <= i /\ i < off + sz ==>
    lookup_storage (n2w i) (update_storage slot u st) =
    lookup_storage (n2w i) st
Proof
  cheat
QED

Theorem nested_pop_array_offset_frame[local]:
  !(a:num) (k:num) (base:num) (sz:num) (slot:bytes32).
  a <> k /\ base + k * sz <= w2n slot /\
  w2n slot < base + (k + 1) * sz ==>
  w2n slot < base + a * sz \/ base + (a + 1) * sz <= w2n slot
Proof
  cheat
QED

Theorem nested_pop_dead_list[local]:
  !tvs i elem off slot u st.
    oEL i tvs = SOME elem /\
    off + type_slot_size_list tvs <= dimword (:256) /\
    off + tuple_prefix_slot_size i tvs <= w2n slot /\
    w2n slot < off + tuple_prefix_slot_size i tvs + type_slot_size elem /\
    (!j b. dead_bytes st (off + tuple_prefix_slot_size i tvs) elem j b ==>
      dead_bytes (update_storage slot u st)
        (off + tuple_prefix_slot_size i tvs) elem j b) ==>
    !j b. dead_bytes_list st off tvs j b ==>
      dead_bytes_list (update_storage slot u st) off tvs j b
Proof
  cheat
QED

Theorem nested_pop_dead_fields[local]:
  !fields id delta elem off slot u st.
    struct_field_slot fields id = SOME (delta,elem) /\
    off + type_slot_size (StructTV fields) <= dimword (:256) /\
    off + delta <= w2n slot /\
    w2n slot < off + delta + type_slot_size elem /\
    (!j b. dead_bytes st (off + delta) elem j b ==>
      dead_bytes (update_storage slot u st) (off + delta) elem j b) ==>
    !j b. dead_bytes_fields st off fields j b ==>
      dead_bytes_fields (update_storage slot u st) off fields j b
Proof
  cheat
QED

Theorem nested_pop_dead_bytes_subregion[local]:
  !path root delta etv n off slot st j b.
    storage_subregion root path delta (ArrayTV etv (Dynamic n)) /\
    off + type_slot_size root <= dimword (:256) /\
    w2n slot = off + delta /\
    dead_bytes st off root j b ==>
    dead_bytes (update_storage slot
      (n2w (w2n (lookup_storage slot st) - 1)) st) off root j b
Proof
  cheat
QED

Theorem nested_pop_eval_base_pure_state[local]:
  !bt cx st res st'.
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (res,st') ==> st' = st
Proof
  cheat
QED

Theorem nested_pop_eval_target_pure_state[local]:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (res,st') ==> st' = st
Proof
  cheat
QED

Theorem nested_pop_dead_tuple_selected[local]:
  !tvs k elem st off j b.
    oEL k tvs = SOME elem /\ dead_bytes_list st off tvs j b /\
    off + tuple_prefix_slot_size k tvs <= j /\
    j < off + tuple_prefix_slot_size k tvs + type_slot_size elem ==>
    dead_bytes st (off + tuple_prefix_slot_size k tvs) elem j b
Proof
  cheat
QED

Theorem nested_pop_live_fixed_element[local]:
  !cx tr st w elem n k.
    storage_read_live cx tr st w (ArrayTV elem (Fixed n)) /\ k < n ==>
    storage_read_live cx tr st (w + n2w (k * type_slot_size elem)) elem
Proof
  cheat
QED

Theorem nested_pop_live_dynamic_element[local]:
  !cx tr st w elem n k.
    storage_read_live cx tr st w (ArrayTV elem (Dynamic n)) /\
    k < n /\ k < w2n (lookup_storage w st) ==>
    storage_read_live cx tr st (w + n2w (k * type_slot_size elem + 1)) elem
Proof
  cheat
QED

Theorem nested_pop_live_tuple_element[local]:
  !cx tr st w tvs k elem.
    storage_read_live cx tr st w (TupleTV tvs) /\ oEL k tvs = SOME elem ==>
    storage_read_live cx tr st (w + n2w (tuple_prefix_slot_size k tvs)) elem
Proof
  cheat
QED

Theorem nested_pop_resolve_array_empty[local]:
  resolve_array_element cx tr slot tv [] st = (INL (slot,tv,[]),st)
Proof
  cheat
QED

Theorem nested_pop_extend_storage_live[local]:
  get_storage_backend cx tr st = (INL raw,st) /\
  storage_read_live cx tr raw slot tv /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr' slot' tv'),st') ==>
  tr' = tr /\ storage_read_live cx tr raw slot' tv'
Proof
  cheat
QED

Definition nested_pop_result_live_def:
  nested_pop_result_live cx st (PlaceR (StoragePlace tr slot tv)) =
    (!raw. get_storage_backend cx tr st = (INL raw,st) ==>
       storage_read_live cx tr raw slot tv) /\
  nested_pop_result_live cx st (PlaceR _) = T /\
  nested_pop_result_live cx st (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  nested_pop_result_live cx st (Value _) = T
End

Theorem nested_pop_mapping_leaf_live[local]:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  storage_read_live cx tr raw slot tv
Proof
  cheat
QED

Theorem nested_pop_lookup_global_live[local]:
  lookup_global cx mid var_name st = (INL pv,st') ==>
  nested_pop_result_live cx st pv
Proof
  cheat
QED

Theorem nested_pop_extend_result_live[local]:
  nested_pop_result_live cx st pv /\
  extend_place cx pv sb st = (INL pv',st') ==>
  nested_pop_result_live cx st pv'
Proof
  cheat
QED

Theorem nested_pop_eval_base_live[local]:
  !bt cx st pv st'.
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (INL pv,st') ==>
    nested_pop_result_live cx st pv
Proof
  cheat
QED

Theorem nested_pop_eval_target_live[local]:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  storage_read_live cx tr raw slot tv
Proof
  cheat
QED

Theorem nested_pop_eval_target_live_post[local]:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st' = (INL raw,st') ==>
  storage_read_live cx tr raw slot tv
Proof
  cheat
QED

Theorem nested_pop_storage_dead_header[local]:
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta /\ storage_dead cx tr st j b ==>
  storage_dead cx tr
    (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) j b
Proof
  cheat
QED

Theorem nested_pop_stmt_state_rel_header[local]:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta ==>
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

Theorem nested_pop_live_array_agree[local]:
  stmt_state_rel ctx func cenv cx es s /\
  storage_read_live cx tr (vyperStorageBackend$get_storage cx es tr) slot (ArrayTV tv (Dynamic n)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) ==>
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) slot (ArrayTV tv (Dynamic n))
Proof
  cheat
QED

Theorem nested_pop_array_header_load[local]:
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) slot (ArrayTV tv (Dynamic n)) ==>
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (vyperStorageBackend$get_storage cx es tr)
Proof
  cheat
QED

Theorem nested_pop_updated_state_rel[local]:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta /\
  local_ptrs_reserved cenv sa /\
  u = (if tr then tstore slot
         (n2w (w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr)) - 1)) s
       else sstore slot
         (n2w (w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr)) - 1)) s)
        with vs_vars := u.vs_vars /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes slot [(0,n2w (w2n (lookup_storage slot
        (vyperStorageBackend$get_storage cx es tr)) - 1))]
        (vyperStorageBackend$get_storage cx es tr))) u
Proof
  cheat
QED

Theorem nested_pop_positive_holds[local]:
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) w (ArrayTV tv (Dynamic n)) /\
  slots_in_range (vyperStorageBackend$get_storage cx es tr) (w2n w) (ArrayTV tv (Dynamic n)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage w (vyperStorageBackend$get_storage cx es tr)) /\ 0 < len /\
  elem = w + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore w (n2w (len - 1)) s else sstore w (n2w (len - 1)) s)
        with vs_vars := u.vs_vars ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes w [(0,n2w (len - 1))] (vyperStorageBackend$get_storage cx es tr))) u
Proof
  cheat
QED

Theorem nested_pop_target_callback_cong[local]:
  !bt f g cenv.
    (!e. MEM e (target_indices bt) ==> !ce t st. f ce t e st = g ce t e st) ==>
    compile_get_target_ptr f cenv bt = compile_get_target_ptr g cenv bt
Proof
  cheat
QED

Theorem nested_pop_index_size[local]:
  !bt e. MEM e (target_indices bt) ==> expr_size e < base_assignment_target_size bt
Proof
  cheat
QED

Theorem nested_pop_target_guard_erasure[local]:
  compile_get_target_ptr
    (expr_child_callback (expr_size (Pop ann bt)) f) cenv bt =
  compile_get_target_ptr f cenv bt
Proof
  cheat
QED

Theorem nested_pop_compile_eq[local]:
  compile_expr cenv ty (Pop ann bt) sa =
    (let ((hdr,loc_opt,pt_opt),sm) = compile_get_target_ptr compile_expr cenv bt sa in
     let loc = (case loc_opt of SOME l => l | NONE => LocMemory) in
     let et = (case pt_opt of SOME (ValPT (ArrayT t _)) => t | _ => BaseT (IntT 256)) in
     let (elem,sb) = compile_dynarray_pop hdr (word_scale loc)
       (elem_size_in_location cenv loc et)
       cenv.ce_is_ctor cenv.ce_imm_alloca loc sm in
     (LocatedValue ann (mk_ptr elem loc),sb))
Proof
  cheat
QED

Theorem nested_pop_compile_storage_eq[local]:
  compile_get_target_ptr compile_expr cenv bt sa =
    ((hdr,SOME (if tr then LocTransient else LocStorage),
      SOME (ValPT (ArrayT et (Dynamic n)))),sm) ==>
  compile_expr cenv ty (Pop ann bt) sa =
    (let (elem,sb) = compile_dynarray_pop hdr 1
       (elem_size_in_location cenv (if tr then LocTransient else LocStorage) et)
       cenv.ce_is_ctor cenv.ce_imm_alloca
       (if tr then LocTransient else LocStorage) sm in
     (LocatedValue ann (mk_ptr elem (if tr then LocTransient else LocStorage)),sb))
Proof
  cheat
QED

Theorem nested_pop_extend_storage_class[local]:
  ((?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
   (?tr slot kt vt. pv = HashMapRef tr slot kt vt)) /\
  extend_place cx pv sb st = (INL next,st') ==>
  (?tr slot tv. next = PlaceR (StoragePlace tr slot tv)) \/
  (?tr slot kt vt. next = HashMapRef tr slot kt vt)
Proof
  cheat
QED

Theorem nested_pop_lookup_storage_class[local]:
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
  lookup_global cx src id st = (INL pv,st') ==>
  (?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
  (?tr slot kt vt. pv = HashMapRef tr slot kt vt)
Proof
  cheat
QED

Theorem nested_pop_eval_base_storage_class[local]:
  !bt cx st pv st' src id ts d.
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    eval_base_place cx bt st = (INL pv,st') ==>
    (?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
    (?tr slot kt vt. pv = HashMapRef tr slot kt vt)
Proof
  cheat
QED

Theorem nested_pop_eval_target_storage_class[local]:
  target_root bt = TopLevelNameTarget (src,id) /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
  eval_target_place cx bt st = (INL p,st') ==>
  ?tr slot tv. p = StoragePlace tr slot tv
Proof
  cheat
QED

Theorem nested_pop_storage_target_metadata[local]:
  target_post ctx func cenv cx es sa sm s0 es' (PlaceR (StoragePlace tr slot vt))
    (Type (ArrayT ann (Dynamic n))) (hdr,loc,pt) t ==>
  ?tv. vt = ArrayTV tv (Dynamic n) /\
    evaluate_type (get_tenv cx) ann = SOME tv /\
    eval_operand hdr t = SOME slot /\ loc = SOME (slot_loc tr) /\
    pt = SOME (ValPT (ArrayT ann (Dynamic n))) /\
    (!x. hdr = Var x ==> not_fresh_at sm x) /\
    stmt_state_rel ctx func cenv cx es' t
Proof
  cheat
QED

Theorem nested_pop_storage_natural_region[local]:
  storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) ==>
  ?mid name keys root root_tv path delta.
    declared_storage_region cx mid name keys = SOME (tr,root,root_tv) /\
    storage_subregion root_tv path delta (ArrayTV tv (Dynamic n)) /\
    slot = root + n2w delta /\ w2n slot = w2n root + delta /\
    w2n root + type_slot_size root_tv <= dimword(:256) /\
    w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)
Proof
  cheat
QED

Theorem nested_pop_slots_word_offset[local]:
  slots_in_range raw (w2n (w:bytes32) + off) tv ==>
  slots_in_range raw (w2n (w + n2w off)) tv
Proof
  cheat
QED

Theorem nested_pop_tuple_slots_index[local]:
  !tvs k off raw.
    tuple_slots_in_range raw off tvs /\ k < LENGTH tvs ==>
    slots_in_range raw (off + tuple_prefix_slot_size k tvs) (EL k tvs)
Proof
  cheat
QED

Theorem nested_pop_tuple_slots[local]:
  slots_in_range raw (w2n (w:bytes32)) (TupleTV tvs) /\
  oEL k tvs = SOME tv ==>
  slots_in_range raw (w2n (w + n2w (tuple_prefix_slot_size k tvs))) tv
Proof
  cheat
QED

Theorem nested_pop_fixed_slots[local]:
  slots_in_range raw (w2n (w:bytes32)) (ArrayTV tv (Fixed n)) /\ k < n ==>
  slots_in_range raw (w2n (w + n2w (k * type_slot_size tv))) tv
Proof
  cheat
QED

Theorem nested_pop_dynamic_slots[local]:
  slots_in_range raw (w2n (w:bytes32)) (ArrayTV tv (Dynamic n)) /\
  k < w2n (lookup_storage w raw) ==>
  slots_in_range raw (w2n (w + n2w (k * type_slot_size tv + 1))) tv
Proof
  cheat
QED

Theorem nested_pop_extend_storage_slots[local]:
  get_storage_backend cx tr st = (INL raw,st) /\
  slots_in_range raw (w2n slot) tv /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr' slot' tv'),st') ==>
  tr' = tr /\ slots_in_range raw (w2n slot') tv'
Proof
  cheat
QED

Definition nested_pop_result_slots_def:
  nested_pop_result_slots cx st (PlaceR (StoragePlace tr slot tv)) =
    (!raw. get_storage_backend cx tr st = (INL raw,st) ==>
       slots_in_range raw (w2n slot) tv) /\
  nested_pop_result_slots cx st (PlaceR _) = T /\
  nested_pop_result_slots cx st (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  nested_pop_result_slots cx st (Value _) = T
End

Theorem nested_pop_mapping_leaf_slots[local]:
  contract_storage_well_formed cx st /\
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  slots_in_range raw (w2n slot) tv
Proof
  cheat
QED

Theorem nested_pop_lookup_global_slots[local]:
  contract_storage_well_formed cx st /\
  lookup_global cx mid var_name st = (INL pv,st') ==>
  nested_pop_result_slots cx st pv
Proof
  cheat
QED

Theorem nested_pop_extend_result_slots[local]:
  contract_storage_well_formed cx st /\
  nested_pop_result_slots cx st pv /\
  extend_place cx pv sb st = (INL pv',st') ==>
  nested_pop_result_slots cx st pv'
Proof
  cheat
QED

Theorem nested_pop_eval_base_slots[local]:
  !bt cx st pv st'.
    contract_storage_well_formed cx st /\
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (INL pv,st') ==>
    nested_pop_result_slots cx st pv
Proof
  cheat
QED

Theorem nested_pop_eval_target_slots[local]:
  contract_storage_well_formed cx st /\
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  slots_in_range raw (w2n slot) tv
Proof
  cheat
QED

Theorem nested_pop_suffix_vv_post[local]:
  target_post ctx func cenv cx es sa sm s0 es pv vt op t /\
  ci_mono sa sm /\ stmt_state_rel ctx func cenv cx es' u /\
  storage_holds cx tr ann v slot es' u /\ lookup_var x u = SOME slot /\
  u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
  (!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q t) ==>
  vv_post ctx func cenv cx (Pop ann bt) es sa r s0 es' v
    (LocatedValue ann (mk_ptr (Var x) (if tr then LocTransient else LocStorage))) u
Proof
  cheat
QED

Theorem nested_pop_storage_suffix_sim[local]:
  expr_sim_inv cenv cx env es /\
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt es = (INL (StoragePlace tr slot (ArrayTV tv (Dynamic n))),es) /\
  target_post ctx func cenv cx es sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n))))
    (Type (ArrayT ann (Dynamic n))) (hdr,SOME (slot_loc tr),pt) t /\
  compile_dynarray_pop hdr 1 (type_slot_size tv) cenv.ce_is_ctor
    cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sm = (q,r) /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) es = (res,es') /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm ==>
  frag_exec ctx sm r (\s. s = t)
    (\s. ?v. res = INL v /\ vv_post ctx func cenv cx (Pop ann bt) es sa r s0 es' v
      (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) s)
    (expr_exit res)
Proof
  cheat
QED




Theorem pop_nested_storage_pure_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED




(* RESIDUAL (effectful storage indices): an index that pops or calls can
   shrink an array the target already points into, so the header the pop
   reads can be dead.  Source and Venom read the same raw slot, but
   stmt_state_rel relates only live storage.  Needs raw agreement on slots
   made dead by a pop.  The AugAssign on a storage place with an
   effectful index, and targetPlaceSimCases' target_subscript_case, have
   the same exposure. *)
Theorem pop_nested_storage_effectful_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

Theorem pop_nested_storage_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

Theorem no_storage_root_untyped_runtime[local]:
  !env cx src id.
    env_context_consistent env cx /\ ~cx.in_deploy /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    type_place_target env (TopLevelNameTarget (src,id)) = NONE
Proof
  cheat
QED

Theorem target_root_untyped[local]:
  !env bt. type_place_target env (target_root bt) = NONE ==>
    type_place_target env bt = NONE
Proof
  cheat
QED

(* An immutable or constant root at runtime: bare_global_assignable is
   empty outside the constructor (bare_global_assignable_complete), so the
   root names a bare global, which type_place_target rejects, and the pop
   does not type. *)
Theorem pop_nested_immutable_runtime_sim:
  !ctx func cenv cx env ann bt ty es src id.
    ~cx.in_deploy /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* RESIDUAL (constructor immutables): pop on a member of an immutable in
   the constructor, which Python's checker accepts for a complex immutable
   (local.py skips the modification count when var_info is None).  The
   lowering loads and stores the length through the immutables buffer
   (compile_ptr_load/compile_ptr_store), and immutable_holds accepts the
   code pointer to the popped element, whose bytes the pop leaves in the
   buffer.  The proof also needs the constructor immutable invariant. *)
Theorem pop_nested_immutable_deploy_sim:
  !ctx func cenv cx env ann bt ty es src id.
    cx.in_deploy /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* RESIDUAL (nested length words), unprovable under the current frame:
   pop on an array inside a memory local.  The pop writes the array's
   length word inside the local's region, which locals_kept exempts only
   for a root dynamic array, so vv_post's locals_kept fails.  Once
   locals_kept exempts every length word in a local's declared type
   (PR #1040), the run is compile_pop_name_sim's at the target's
   pointer. *)
Theorem pop_nested_local_sim:
  !ctx func cenv cx env ann bt ty es id.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

Theorem target_root_cases[local]:
  !bt. (?id. target_root bt = NameTarget id) \/
       (?src id. target_root bt = TopLevelNameTarget (src,id))
Proof
  cheat
QED

(* By the target's root: a local, a storage or transient variable, or a
   module name with no storage declaration (an immutable or a constant). *)
Theorem pop_nested_sim:
  !ctx func cenv cx env ann bt ty es.
    (~immutable_root cx bt ==> pop_target_frag ctx func cenv cx env bt es) /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* RESIDUAL (target metadata): the target's fragment judgment at the
   expression level.  targetPlaceSimCases' target_case_all gives target_sim
   from target_pre, whose target_env_ok asks for every storage and mapping
   declaration of every module to have its type in the compile
   environment's tables.  expr_sim_inv gives that for the storage
   variables, and for a mapping only when its type is in toplevel_vtypes
   (place_map_tables_agree_on_defined), which needs a layout slot.  The
   target only reads its root's entry, which typing puts in
   toplevel_vtypes, so a target_env_ok on the root alone would follow from
   expr_sim_inv. *)
Theorem pop_nested_expr_target_frag:
  !cenv ann bt ctx func cx env es.
    expr_sim_below cenv (expr_size (Pop ann bt)) /\
    expr_sim_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  cheat
QED

(* RESIDUAL (target metadata): the target's fragment judgment in the body,
   where an index may make an internal call.  target_case_all gives
   target_sim from body_base_target_ok's index judgments and target_pre,
   whose target_env_ok asks for every module's storage and mapping
   declarations to be in the compile environment's tables, which body_inv
   gives for the main module only (exprSimPopNested's
   pop_nested_expr_target_frag has the same gap). *)
Theorem body_pop_nested_target_frag:
  !cx bt tops ctx func cenv env ann es.
    body_base_target_ok cx bt /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  cheat
QED
