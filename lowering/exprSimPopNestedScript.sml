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
 *   pop_nested_storage_sim  — a storage or transient root: the header
 *                             load and store and the element's slots, as
 *                             exprSimPopStorage's compile_pop_storage_sim
 *                             has them at a declared variable's slot.
 *   pop_nested_immutable_runtime_sim — an immutable or constant root at
 *                             runtime: such a target does not type
 *                             (bare_global_assignable is empty at runtime).
 *   pop_nested_immutable_deploy_sim — RESIDUAL: an immutable root in the
 *                             constructor, which Python accepts for a
 *                             member of a complex immutable.
 *   pop_nested_local_sim    — RESIDUAL: a memory local root, whose
 *                             nested length word locals_kept does not
 *                             exempt yet.
 *)

Theory exprSimPopNested
Ancestors
  list fragExec exprSim exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map

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
  simp[pop_target_frag_def] >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_tac >> irule target_place_sim >> metis_tac[]
QED

(* Diagnostic: capacity provenance alone does not make a nested header live.
   Once the outer array has length zero, its first child's header is dead,
   although that header is not dead relative to the child itself. *)
Theorem nested_dead_header_probe[local]:
  !st. lookup_storage (0w : bytes32) st = 0w ==>
    dead_bytes st 0
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1)) 1 0 /\
    ~dead_bytes st 1 (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) 1 0
Proof
  rpt strip_tac >> gvs[compileEnvTheory.dead_bytes_def, vyperValueTheory.type_slot_size_def]
QED

(* A storage pop returns a pointer and writes only the outer header; it
   does not erase a nested header in the element that became dead. *)
Theorem nested_pop_header_only_probe[local]:
  !cx es tr.
    lookup_storage (0w : bytes32) (get_storage cx es tr) = 1w ==>
    pop_place cx
      (StoragePlace tr 0w
        (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1))) es =
    (INL (PlaceR (StoragePlace tr 1w
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))),
     set_storage cx es tr
       (apply_writes 0w [(0,0w)] (get_storage cx es tr)))
Proof
  rpt strip_tac >>
  simp[pop_place_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, ignore_bind_def, return_def, check_def, assert_def,
       vyperStorageBackendTheory.write_storage_slot_eq,
       vyperStorageTheory.encode_value_def,
       vyperStorageTheory.encode_base_to_slot_def,
       integer_wordTheory.i2w_def]
QED

Theorem nested_header_update_agree_probe[local]:
  !cx es tr s k.
    k <> (0w : bytes32) /\
    lookup_storage k (get_storage cx es tr) =
      (if tr then tload k s else sload k s) ==>
    lookup_storage k
      (get_storage cx
        (set_storage cx es tr
          (apply_writes 0w [(0,0w)] (get_storage cx es tr))) tr) =
      (if tr then tload k (tstore 0w 0w s)
       else sload k (sstore 0w 0w s))
Proof
  rpt strip_tac >> Cases_on `tr` >>
  gvs[vyperStorageBackendTheory.get_storage_after_set,
      vyperStorageTheory.apply_writes_def,
      venomStateTheory.tload_def, venomStateTheory.tstore_def,
      venomStateTheory.sload_def, venomStateTheory.sstore_def,
      venomStateTheory.contract_transient_def,
      venomStateTheory.contract_storage_def,
      vfmStateTheory.lookup_account_def,
      vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
      combinTheory.APPLY_UPDATE_THM]
QED

Theorem nested_retained_headers_run_probe[local]:
  !cx es tr s id x0 x1 x2 x3 x4 x5 x6.
    ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
    lookup_storage 0w (get_storage cx es tr) = 1w /\
    (if tr then tload 0w s else sload 0w s) = 1w /\
    (!k. k = 1w \/ k = 2w ==>
      lookup_storage k (get_storage cx es tr) =
        (if tr then tload k s else sload k s)) ==>
    ?u.
      pop_place cx (StoragePlace tr 0w
        (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1))
          (Dynamic 1)) (Dynamic 1))) es =
        (INL (PlaceR (StoragePlace tr 1w
          (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1)))),
         set_storage cx es tr
           (apply_writes 0w [(0,0w)] (get_storage cx es tr))) /\
      run_inst_seq
        [mk_inst id (if tr then TLOAD else SLOAD) [Lit 0w] [x0];
         mk_inst (id+1) ISZERO [Var x0] [x1];
         mk_inst (id+2) ISZERO [Var x1] [x2];
         mk_inst (id+3) ASSERT [Var x2] [];
         mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
         mk_inst (id+5) (if tr then TSTORE else SSTORE) [Lit 0w; Var x3] [];
         mk_inst (id+6) ADD [Lit 0w; Lit 1w] [x4];
         mk_inst (id+7) MUL [Var x3; Lit 3w] [x5];
         mk_inst (id+8) ADD [Var x4; Var x5] [x6]] s = OK u /\
      lookup_var x6 u = SOME 1w /\
      (!k. k = 1w \/ k = 2w ==>
        lookup_storage k
          (get_storage cx (set_storage cx es tr
            (apply_writes 0w [(0,0w)] (get_storage cx es tr))) tr) =
          (if tr then tload k u else sload k u))
Proof
  rpt gen_tac >> strip_tac >>
  drule dynarray_pop_storage_run >>
  disch_then (qspecl_then [`tr`, `0w`, `s`, `id`, `3`] mp_tac) >>
  Cases_on `tr` >> (gvs[] >> strip_tac >> qexists_tac `u` >>
  gvs[wordsTheory.WORD_SUB_REFL, wordsTheory.word_add_n2w,
      wordsTheory.word_mul_n2w] >> conj_tac
  >- simp[pop_place_def, vyperStorageBackendTheory.get_storage_backend_eq,
          bind_def, ignore_bind_def, return_def, check_def, assert_def,
          vyperStorageBackendTheory.write_storage_slot_eq,
          vyperStorageTheory.encode_value_def,
          vyperStorageTheory.encode_base_to_slot_def,
          integer_wordTheory.i2w_def] >>
  rpt strip_tac >>
  qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
  gvs[vyperStorageBackendTheory.get_storage_after_set,
      vyperStorageTheory.apply_writes_def,
      venomStateTheory.tload_def, venomStateTheory.tstore_def,
      venomStateTheory.sload_def, venomStateTheory.sstore_def,
      venomStateTheory.contract_transient_def,
      venomStateTheory.contract_storage_def,
      vfmStateTheory.lookup_account_def,
      vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
      combinTheory.APPLY_UPDATE_THM])
QED

(* Shrink-assignment diagnostic: outer capacity two, child capacity one.
   The second child's header and payload occupy slots 3 and 4. *)
Theorem nested_shrink_encode_probe[local]:
  encode_value
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 2))
    (ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7])])) =
    SOME [(0,1w);(1,1w);(2,7w)]
Proof
  EVAL_TAC >> simp[]
QED

Theorem nested_shrink_source_slots_probe[local]:
  !st.
    let st' = apply_writes (0w:bytes32) [(0,1w);(1,1w);(2,7w)] st in
    lookup_storage 3w st' = lookup_storage 3w st /\
    lookup_storage 4w st' = lookup_storage 4w st
Proof
  simp[vyperStorageTheory.apply_writes_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem nested_shrink_assignment_dispatch_probe[local]:
  !cenv ty tr sa.
    compile_assign_value cenv (Lit 0w)
      (if tr then LocTransient else LocStorage) (Lit 0w) F
      (SOME LocMemory) ty ty (SOME (2,64)) 160 sa =
    compile_dynarray_to_storage (Lit 0w) (Lit 0w) 2 64 tr sa
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_assign_value_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def]
QED
(* With both children live, byte agreement at the captured second child
   follows from range agreement; after shrink it does not follow from the
   root's live-byte relation alone. *)
Theorem nested_shrink_initial_live_probe[local]:
  !st b.
    lookup_storage (0w:bytes32) st = 2w /\
    lookup_storage (3w:bytes32) st = 1w ==>
    ~dead_bytes st 0
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 2)) 3 b /\
    ~dead_bytes st 0
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 2)) 4 b
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compileEnvTheory.dead_bytes_def, vyperValueTheory.type_slot_size_def] >>
  gen_tac >> Cases_on `i = 1` >> gvs[] >> decide_tac
QED


Definition nested_shrink_function_def[local]:
  nested_shrink_function tr =
    let st = SND (compile_dynarray_to_storage (Lit 0w) (Lit 0w) 2 64 tr
                   (initial_compile_state "entry")) in
    let st' = SND (emit_void STOP [] st) in
    mk_raw_function "entry"
      (REVERSE st'.cs_blocks ++
       [<|bb_label := st'.cs_current_bb;
          bb_instructions := st'.cs_current_insts|>])
End

Theorem nested_shrink_run_probe[local]:
  !ctx tr h v. case run_blocks 20 ctx (nested_shrink_function tr)
    ((if tr then tstore else sstore) 4w v
      ((if tr then tstore else sstore) 3w h
      (((if tr then tstore else sstore) 0w 2w (init_venom_state "entry")) with vs_memory :=
        word_to_bytes (1w:bytes32) T ++ word_to_bytes (1w:bytes32) T ++
        word_to_bytes (7w:bytes32) T))) of
    Halt s =>
      (if tr then tload else sload) 0w s = 1w /\
      (if tr then tload else sload) 1w s = 1w /\
      (if tr then tload else sload) 2w s = 7w /\
      (if tr then tload else sload) 3w s = h /\
      (if tr then tload else sload) 4w s = v
  | _ => F
Proof
  rpt gen_tac >> Cases_on `tr` >> CONV_TAC (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))
QED
Theorem nested_shrink_paired_slots_probe[local]:
  !ctx tr st h v.
    lookup_storage 3w st = h /\ lookup_storage 4w st = v ==>
    case run_blocks 20 ctx (nested_shrink_function tr)
      ((if tr then tstore else sstore) 4w v
        ((if tr then tstore else sstore) 3w h
        (((if tr then tstore else sstore) 0w 2w (init_venom_state "entry")) with vs_memory :=
          word_to_bytes (1w:bytes32) T ++ word_to_bytes (1w:bytes32) T ++
          word_to_bytes (7w:bytes32) T))) of
      Halt s =>
        let st' = apply_writes (0w:bytes32) [(0,1w);(1,1w);(2,7w)] st in
        lookup_storage 3w st' = (if tr then tload else sload) 3w s /\
        lookup_storage 4w st' = (if tr then tload else sload) 4w s
    | _ => F
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `tr`, `h`, `v`] mp_tac nested_shrink_run_probe >>
  qspec_then `st` strip_assume_tac nested_shrink_source_slots_probe >>
  BasicProvers.TOP_CASE_TAC >> gvs[]
QED


(* Different copy branch: a live outer element contains an inner array
   that becomes empty. Source sparse encoding skips its dead descendants;
   the generated multi-word copy still writes their capacity words. *)
Definition nested_inner_shrink_type_def[local]:
  nested_inner_shrink_type =
    ArrayTV (ArrayTV (ArrayTV
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Fixed 1)) (Dynamic 1)) (Dynamic 1)
End

Definition nested_inner_shrink_ast_type_def[local]:
  nested_inner_shrink_ast_type =
    ArrayT (ArrayT (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 1))
      (Dynamic 1)) (Dynamic 1)
End

Theorem nested_inner_shrink_sizes_probe[local]:
  !cenv.
    type_memory_bytes cenv nested_inner_shrink_ast_type = 128 /\
    type_slot_size nested_inner_shrink_type = 4
Proof
  gen_tac >> EVAL_TAC
QED

Theorem nested_inner_shrink_dispatch_probe[local]:
  !cenv tr sa.
    compile_assign_value cenv (Lit 0w)
      (if tr then LocTransient else LocStorage) (Lit 0w) F
      (SOME LocMemory) nested_inner_shrink_ast_type nested_inner_shrink_ast_type
      (SOME (3,96)) 128 sa =
    compile_dynarray_to_storage (Lit 0w) (Lit 0w) 3 96 tr sa
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_assign_value_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def]
QED

Theorem nested_inner_shrink_encode_probe[local]:
  encode_value nested_inner_shrink_type
    (ArrayV (DynArrayV [ArrayV (DynArrayV [])])) = SOME [(0,1w);(1,0w)]
Proof
  EVAL_TAC
QED

Theorem nested_inner_shrink_memory_probe[local]:
  val_in_memory nested_inner_shrink_type
    (ArrayV (DynArrayV [ArrayV (DynArrayV [])])) 0
    (word_to_bytes (1w:bytes32) T ++ REPLICATE 96 (0w:word8))
Proof
  CONV_TAC (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))
QED

Definition nested_inner_shrink_function_def[local]:
  nested_inner_shrink_function tr =
    let st = SND (compile_dynarray_to_storage (Lit 0w) (Lit 0w) 3 96 tr
                   (initial_compile_state "entry")) in
    let st' = SND (emit_void STOP [] st) in
    mk_raw_function "entry"
      (REVERSE st'.cs_blocks ++
       [<|bb_label := st'.cs_current_bb;
          bb_instructions := st'.cs_current_insts|>])
End

Theorem nested_inner_shrink_run_probe[local]:
  !ctx tr. case run_blocks 24 ctx (nested_inner_shrink_function tr)
    ((if tr then tstore else sstore) 3w 7w
      ((if tr then tstore else sstore) 2w 1w
      ((if tr then tstore else sstore) 1w 1w
      ((if tr then tstore else sstore) 0w 1w
      ((init_venom_state "entry") with vs_memory :=
        word_to_bytes (1w:bytes32) T ++ REPLICATE 96 (0w:word8)))))) of
    Halt s =>
      (if tr then tload else sload) 0w s = 1w /\
      (if tr then tload else sload) 1w s = 0w /\
      (if tr then tload else sload) 2w s = 0w /\
      (if tr then tload else sload) 3w s = 0w
  | _ => F
Proof
  rpt gen_tac >> Cases_on `tr` >> CONV_TAC (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))
QED

Theorem nested_inner_shrink_source_probe[local]:
  !st. lookup_storage (2w:bytes32) st = 1w ==>
    lookup_storage 2w (apply_writes (0w:bytes32) [(0,1w);(1,0w)] st) = 1w
Proof
  simp[vyperStorageTheory.apply_writes_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem nested_captured_fixed_extension_probe[local]:
  !cx es tr.
    extend_place cx
      (PlaceR (StoragePlace tr 2w
        (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Fixed 1))))
      (ValueSubscript (IntV 0)) es =
    (INL (PlaceR (StoragePlace tr 2w
      (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)))), es)
Proof
  rpt gen_tac >>
  simp[extend_place_def, extend_storage_place_def, resolve_array_element_def,
       bind_def, ignore_bind_def, return_def, check_def, assert_def,
       vyperValueTheory.type_slot_size_def]
QED

Theorem nested_captured_fixed_no_load_probe[local]:
  !base idx loader loader' sa.
    compile_array_subscript base idx F 1 1 2 F loader sa =
    compile_array_subscript base idx F 1 1 2 F loader' sa
Proof
  simp[compile_array_subscript_def]
QED

(* Concrete source fixture for the retained-place audit.
   The checked support and expression-typing facts below do NOT establish
   expr_body_pre or a counterexample to either frozen theorem.
   Remaining body-pre obligations:
   - env_context_consistent (function liveness, declaration completeness,
     storage layout, and well-formed vtypes); scopes/immutables consistency;
   - state/accounts/context/functions well-typed; outcomes typed;
   - contract_storage_well_formed, storage_layout_safe, oracle_storage_ok;
   - compile-env flag/struct/module/place-map agreement and popped-key indexing;
   - call_evaluation_safe, using owner (NONE,"caller") and edge to shrink.
   context_well_typed only bounds transaction fields; call_stack_follows
   accepts a singleton stack without requiring a declared caller.
   build_compile_env supplies internal function IDs/info/parameter tables.
   A full compiled witness must package shrink via package_internal_fn and
   install its compiled function in the execution context. The arbitrary
   caller func must contain the target/Pop fragment (fn_has_code) with distinct
   instruction IDs. Neither that execution context nor the universal
   pop_target_frag premise is certified by these syntax checks. *)
Definition nested_counterexample_program_def[local]:
  nested_counterexample_program =
    [VariableDecl Private Storage "a" nested_inner_shrink_ast_type (SOME 0);
     FunctionDecl Internal Nonpayable F F "shrink" [] [] (BaseT (UintT 256))
       [Assign (BaseTarget (TopLevelNameTarget (NONE,"a")))
          (Builtin nested_inner_shrink_ast_type
            (MakeArray (SOME (ArrayT (ArrayT
              (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 1)) (Dynamic 1)))
              (Dynamic 1))
            [Builtin (ArrayT (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1))
                         (Fixed 1)) (Dynamic 1))
               (MakeArray (SOME (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1))
                                 (Fixed 1))) (Dynamic 1)) []]);
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]]
End

Definition nested_counterexample_target_def[local]:
  nested_counterexample_target =
    SubscriptTarget
      (SubscriptTarget
        (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
          (Literal (BaseT (UintT 256)) (IntL 0)))
        (Literal (BaseT (UintT 256)) (IntL 0)))
      (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
End

Definition nested_counterexample_context_def[local]:
  nested_counterexample_context = empty_evaluation_context with
    <| stk := [(NONE,"caller")];
       sources := [(0w, [(NONE,nested_counterexample_program)])];
       layouts := [(0w, ([((NONE,"a"),0)], []))] |>
End

Definition nested_counterexample_env_def[local]:
  nested_counterexample_env =
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY |+ ((NONE,"a"),Type nested_inner_shrink_ast_type);
       type_defs := FEMPTY;
       fn_sigs := FEMPTY |+ ((NONE,"shrink"),
         <| param_types := []; num_defaults := 0; ret_ty := BaseT (UintT 256) |>);
       flag_members := FEMPTY; event_fields := FEMPTY |>
End

Definition nested_counterexample_cenv_def[local]:
  nested_counterexample_cenv =
    build_compile_env nested_counterexample_program External Nonpayable "caller"
      [] (BaseT (UintT 256)) [] T
End

Definition nested_counterexample_state_def[local]:
  nested_counterexample_state =
    SND (set_storage_backend nested_counterexample_context F
      (update_storage 3w 7w (update_storage 2w 1w
        (update_storage 1w 1w (update_storage 0w 1w empty_storage))))
      (empty_state with <| scopes := [FEMPTY]; outcomes := SOME [] |>))
End

Theorem nested_counterexample_typed_probe[local]:
  well_typed_expr nested_counterexample_env
    (Pop (BaseT (UintT 256)) nested_counterexample_target)
Proof
  EVAL_TAC >> simp[subscript_vtype_def] >> EVAL_TAC
QED

Theorem nested_counterexample_syntax_probe[local]:
  int_calls_expr (Pop (BaseT (UintT 256)) nested_counterexample_target) =
    [(NONE,"shrink")] /\
  byte_widths_expr (Pop (BaseT (UintT 256)) nested_counterexample_target) /\
  ~expr_has_evm_run (Pop (BaseT (UintT 256)) nested_counterexample_target) /\
  alloc_limits_expr nested_counterexample_cenv
    (Pop (BaseT (UintT 256)) nested_counterexample_target)
Proof
  EVAL_TAC
QED

Theorem nested_counterexample_supported_probe[local]:
  supported_program nested_counterexample_program
Proof
  EVAL_TAC
QED

Definition nested_counterexample_body_def[local]:
  nested_counterexample_body =
    case LAST nested_counterexample_program of
      FunctionDecl fv fm nr rr id args dflts ret bdy => bdy
    | _ => []
End

Theorem nested_counterexample_module_lookup[local]:
  get_module_code nested_counterexample_context src =
    if src = NONE then SOME nested_counterexample_program else NONE
Proof
  Cases_on `src` >> EVAL_TAC
QED

Theorem nested_counterexample_callable_lookup[local]:
  lookup_callable_function dep fn nested_counterexample_program =
    if fn = "shrink" then
      SOME (Nonpayable,F,[],[],BaseT (UintT 256),nested_counterexample_body)
    else if dep then SOME (Payable,F,[],[],NoneT,[]) else NONE
Proof
  simp[nested_counterexample_program_def, nested_counterexample_body_def,
       lookup_callable_function_def, vyperInterpreterTheory.lookup_function_def] >>
  Cases_on `fn = "shrink"` >> simp[]
QED

Theorem nested_counterexample_body_calls[local]:
  function_int_calls [] nested_counterexample_body = []
Proof
  EVAL_TAC
QED

Theorem nested_counterexample_body_typed[local]:
  env.current_src = NONE /\ env.type_defs = FEMPTY /\
  FLOOKUP env.bare_globals (NONE,"a") = NONE /\
  FLOOKUP env.bare_global_assignable (NONE,"a") = NONE /\
  FLOOKUP env.toplevel_vtypes (NONE,"a") =
    SOME (Type nested_inner_shrink_ast_type) ==>
  type_stmts env (BaseT (UintT 256)) nested_counterexample_body = SOME env
Proof
  strip_tac >>
  simp[nested_counterexample_body_def, nested_counterexample_program_def] >>
  EVAL_TAC >> gvs[nested_inner_shrink_ast_type_def]
QED

Theorem nested_counterexample_toplevel_complete[local]:
  toplevel_vtypes_complete tvs nested_counterexample_context ==>
  FLOOKUP tvs (NONE,"a") = SOME (Type nested_inner_shrink_ast_type)
Proof
  rw[vyperTypeInvariantsTheory.toplevel_vtypes_complete_def] >>
  first_x_assum irule >>
  qexistsl_tac [`SOME 0`, `Storage`, `nested_counterexample_program`, `Private`] >>
  simp[nested_counterexample_module_lookup, nested_counterexample_program_def] >>
  EVAL_TAC
QED

Theorem nested_counterexample_type_env[local]:
  get_tenv nested_counterexample_context = FEMPTY /\
  find_var_decl_by_name "a" nested_counterexample_program =
    SOME (StorageVarDecl F nested_inner_shrink_ast_type,"a") /\
  stmts_no_fallthrough nested_counterexample_body /\
  stmts_no_control_escape nested_counterexample_body
Proof
  EVAL_TAC >> simp[]
QED

Theorem nested_counterexample_context_fields[local]:
  nested_counterexample_context.stk = [(NONE,"caller")] /\
  ~nested_counterexample_context.in_deploy
Proof
  EVAL_TAC
QED

Theorem nested_counterexample_functions_typed[local]:
  functions_well_typed nested_counterexample_context
Proof
  rw[vyperTypeInvariantsTheory.functions_well_typed_def] >>
  gvs[nested_counterexample_module_lookup, AllCaseEqs(),
      nested_counterexample_callable_lookup, nested_counterexample_context_fields] >>
  drule nested_counterexample_toplevel_complete >> strip_tac >>
  `FLOOKUP bare_globals (NONE,"a") = NONE` by
    (Cases_on `FLOOKUP bare_globals (NONE,"a")` >> simp[] >>
     qpat_x_assum `!src id ty. FLOOKUP bare_globals _ = _ ==> _` drule >>
     simp[nested_counterexample_type_env]) >>
  `FLOOKUP bare_global_assignable (NONE,"a") = NONE` by
    (Cases_on `FLOOKUP bare_global_assignable (NONE,"a")` >> simp[] >>
     qpat_x_assum `!src id ty. FLOOKUP bare_global_assignable _ = _ ==> _` drule >>
     simp[nested_counterexample_type_env]) >>
  qabbrev_tac `eb = nested_counterexample_env with
    <| fn_sigs := fn_sigs; bare_globals := bare_globals;
       bare_global_assignable := bare_global_assignable;
       toplevel_vtypes := toplevel_vtypes; flag_members := flag_members |>` >>
  qexistsl_tac [`eb`, `BaseTV (UintT 256)`, `eb`] >>
  simp[Abbr `eb`, nested_counterexample_env_def, nested_counterexample_type_env,
       vyperValueTheory.evaluate_type_def, well_typed_expr_def] >>
  irule nested_counterexample_body_typed >>
  simp[nested_counterexample_env_def]
QED

Theorem nested_counterexample_graph_tc[local]:
  !x y. TC (call_edge_rel [((NONE,"caller"),(NONE,"shrink"))]) x y ==>
    x = (NONE,"caller") /\ y = (NONE,"shrink")
Proof
  ho_match_mp_tac relationTheory.TC_INDUCT >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def] >> metis_tac[]
QED

Theorem nested_counterexample_call_safe[local]:
  call_evaluation_safe nested_counterexample_context [(NONE,"shrink")]
Proof
  rw[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
  qexistsl_tac [`[((NONE,"caller"),(NONE,"shrink"))]`,
               `(NONE,"caller")`, `[]`] >>
  simp[nested_counterexample_context_fields,
       vyperTypeCallStackSoundnessTheory.call_stack_follows_def,
       vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_def,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def] >>
  conj_tac
  >- (rw[relationTheory.irreflexive_def] >> strip_tac >>
      drule nested_counterexample_graph_tc >> simp[]) >>
  rw[vyperTypeCallStackSoundnessTheory.functions_follow_call_graph_def,
     nested_counterexample_module_lookup] >>
  gvs[AllCaseEqs(), nested_counterexample_callable_lookup,
      nested_counterexample_context_fields] >>
  simp[nested_counterexample_body_calls]
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
  !hdr tr esz sa r sb.
    compile_dynarray_pop hdr 1 esz
      (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = (r,sb) ==>
    ?x0 x1 x2 x3 x4 x5 x6.
      ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
      EVERY (\x. ~not_fresh_at sa x) [x0;x1;x2;x3;x4;x5;x6] /\
      r = Var x6 /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
      sb.cs_current_insts = sa.cs_current_insts ++
        nested_pop_suffix hdr tr sa.cs_next_id esz x0 x1 x2 x3 x4 x5 x6
Proof
  simp[compile_dynarray_pop_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt strip_tac >> gvs[APPEND_ASSOC] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var + 1))`,
                `STRING #"%" (toString (sa.cs_next_var + 2))`,
                `STRING #"%" (toString (sa.cs_next_var + 3))`,
                `STRING #"%" (toString (sa.cs_next_var + 4))`,
                `STRING #"%" (toString (sa.cs_next_var + 5))`] >>
  simp[ASCIInumbersTheory.toString_11, not_fresh_at_def, APPEND_ASSOC,
       nested_pop_suffix_def]
QED

Theorem nested_pop_step_load[local]:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]) s =
    OK (update_var out (if tr then tload (THE (eval_operand hdr s)) s
                       else sload (THE (eval_operand hdr s)) s) s)
Proof
  Cases_on `tr` >> Cases_on `eval_operand hdr s` >>
  simp[step_inst_base_def, exec_read1_def, mk_inst_def]
QED

Theorem nested_pop_step_store[local]:
  IS_SOME (eval_operand hdr s) /\ IS_SOME (lookup_var x s) ==>
  step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [hdr; Var x] []) s =
    OK (if tr then tstore (THE (eval_operand hdr s)) (THE (lookup_var x s)) s
        else sstore (THE (eval_operand hdr s)) (THE (lookup_var x s)) s)
Proof
  Cases_on `tr` >> Cases_on `eval_operand hdr s` >> Cases_on `lookup_var x s` >>
  simp[step_inst_base_def, exec_write2_def, mk_inst_def, eval_operand_def]
QED

Theorem nested_pop_step_add[local]:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id ADD [hdr; Lit 1w] [out]) s =
    OK (update_var out (THE (eval_operand hdr s) + 1w) s)
Proof
  Cases_on `eval_operand hdr s` >> simp[] >>
  irule step_ADD >> simp[eval_operand_def]
QED


Theorem nested_pop_suffix_empty[local]:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME slot /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  (if tr then tload slot s else sload slot s) = 0w ==>
  ?a s'. run_inst_seq
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = Abort a s'
Proof
  Cases_on `hdr` >>
  simp[eval_operand_def] >> strip_tac >>
  fs[nested_pop_suffix_def, run_inst_seq_def, nested_pop_step_load,
     pop_step_ISZERO, pop_step_ASSERT, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def]
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
  Cases_on `hdr` >> simp[eval_operand_def] >> strip_tac >>
  fs[nested_pop_suffix_def, run_inst_seq_def, nested_pop_step_load,
     nested_pop_step_store, nested_pop_step_add,
     pop_step_ISZERO, pop_step_ASSERT, pop_step_SUB_lit,
     pop_step_MUL_lit, pop_step_ADD_var, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
  Cases_on `tr` >>
  fs[nested_pop_step_store, nested_pop_step_add,
     pop_step_MUL_lit, pop_step_ADD_var, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, sstore_def, tstore_def] >>
  simp[venom_state_component_equality, FLOOKUP_UPDATE] >> rw[] >> gvs[]
QED

(* A storage or transient root.  compile_get_target_ptr hands out the
   array's header slot with location storage (transient), and the source's
   pop_place pops the StoragePlace there, so the run is
   compile_pop_storage_sim's at that slot: the header load, the abort on
   zero, the store of the length less one, and the last element's slot.
   The element is past the new length, so its slots are dead in the
   array; storage_holds asks for them to agree (storage_range_agree),
   before the pop by storage_rel and after it since only the header slot
   changed. *)
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
   the constructor.  Python's checker accepts it for a complex immutable
   (local.py skips the modification count when var_info is None), and the
   lowering pops at the immutable's deploy-time memory.  Needs the
   constructor immutable invariant relating that memory to the source's
   immutables. *)
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

(* RESIDUAL (nested length words): pop on an array inside a memory local.
   The pop writes the array's length word inside the local's region, which
   locals_kept does not exempt for a nested array, only for a root one.
   Once it does (local_path_at_dynarray_len_at), the run is
   compile_pop_name_sim's at the target's pointer. *)
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
  `(!e:expr. T) /\
   !bt. (?id. target_root bt = NameTarget id) \/
        (?src id. target_root bt = TopLevelNameTarget (src,id))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  rw[target_root_def] >> Cases_on `p` >> simp[]
QED

(* By the target's root: a local, a storage or transient variable, or a
   module name with no storage declaration (an immutable or a constant). *)
Theorem pop_nested_sim:
  !ctx func cenv cx env ann bt ty es.
    (~immutable_root cx bt ==> pop_target_frag ctx func cenv cx env bt es) /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >>
  qspec_then `bt` strip_assume_tac target_root_cases
  >- (`~immutable_root cx bt` by gvs[immutable_root_def] >>
      irule pop_nested_local_sim >> metis_tac[]) >>
  Cases_on `?ts d. get_module_code cx src = SOME ts /\
                   find_var_decl_by_name id ts = SOME d`
  >- (gvs[] >> `~immutable_root cx bt` by gvs[immutable_root_def] >>
      irule pop_nested_storage_sim >> metis_tac[]) >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts = NONE` by
    (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >> metis_tac[]) >>
  Cases_on `cx.in_deploy`
  >- (irule pop_nested_immutable_deploy_sim >> metis_tac[]) >>
  irule pop_nested_immutable_runtime_sim >> metis_tac[]
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
