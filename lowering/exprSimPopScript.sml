(*
 * Expression simulation: pop on a local dynamic array (#636, Places row 3)
 *
 * x.pop() on a local x of type DynArray[T, n] lowers to
 * compile_dynarray_pop on x's pointer variable p, in memory: an MLOAD of the
 * length word at p, an ASSERT that it is not 0, an MSTORE of the length less
 * one, and the address p + 32 + (len - 1) * type_memory_bytes T of the
 * popped element, handed out as a pointer into memory.  The source pops the
 * last element of x's value (pop_element), raising "pop empty" on an empty
 * array, where the ASSERT aborts.  The lowering does not clear the popped
 * element, so it stays in x's region, past the new length, and the pointer
 * holds the source result there; x's region holds the shortened array, so
 * the locals stay related (local_ptrs_rel_write_local).
 *
 * TOP-LEVEL:
 *   compile_pop_name_sim — expr_vv_sim of x.pop() on a local
 *
 * Helpers:
 *   elems_val_wf_EL, elems_val_wf_FRONT, elems_in_memory_FRONT,
 *     elems_in_memory_mstore_before — the array's layout
 *   lookup_scopes_update_other, eval_target_place_name, eval_pop_name — the
 *     source side
 *   compile_expr_pop_name, dynarray_pop_mem_shape, dynarray_pop_mem_run_empty,
 *     dynarray_pop_mem_run — the lowering and its run
 *   pop_name_facts, pop_ptr_w2n, pop_elem_fits, pop_vv_post — the parts
 *     of the simulation
 *)

Theory exprSimPop
Ancestors
  list rich_list finite_map arithmetic words
  fragExec loweringSlice exprSim exprSimHyps exprSimLeaves exprSimAggregateLayout
  exprSimAggregateEncoding exprLowering exprLoweringProps emitHelper
  emitHelperProps compileEnv localPtrsProps valueEncoding valueEncodingProps
  vyperAST vyperInterpreter vyperState vyperValue vyperValueOperation
  vyperLookup vyperTyping vyperTypeSystem vyperTypeInvariants vyperTypeEnv
  vyperTypeExprResult vyperTypeExprSoundness
  venomExecSemantics venomInst venomState
Libs
  pairLib

(* ===== The array's layout ===== *)

Theorem elems_val_wf_EL:
  !vs tv i. elems_val_wf vs tv /\ i < LENGTH vs ==> val_wf tv (EL i vs)
Proof
  Induct >> simp[val_wf_def] >> rpt strip_tac >> Cases_on `i` >> gvs[]
QED

Theorem elems_val_wf_FRONT:
  !vs tv. elems_val_wf vs tv /\ vs <> [] ==> elems_val_wf (FRONT vs) tv
Proof
  Induct >> rw[val_wf_def, FRONT_DEF] >> gvs[val_wf_def]
QED

Theorem elems_in_memory_FRONT:
  !vs off tv mem.
    elems_in_memory vs off tv mem /\ vs <> [] ==>
    elems_in_memory (FRONT vs) off tv mem
Proof
  Induct >> rw[val_in_memory_def, FRONT_DEF] >> gvs[val_in_memory_def]
QED

(* A store below the elements leaves them in place. *)
Theorem elems_in_memory_mstore_before:
  !vs off tv s a w.
    elems_in_memory vs off tv s.vs_memory /\ elems_val_wf vs tv /\
    a + 32 <= off ==>
    elems_in_memory vs off tv (mstore a w s).vs_memory
Proof
  Induct >> simp[val_in_memory_def, val_wf_def] >> rpt strip_tac
  >- (irule val_in_memory_mem_agree >> simp[] >>
      qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >>
      simp[mstore_mem_bytes_at_disjoint]) >>
  first_x_assum irule >> simp[]
QED

(* ===== The source side ===== *)

Theorem lookup_scopes_update_other:
  !pre n id env v rest.
    n <> id ==>
    lookup_scopes n (pre ++ env |+ (id, v) :: rest) =
    lookup_scopes n (pre ++ env :: rest)
Proof
  Induct >> rw[lookup_scopes_def, FLOOKUP_UPDATE]
QED

(* Setting the entry find_containing_scope found leaves every other name. *)
Theorem lookup_scopes_set_other:
  !id sc pre env e rest v n.
    find_containing_scope id sc = SOME (pre, env, e, rest) /\ n <> id ==>
    lookup_scopes n (pre ++ env |+ (id, v) :: rest) = lookup_scopes n sc
Proof
  rpt strip_tac >> drule find_containing_scope_structure >> strip_tac >>
  qpat_x_assum `sc = _` (fn th => REWRITE_TAC [th, GSYM APPEND_ASSOC, APPEND]) >>
  irule lookup_scopes_update_other >> first_assum ACCEPT_TAC
QED

Theorem eval_target_place_name:
  !cx id es.
    IS_SOME (lookup_scopes id es.scopes) ==>
    eval_target_place cx (NameTarget id) es = (INL (MemoryPlace id []), es)
Proof
  simp[Once evaluate_def, bind_def, get_place_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, get_place_def]
QED

(* The popped element's place: the last index of x, past its new length,
   where the entry's popped history keeps the element. *)
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
         pre ++ env |+ (id, entry with
           <| value := ArrayV (DynArrayV (FRONT vs));
              popped := ([ValueSubscript (IntV &(LENGTH vs - 1))], LAST vs)
                          :: entry.popped |>)
           :: rest)
Proof
  rpt gen_tac >> strip_tac >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  `IS_SOME (lookup_scopes id es.scopes)` by simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  drule_then (qspec_then `cx` SUBST1_TAC) eval_target_place_name >>
  simp[pop_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, check_def, assert_def,
       return_def, raise_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, assign_subscripts_def, pop_element_def,
       popped_value_def, record_pop_def, set_scopes_def, LET_THM] >>
  Cases_on `vs = []` >> simp[raise_def, return_def, bind_def] >>
  rw[] >> gvs[]
QED

(* ===== The lowering ===== *)

Theorem compile_expr_pop_name:
  !cenv ty ann id p sz et bd sa.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (ArrayT et bd) ==>
    compile_expr cenv ty (Pop ann (NameTarget id)) sa =
      (LocatedValue ann
         (mk_ptr (FST (compile_dynarray_pop (Var p) 32
                         (type_memory_bytes cenv et) MLOAD MSTORE sa))
                 LocMemory),
       SND (compile_dynarray_pop (Var p) 32 (type_memory_bytes cenv et)
              MLOAD MSTORE sa))
Proof
  rpt strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       expr_type_def, compile_target_base_def, infer_array_location_def,
       word_scale_def, elem_size_in_location_def, is_slot_addressed_def] >>
  pairarg_tac >> simp[]
QED

Theorem dynarray_pop_mem_shape:
  !p esz sa r sb.
    compile_dynarray_pop (Var p) 32 esz MLOAD MSTORE sa = (r, sb) ==>
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
  simp[ASCIInumbersTheory.toString_11, not_fresh_at_def, APPEND_ASSOC]
QED

(* The pop's instructions on variable operands, as rewrites whose
   conditions name no other variable: simp unfolds no opcode case. *)
Theorem pop_step_MLOAD[local]:
  !id x out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id MLOAD [Var x] [out]) s =
      OK (update_var out (mload (w2n (THE (lookup_var x s))) s) s)
Proof
  rpt strip_tac >> Cases_on `lookup_var x s` >> gvs[] >>
  irule step_MLOAD >> simp[eval_operand_def]
QED

Theorem pop_step_ISZERO[local]:
  !id x out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id ISZERO [Var x] [out]) s =
      OK (update_var out (bool_to_word (THE (lookup_var x s) = 0w)) s)
Proof
  rpt strip_tac >> Cases_on `lookup_var x s` >> gvs[] >>
  irule step_ISZERO >> simp[eval_operand_def]
QED

Theorem pop_step_ASSERT[local]:
  !id x s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id ASSERT [Var x] []) s =
      if THE (lookup_var x s) = 0w
      then Abort Revert_abort (revert_state (set_returndata [] s))
      else OK s
Proof
  rpt strip_tac >> Cases_on `lookup_var x s` >> gvs[] >> rw[]
  >- (irule step_ASSERT_revert >> simp[eval_operand_def]) >>
  irule step_ASSERT_ok >> simp[eval_operand_def]
QED

Theorem pop_step_SUB_lit[local]:
  !id x c out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id SUB [Var x; Lit c] [out]) s =
      OK (update_var out (THE (lookup_var x s) - c) s)
Proof
  rpt strip_tac >> Cases_on `lookup_var x s` >> gvs[] >>
  irule step_SUB >> simp[eval_operand_def]
QED

Theorem pop_step_ADD_lit[local]:
  !id x c out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id ADD [Var x; Lit c] [out]) s =
      OK (update_var out (THE (lookup_var x s) + c) s)
Proof
  rpt strip_tac >> Cases_on `lookup_var x s` >> gvs[] >>
  irule step_ADD >> simp[eval_operand_def]
QED

Theorem pop_step_MUL_lit[local]:
  !id x c out s.
    IS_SOME (lookup_var x s) ==>
    step_inst_base (mk_inst id MUL [Var x; Lit c] [out]) s =
      OK (update_var out (THE (lookup_var x s) * c) s)
Proof
  rpt strip_tac >> Cases_on `lookup_var x s` >> gvs[] >>
  irule step_MUL >> simp[eval_operand_def]
QED

Theorem pop_step_ADD_var[local]:
  !id x y out s.
    IS_SOME (lookup_var x s) /\ IS_SOME (lookup_var y s) ==>
    step_inst_base (mk_inst id ADD [Var x; Var y] [out]) s =
      OK (update_var out (THE (lookup_var x s) + THE (lookup_var y s)) s)
Proof
  rpt strip_tac >> Cases_on `lookup_var x s` >> Cases_on `lookup_var y s` >>
  gvs[] >> irule step_ADD >> simp[eval_operand_def]
QED

Theorem pop_step_MSTORE[local]:
  !id x y s.
    IS_SOME (lookup_var x s) /\ IS_SOME (lookup_var y s) ==>
    step_inst_base (mk_inst id MSTORE [Var x; Var y] []) s =
      OK (mstore (w2n (THE (lookup_var x s))) (THE (lookup_var y s)) s)
Proof
  rpt strip_tac >> Cases_on `lookup_var x s` >> Cases_on `lookup_var y s` >>
  gvs[] >> irule step_MSTORE >> simp[eval_operand_def]
QED

Theorem mstore_vs_vars[local]:
  !a v s X. (mstore a v s).vs_vars = s.vs_vars /\
            mstore a v (s with vs_vars := X) = mstore a v s with vs_vars := X
Proof
  simp[mstore_def]
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
  rpt strip_tac >> fs pop_run_simps >> gvs[lookup_var_def]
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
  rpt strip_tac >> fs pop_run_simps >>
  simp[venom_state_component_equality, FLOOKUP_UPDATE] >>
  simp[mstore_def] >> rw[] >> gvs[]
QED

(* ===== The simulation ===== *)

Theorem pop_ptr_w2n:
  !w len esz.
    0 < len /\ w2n (w:bytes32) + 32 + len * esz < dimword (:256) ==>
    w2n (w + 32w + (n2w len - 1w) * n2w esz) = w2n w + 32 + (len - 1) * esz
Proof
  rpt strip_tac >>
  `n2w len - 1w = n2w (len - 1) : bytes32` by
    simp[GSYM wordsTheory.n2w_sub] >>
  `(len - 1) * esz <= len * esz` by simp[] >>
  Cases_on `w` >> gvs[wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w]
QED

(* The popped element's footprint lies in the local's region. *)
Theorem pop_elem_fits:
  !len n esz fp sz base.
    0 < len /\ len <= n /\ fp <= esz /\ 32 + n * esz <= sz ==>
    base + 32 + (len - 1) * esz + fp <= base + sz
Proof
  rpt strip_tac >>
  `(len - 1) * esz + esz = len * esz` by
    (Cases_on `len` >> gvs[MULT_CLAUSES]) >>
  `len * esz <= n * esz` by simp[] >>
  decide_tac
QED

Theorem value_has_type_dynarray[local]:
  !etv n v.
    value_has_type (ArrayTV etv (Dynamic n)) v ==>
    ?vs. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= n /\ all_have_type etv vs
Proof
  Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[value_has_type_def]
QED

(* What expr_sim_pre and stmt_state_rel give of the local popped from. *)
Theorem pop_name_facts:
  !cenv cx env ann id es func s0.
    expr_sim_pre cenv cx env (Pop ann (NameTarget id)) es /\
    stmt_state_rel func cenv cx es s0 ==>
    ?n p sz entry etv vs w.
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      cenv.ce_var_type id = SOME (ArrayT ann (Dynamic n)) /\
      lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
      evaluate_type (get_tenv cx) ann = SOME etv /\
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
  rpt strip_tac >>
  `expr_sim_inv cenv cx env es /\
   ?n. FLOOKUP env.var_types id = SOME (ArrayT ann (Dynamic n)) /\
       FLOOKUP env.var_assignable id = SOME T` by
    (gvs[expr_sim_pre_def, well_typed_expr_def, type_place_target_NameTarget,
         AllCaseEqs()] >> metis_tac[]) >>
  qexists_tac `n` >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_def] >>
  `cenv.ce_var_type id = SOME (ArrayT ann (Dynamic n))` by
    metis_tac[expr_sim_inv_def] >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
     evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) = SOME entry.type` by
    (gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `value_has_type entry.type entry.value` by
    (gvs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  rename1 `evaluate_type _ ann = SOME etv` >>
  `entry.type = ArrayTV etv (Dynamic n)` by simp[] >>
  `value_has_type (ArrayTV etv (Dynamic n)) entry.value` by metis_tac[] >>
  drule value_has_type_dynarray >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  qpat_x_assum `!name entry p sz. _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `val_wf _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [val_wf_def] o
     REWRITE_RULE [ASSUME ``entry.type = ArrayTV etv (Dynamic n)``,
                   ASSUME ``entry.value = ArrayV (DynArrayV vs)``]) >>
  qpat_x_assum `val_in_memory _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [val_in_memory_def] o
     REWRITE_RULE [ASSUME ``entry.type = ArrayTV etv (Dynamic n)``,
                   ASSUME ``entry.value = ArrayV (DynArrayV vs)``]) >>
  qpat_x_assum `type_memory_size _ <= _`
    (assume_tac o SIMP_RULE (srw_ss()) [type_memory_size_def] o
     REWRITE_RULE [ASSUME ``entry.type = ArrayTV etv (Dynamic n)``]) >>
  qpat_x_assum `all_have_type _ _` (assume_tac o REWRITE_RULE [all_have_type_EVERY]) >>
  `n < dimword (:256)` by
    (`n <= n * type_slot_size etv` by
       (qpat_x_assum `0 < type_slot_size etv` mp_tac >>
        simp[arithmeticTheory.LE_MULT_CANCEL_LBARE]) >>
     qpat_x_assum `type_slot_size (ArrayTV _ _) < _` mp_tac >>
     simp[type_slot_size_def] >> decide_tac) >>
  `type_memory_bytes cenv ann = type_memory_size etv` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  qexistsl_tac [`etv`, `vs`, `w`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac, metis_tac[]]
QED

(* The local after the pop: its region holds the shortened array, and the
   other live locals' regions are untouched by the store of the length. *)
Theorem pop_local_ptrs_rel:
  !func cenv es s0 u id pre env entry rest p sz w etv n vs hist.
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
      (pre ++ env |+ (id, entry with
         <| value := ArrayV (DynArrayV (FRONT vs)); popped := hist |>)
         :: rest) u
Proof
  rpt strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  drule find_containing_scope_structure >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  `local_region cenv es.scopes s0 id (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `!nm b sz'. nm <> id /\ local_region cenv es.scopes s0 nm b sz' ==>
              regions_disjoint (w2n w) sz b sz'` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `32 <= sz` by (qpat_x_assum `32 + _ <= sz` mp_tac >> simp[]) >>
  `n2w (LENGTH vs) - 1w = n2w (LENGTH (FRONT vs)) : bytes32` by
    (`0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
     simp[LENGTH_FRONT, GSYM wordsTheory.n2w_sub, arithmeticTheory.PRE_SUB1]) >>
  irule local_ptrs_rel_write_local >>
  qexistsl_tac [`entry with <| value := ArrayV (DynArrayV (FRONT vs));
                              popped := hist |>`, `id`,
                `p`, `es.scopes`, `s0`, `sz`, `w`] >>
  rpt conj_tac
  >~ [`mem_bytes_at`]
  >- (rpt strip_tac >>
      `regions_disjoint (w2n w) sz b sz'` by
        (first_x_assum irule >> fs[] >> metis_tac[]) >>
      `b + sz' <= w2n w \/ w2n w + 32 <= b` by
        (qpat_x_assum `32 <= sz` mp_tac >>
         qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
      qpat_x_assum `u.vs_memory = _` SUBST1_TAC >> irule EQ_SYM >>
      irule mstore_mem_bytes_at_disjoint >> fs[]) >>
  FIRST [
    first_assum ACCEPT_TAC,
    decide_tac,
    irule lookup_scopes_update >> first_assum ACCEPT_TAC,
    rpt strip_tac >> irule lookup_scopes_set_other >> metis_tac[],
    fs[type_memory_size_def] >> NO_TAC,
    rpt strip_tac >> gvs[] >> NO_TAC,
    rpt strip_tac >> first_x_assum irule >> fs[] >> metis_tac[],
    fs[val_wf_def, LENGTH_FRONT, elems_val_wf_FRONT] >> NO_TAC,
    fs[val_in_memory_def, mstore_mem_word_at_same, elems_in_memory_FRONT,
       elems_in_memory_mstore_before] >> NO_TAC,
    metis_tac[]]
QED

(* stmt_state_rel after the pop: the source changed only the scopes, Venom
   only variables and memory. *)
Theorem pop_stmt_state_rel:
  !func cenv cx es es' s0 u.
    stmt_state_rel func cenv cx es s0 /\
    local_ptrs_rel func cenv es'.scopes u /\
    es' = es with scopes := es'.scopes /\
    u = s0 with <| vs_vars := u.vs_vars; vs_memory := u.vs_memory |> ==>
    stmt_state_rel func cenv cx es' u
Proof
  rpt strip_tac >>
  `u.vs_accounts = s0.vs_accounts /\ u.vs_transient = s0.vs_transient /\
   u.vs_call_ctx = s0.vs_call_ctx /\ u.vs_tx_ctx = s0.vs_tx_ctx /\
   u.vs_block_ctx = s0.vs_block_ctx /\ u.vs_logs = s0.vs_logs /\
   u.vs_outcomes = s0.vs_outcomes /\ u.vs_requests = s0.vs_requests /\
   u.vs_immutables = s0.vs_immutables /\
   u.vs_data_section = s0.vs_data_section /\
   u.vs_allocas = s0.vs_allocas /\ u.vs_alloca_next = s0.vs_alloca_next` by
    (qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_state_rel_def] >> strip_tac >> rpt conj_tac
  >- (irule state_rel_frame >>
      qpat_assum `local_ptrs_rel _ _ _ _` (irule_at Any) >>
      qexistsl_tac [`s0`, `es`] >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])
  >- (irule alloca_inv_fields >> qexists_tac `s0` >> simp[])
  >- (irule alloca_room_fields >> qexists_tac `s0` >> simp[]) >>
  metis_tac[]
QED

Theorem pop_stmt_state_rel_scopes:
  !func cenv cx es sc s0 u.
    stmt_state_rel func cenv cx es s0 /\ local_ptrs_rel func cenv sc u /\
    u = s0 with <| vs_vars := u.vs_vars; vs_memory := u.vs_memory |> ==>
    stmt_state_rel func cenv cx (es with scopes := sc) u
Proof
  rpt strip_tac >> irule pop_stmt_state_rel >> simp[] >>
  qexistsl_tac [`es`, `s0`] >> fs[]
QED

Theorem lookup_var_inst_idx[local]:
  !x s k. lookup_var x (s with vs_inst_idx := k) = lookup_var x s
Proof
  simp[lookup_var_def]
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
  rpt strip_tac >>
  `elems_in_memory vs (w2n w + 32) etv u.vs_memory` by
    (asm_rewrite_tac[] >> irule elems_in_memory_mstore_before >> simp[]) >>
  drule elems_in_memory_EL >>
  disch_then (qspec_then `LENGTH vs - 1` mp_tac) >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  simp[LAST_EL, arithmeticTheory.PRE_SUB1]
QED

(* Reading the popped place after the pop: the index is past the new
   length, so the popped history supplies the element. *)
Theorem read_pop_name:
  !cx es pre envs entry rest id etv n vs.
    find_containing_scope id es.scopes = SOME (pre, envs, entry, rest) /\
    entry.type = ArrayTV etv (Dynamic n) /\ vs <> [] /\ LENGTH vs <= n ==>
    read_result cx
      (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))]))
      (es with scopes :=
         pre ++ envs |+ (id, entry with
           <| value := ArrayV (DynArrayV (FRONT vs));
              popped := ([ValueSubscript (IntV &(LENGTH vs - 1))], LAST vs)
                          :: entry.popped |>)
           :: rest) =
    (INL (LAST vs),
     es with scopes :=
       pre ++ envs |+ (id, entry with
         <| value := ArrayV (DynArrayV (FRONT vs));
            popped := ([ValueSubscript (IntV &(LENGTH vs - 1))], LAST vs)
                        :: entry.popped |>)
         :: rest)
Proof
  rpt strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  `oEL (LENGTH vs - 1) (FRONT vs) = NONE` by simp[oEL_THM, LENGTH_FRONT] >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  simp[read_result_def, read_place_def, bind_def, get_scopes_def,
       return_def, lift_option_type_def, lift_sum_def, lookup_scopes_update,
       read_memory_path_def, evaluate_subscripts_def, array_index_def,
       read_popped_def, subscripts_type_def, subscript_type_def,
       bound_length_def]
QED

Theorem pop_vv_post:
  !func cenv cx ann id es sa sb s0 u k pre envs entry rest p sz w etv n vs x6.
    stmt_state_rel func cenv cx es s0 /\
    local_ptrs_rel func cenv es.scopes s0 /\
    find_containing_scope id es.scopes = SOME (pre, envs, entry, rest) /\
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
    lookup_var x6 u =
      SOME (w + 32w + (n2w (LENGTH vs) - 1w) * n2w (type_memory_size etv)) /\
    EVERY (value_has_type etv) vs /\
    evaluate_type (get_tenv cx) ann = SOME etv ==>
    vv_post func cenv cx (Pop ann (NameTarget id)) es sa sb s0
      (es with scopes :=
         pre ++ envs |+ (id, entry with
           <| value := ArrayV (DynArrayV (FRONT vs));
              popped := ([ValueSubscript (IntV &(LENGTH vs - 1))], LAST vs)
                          :: entry.popped |>)
           :: rest)
      (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))]))
      (LocatedValue ann (mk_ptr (Var x6) LocMemory))
      (u with vs_inst_idx := k)
Proof
  rpt gen_tac >> strip_tac >>
  `u.vs_allocas = s0.vs_allocas /\ u.vs_alloca_next = s0.vs_alloca_next` by
    (qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  drule_all pop_local_ptrs_rel >>
  disch_then (qspec_then
    `([ValueSubscript (IntV &(LENGTH vs - 1))], LAST vs) :: entry.popped`
    assume_tac) >>
  `s0.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  `LENGTH vs * type_memory_size etv <= n * type_memory_size etv` by simp[] >>
  `w2n (w + 32w + (n2w (LENGTH vs) - 1w) * n2w (type_memory_size etv)) =
   w2n w + 32 + (LENGTH vs - 1) * type_memory_size etv` by
    (irule pop_ptr_w2n >> decide_tac) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  drule find_containing_scope_pre_none >> strip_tac >>
  qmatch_goalsub_abbrev_tac `vv_post _ _ _ _ _ _ _ _ es1 _ _ _` >>
  `read_result cx
     (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))])) es1 =
   (INL (LAST vs), es1)` by
    (simp[Abbr `es1`] >> irule read_pop_name >> simp[] >> metis_tac[]) >>
  `local_region cenv es1.scopes (u with vs_inst_idx := k) id (w2n w) sz` by
    (simp[Abbr `es1`, local_region_def, lookup_scopes_update,
          lookup_var_inst_idx] >>
     metis_tac[]) >>
  `LENGTH vs - 1 < LENGTH vs` by decide_tac >>
  unabbrev_all_tac >>
  simp[vv_post_def, expr_type_def, stmt_state_rel_inst_idx, lookup_var_inst_idx] >>
  rpt conj_tac
  >- (irule pop_stmt_state_rel_scopes >> conj_tac
      >- first_assum ACCEPT_TAC >>
      qexists_tac `s0` >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (simp[vv_holds_def, contextTheory.mk_ptr_def, eval_operand_def,
           lookup_var_inst_idx, return_def] >>
      `val_in_memory etv (LAST vs)
         (w2n w + 32 + (LENGTH vs - 1) * type_memory_size etv) u.vs_memory` by
        (irule pop_elem_in_memory >> simp[] >> metis_tac[]) >>
      simp[] >> rpt strip_tac >>
      TRY (qpat_x_assum `val_in_memory etv (LAST vs) _ _` mp_tac >>
           simp[] >> NO_TAC) >>
      irule val_in_memory_word_type >> rpt conj_tac
      >- metis_tac[]
      >- gvs[EVERY_EL, LAST_EL, arithmeticTheory.PRE_SUB1] >>
      qpat_x_assum `val_in_memory etv (LAST vs) _ _` mp_tac >> simp[])
  >- (simp[vv_at_def, contextTheory.mk_ptr_def, eval_operand_def,
           lookup_var_inst_idx, return_def] >>
      `val_wf etv (LAST vs)` by
        gvs[LAST_EL, arithmeticTheory.PRE_SUB1, elems_val_wf_EL] >>
      `w2n w + 32 + (LENGTH vs - 1) * type_memory_size etv +
         val_footprint etv (LAST vs) <= w2n w + sz` by
        (irule pop_elem_fits >> metis_tac[val_footprint_le]) >>
      simp[] >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`id`, `w2n w`, `sz`] >> fs[]) >>
  `32 <= sz` by (qpat_x_assum `32 + _ <= sz` mp_tac >> simp[]) >>
  FIRST [
    rpt strip_tac >>
      `regions_disjoint off sz' (w2n w) sz` by
        (first_x_assum (qspecl_then [`id`, `w2n w`, `sz`] mp_tac) >>
         simp[local_region_def, compileEnvTheory.regions_disjoint_def] >>
         metis_tac[]) >>
      `off + sz' <= w2n w \/ w2n w + 32 <= off` by
        (qpat_x_assum `32 <= sz` mp_tac >>
         qpat_x_assum `regions_disjoint off _ _ _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
      simp[] >> qpat_x_assum `u.vs_memory = _` SUBST1_TAC >>
      irule mstore_mem_bytes_at_disjoint >> fs[],
    rpt strip_tac >> fs[] >> NO_TAC,
    rpt strip_tac >> fs[lookup_var_inst_idx] >> metis_tac[]]
QED

(* TOP-LEVEL *)
Theorem compile_pop_name_sim:
  !ctx func cenv cx env ty ann id es.
    expr_sim_pre cenv cx env (Pop ann (NameTarget id)) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann (NameTarget id)) es
Proof
  rw[expr_vv_sim_def] >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
  drule_all pop_name_facts >> strip_tac >>
  drule_all compile_expr_pop_name >> strip_tac >> gvs[] >>
  Cases_on `compile_dynarray_pop (Var p) 32 (type_memory_size etv)
              MLOAD MSTORE sa` >>
  qmatch_asmsub_rename_tac `compile_dynarray_pop _ _ _ _ _ _ = (rop, sc)` >>
  gvs[] >>
  drule dynarray_pop_mem_shape >> strip_tac >> gvs[] >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `~MEM p [x0; x1; x2; x3; x4; x5; x6]` by (simp[] >> metis_tac[]) >>
  `ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0] /\
   EVERY (\x. x <> p) [x0; x1; x2; x3; x4; x5; x6]` by
    (fs[] >> metis_tac[]) >>
  `!q n' sq. FLOOKUP cenv.ce_vars n' = SOME (PtrVar (Var q) sq) ==>
             ~MEM q [x0; x1; x2; x3; x4; x5; x6]` by
    (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> rpt conj_tac >>
  TRY (fs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def,
          rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
       NO_TAC) >>
  rpt strip_tac >> TRY (qpat_x_assum `_ = s0` SUBST_ALL_TAC) >>
  TRY (qpat_x_assum `s0 = _` (SUBST_ALL_TAC o SYM)) >>
  fs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `mload (w2n w) s0 = n2w (LENGTH vs)` by
    gvs[mload_def, mem_word_at_def] >>
  drule_all eval_pop_name >> strip_tac >> gvs[]
  >- (TRY disj2_tac >>
      `ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0]` by fs[] >>
      drule_all dynarray_pop_mem_run_empty >>
      simp[expr_exit_def] >> metis_tac[]) >>
  TRY disj1_tac >>
  `n2w (LENGTH vs) <> 0w : bytes32` by
    (`LENGTH vs <> 0 /\ LENGTH vs < dimword (:256)` by
       (Cases_on `vs` >> gvs[]) >>
     simp[wordsTheory.n2w_11]) >>
  `ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0] /\
   EVERY (\x. x <> p) [x0; x1; x2; x3; x4; x5; x6]` by fs[] >>
  `mload (w2n w) s <> 0w` by fs[] >>
  drule_all dynarray_pop_mem_run >>
  disch_then (qspecl_then [`type_memory_size etv`, `sa.cs_next_id`]
                strip_assume_tac) >>
  qexists_tac `u` >> fs[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!q n' sq. FLOOKUP cenv.ce_vars n' = SOME (PtrVar (Var q) sq) ==>
             lookup_var q u = lookup_var q s` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >>
     `x <> x0 /\ x <> x1 /\ x <> x2 /\ x <> x3 /\ x <> x4 /\ x <> x5 /\
      x <> x6` by (rpt conj_tac >> CCONTR_TAC >> fs[]) >>
     fs[]) >>
  `w2n w + sz <= s.vs_alloca_next /\ 32 + n * type_memory_size etv <= sz` by
    fs[] >>
  `mload (w2n w) s = n2w (LENGTH vs)` by gvs[mload_def, mem_word_at_def] >>
  qpat_x_assum `mload _ _ = n2w _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `u = s with <| vs_vars := u.vs_vars; vs_memory := u.vs_memory |>` by
    (qpat_x_assum `u = _` mp_tac >> simp[venom_state_component_equality]) >>
  drule_all pop_vv_post >> simp[]
QED
