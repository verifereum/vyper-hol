(*
 * Expression simulation: the leaves (#636, Leaves)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the expressions
 * without subexpressions.  Each concludes expr_sim_ok (exprSimHyps).
 *
 * TOP-LEVEL:
 *   compile_name_vv_sim      — a local of any type: its pointer variable,
 *                              as a memory pointer, no code
 *   compile_name_sim         — a local: word locals by compile_name_word_sim
 *                              (exprSim), the rest by compile_name_other_sim
 *                              (compile_name_vv_sim and unwrap_value)
 *   compile_literal_sim      — a literal: bool, integer and decimal literals
 *                              of a word type by compile_literal_word_sim
 *                              (exprSim), the rest by
 *                              compile_literal_other_sim: address and bytesN
 *                              literals by compile_literal_bytes_word_sim,
 *                              bytes and string literals by
 *                              compile_literal_memory_sim, from
 *                              compile_literal_other_vv_sim
 *                              (exprSimLiteralBuffer)
 *   compile_env_case_sim     — an environment read: by compile_env_sim
 *                              (exprSim), block.prevhash by
 *                              compile_prevhash_sim, msg.gas by
 *                              compile_msg_gas_sim
 *   compile_toplevel_name_sim — storage, transient, immutable and constant
 *                              reads: a storage or transient variable by
 *                              compile_toplevel_storage_vv_sim, a pointer
 *                              to its slot, whose ce_vars entry comes from
 *                              storage_vars_rel and transient_vars_rel
 *   compile_flag_member_case_sim — a flag member: the literal 2 ** id, by
 *                              expr_sim_inv's flag members clause
 *
 * Helpers: expr_sim_of_vv_sim_memory, val_in_memory_word_type,
 *   eval_expr_toplevel_storage, toplevel_storage_ce_vars,
 *   compile_toplevel_no_module_sim
 *
 * Unprovable as the definitions stand, to be fixed in the lowering, in
 * state_rel or in the judgment before their PRs:
 *   compile_toplevel_storage_undecodable_sim — a storage or transient
 *                              variable whose slot does not decode (row 3):
 *                              the source raises a RuntimeError where the
 *                              lowering emits no code.  It needs a storage
 *                              invariant keeping the variables' slots
 *                              decodable.
 *   compile_toplevel_immutable_sim — immutables and constants (row 3),
 *                              which lookup_global reads from the
 *                              immutables: nothing puts them in ce_vars,
 *                              so the lowering may emit INVALID where the
 *                              source reads a value (#563 for immutables).
 *   compile_prevhash_sim     — block.prevhash (row 5): the source raises a
 *                              RuntimeError where BLOCKHASH returns 0 (#671),
 *                              and call_ctx_rel does not relate the block
 *                              hashes.
 *   compile_msg_gas_sim      — msg.gas: the source reads the next of the
 *                              state's gas readings where the lowering emits
 *                              GAS, and call_ctx_rel does not relate the two;
 *                              with no readings left the source raises a
 *                              RuntimeError where GAS does not abort.  It
 *                              needs call_ctx_rel to relate gas_obs to the
 *                              frame's GAS readings.
 *)

Theory exprSimLeaves
Ancestors
  list finite_map
  exprSim exprSimHyps exprSimUnwrap exprLowering exprLoweringProps
  compileEnv loweringSlice
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeInvariants vyperTypeEnv vyperTyping vyperTypeGlobalLookupSoundness
  vyperValueOperation valueEncoding fragExec venomState exprSimLiteralBuffer

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

(* ===== No code before unwrap_value ===== *)

(* expr_sim_of_vv_sim (exprSimUnwrap) for a form whose compile_expr emits
   no code and hands out a pointer into memory: the compile state does not
   move, so compile_expr_extends is not needed, and unwrap_value is
   unwrap_memory_sim's load or nothing, so no cheated unwrap case is. *)
Theorem expr_sim_of_vv_sim_memory:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa vv sm. compile_expr cenv ty e sa = (vv, sm) ==>
                sm = sa /\
                ?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  qpat_x_assum `!sa vv sm. _` (drule_then strip_assume_tac) >>
  gvs[] >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sa func` by metis_tac[fn_has_code_split, cs_extends_refl] >>
  `expr_vv_res_ok res` by simp[expr_vv_res_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sa`, `LocatedValue t p`, `res`, `es'`, `s0`]
                mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_seq >> first_x_assum (irule_at Any) >>
  simp[cs_extends_refl] >>
  Cases_on `?v. res = INL (Value v)`
  >- (gvs[] >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `e`, `es`, `sa`, `sa`, `sb`,
                   `s0`, `es'`, `v`, `t`, `p`, `op`,
                   `expr_exit (INL (Value v))`]
        mp_tac unwrap_memory_sim >>
      impl_tac >- asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
      strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. F`, `\s. F`, `expr_exit res`] >>
  simp[fragExecTheory.frag_exec_false_pre] >>
  gvs[expr_res_ok_def]
QED

(* ===== Locals ===== *)

(* A value of a word type in memory: its word is the typed encoding. *)
Theorem val_in_memory_word_type:
  !tenv t tvt v off mem.
    is_word_type t /\ evaluate_type tenv t = SOME tvt /\
    value_has_type tvt v /\ val_in_memory tvt v off mem ==>
    mem_word_at off mem = typed_val_to_w256 tvt v
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, val_in_memory_def,
      typed_val_to_w256_def]
QED

(* A local held through its pointer variable p, as expr_sim_inv's locals
   clause has every local: its value_vv is p as a memory pointer, no code,
   and local_ptrs_rel lays the value out at p's word, inside the local's
   region. *)
Theorem compile_name_vv_sim:
  !cenv ann id. expr_vv_ok cenv (Name ann id)
Proof
  rw[expr_vv_ok_def, expr_vv_sim_def] >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >>
  gvs[compile_expr_def, compile_name_vv_def, comp_return_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  `?w. lookup_var p s = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value /\
       val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  simp[vv_post_def, vv_holds_def, vv_at_def, materialise_def, return_def,
       vyperASTTheory.expr_type_def, eval_operand_def] >>
  rpt conj_tac
  >- metis_tac[val_in_memory_word_type]
  >- (qexistsl_tac [`id`, `w2n w`, `sz`] >> simp[local_region_def] >>
      drule val_footprint_le >> decide_tac) >>
  rpt strip_tac >> gvs[]
QED

Theorem compile_name_other_sim:
  !ctx func cenv cx env ty ann id es.
    expr_sim_pre cenv cx env (Name ann id) es /\
    ~(is_word_type ann /\
      ?entry. lookup_scopes id es.scopes = SOME entry /\
              word_value entry.value) ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
Proof
  rpt strip_tac >> irule expr_sim_of_vv_sim_memory >> conj_tac
  >~ [`expr_vv_sim`] >- metis_tac[compile_name_vv_sim, expr_vv_ok_def] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  simp[compile_expr_def, compile_name_vv_def, comp_return_def,
       contextTheory.mk_ptr_def]
QED

Theorem compile_name_sim:
  !cenv ann id. expr_sim_ok cenv (Name ann id)
Proof
  rw[expr_sim_ok_def] >>
  Cases_on `is_word_type ann /\
            ?entry. lookup_scopes id es.scopes = SOME entry /\
                    word_value entry.value`
  >- (gvs[] >>
      `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
        gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
      irule compile_name_word_sim >> metis_tac[]) >>
  irule compile_name_other_sim >> metis_tac[]
QED

Theorem compile_name_case_sim:
  !cenv ann id. expr_ok cenv (Name ann id)
Proof
  simp[expr_ok_def, compile_name_sim, compile_name_vv_sim]
QED

(* ===== Literals ===== *)

val literal_bytes_word_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def,
      vyperASTTheory.expr_type_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def];

(* An address or bytesN literal: a Lit of its typed encoding, the 20 bytes
   of an address right-aligned and the bytes of a bytesN left-aligned, as
   expr_val_rel has them.  No code. *)
Theorem compile_literal_bytes_word_sim:
  !ctx func cenv cx env ty ann bs es.
    expr_sim_pre cenv cx env (Literal ann (BytesL bs)) es /\
    is_word_type ann ==>
    expr_sim ctx func cenv cx ty (Literal ann (BytesL bs)) es
Proof
  rw[expr_sim_def] >> gvs[Once evaluate_def, return_def, expr_sim_pre_def,
                          well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def]
  >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >>
                       literal_bytes_word_tac) >>
  literal_bytes_word_tac
QED

Theorem compile_literal_memory_sim:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rpt strip_tac >> irule exprSimUnwrapTheory.expr_sim_of_vv_sim_buffer >>
  `(?bs. l = BytesL bs /\ ~is_word_type ann) \/ (?str. l = StringL str)` by
    (gvs[expr_sim_pre_def, well_typed_expr_def] >> Cases_on `l` >> gvs[] >>
     Cases_on `ann` >> gvs[well_typed_literal_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[well_typed_literal_def, is_word_type_def]) >>
  `expr_vv_ok cenv (Literal ann l)` by
    (irule compile_literal_other_vv_sim >> gvs[]) >>
  `expr_vv_sim ctx func cenv cx ty (Literal ann l) es` by
    (gvs[expr_vv_ok_def] >> metis_tac[]) >>
  simp[Once evaluate_def, return_def, evaluate_literal_def] >>
  gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def] >>
  rpt gen_tac >>
  simp[compile_expr_def, compile_literal_vv_def, vyperASTTheory.expr_type_def,
       is_word_type_def, comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  simp[contextTheory.base_ptr_def, is_word_type_def] >>
  rename1 `BaseT (BytesT bd)` >> Cases_on `bd` >>
  gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
      is_word_type_def, comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  simp[contextTheory.base_ptr_def, is_word_type_def]
QED

Theorem compile_literal_other_sim:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\
    ~(is_word_type ann /\
      ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i))) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rpt strip_tac >> Cases_on `is_word_type ann`
  >- (Cases_on `l` >> gvs[]
      >~ [`BytesL bs`] >- (irule compile_literal_bytes_word_sim >> metis_tac[]) >>
      gvs[expr_sim_pre_def, well_typed_expr_def] >>
      Cases_on `ann` >> gvs[well_typed_literal_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[well_typed_literal_def, is_word_type_def]) >>
  irule compile_literal_memory_sim >> metis_tac[]
QED

Theorem compile_literal_sim:
  !cenv ann l. expr_sim_ok cenv (Literal ann l)
Proof
  rw[expr_sim_ok_def] >>
  Cases_on `is_word_type ann /\
            ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i))`
  >- (irule compile_literal_word_sim >> fs[]) >>
  irule compile_literal_other_sim >> metis_tac[]
QED


(* A bytes literal is a word unless it is annotated with a dynamic bytes
   type. *)
Theorem compile_literal_bytes_stack:
  !ty bs st.
    (!n. ty <> BaseT (BytesT (Dynamic n))) ==>
    ?op. compile_literal_vv ty (BytesL bs) st = (StackValue ty op, st)
Proof
  rw[compile_literal_vv_def, comp_return_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[comp_return_def])
QED

Theorem compile_literal_case_sim:
  !cenv ann l. expr_ok cenv (Literal ann l)
Proof
  rpt gen_tac >>
  Cases_on `(?bs. l = BytesL bs /\ ~is_word_type ann) \/ (?str. l = StringL str)`
  >- (simp[expr_ok_def, compile_literal_sim] >>
      irule compile_literal_other_vv_sim >> simp[]) >>
  irule expr_ok_stack >> simp[compile_literal_sim] >> rpt conj_tac
  >~ [`eval_expr`]
  >- (rpt strip_tac >> drule eval_expr_literal_value >> simp[]) >>
  Cases_on `l` >> gvs[]
  >~ [`BytesL bs`]
  >- (`!n. ann <> BaseT (BytesT (Dynamic n))` by
        (rpt strip_tac >> gvs[is_word_type_def]) >>
      simp[compile_expr_def, vyperASTTheory.expr_type_def] >> rpt gen_tac >>
      drule compile_literal_bytes_stack >>
      disch_then (qspecl_then [`bs`, `sa`] strip_assume_tac) >> simp[])
  >~ [`BoolL b`]
  >- (Cases_on `b` >>
      simp[compile_expr_def, compile_literal_vv_def, comp_return_def]) >>
  simp[compile_expr_def, compile_literal_vv_def, comp_return_def]
QED

(* ===== Environment reads ===== *)

Theorem compile_prevhash_sim:
  !cenv ann args. expr_sim_ok cenv (Builtin ann (Env PrevHash) args)
Proof
  cheat
QED

Theorem compile_msg_gas_sim:
  !cenv ann args. expr_sim_ok cenv (Builtin ann (Env MsgGas) args)
Proof
  cheat
QED

Theorem compile_env_case_sim:
  !cenv ann item args. expr_sim_ok cenv (Builtin ann (Env item) args)
Proof
  rpt gen_tac >> Cases_on `item = PrevHash`
  >- simp[compile_prevhash_sim] >>
  Cases_on `item = MsgGas`
  >- simp[compile_msg_gas_sim] >>
  rw[expr_sim_ok_def] >>
  `args = [] /\ ann = env_item_type item` by
    gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> irule compile_env_sim >> simp[]
QED

(* An environment read goes to the builtin dispatcher, whatever its
   arguments (as exprBopLowering's compile_expr_bop). *)
Theorem compile_expr_env:
  !cenv ty ann item args st.
    compile_expr cenv ty (Builtin ann (Env item) args) st =
    compile_builtin_dispatch cenv ann ty (Env item) args st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       vyperASTTheory.expr_type_def] >>
  namedCases_on `args` ["", "arg rest"] >> simp[] >>
  Cases_on `arg` >> simp expr_sizes
  >~ [`_ = compile_builtin_dispatch _ _ _ _ (Name _ _ :: suffix) _`]
  >- (namedCases_on `suffix` ["", "arg2 tail2"] >> simp expr_sizes >>
      Cases_on `arg2` >> simp expr_sizes
      >~ [`_ = compile_builtin_dispatch _ _ _ _ (Name _ _ :: Name _ _ :: suffix2) _`]
      >- (namedCases_on `suffix2` ["", "arg3 tail3"] >> simp expr_sizes >>
          Cases_on `arg3` >> simp expr_sizes
          >~ [`_ = compile_builtin_dispatch _ _ _ _ (Name _ _ :: Name _ _ :: Name _ _ :: suffix3) _`]
          >- (Cases_on `suffix3` >> simp expr_sizes) >>
          rename1 `Call _ _ _ opt` >> Cases_on `opt` >> simp expr_sizes) >>
      rename1 `Call _ _ _ opt` >> Cases_on `opt` >> simp expr_sizes) >>
  rename1 `Call _ _ _ opt` >> Cases_on `opt` >> simp expr_sizes
QED

Theorem compile_env_case_ok:
  !cenv ann item args. expr_ok cenv (Builtin ann (Env item) args)
Proof
  rpt gen_tac >> irule expr_ok_stack >> simp[compile_env_case_sim] >>
  rpt conj_tac
  >~ [`eval_expr`]
  >- (rpt strip_tac >> drule eval_expr_builtin_value >> simp[]) >>
  rpt gen_tac >>
  simp[compile_expr_env] >> simp[Once compile_expr_def] >>
  metis_tac[as_stack_val_stack]
QED

(* ===== Top-level names and flag members ===== *)

val lookup_global_tac =
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM];

(* A storage or transient variable whose slot decodes at es: the source
   reads it (an aggregate array stays an ArrayRef, which materialise reads
   the same way) and leaves the state alone. *)
Theorem eval_expr_toplevel_storage:
  !cx ann src id es res es' ts tr typ id_str slot tvt v.
    eval_expr cx (TopLevelName ann (src, id)) es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) ==>
    es' = es /\ ?tv. res = INL tv /\ materialise cx tv es = (INL v, es)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >> lookup_global_tac >>
  Cases_on `tvt` >> gvs[return_def, bind_def, materialise_def] >>
  rpt strip_tac >> gvs[materialise_def, return_def, bind_def]
QED

(* The compile environment holds a storage or transient variable at the
   layout's slot (storage_vars_rel, transient_vars_rel). *)
Theorem toplevel_storage_ce_vars:
  !cenv cx src id ts tr typ id_str slot.
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot ==>
    FLOOKUP cenv.ce_vars (module_var_key (src, id)) =
      SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))
Proof
  rpt strip_tac >> Cases_on `tr` >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >>
  first_x_assum irule >> simp[var_decl_transient_def]
QED

(* A storage or transient variable whose slot decodes: a pointer to its
   slot, no code. *)
Theorem compile_toplevel_storage_vv_sim:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str slot tvt v.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_def] >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[vyperTypeGlobalLookupSoundnessTheory.TopLevelName_storage_decl_type_eq]) >>
  gvs[] >>
  drule_all eval_expr_toplevel_storage >> strip_tac >> gvs[] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. F`, `\s. F`, `expr_exit (INL tv)`] >>
      simp[fragExecTheory.frag_exec_false_pre] >>
      gvs[stmt_state_rel_def, state_rel_def]) >>
  fs[] >> drule_all toplevel_storage_ce_vars >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_def, vyperASTTheory.expr_type_def] >>
  Cases_on `tr` >> simp[] >> strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  simp[vv_post_def, vv_holds_def, vv_at_def, storage_holds_def,
       contextTheory.mk_ptr_def, eval_operand_def,
       vyperASTTheory.expr_type_def]
QED

(* A storage or transient variable whose slot does not decode at es (a
   dynamic array, bytestring or string, or an aggregate holding one, whose
   length word is above its bound).  Cheated, and false as stated: the
   source raises a RuntimeError reading it (or materialising the ArrayRef
   later), where the lowering emits no code and hands out the slot.
   Nothing in stmt_state_rel keeps a variable's slots decodable; the fix is
   a storage invariant, as for exprSimUnwrap's unwrap_storage_word_sim. *)
Theorem compile_toplevel_storage_undecodable_sim:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    ~(?slot tvt v. lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
                   evaluate_type (get_tenv cx) typ = SOME tvt /\
                   read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)) ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  cheat
QED

(* An immutable or a constant (no storage declaration of the name; both
   are read from the immutables).  Cheated, and false as stated: nothing in
   expr_sim_inv puts them in ce_vars (the lowering has no ImmutableLoc for
   immutables yet, #563) nor bounds their offsets (immutable_holds), so the
   lowering may emit INVALID where the source reads a value. *)
Theorem compile_toplevel_immutable_sim:
  !ctx func cenv cx env ty ann src id es ts.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  cheat
QED

(* A name whose module the context does not have: a type error. *)
Theorem compile_toplevel_no_module_sim:
  !ctx func cenv cx ty ann src id es.
    get_module_code cx src = NONE ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >> lookup_global_tac >>
  strip_tac >> gvs[expr_vv_res_ok_def, expr_res_ok_def]
QED

(* Storage, transient, immutable and constant reads.  A hashmap is not a
   typed TopLevelName. *)
Theorem compile_toplevel_name_sim:
  !cenv ann nsid. expr_vv_ok cenv (TopLevelName ann nsid)
Proof
  rw[expr_vv_ok_def] >> PairCases_on `nsid` >>
  rename1 `TopLevelName ann (src, id)` >>
  Cases_on `get_module_code cx src`
  >- simp[compile_toplevel_no_module_sim] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `find_var_decl_by_name id ts`
  >- (irule compile_toplevel_immutable_sim >> metis_tac[]) >>
  rename1 `find_var_decl_by_name id ts = SOME di` >>
  PairCases_on `di` >> Cases_on `di0`
  >~ [`HashMapVarDecl`]
  >- (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
      metis_tac[vyperTypeGlobalLookupSoundnessTheory.TopLevelName_Type_HashMapVarDecl_impossible]) >>
  rename1 `StorageVarDecl tr typ` >>
  Cases_on `?slot tvt v. lookup_var_slot_from_layout cx tr src di1 = SOME slot /\
                         evaluate_type (get_tenv cx) typ = SOME tvt /\
                         read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)`
  >- (gvs[] >> irule compile_toplevel_storage_vv_sim >> metis_tac[]) >>
  irule compile_toplevel_storage_undecodable_sim >> metis_tac[]
QED

Theorem eval_expr_flag_member:
  !cx ann src fid mid es res es'.
    eval_expr cx (FlagMember ann (src, fid) mid) es = (res, es') /\
    expr_res_ok res ==>
    es' = es /\
    ?ts ls i. get_module_code cx src = SOME ts /\
              lookup_flag fid ts = SOME ls /\ INDEX_OF mid ls = SOME i /\
              res = INL (Value (FlagV (2 ** i)))
Proof
  rpt gen_tac >> simp[Once evaluate_def, lookup_flag_mem_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >>
  rw[] >> gvs[expr_res_ok_def]
QED

(* A flag member is the literal 2 ** id, id its index in its flag's
   declaration by expr_sim_inv's flag members clause. *)
Theorem compile_flag_member_word_sim:
  !cenv ann nsid mid. expr_sim_ok cenv (FlagMember ann nsid mid)
Proof
  rw[expr_sim_ok_def, expr_sim_def] >> PairCases_on `nsid` >>
  drule_all eval_expr_flag_member >> strip_tac >> gvs[] >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0, nsid1)) mid = i` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0, nsid1)` by gvs[expr_sim_pre_def, well_typed_expr_def] >>
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      unwrap_value_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def]
QED

Theorem compile_flag_member_case_sim:
  !cenv ann nsid mid. expr_ok cenv (FlagMember ann nsid mid)
Proof
  rpt gen_tac >> irule expr_ok_stack >>
  simp[compile_flag_member_word_sim, compile_expr_def] >>
  PairCases_on `nsid` >> rpt gen_tac >>
  simp[Once evaluate_def, lookup_flag_mem_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >> rw[]
QED

Theorem compile_flag_member_sim:
  !cenv ann nsid mid. expr_vv_ok cenv (FlagMember ann nsid mid)
Proof
  metis_tac[compile_flag_member_case_sim, expr_ok_def]
QED
