(*
 * The hypotheses of the expression simulation theorem (#636)
 *
 * The main theorems (exprSimMain's compile_expr_sim and
 * compile_expr_vv_sim) say expr_ok of every expression: expr_sim and
 * expr_vv_sim (exprSim) hold at every source state where expr_sim_pre
 * holds.  expr_sim speaks of lower_value's code, expr_vv_sim of
 * compile_expr's alone and the value_vv it hands out, for a case that
 * unwraps an operand later or never.  The case lemmas each prove expr_ok,
 * or expr_vv_ok, from which expr_ok follows (expr_ok_of_vv), of one form of
 * expression from expr_sim_below, expr_ok of every smaller expression,
 * which is the induction hypothesis compile_expr_ind gives.
 *
 * TOP-LEVEL:
 *   expr_sim_inv      — the facts about the source state and the context
 *                       that every subexpression keeps: type soundness's
 *                       invariants, and the locals of the type environment
 *                       held through pointer variables
 *   expr_sim_pre      — expr_sim_inv, the expression well typed, and no
 *                       internal call in it
 *   expr_sim_ok       — expr_sim wherever expr_sim_pre holds
 *   expr_vv_ok        — expr_vv_sim wherever expr_sim_pre holds
 *   expr_ok           — both: the induction predicate
 *   expr_sim_below    — expr_ok of every expression below a size
 *   builtin_sim_ok, type_builtin_sim_ok — expr_ok of a builtin and a type
 *                       builtin, the dispatchers' induction predicates
 *   names_builtin     — the three builtins on names that compile_expr does
 *                       not hand to compile_builtin_dispatch
 *   compile_expr_type_builtin_dispatch — compile_expr of a type builtin is
 *                       its dispatcher's
 *   word_value_type   — the types whose values are word_values
 *   expr_sim_pre_eval — type soundness: evaluation keeps expr_sim_inv and
 *                       raises no type error
 *   expr_sim_pre_res_ok, expr_sim_pre_word_result — the results of an
 *                       expression are those expr_sim speaks of; a
 *                       word_value_type one's values are word_values
 *   expr_sim_pre_builtin_arg — an argument of a builtin meets expr_sim_pre
 *                       wherever expr_sim_inv holds
 *   well_typed_expr_type_evaluates — a well-typed expression's type
 *                       evaluates
 *   expr_sim_of_vv_sim — unwrap_value's step: expr_vv_sim gives expr_sim,
 *                       by unwrap_value_sim, one case per value_vv form.
 *                       It rests on these cheats:
 *                       compile_expr_extends and
 *                       compile_ensure_in_memory_extends (the compile-side
 *                       shape facts, #679); unwrap_storage_word_sim (a load
 *                       from storage of a slot holding a word outside the
 *                       type's range); unwrap_ctor_immutable_word_sim (ILOAD
 *                       reads memory, immutables_rel the constructor's
 *                       vs_immutables); unwrap_copy_sim (the copy of an
 *                       aggregate out of storage or code)
 *   expr_ok_of_vv, expr_ok_stack — expr_ok from expr_vv_ok, and from
 *                       expr_sim_ok for a form lowered to a StackValue
 *
 * Why these hypotheses:
 *   - well_typed_expr, env_consistent, state_well_typed,
 *     accounts_well_typed, context_well_typed, functions_well_typed and
 *     call_evaluation_safe are exactly the premises of type soundness
 *     (vyperTypeEvalSoundness's eval_all_type_sound_mutual, the expression
 *     conjunct).  The lowering trusts the annotations: an operator picks its
 *     bounds from the operand's annotated type, a literal is emitted at its
 *     annotated type.  So an expression whose values do not have their
 *     annotated types is lowered to code that does not simulate it.  Type
 *     soundness gives what the case lemmas need of the source values (a word
 *     operand evaluates to a word, a result has its type) and carries
 *     env_consistent, state_well_typed and accounts_well_typed to the next
 *     operand; the others are about the context and do not change.  With no
 *     internal call, call_evaluation_safe is call_evaluation_safe cx [], a
 *     fact about the call stack.
 *   - The locals clause: every local of the type environment is held
 *     through a pointer variable (PtrVar (Var p)).  This is how the
 *     statement lowering registers the parameters and locals of an external
 *     function without default arguments; state_rel only relates the locals
 *     that are held so (local_ptrs_rel), and compile_name_vv emits INVALID
 *     for a name it does not find.  Default arguments, and the locals of
 *     internal functions and the constructor, are MemLoc
 *     (compile_register_kwarg_vars, local_ptrs_reserved), so the theorem
 *     says nothing yet about expressions there.
 *   - int_calls_expr e = []: no internal call.  An internal call lowers to
 *     INVOKE, whose simulation is #638's call step; until that is stated
 *     this theorem excludes them, and #638 replaces this conjunct with its
 *     hypothesis on the callees.
 *
 * Not here yet:
 *   - The compile environment's metadata (struct fields, flag member ids,
 *     dynamic array capacities, method ids) is not related to the source
 *     context.  The cases that read it (StructLit, Attribute, FlagMember,
 *     Pop, method_id, ...) will need a clause each in expr_sim_inv, and
 *     TopLevelName needs every module variable to be in ce_vars.  Each is
 *     to match what Vyper's compiler guarantees.
 *   - Keeping an operand's value_vv through the code between compile_expr
 *     and unwrap_value (a later operand's fragment) needs the operand
 *     composition of #636's Infrastructure: vv_post's memory frame for a
 *     pointer into memory, unchanged storage for a storage pointer.
 *)

Theory exprSimHyps
Ancestors
  list finite_map
  exprSim exprCallBounds exprBopLowering exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperTypeExprResult vyperTypeEvalSoundness vyperTypeBuiltins
  vyperExprNoControl loweringSlice fragExec venomInst venomExecSemantics
  venomState
Libs
  pairLib

(* ===== The hypotheses ===== *)

Definition expr_sim_inv_def:
  expr_sim_inv cenv cx env (es:evaluation_state) <=>
    env_consistent env cx es /\ state_well_typed es /\
    accounts_well_typed es.accounts /\
    context_well_typed cx /\ functions_well_typed cx /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
             ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz))
End

(* The types whose values are word_values (loweringSlice): integers,
   decimals, booleans and flags.  address and bytesN values are BytesV. *)
Definition word_value_type_def:
  word_value_type t <=> is_numeric_type t \/ is_bool_type t \/ is_flag_type t
End

Definition expr_sim_pre_def:
  expr_sim_pre cenv cx env e es <=>
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    int_calls_expr e = [] /\ call_evaluation_safe cx (int_calls_expr e)
End

Definition expr_sim_ok_def:
  expr_sim_ok cenv e <=>
    !ctx func cx env ty es.
      expr_sim_pre cenv cx env e es ==> expr_sim ctx func cenv cx ty e es
End

Definition expr_vv_ok_def:
  expr_vv_ok cenv e <=>
    !ctx func cx env ty es.
      expr_sim_pre cenv cx env e es ==> expr_vv_sim ctx func cenv cx ty e es
End

(* The induction predicate: both judgments, so a case can use whichever an
   operand's lowering needs. *)
Definition expr_ok_def:
  expr_ok cenv e <=> expr_sim_ok cenv e /\ expr_vv_ok cenv e
End

Definition expr_sim_below_def:
  expr_sim_below cenv n <=> !e. expr_size e < n ==> expr_ok cenv e
End

(* AddMod, MulMod and PowMod256 applied to names: compile_expr lowers these
   itself (compile_addmod_names, ...), not through
   compile_builtin_dispatch. *)
Definition names_builtin_def:
  (names_builtin AddMod [Name _ _; Name _ _; Name _ _] <=> T) /\
  (names_builtin MulMod [Name _ _; Name _ _; Name _ _] <=> T) /\
  (names_builtin PowMod256 [Name _ _; Name _ _] <=> T) /\
  (names_builtin _ _ <=> F)
End

Definition builtin_sim_ok_def:
  builtin_sim_ok cenv ann bi args <=>
    ~names_builtin bi args ==> expr_ok cenv (Builtin ann bi args)
End

Definition type_builtin_sim_ok_def:
  type_builtin_sim_ok cenv ann tb t args <=>
    expr_ok cenv (TypeBuiltin ann tb t args)
End

(* ===== The induction hypothesis ===== *)

Theorem expr_sim_below_mono:
  !cenv m n. expr_sim_below cenv n /\ m <= n ==> expr_sim_below cenv m
Proof
  rw[expr_sim_below_def]
QED

Theorem expr_sim_below_mem:
  !cenv args e.
    expr_sim_below cenv (list_size expr_size args) /\ MEM e args ==>
    expr_ok cenv e
Proof
  rw[expr_sim_below_def] >> first_x_assum irule >>
  irule expr_list_member_bound >> simp[]
QED

(* ===== compile_expr of a builtin ===== *)

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

Theorem compile_expr_type_builtin_dispatch:
  !cenv ty ann tb t args st.
    compile_expr cenv ty (TypeBuiltin ann tb t args) st =
    compile_type_builtin_dispatch cenv ann ty tb t args st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       vyperASTTheory.expr_type_def] >>
  simp expr_sizes
QED

(* ===== Type soundness ===== *)

Theorem expr_sim_pre_eval:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ no_type_error_result res /\
    !tv. res = INL tv ==> expr_result_typed env e tv
Proof
  rpt gen_tac >> simp[expr_sim_pre_def, expr_sim_inv_def] >> strip_tac >>
  qspecl_then [`cx`, `e`, `env`, `es`, `res`, `es'`] mp_tac
    (cj 8 eval_all_type_sound_mutual) >>
  impl_tac >- gvs[] >> disch_then (mp_tac o CONJUNCT1) >>
  impl_tac >- gvs[] >>
  Cases_on `res` >> rpt strip_tac >> gvs[]
QED

Theorem expr_sim_pre_res_ok:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ eval_expr cx e es = (res, es') /\
    (!tv. res = INL tv ==> is_Value tv) ==>
    expr_res_ok res
Proof
  rpt strip_tac >> drule_all expr_sim_pre_eval >> strip_tac >>
  Cases_on `res` >> gvs[expr_res_ok_def]
  >- (rename1 `is_Value tv` >> Cases_on `tv` >> gvs[]) >>
  drule (cj 1 eval_expr_no_control) >>
  rename1 `INR exc` >>
  Cases_on `exc` >> gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem word_value_type_typed:
  !t tenv tyv x.
    word_value_type t /\ evaluate_type tenv t = SOME tyv /\
    toplevel_value_typed x tyv ==>
    ?v. x = Value v /\ word_value v /\ value_has_type tyv v
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT \/ t = BaseT BoolT \/ (?nsid. t = FlagT nsid)` by
    (Cases_on `t` >> fs[word_value_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_int_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `x` >> gvs[toplevel_value_typed_def] >>
  rename1 `value_has_type _ v` >> Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, word_value_def]
QED

Theorem expr_sim_pre_word_result:
  !cenv cx env e es res es'.
    expr_sim_pre cenv cx env e es /\ word_value_type (expr_type e) /\
    eval_expr cx e es = (res, es') ==>
    expr_sim_inv cenv cx env es' /\ expr_res_ok res /\
    !tv. res = INL tv ==>
         ?v tyv. tv = Value v /\ word_value v /\
                 evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
                 value_has_type tyv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_sim_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  Cases_on `res` >> gvs[]
  >- (gvs[expr_result_typed_def, expr_runtime_typed_def] >>
      drule_all word_value_type_typed >> strip_tac >> gvs[expr_res_ok_def]) >>
  irule expr_sim_pre_res_ok >> simp[] >> metis_tac[]
QED

Theorem well_typed_exprs_mem:
  !args env e.
    well_typed_exprs env args /\ int_calls_exprs args = [] /\ MEM e args ==>
    well_typed_expr env e /\ int_calls_expr e = []
Proof
  Induct >> rw[well_typed_expr_def, int_calls_expr_def] >> metis_tac[]
QED

Theorem expr_sim_pre_builtin_arg:
  !cenv cx env ann bi args e es es'.
    expr_sim_pre cenv cx env (Builtin ann bi args) es /\ MEM e args /\
    expr_sim_inv cenv cx env es' ==>
    expr_sim_pre cenv cx env e es'
Proof
  rw[expr_sim_pre_def, well_typed_expr_def, int_calls_expr_def] >>
  drule_all well_typed_exprs_mem >> gvs[]
QED

Theorem env_consistent_var_type_evaluates:
  !env cx st id ty.
    env_consistent env cx st /\ FLOOKUP env.var_types id = SOME ty ==>
    IS_SOME (evaluate_type (get_tenv cx) ty)
Proof
  rw[env_consistent_def, env_scopes_consistent_def] >>
  Cases_on `lookup_scopes id st.scopes` >>
  metis_tac[optionTheory.IS_SOME_DEF]
QED

(* A well-typed expression's type evaluates: its typing rule says the type
   is well formed, but for a local, whose type evaluates by
   env_scopes_consistent, and pop, whose type is assignable. *)
Theorem well_typed_expr_type_evaluates:
  !cenv cx env e es.
    expr_sim_pre cenv cx env e es ==>
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e))
Proof
  rw[expr_sim_pre_def] >>
  `env_consistent env cx es` by gvs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `well_formed_type env.type_defs (expr_type e)` suffices_by
    gvs[well_formed_type_def] >>
  Cases_on `e` >> simp[vyperASTTheory.expr_type_def]
  >~ [`Name _ _`]
  >- (gvs[well_typed_expr_def, well_formed_type_def] >>
      metis_tac[env_consistent_var_type_evaluates])
  >~ [`TopLevelName _ nsid`]
  >- (PairCases_on `nsid` >> gvs[well_typed_expr_def])
  >~ [`Pop _ _`]
  >- (gvs[well_typed_expr_def, assignable_type_def] >>
      metis_tac[assignable_type_well_formed])
  >~ [`Call _ target _ _`]
  >- (Cases_on `target` >>
      gvs[well_typed_expr_def, well_formed_type_def,
          vyperValueTheory.evaluate_type_def]
      >~ [`IntCall nsid`]
      >- (PairCases_on `nsid` >> gvs[well_typed_expr_def, well_formed_type_def])
      >~ [`ExtCall _ _ sig _`]
      >- (PairCases_on `sig` >> gvs[well_typed_expr_def, well_formed_type_def]) >>
      irule (REWRITE_RULE [well_formed_type_def]
               raw_call_return_type_well_formed) >> simp[]) >>
  gvs[well_typed_expr_def]
QED

(* ===== From one judgment to the other ===== *)

(* compile_expr only appends to the compile state and hands out variables
   from its start counter on.  Cheated: the shape fact compile_expr_shape
   (#679) proves for the shape judgment. *)
Theorem compile_expr_extends:
  !cenv ty e sa vv sm.
    compile_expr cenv ty e sa = (vv, sm) ==>
    cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var
Proof
  cheat
QED

(* compile_ensure_in_memory's copy only appends to the compile state.
   Cheated with compile_expr_extends: its copy loops start blocks of their
   own, as compile_expr's do. *)
Theorem compile_ensure_in_memory_extends:
  !ptr loc mem_bytes word_count is_ctor sm op sb.
    compile_ensure_in_memory ptr loc mem_bytes word_count is_ctor sm =
      (op, sb) ==>
    cs_extends sm sb
Proof
  cheat
QED

Theorem emit_op_cs_extends:
  !opc args sm op sb. emit_op opc args sm = (op, sb) ==> cs_extends sm sb
Proof
  rpt strip_tac >> drule exprLoweringPropsTheory.emit_op_extends >>
  rw[exprLoweringPropsTheory.same_blocks_def] >>
  irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem unwrap_value_extends:
  !cenv vv sm op sb. unwrap_value cenv vv sm = (op, sb) ==> cs_extends sm sb
Proof
  Cases_on `vv` >>
  rw[unwrap_value_def, comp_return_def, cs_extends_refl]
  >- (rename1 `compile_ptr_load _ loc` >> Cases_on `loc` >>
      gvs[contextTheory.compile_ptr_load_def, AllCaseEqs()] >>
      metis_tac[emit_op_cs_extends]) >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  gvs[comp_return_def, cs_extends_refl] >>
  metis_tac[compile_ensure_in_memory_extends]
QED

Theorem not_fresh_at_le[local]:
  !st st' x.
    not_fresh_at st x /\ st.cs_next_var <= st'.cs_next_var ==>
    not_fresh_at st' x
Proof
  rw[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* unwrap_value's code, run where compile_expr's code ends, takes vv_post to
   expr_post.  One lemma per form of value_vv. *)

(* A StackValue: no code. *)
Theorem expr_post_of_vv_post_stack:
  !func cenv cx e es sa sb s0 es' v t op s.
    vv_post func cenv cx e es sa sb s0 es' (Value v) (StackValue t op) s ==>
    expr_post func cenv cx e es sa sb s0 es' v op s
Proof
  rw[vv_post_def, expr_post_def, vv_holds_def, vv_at_def]
QED

(* An aggregate in memory: the pointer is the operand, no code. *)
Theorem expr_post_of_vv_post_memory:
  !func cenv cx e es sa sb s0 es' v t p s.
    vv_post func cenv cx e es sa sb s0 es' (Value v) (LocatedValue t p) s /\
    p.ptr_location = LocMemory /\ ~is_word_type t ==>
    expr_post func cenv cx e es sa sb s0 es' v p.ptr_operand s
Proof
  rw[vv_post_def, expr_post_def, vv_holds_def, vv_at_def] >>
  gvs[materialise_def, return_def, expr_val_rel_def, expr_val_at_def] >>
  metis_tac[]
QED

(* The end of a one-instruction load of a word: the loaded word in a fresh
   variable, nothing else changed. *)
Theorem expr_post_of_vv_post_load:
  !func cenv cx e es sa sm sb s0 es' v t p op s1 s w.
    vv_post func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s1 /\
    is_word_type (expr_type e) /\ sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel func cenv cx es' s /\ eval_operand op s = SOME w /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
           w = typed_val_to_w256 tvt v) /\
    (!x w'. not_fresh_at sm x /\ lookup_var x s1 = SOME w' ==>
            lookup_var x s = SOME w') /\
    (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    s.vs_memory = s1.vs_memory ==>
    expr_post func cenv cx e es sa sb s0 es' v op s
Proof
  rw[expr_post_def]
  >~ [`expr_val_rel`] >- gvs[expr_val_rel_def]
  >~ [`expr_val_at`] >- simp[expr_val_at_def]
  >~ [`lookup_var x s`]
  >- (fs[vv_post_def] >> metis_tac[not_fresh_at_le])
  >~ [`FLOOKUP s.vs_allocas`] >- fs[vv_post_def] >>
  fs[vv_post_def] >> metis_tac[]
QED

(* A word in memory: an MLOAD. *)
Theorem unwrap_memory_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op MLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocMemory /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       !tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
             mem_word_at (w2n w) s1.vs_memory = typed_val_to_w256 tvt v` by
    (gvs[vv_post_def, vv_holds_def, materialise_def, return_def] >>
     metis_tac[]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule loweringSliceTheory.emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s1`,
                           `mload (w2n w) s1`, `R`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- simp[]
      >- simp[is_terminator_def] >>
      rpt strip_tac >> irule emitHelperPropsTheory.step_MLOAD >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`] >- (
  qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`, `es'`,
               `v`, `expr_type e`, `p`, `op`, `s1`, `s`, `mload (w2n w) s1`]
    mp_tac expr_post_of_vv_post_load >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt strip_tac >>
      fs[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  simp[]) >>
  gvs[vv_post_def]
QED

Theorem step_DLOAD:
  !op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ==>
    step_inst_base (mk_inst id DLOAD [op1] [out]) ss =
      OK (update_var out
            (word_of_bytes T (0w:bytes32)
               (TAKE 32 (DROP (w2n v1) ss.vs_data_section ++
                         REPLICATE 32 0w))) ss)
Proof
  rw[venomExecSemanticsTheory.step_inst_base_def,
     venomExecSemanticsTheory.exec_read1_def]
QED

(* At runtime an immutable's word is in the data section at its offset, as
   immutables_rel says. *)
Theorem immutable_holds_dload:
  !func cenv cx es s t v w.
    stmt_state_rel func cenv cx es s /\ ~cenv.ce_is_ctor /\
    immutable_holds cenv cx t (Value v) w es ==>
    ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\
          word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) =
          typed_val_to_w256 tvt v
Proof
  rw[immutable_holds_def, exprLoweringPropsTheory.stmt_state_rel_def,
     state_rel_def, immutables_rel_def] >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  simp[rich_listTheory.TAKE_APPEND1]
QED

(* A word immutable at runtime: a DLOAD. *)
Theorem unwrap_runtime_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    emit_op DLOAD [p.ptr_operand] sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rw[] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ s1` >>
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s1 = SOME w /\
       immutable_holds cenv cx (expr_type e) (Value v) w es' /\
       stmt_state_rel func cenv cx es' s1` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all immutable_holds_dload >> strip_tac >>
  drule loweringSliceTheory.emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s1`,
    `word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s1.vs_data_section ++ REPLICATE 32 0w))`,
    `R`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- simp[]
      >- simp[is_terminator_def] >>
      rpt strip_tac >> irule step_DLOAD >> first_assum ACCEPT_TAC) >>
  strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt strip_tac
  >~ [`expr_post`] >- (
  qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`, `s0`, `es'`,
               `v`, `expr_type e`, `p`, `op`, `s1`, `s`,
               `word_of_bytes T (0w:bytes32)
                  (TAKE 32 (DROP (w2n w) s1.vs_data_section ++
                            REPLICATE 32 0w))`]
    mp_tac expr_post_of_vv_post_load >>
  impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  simp[]) >>
  gvs[]
QED

(* A word in storage or transient storage: an SLOAD or TLOAD.  Cheated:
   storage_holds relates the slot through decode_base_from_slot, which
   truncates, so a slot holding a word outside the type's range (0x1FF for a
   uint8) decodes to a value of the type while the load returns the raw
   word.  storage_rel as it stands does not rule such a slot out. *)
Theorem unwrap_storage_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* A word immutable in the constructor: an ILOAD.  Cheated, and not
   provable as the definitions stand: ILOAD reads memory, while
   immutables_rel relates the constructor's immutables to vs_immutables.
   Python reads them from memory at the immutables' buffer
   (iload(immutables_alloca + offset)); compile_load_immutable_ctor, which
   would match, is not used. *)
Theorem unwrap_ctor_immutable_word_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* An aggregate in storage, transient storage or code: a copy into a buffer
   of the expression's own.  Cheated.  From storage and transient storage
   it is the copy loop's proof; from code it is not provable as the
   definitions stand: immutables_rel relates only an immutable's 32-byte
   word, where Python copies the value's whole memory layout
   (copy_to_memory of memory_bytes_required bytes from the data section).
   The fix is for immutables_rel to say the data section holds the value as
   val_in_memory lays it out at its offset. *)
Theorem unwrap_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

(* No value_vv points into calldata. *)
Theorem vv_post_calldata:
  !func cenv cx e es sa sm s0 es' tv t p s.
    p.ptr_location = LocCalldata ==>
    ~vv_post func cenv cx e es sa sm s0 es' tv (LocatedValue t p) s
Proof
  rw[vv_post_def, vv_holds_def]
QED

Theorem unwrap_value_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op R.
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
    frag_exec ctx sm sb
      (\s. vv_post func cenv cx e es sa sm s0 es' (Value v) vv s)
      (\s. expr_post func cenv cx e es sa sb s0 es' v op s) R
Proof
  rpt strip_tac >> Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
      rw[] >> metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. F`, `\s. F`, `R`] >>
      gvs[fragExecTheory.frag_exec_false_pre, vv_post_calldata]) >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (Cases_on `is_word_type t`
      >- (irule unwrap_storage_word_sim >> gvs[]) >>
      irule unwrap_copy_sim >> gvs[] >>
      qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (Cases_on `is_word_type t` >~ [`~is_word_type t`]
      >- (irule unwrap_copy_sim >> gvs[]) >>
      Cases_on `cenv.ce_is_ctor`
      >- (irule unwrap_ctor_immutable_word_sim >> gvs[]) >>
      irule unwrap_runtime_immutable_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  `p.ptr_location = LocMemory` by (Cases_on `p.ptr_location` >> gvs[]) >>
  Cases_on `is_word_type t`
  >- (irule unwrap_memory_word_sim >>
      gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  gvs[unwrap_value_def, comp_return_def] >> irule frag_exec_refl >>
  rw[] >> metis_tac[expr_post_of_vv_post_memory]
QED

(* unwrap_value's step: expr_vv_sim gives expr_sim.  compile_expr's
   fragment ends in vv_post, and unwrap_value's code takes that to
   expr_post. *)
Theorem expr_sim_of_vv_sim:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es ==> expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `expr_vv_res_ok res` by simp[expr_vv_res_ok_def] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `res`, `es'`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_seq >> first_x_assum (irule_at Any) >> simp[] >>
  Cases_on `?v. res = INL (Value v)`
  >- (gvs[] >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `sb`,
                   `s0`, `es'`, `v`, `vv`, `op`, `expr_exit (INL (Value v))`]
        mp_tac unwrap_value_sim >>
      impl_tac >- asm_rewrite_tac[] >>
      strip_tac >> irule frag_exec_conseq >> first_x_assum (irule_at Any) >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. F`, `\s. F`, `expr_exit res`] >>
  simp[fragExecTheory.frag_exec_false_pre] >>
  gvs[expr_res_ok_def]
QED

(* A case lemma that proves expr_vv_ok proves expr_ok. *)
Theorem expr_ok_of_vv:
  !cenv e. expr_vv_ok cenv e ==> expr_ok cenv e
Proof
  rw[expr_ok_def, expr_sim_ok_def] >>
  metis_tac[expr_sim_of_vv_sim, expr_vv_ok_def]
QED

(* A form lowered to a StackValue, with only values as results: expr_ok
   from expr_sim_ok (exprSim's expr_vv_sim_stack). *)
Theorem expr_ok_stack:
  !cenv e.
    expr_sim_ok cenv e /\
    (!ty sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!cx es tv es'. eval_expr cx e es = (INL tv, es') ==> ?v. tv = Value v) ==>
    expr_ok cenv e
Proof
  rw[expr_ok_def, expr_vv_ok_def] >> irule expr_vv_sim_stack >>
  gvs[expr_sim_ok_def] >> metis_tac[]
QED

Theorem as_stack_val_stack:
  !ty p. ?op st. as_stack_val ty p = (StackValue ty op, st)
Proof
  Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem eval_expr_builtin_value:
  !cx ann bi args es tv es'.
    eval_expr cx (Builtin ann bi args) es = (INL tv, es') ==> ?v. tv = Value v
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, COND_RATOR] >>
  rw[] >> gvs[AllCaseEqs()]
QED

Theorem eval_expr_literal_value:
  !cx ann l es tv es'.
    eval_expr cx (Literal ann l) es = (INL tv, es') ==> ?v. tv = Value v
Proof
  simp[Once evaluate_def, return_def]
QED
