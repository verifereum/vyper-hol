(*
 * Expression simulation in the unit context (#636, part 1)
 *
 * The judgment expr_sim: the fragment of an expression, run from
 * stmt_state_rel at the source state where the expression is evaluated,
 * either reaches its end with stmt_state_rel at the source state after it
 * and the operand holding its value (expr_post), or, where the source
 * raises an error other than a type error or an assertion, exits with an
 * Abort as result_rel allows.
 *
 * TOP-LEVEL:
 *   expr_exit, expr_res_ok, expr_val_rel, expr_post, expr_sim
 *   expr_sim_values        — expr_sim of an expression whose results are
 *                            values, from its fragment reaching expr_post
 *   expr_sim_expr_frag     — expr_sim gives loweringSlice's expr_frag
 *   stmt_state_rel_vars_frame, stmt_state_rel_vars_ext,
 *   stmt_state_rel_drop_fresh — stmt_state_rel reads the variables only
 *                            through the live locals' pointers
 *   compile_literal_word_sim — bool, integer and decimal literals
 *   compile_name_word_sim  — a word local
 *   compile_env_sim        — environment reads (msg.sender, block.number,
 *                            ...), all but block.prevhash
 *
 * Helpers: expr_exit_INL, typed_val_to_w256_word_value, eval_expr_env,
 *   lower_value_env
 *
 * Values are related by expr_val_rel, by the expression's type: a word
 * type's value as the operand in the typed encoding typed_val_to_w256, any
 * other type's value in memory at the operand, as val_in_memory has it.
 * expr_post keeps the memory of the allocations made before the
 * fragment's start, but its own and the live locals'.  So two operands
 * lowered in turn compose where the first one's value sits in a buffer it
 * allocated: that allocation's id is below the second's start counter and
 * it holds no local, so the second's expr_post keeps its bytes, and
 * val_in_memory with them (a lemma that val_in_memory reads only the
 * value's bytes is still to be proved).  expr_val_rel does not say where
 * the bytes are; an operator's proof takes that from the operand's
 * lowering.  A first operand that points into a local stays related
 * through stmt_state_rel, as long as the source leaves that local alone
 * in between.  expr_frag, which relates values by val_to_w256, follows
 * for a word type whose typed encoding is val_to_w256
 * (expr_sim_expr_frag).
 *
 * Not covered by the leaves here:
 *   - bytes and string literals: a bytesN literal is a Lit of its typed
 *     encoding, a dynamic bytes or string literal a memory buffer;
 *   - locals other than word_value ones (address, bytesN, memory-backed);
 *   - block.prevhash: evaluate_block_hash raises a RuntimeError when the
 *     block number is 0 or the hash list is too short, while Venom's
 *     BLOCKHASH is total, so the lowered code does not abort there; and
 *     call_ctx_rel does not relate bc_blockhash to the transaction's block
 *     hashes.  expr_sim is unprovable for it as things stand.
 * Nor does the memory frame in expr_post follow from stmt_state_rel for an
 * expression whose lowering writes a DALLOCA buffer (raw_call of msg.data,
 * the create copy and blueprint lowerings): DALLOCA allocates at vs_fmp,
 * which stmt_state_rel does not relate to the ALLOCA allocations.
 * compile_env_sim holds for msg.gas only because the source raises a
 * TypeError for it (vyperContext's evaluate_builtin), which expr_sim
 * leaves out, while the lowering emits GAS: the two do not agree on
 * msg.gas.
 *)

Theory exprSim
Ancestors
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState

(* ===== The judgment ===== *)

(* The exits a source result allows: an error other than a type error
   (a runtime error, or the revert of a failed external call, create or
   raw_call) any Abort, an assertion a revert, or an exceptional halt for
   "UNREACHABLE", as result_rel relates them.  external_call_result_rel
   asks a revert for RevertData, but result_rel, which the statement lemmas
   conclude, allows any Abort. *)
Definition expr_exit_def:
  (expr_exit (INR (Error (RuntimeError m))) (Abort a s) <=> T) /\
  (expr_exit (INR (Error (RevertData d))) (Abort a s) <=> T) /\
  (expr_exit (INR (AssertException str)) (Abort a s) <=>
     a = Revert_abort \/ (a = ExHalt_abort /\ str = "UNREACHABLE")) /\
  (expr_exit _ _ <=> F)
End

Theorem expr_exit_INL[simp]:
  !x r. ~expr_exit (INL x) r
Proof
  Cases_on `r` >> simp[expr_exit_def]
QED

(* The source results the judgment speaks of: a value, an error other than
   a type error, or an assertion.  Type errors and control exceptions
   (break, continue, return) are left out. *)
Definition expr_res_ok_def:
  expr_res_ok (res : toplevel_value + exception) <=>
    (?v. res = INL (Value v)) \/ (?m. res = INR (Error (RuntimeError m))) \/
    (?d. res = INR (Error (RevertData d))) \/
    (?str. res = INR (AssertException str))
End

(* The value v of an expression of type t held by operand op in s: a word
   type's value as the operand, in the typed word encoding of t (the one
   the lowering uses for address and bytesN), any other type's value in
   memory at the operand's address, as val_in_memory lays it out.  The
   lowering makes the same split: unwrap_value loads a word type and hands
   out the pointer of any other.  Nothing is said where t does not
   evaluate. *)
Definition expr_val_rel_def:
  expr_val_rel cx t v op s <=>
    ?w. eval_operand op s = SOME w /\
        !tv. evaluate_type (get_tenv cx) t = SOME tv ==>
             if is_word_type t then w = typed_val_to_w256 tv v
             else val_in_memory tv v (w2n w) s.vs_memory
End

(* Where the fragment of e that started in s0, related at es, at compile
   state sa ends when the source gives v and es': related at es', the
   operand op holding v, the variables handed out before sa and the
   allocations of s0 kept, and the memory of the allocations of s0 kept,
   but for two kinds:
   - those of e's own ALLOCAs (instruction id sa.cs_next_id or above): an
     ALLOCA run again, in a loop body, returns its earlier buffer, which e
     then writes again;
   - those holding a live local: e can write a local (x.pop()), and
     stmt_state_rel at es' says what the locals hold.
   The rest are the buffers of the expressions lowered before e, so a
   value an earlier operand left in memory survives e's fragment. *)
Definition expr_post_def:
  expr_post func cenv cx e es sa s0 es' v op s <=>
    stmt_state_rel func cenv cx es' s /\
    expr_val_rel cx (expr_type e) v op s /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory)
End

(* The fragment of e lowered as a value of type ty, run from a state
   related at es, the source state where e is evaluated, under the code
   premises of the statement lemmas.  On a value it reaches its end in
   expr_post; on an error other than a type error or an assertion it exits
   as expr_exit allows.  This is expr_frag (loweringSlice) with the failing
   outcomes added. *)
Definition expr_sim_def:
  expr_sim ctx func cenv cx ty e es <=>
    !sa sb op res es' s0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      eval_expr cx e es = (res, es') /\ expr_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
        (\s. ?v. res = INL (Value v) /\
                 expr_post func cenv cx e es sa s0 es' v op s)
        (expr_exit res)
End

(* expr_sim gives expr_frag where the expression's type is a word type
   whose typed encoding agrees, on the values the expression evaluates to,
   with val_to_w256, the encoding expr_frag uses. *)
Theorem expr_sim_expr_frag:
  !ctx func cenv cx ty e es R tv.
    expr_sim ctx func cenv cx ty e es /\ is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    (!v es'. eval_expr cx e es = (INL (Value v), es') ==>
             typed_val_to_w256 tv v = val_to_w256 v) ==>
    expr_frag ctx func cenv cx ty e es R
Proof
  rw[expr_sim_def, expr_frag_def] >>
  first_x_assum (qspecl_then [`sa`, `sb`, `op`, `INL (Value v)`, `es'`, `s0`]
                   mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  strip_tac >> irule frag_exec_conseq >>
  first_x_assum (irule_at Any) >>
  simp[expr_post_def, expr_val_rel_def] >> rpt strip_tac >>
  qpat_x_assum `!tv. evaluate_type _ _ = SOME tv ==> _`
    (qspec_then `tv` mp_tac) >>
  qpat_x_assum `!v es'. eval_expr _ _ _ = _ ==> _` drule >>
  gvs[]
QED

(* An expression whose results the judgment speaks of are all values: its
   fragment need only reach expr_post. *)
Theorem expr_sim_values:
  !ctx func cenv cx ty e es.
    (!res es'. eval_expr cx e es = (res, es') /\ expr_res_ok res ==>
               ?v. res = INL (Value v)) /\
    (!sa sb op v es' s0.
       lower_value compile_expr cenv ty e sa = (op, sb) /\
       eval_expr cx e es = (INL (Value v), es') /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa ==>
       frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
         (expr_post func cenv cx e es sa s0 es' v op) (\r. F)) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rpt gen_tac >> strip_tac >> simp[expr_sim_def] >> rpt strip_tac >>
  qpat_x_assum `!res es'. _ ==> _` (drule_all_then strip_assume_tac) >>
  gvs[] >>
  first_x_assum (drule_all_then (qspec_then `s0` assume_tac)) >>
  irule frag_exec_conseq >>
  first_x_assum (irule_at Any) >> simp[]
QED

(* ===== stmt_state_rel and the variables ===== *)

(* stmt_state_rel reads the variables only through the pointers of the
   live locals. *)
Theorem stmt_state_rel_vars_frame:
  !func cenv cx es s V.
    stmt_state_rel func cenv cx es s /\
    (!name entry p sz.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p (s with vs_vars := V) = lookup_var p s) ==>
    stmt_state_rel func cenv cx es (s with vs_vars := V)
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes (s with vs_vars := V)` by
    (irule local_ptrs_rel_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, state_rel_def] >> conj_tac
     >- metis_tac[] >>
     rpt strip_tac >> gvs[]) >>
  `alloca_inv (s with vs_vars := V)` by
    (irule alloca_inv_fields >> qexists_tac `s` >> fs[stmt_state_rel_def]) >>
  fs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
     immutables_rel_def, logs_rel_def, contract_storage_def,
     contract_transient_def] >>
  metis_tac[]
QED

Theorem stmt_state_rel_vars_ext:
  !func cenv cx es t t'.
    stmt_state_rel func cenv cx es t /\ vars_ext t t' ==>
    stmt_state_rel func cenv cx es t'
Proof
  rw[vars_ext_def] >>
  qpat_x_assum `t' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[lookup_var_def] >> metis_tac[SUBMAP_FLOOKUP_EQN]
QED

Theorem stmt_state_rel_drop_fresh:
  !func cenv cx es st s.
    local_ptrs_reserved cenv st ==>
    (stmt_state_rel func cenv cx es (drop_fresh st s) <=>
     stmt_state_rel func cenv cx es s)
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- (irule stmt_state_rel_vars_ext >> qexists_tac `drop_fresh st s` >>
      simp[vars_ext_drop_fresh]) >>
  simp[drop_fresh_def] >> irule stmt_state_rel_vars_frame >> simp[] >>
  rpt strip_tac >> simp[GSYM drop_fresh_def] >>
  irule lookup_var_drop_fresh >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* ===== Leaves ===== *)

Theorem typed_val_to_w256_word_value:
  !tv v. word_value v ==> typed_val_to_w256 tv v = val_to_w256 v
Proof
  rw[word_value_def] >> Cases_on `tv` >> simp[typed_val_to_w256_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[typed_val_to_w256_def]
QED

(* A word local held through its pointer (loweringSlice's
   compile_name_word_frag). *)
Theorem compile_name_word_sim:
  !ctx func cenv cx ty ann id es p sz entry.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
Proof
  rpt strip_tac >> irule expr_sim_values >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule_all lower_value_name_word >> strip_tac >>
  irule frag_exec_conseq >>
  drule emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`,
                           `val_to_w256 entry.value`, `\r. F`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> strip_tac >>
      drule_all step_name_word >> simp[]) >>
  strip_tac >> first_x_assum (irule_at Any) >> rpt strip_tac >>
  gvs[expr_post_def, expr_val_rel_def, vyperASTTheory.expr_type_def,
      typed_val_to_w256_word_value]
QED

val literal_word_tac =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, evaluate_literal_def] >>
  irule frag_exec_refl >>
  simp[expr_post_def, expr_val_rel_def, vyperASTTheory.expr_type_def,
       eval_operand_def, typed_val_to_w256_word_value, word_value_def] >>
  simp[val_to_w256_def];

(* A bool, integer or decimal literal annotated with a word type: a Lit,
   no code. *)
Theorem compile_literal_word_sim:
  !ctx func cenv cx ty ann l es.
    is_word_type ann /\
    ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i)) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  rw[expr_sim_def] >> gvs[Once evaluate_def, return_def]
  >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_tac) >>
  literal_word_tac
QED

Theorem eval_expr_env:
  !cx ann item es res es'.
    eval_expr cx (Builtin ann (Env item) []) es = (res, es') /\
    expr_res_ok res /\ item <> PrevHash ==>
    es' = es /\
    ?v. res = INL (Value v) /\
        evaluate_builtin cx es.accounts ann (Env item) [] = INL v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def] >>
  simp[Once evaluate_def, return_def] >>
  Cases_on `item` >> fs[evaluate_builtin_def, return_def, raise_def] >>
  rw[] >> gvs[expr_res_ok_def]
QED

Theorem lower_value_env:
  !cenv ty ann item sa op sb.
    lower_value compile_expr cenv ty (Builtin ann (Env item) []) sa =
      (op, sb) ==>
    compile_env_var item sa = (op, sb)
Proof
  rpt gen_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def] >>
  Cases_on `compile_env_var item sa` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

(* An environment read (msg.sender, block.timestamp, ...) annotated with
   its type, but block.prevhash, for which expr_sim does not hold (see the
   header).  msg.gas holds vacuously: the source raises a TypeError for
   it. *)
Theorem compile_env_sim:
  !ctx func cenv cx ty ann item es.
    item <> PrevHash /\ ann = env_item_type item ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Env item) []) es
Proof
  rpt strip_tac >> irule expr_sim_values >>
  conj_tac >~ [`expr_res_ok _`]
  >- (rpt strip_tac >> drule_all eval_expr_env >> strip_tac >> simp[]) >>
  rpt strip_tac >>
  `expr_res_ok (INL (Value v) : toplevel_value + exception)` by
    simp[expr_res_ok_def] >>
  drule_all eval_expr_env >> strip_tac >> gvs[] >>
  `is_word_type (env_item_type item) /\
   !tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv ==>
        typed_val_to_w256 tv v = val_to_w256 v` by
    (Cases_on `item` >>
     gvs[evaluate_builtin_def, env_item_type_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
         val_to_w256_def] >>
     simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []) >>
  drule lower_value_env >> strip_tac >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                `\s. stmt_state_rel func cenv cx es s /\
                     eval_operand op s = SOME (val_to_w256 v) /\
                     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                            lookup_var x s = SOME w) /\
                     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                              FLOOKUP s.vs_allocas aid = SOME b) /\
                     s.vs_memory = s0.vs_memory`,
                `\r. F`] >>
  simp[expr_post_def, expr_val_rel_def, vyperASTTheory.expr_type_def] >>
  Cases_on `item` >>
  gvs[compile_env_var_def, evaluate_builtin_def] >>
  drule emit_op_frag >> disch_then irule >>
  simp[is_terminator_def] >> rpt strip_tac >>
  simp[step_inst_base_opcode_eqs, exec_read0_def, venomInstTheory.mk_inst_def] >>
  fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
     val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def]
QED
