(*
 * Expression simulation: the leaves (#636, Leaves)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the expressions
 * without subexpressions.  Each concludes expr_sim_ok (exprSimHyps).
 *
 * TOP-LEVEL:
 *   compile_name_sim         — a local: word locals by compile_name_word_sim
 *                              (exprSim), the rest by compile_name_other_sim
 *   compile_literal_sim      — a literal: bool, integer and decimal literals
 *                              of a word type by compile_literal_word_sim
 *                              (exprSim), the rest by
 *                              compile_literal_other_sim
 *   compile_env_case_sim     — an environment read: by compile_env_sim
 *                              (exprSim), block.prevhash by
 *                              compile_prevhash_sim
 *   compile_toplevel_name_sim — storage, transient, immutable and constant
 *                              reads
 *   compile_flag_member_sim  — a flag member
 *
 * Cheated, for the later #636 PRs:
 *   compile_name_other_sim   — locals of other types: address, bytesN and
 *                              memory-backed (#636 Leaves, row 1)
 *   compile_literal_other_sim — address, bytesN, bytes and string literals
 *                              (row 2)
 *   compile_toplevel_name_sim (row 3), compile_flag_member_sim (row 4).
 *                              compile_toplevel_name_sim takes the
 *                              ce_vars entry of a storage or transient
 *                              variable from storage_vars_rel and
 *                              transient_vars_rel; immutables are #563.
 *   compile_prevhash_sim     — block.prevhash (row 5).  Unprovable as the
 *                              definitions stand: the source raises a
 *                              RuntimeError where BLOCKHASH returns 0 (#671),
 *                              and call_ctx_rel does not relate the block
 *                              hashes.
 *
 * msg.gas is not a typed expression (well_typed_builtin_app excludes it),
 * so expr_sim_ok says nothing about it; the source raises a TypeError for
 * it too, while the lowering emits GAS.
 *)

Theory exprSimLeaves
Ancestors
  list finite_map
  exprSim exprSimHyps exprLowering compileEnv loweringSlice
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

(* ===== Locals ===== *)

Theorem compile_name_other_sim:
  !ctx func cenv cx env ty ann id es.
    expr_sim_pre cenv cx env (Name ann id) es /\
    ~(is_word_type ann /\
      ?entry. lookup_scopes id es.scopes = SOME entry /\
              word_value entry.value) ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
Proof
  cheat
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

(* A local's value_vv is a pointer to its region. *)
Theorem compile_name_vv_sim:
  !cenv ann id. expr_vv_ok cenv (Name ann id)
Proof
  cheat
QED

Theorem compile_name_case_sim:
  !cenv ann id. expr_ok cenv (Name ann id)
Proof
  simp[expr_ok_def, compile_name_sim, compile_name_vv_sim]
QED

(* ===== Literals ===== *)

Theorem compile_literal_other_sim:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\
    ~(is_word_type ann /\
      ((?b. l = BoolL b) \/ (?i. l = IntL i) \/ (?i. l = DecimalL i))) ==>
    expr_sim ctx func cenv cx ty (Literal ann l) es
Proof
  cheat
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

(* Bytes and string literals: a word, or a buffer of their own. *)
Theorem compile_literal_other_vv_sim:
  !cenv ann l.
    ((?bs. l = BytesL bs) \/ (?str. l = StringL str)) ==>
    expr_vv_ok cenv (Literal ann l)
Proof
  cheat
QED

Theorem compile_literal_case_sim:
  !cenv ann l. expr_ok cenv (Literal ann l)
Proof
  rpt gen_tac >>
  Cases_on `(?bs. l = BytesL bs) \/ (?str. l = StringL str)`
  >- (irule expr_ok_of_vv >> irule compile_literal_other_vv_sim >> simp[]) >>
  irule expr_ok_stack >> simp[compile_literal_sim] >> rpt conj_tac
  >~ [`eval_expr`]
  >- (rpt strip_tac >> drule eval_expr_literal_value >> simp[]) >>
  Cases_on `l` >> gvs[] >>
  TRY (rename1 `BoolL b` >> Cases_on `b`) >>
  simp[compile_expr_def, compile_literal_vv_def, comp_return_def]
QED

(* ===== Environment reads ===== *)

Theorem compile_prevhash_sim:
  !cenv ann args. expr_sim_ok cenv (Builtin ann (Env PrevHash) args)
Proof
  cheat
QED

Theorem compile_env_case_sim:
  !cenv ann item args. expr_sim_ok cenv (Builtin ann (Env item) args)
Proof
  rpt gen_tac >> Cases_on `item = PrevHash`
  >- simp[compile_prevhash_sim] >>
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
  Cases_on `args` >> simp[] >> Cases_on `h` >> simp expr_sizes >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp expr_sizes) >>
  rpt (qpat_x_assum `~(_ < _)` mp_tac) >> Cases_on `o'` >> simp expr_sizes
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

Theorem compile_toplevel_name_sim:
  !cenv ann nsid. expr_vv_ok cenv (TopLevelName ann nsid)
Proof
  cheat
QED

Theorem compile_flag_member_sim:
  !cenv ann nsid mid. expr_vv_ok cenv (FlagMember ann nsid mid)
Proof
  cheat
QED
