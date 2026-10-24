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
 *   compile_literal_other_sim — bytesN, bytes and string literals (row 2)
 *   compile_toplevel_name_sim (row 3), compile_flag_member_sim (row 4)
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

(* ===== Top-level names and flag members ===== *)

Theorem compile_toplevel_name_sim:
  !cenv ann nsid. expr_sim_ok cenv (TopLevelName ann nsid)
Proof
  cheat
QED

Theorem compile_flag_member_sim:
  !cenv ann nsid mid. expr_sim_ok cenv (FlagMember ann nsid mid)
Proof
  cheat
QED
