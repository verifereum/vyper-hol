(*
 * Statement simulation: more statements over stmt_frag (#637)
 *
 * Cases of the statement judgment stmt_frag (stmtSim) beyond the ones
 * stmtSim proves.
 *
 * TOP-LEVEL:
 *   compile_annassign_word_stmt_frag — a word-local declaration, for every
 *                                      outcome of its right-hand side
 *   compile_raise_reason_lit_frag    — raise with a string literal reason
 *   compile_assert_reason_lit_frag   — assert with a string literal reason
 *)

Theory stmtSimCases
Ancestors
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice stmtSim
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperValueOperation
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* ===== A word-local declaration ===== *)

Theorem stmt_state_rel_declare_local_entry:
  !func cenv cx es ss id ty st c st1.
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) /\
    stmt_state_rel func cenv cx es ss ==>
    stmt_state_rel func c cx es ss
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  irule stmt_state_rel_cenv_cong >> qexists `cenv` >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >> Cases_on `n = id` >> gvs[])
  >- (rpt strip_tac >> Cases_on `n = id` >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> Cases_on `n = id` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
                         ce_dynarray_capacity := _ |> = cenv` mp_tac >>
  simp[compileEnvTheory.compile_env_component_equality]
QED

Theorem cenv_top_ext_declare_local:
  !cenv id ty st c st1 sc rest.
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals /\
    lookup_scopes id rest = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) ==>
    cenv_top_ext cenv c (sc :: rest)
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  simp[cenv_top_ext_def] >> rpt strip_tac >>
  `n = id` by metis_tac[] >> gvs[]
QED

(* x: T = e for a word type T, for every outcome: the right-hand side's
   errors exit, and on a value the local is declared and stored
   (compile_annassign_word_frag).  The right-hand side's judgment is at the
   environment after the declaration, which binds x to its pointer; x is
   not in scope at es. *)
(* Why it holds.  The relation at the declared environment c comes from
   stmt_state_rel_cenv_cong: declare_local_ptr changes only id, which no
   scope at es holds, and binds it to a pointer, as cenv does if at all.
   The ALLOCA then runs with the relation kept at c (its output is fresh,
   local_ptrs_reserved), and expr_sim at c either exits with expr_exit, an
   Abort that carries back over the ALLOCA, or reaches the MSTORE in
   expr_post.  materialise and new_variable fail only with type errors,
   which stmt_res_ok leaves out.  On success cenv'' = c; cenv_top_ext holds
   since only id changes, a pointer on both sides, and the rest of the
   scopes do not hold it.  The ALLOCA's output is fresh at sa, so the
   lookup_var frame does not speak of it; a second run of the ALLOCA (in a
   loop) keeps its allocation.  compile_annassign_word_frag's post has no
   lookup_var or allocas frame, so the success case re-chains ALLOCA,
   expr_post and MSTORE rather than citing it. *)
Theorem compile_annassign_word_stmt_frag:
  !ctx func cx lctx RetQ cenv ty id vtyp e es res es' etv.
    eval_stmt cx (AnnAssign id vtyp e) es = (res, es') /\
    cenv.ce_alloca_locals /\
    is_word_type vtyp /\ ~has_length_word vtyp /\
    32 <= type_memory_bytes cenv vtyp /\
    type_memory_bytes cenv vtyp < dimword (:256) /\
    (!tyv. evaluate_type (get_tenv cx) vtyp = SOME tyv ==>
           type_memory_size tyv = 32) /\
    lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!tv es1. eval_expr cx e es = (INL tv, es1) ==>
              ?v. tv = Value v /\ word_value v /\
                  typed_val_to_w256 etv v = val_to_w256 v) /\
    (!st0 c st1. declare_local cenv id vtyp st0 = (c, st1) ==>
       expr_sim ctx func c cx (expr_type e) e es /\
       !sa sb op. lower_value compile_expr c (expr_type e) e sa = (op, sb) ==>
                  cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (AnnAssign id vtyp e)) es res es'
Proof
  cheat
QED

(* raise and assert with a string literal as the reason: the literal's
   buffer and the Error(string) encoding of compile_revert_with_reason,
   straight-line code that ends in a REVERT, which every assertion
   allows.  A reason other than a literal is compiled with compile_expr
   and read back with unwrap_value after code of its own; those forms are
   not covered yet. *)
(* Why they hold.  The literal evaluates to StringV str, so the source
   raises AssertException str, which expr_exit takes as Revert_abort.  The
   reason code is one run of instructions in the open block, none a
   terminator before the REVERT: ALLOCAs with a literal size and one
   output, MSTOREs, ADD/AND, MLOAD, MCOPY, all total, each Var operand the
   output of an earlier one; unwrap_value of the literal's memory pointer
   emits nothing.  So it reaches the REVERT from any state.  The assert form
   is compile_assert_frag's shape with this run in place of the one
   aborting instruction of the fail block. *)
Theorem compile_raise_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty ml str es res es'.
    eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es res es'
Proof
  cheat
QED

Theorem compile_assert_reason_lit_frag:
  !ctx func cx lctx RetQ cenv ty e ml str es res es'.
    eval_stmt cx
      (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es res es'
Proof
  cheat
QED
