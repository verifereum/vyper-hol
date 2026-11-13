(*
 * Dynamic-array append over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAppend
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

val _ = Parse.hide "body";

(* The top-level storage/transient dynamic array. *)
Theorem body_append_storage_full:
  !cx nid e.
    (!s'' p t'.
       eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  cheat
QED

(* A local memory dynamic array named directly (gate SEQ-4806). *)
Theorem body_append_local_full:
  !cx id e.
    (!s'' p t'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (NameTarget id) e)
Proof
  cheat
QED

(* A dynamic array reached through subscripts/attributes, rooted at a local
   (memory) or at a storage/transient/hashmap variable (gate SEQ-4806). *)
Theorem body_append_nested_full:
  !cx t e.
    (!id. t <> NameTarget id) /\ (!nid. t <> TopLevelNameTarget nid) /\
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t ==>
    body_stmt_full_ok cx (Append t e)
Proof
  cheat
QED
