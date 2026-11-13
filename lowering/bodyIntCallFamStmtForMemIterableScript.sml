(* Internal-call For producer over a general array-typed expression: an
   iterator that is neither a local nor a top-level name. *)
Theory bodyIntCallFamStmtForMemIterable
Ancestors
  bodyIntCallJointContract vyperAST

(* HELD (train 18): intcall analogue of trunk's admitted
   body_for_memory_iterable (whitelist/whitelistForIterScript.sml), which is
   itself a cheat on trunk; this hold goes when that case is proved. *)
Theorem intcall_stmts_producer_for_memory_iterable:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  intcall_stmts_producer fp stmts /\
  (!ty name. arr <> Name ty name) /\ (!ty nid. arr <> TopLevelName ty nid) ==>
  intcall_stmts_producer fp [For id fty (Array arr) bound stmts]
Proof
  cheat
QED
