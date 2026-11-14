(* Uint2Str's actual suffix and ghost updates do not depend on the horizon.
   The constructor fixed region still needs the ghost_inv_at clauses;
   the old lo=0 pointer result does not certify this successful joint prefix. *)
Theory bodyFullBuiltinUint2Str
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV bodyFullAllocaFresh
  bodyFullGhostFrame bodyFullUnwrapRun bodyFullShared
  bodyFullBuiltinUint2StrRun
  exprSimUint2Str bodyMemBiUint2StrBlocks bodyPtrBytestringBuiltinsUintArithmetic
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtrLoop fragGasSeqPtr
  bodyPtrDefs exprSimHypsDefs exprSimSource exprLoweringProps exprLowering
  vyperAST list

val _ = Parse.hide "body";

Theorem uint2str_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
    (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (Uint2Str n) args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Uint2Str n) args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Uint2Str n) args) es
Proof
  rpt gen_tac >> strip_tac
QED
