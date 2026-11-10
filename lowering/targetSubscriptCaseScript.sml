(*
 * The target/place judgment for an element of an array or a mapping
 * (target_subscript_case), on its own so it can be proved apart from the
 * other steps (targetPlaceSimCasesBase).
 *)

Theory targetSubscriptCase
Ancestors
  targetSubscriptSplit targetPlaceSimCasesBase targetPlaceLive
  exprSimFieldLayout
  exprSimSource
  targetPlaceSimDefs
  stmtSimProps
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimBuffer exprSimAttributeFields
  freshWrites stmtLoweringMono targetPlaceSim
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeCallGraph vyperTypeEnv vyperTypeInvariants
  vyperTypeExprSoundness vyperPlaceFrames vyperEvalMisc
  venomState venomInst
Libs
  pairLib

(* An element of an array or a mapping, by the target's root and its
   indices (targetSubscriptSplit): a storage root with an effectful index
   and a local root with a pop in an index are residual; the rest is
   target_subscript_main_case.  A target's root is a name, local or
   module. *)
Theorem target_subscript_case:
  !nocalls ctx func cenv cx bt e.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  rpt strip_tac >>
  `(?id. target_root bt = NameTarget id) \/
   (?nsid. target_root bt = TopLevelNameTarget nsid)` by
    (qid_spec_tac `bt` >> recInduct base_assignment_target_induct >>
     simp[target_root_def]) >>
  gvs[]
  >- (Cases_on `supported_target_exists (\x. ?ty t. x = Pop ty t)
                  (SubscriptTarget bt e)`
      >- (irule target_subscript_local_pop_case >> metis_tac[]) >>
      irule target_subscript_main_case >> gvs[] >> metis_tac[]) >>
  Cases_on `EVERY pure_expr (target_indices (SubscriptTarget bt e))`
  >- (irule target_subscript_main_case >> gvs[] >> metis_tac[]) >>
  irule target_subscript_storage_effectful_case >> metis_tac[]
QED
