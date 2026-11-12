(* Authorized residual: counted twin of S1's
   exprSimPopNestedStorageEffectful.pop_nested_storage_effectful_dead_case.
   Takes the base-target memory predicate and body_inv instead of a target
   simulation, which the effectful storage case cannot supply. *)
Theory popNestedStorageEffectfulMemory
Ancestors
  exprSimPopNestedStorageFrame exprSimMemDefs targetPlaceSimMem
  exprSimPopNestedBase exprSimHypsDefs gasOutcome gasContext loweringPosts
  exprLowering compileEnv vyperInterpreter vyperState venomState
  bodyMemoryPreds bodySim

Theorem pop_nested_storage_effectful_dead_case_mem:
  !ctx func cenv cx env ann bt ty es src id ts d.
    body_base_target_mem_ok cx bt /\ body_inv (cx_tops cx) ctx cenv cx /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) /\
    ~EVERY (storage_frame_expr cx) (target_indices bt) ==>
    expr_vv_sim_mem ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED
