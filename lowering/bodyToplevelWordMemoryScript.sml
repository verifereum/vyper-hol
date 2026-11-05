(* Bounded forced word consumers; aggregate and constructor immutables remain residual. *)
Theory bodyToplevelWordMemory
Ancestors
  exprSimSource
  bodyToplevelMemory bodyUnwrapMemory bodyMemoryDefs exprSimUnwrap exprSimDefs
  exprLowering exprLoweringProps compileEnv context fragExecMem fragExec
  vyperAST vyperValue vyperInterpreter vyperState loweringSlice exprSimLeaves
  exprSimHyps accountsRelProps vyperTypeGlobalLookupSoundness vyperTypeSystem
  bodyMemoryPreds vyperTypeCallGraph

Theorem body_unwrap_location_word_mem:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
   (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor)) /\ is_word_type t /\
  read_result cx raw es' = (INL v,es') /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sb
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' raw (LocatedValue t p) s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  cheat
QED

Theorem body_location_word_sim_mem:
  expr_vv_sim_mem ctx func cenv cx ty e es /\
  (storage_vars_rel cenv cx /\ transient_vars_rel cenv cx ==>
    !sa. ?p. compile_expr cenv ty e sa = (LocatedValue (expr_type e) p,sa) /\
      (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
       (p.ptr_location = LocCode /\ ~cenv.ce_is_ctor))) /\
  is_word_type (expr_type e) ==>
  expr_sim_mem ctx func cenv cx ty e es
Proof
  cheat
QED

Theorem compile_toplevel_storage_word_sim_mem:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str.
    expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
    is_word_type ann /\ get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) ==>
    expr_sim_mem ctx func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  cheat
QED

Theorem compile_toplevel_word_runtime_sim_mem:
  !ctx func cenv cx env ty ann nsid es.
    expr_sim_pre cenv cx env (TopLevelName ann nsid) es /\
    is_word_type ann /\ ~cenv.ce_is_ctor ==>
    expr_sim_mem ctx func cenv cx ty (TopLevelName ann nsid) es
Proof
  cheat
QED

Theorem body_toplevel_storage_word_mem_case:
  !cx ann src id ts tr typ id_str.
    is_word_type ann /\ get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) ==>
    body_expr_mem_ok cx (TopLevelName ann (src,id))
Proof
  cheat
QED

Theorem body_toplevel_word_mem_case:
  !cx ann nsid.
    is_word_type ann ==> body_expr_mem_ok cx (TopLevelName ann nsid)
Proof
  cheat
QED

