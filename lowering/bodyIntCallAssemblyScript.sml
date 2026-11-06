Theory bodyIntCallAssembly
Ancestors
  bodyIntCallCompletedSource bodySim supportedNames supportedProgram
  compileEnv memoryLocalRhsProps compileVyper exprSimDefs exprSimHypsDefs exprLoweringProps loweringPosts
  bodyIntCallReturnBoundaryChecks vyperInterpreter vyperState
Libs
  monadsyntax

Theorem invoke_cleanup_exit_summary:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_marked_exec F (ctx,callee) f (es,entered) marks res ee r /\
  expr_exit res r ==>
  gas_summary_at F (ctx,func) marks
    (do rv <- finally f (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od)
    (es,t) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >> Cases_on `res` >- fs[expr_exit_def] >>
  Cases_on `r` >> fs[expr_exit_def] >>
  irule (SRULE [unlock_if_nr_def] invoke_cleanup_abort_summary) >> goal_assum (drule_at Any) >> simp[] >>
  Cases_on `y` >> fs[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> fs[expr_exit_def]
QED

Theorem body_internal_decl_return_type:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops ==>
  cenv.ce_func_return_type (nsid_to_string (NONE,name)) = ret
Proof
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (fs[body_inv_def] >> drule supported_program_names >>
     simp[supported_declaration_names_def]) >>
  `build_func_return_type tops name = ret` by
    (irule build_func_return_type_distinct >> simp[] >>
     qexistsl_tac [`args`,`[]`,`mut`,`F`,`rr`,`ss`,`Internal`] >> simp[]) >>
  fs[body_inv_def, nsid_to_string_def]
QED

Theorem expr_inv_local_regions_transport:
  expr_sim_inv ce cx env esA /\ expr_sim_inv ce cx env esB /\
  local_ptrs_reserved ce sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x sA = SOME w ==>
    lookup_var x sB = SOME w) ==>
  !n b sz. local_region ce esA.scopes sA n b sz ==>
    local_region ce esB.scopes sB n b sz
Proof
  strip_tac >>
  mp_tac (local_region_env_transport |> SPEC_ALL
    |> Q.INST [`env` |-> `env`, `cx` |-> `cx`, `cenv` |-> `ce`,
               `esA` |-> `esA`, `esB` |-> `esB`, `sa` |-> `sa`,
               `sA` |-> `sA`, `sB` |-> `sB`]) >>
  impl_tac >- fs[expr_sim_inv_def] >> simp[]
QED
