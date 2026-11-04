(* Callee entry invariants for the internal-call body simulation. *)
Theory bodyIntCallEntry
Ancestors
  bodySim bodySimEntry intCallCallee vyperInterpreter vyperContext vyperState list compileVyper bodyIntCallEntryEnv

Theorem body_inv_push_stack:
  body_inv tops ctx cenv cx ==>
  body_inv tops ctx cenv (cx with stk updated_by CONS src_fn)
Proof
  simp[body_inv_def, get_module_code_def]
QED

Theorem body_inv_push_function:
  body_inv tops ctx cenv cx /\
  push_function src_fn sc cx st = (INL cxf,st') ==>
  body_inv tops ctx cenv cxf
Proof
  simp[push_function_def, return_def] >> strip_tac >>
  gvs[] >> irule body_inv_push_stack >> simp[]
QED

(* The initial source environment contains exactly parameter locals; the
   runtime allocation check therefore supplies its local-size invariant. *)
Theorem locals_alloc_ok_params:
  EVERY (\(_,ty). type_memory_bytes cenv ty < 2 ** 64) params /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) params) ==>
  locals_alloc_ok cenv env
Proof
  simp[locals_alloc_ok_def, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem body_inv_build_internal_env:
  body_inv tops ctx caller cx ==>
  body_inv tops ctx
    (build_compile_env tops Internal mut name args ret ss use_trans) cx
Proof
  simp[body_inv_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED
