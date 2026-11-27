(* Transport allocation bounds from the selected unit certificate. *)
Theory bodySelectedBodyAllocBoundsMods
Ancestors
  compileUnit compileEnv allocLimitsProps bodySim list

Theorem selected_body_alloc_bounds_mods:
  fn_allocs_ok_unit mods (src,(mut,nr,rr,name,args,compiled_dflts,ret,b)) /\
  alloc_env_agree
    (build_compile_env_unit mods src Internal mut name args ret b F) body_ce /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> MEM (id,ty) args) ==>
  locals_alloc_ok body_ce env /\ alloc_limits_stmts body_ce b
Proof
  simp[fn_allocs_ok_unit_def] >> strip_tac >>
  reverse conj_tac
  >- (drule (CONJUNCT2 alloc_limits_stmt_struct_fields) >> simp[]) >>
  simp[locals_alloc_ok_def] >> rpt strip_tac >>
  `MEM (id,ty) args` by metis_tac[] >>
  fs[alloc_env_agree_def, EVERY_MEM] >>
  drule type_memory_bytes_frame >> strip_tac >>
  qpat_x_assum `!a. MEM a args ==> _` (qspec_then `(id,ty)` mp_tac) >> simp[]
QED
