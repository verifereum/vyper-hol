Theory s1PrefixIntCallStageConsCut
Ancestors
  s1PrefixIntCallStageSingleton list

Theorem intcall_stage_cons_cut_elim:
  LENGTH flags = LENGTH (e::es) /\ LENGTH dtys = LENGTH (e::es) /\
  compile_stage_intcall_args compile_expr cenv (e::es) flags dtys si = (newops,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T cenv)
    (MAP gas_shadow_expr (e::es)) flags dtys shadow_si = (newops,shadow_sf) /\
  gas_shadow_state si shadow_si /\ fn_has_code si sf func /\
  fn_has_code shadow_si shadow_sf shadow_func ==>
  !K:bool.
    (!flag fs dty ts h sm shadow_sm rest.
      flags = flag::fs /\ dtys = dty::ts /\ newops = h::rest /\
      compile_stage_intcall_args compile_expr cenv [e] [flag] [dty] si = ([h],sm) /\
      compile_stage_intcall_args compile_expr (gas_shadow_env T cenv)
        [gas_shadow_expr e] [flag] [dty] shadow_si = ([h],shadow_sm) /\
      compile_stage_intcall_args compile_expr cenv es fs ts sm = (rest,sf) /\
      compile_stage_intcall_args compile_expr (gas_shadow_env T cenv)
        (MAP gas_shadow_expr es) fs ts shadow_sm = (rest,shadow_sf) /\
      gas_shadow_state sm shadow_sm /\ fn_has_code si sm func /\
      fn_has_code sm sf func /\ fn_has_code shadow_si shadow_sm shadow_func /\
      fn_has_code shadow_sm shadow_sf shadow_func ==> K) ==> K
Proof
  strip_tac >> gen_tac >> strip_tac >>
  namedCases_on `flags` ["", "flag fs"] >- fs[] >>
  namedCases_on `dtys` ["", "dty ts"] >- fs[] >>
  drule_all intcall_stage_cons_singleton_cut >> strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[]
QED
