(* Fuel bounds for linked compile environments and packaged internals. *)
Theory linkedFuelPackage
Ancestors
  compileUnit compileUnitPackageShape compileVyper compileEnv loweringShapeProps
  fragFuel fragFuelStmtBase fragFuelStmt fragFuelFunction finite_map list pair

val _ = Parse.hide "body";

Theorem build_compile_env_unit_fuel_ok:
  (!n. cenv_ptrs_below n (build_compile_env_unit mods src vis mut fname args ret ss trans)) /\
  (build_compile_env_unit mods src vis mut fname args ret ss trans).ce_ctor_exit_label = NONE
Proof
  conj_tac
  >- (simp[cenv_ptrs_below_def] >> rpt strip_tac >>
      mp_tac (Q.INST [`body` |-> `ss`, `use_trans` |-> `trans`]
        build_compile_env_unit_static_locations) >>
      strip_tac >> res_tac >> fs[static_loc_def]) >>
  simp[build_compile_env_unit_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem package_internal_fns_unit_fuel:
  EVERY (\(lbl,ce,params,has_buf,nr,key,trans,view,ctor,imm_len,body,ret).
           ?Wv. fuel_okS (\st. T) Wv {} {}
             (compile_internal_function ce params has_buf nr key trans view ctor imm_len body ret))
    (MAP (set_internal_package_target target o
          package_internal_fn_unit mods use_trans keys is_ctor imm_bytes) fns)
Proof
  simp[EVERY_MAP, EVERY_MEM] >> qx_gen_tac `f` >> strip_tac >>
  `(!n. cenv_ptrs_below n
       (FST (SND (set_internal_package_target target
         (package_internal_fn_unit mods use_trans keys is_ctor imm_bytes f))))) /\
    (FST (SND (set_internal_package_target target
         (package_internal_fn_unit mods use_trans keys is_ctor imm_bytes f)))).ce_ctor_exit_label = NONE` by
    (PairCases_on `f` >>
     mp_tac (Q.INST [`src` |-> `f0`, `vis` |-> `Internal`, `mut` |-> `f1`,
                    `fname` |-> `(f4:string)`, `args` |-> `f5`, `ret` |-> `f7`,
                    `ss` |-> `f8`, `trans` |-> `use_trans`]
       (INST_TYPE [alpha |-> ``:string``] build_compile_env_unit_fuel_ok)) >>
     simp[package_internal_fn_unit_def, set_internal_package_target_def,
          update_cenv_nonreentrant_def, cenv_ptrs_below_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `set_internal_package_target target
              (package_internal_fn_unit mods use_trans keys is_ctor imm_bytes f)` >>
  PairCases_on `r` >> gvs[] >>
  qexists_tac `UNIV` >>
  `(\st:compile_state. cenv_ptrs_below st.cs_next_var r0) = (\st. T)` by
    simp[FUN_EQ_THM] >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule fuel_okS_compile_internal_function >> simp[] >>
  rpt strip_tac >> irule (cj 2 fuel_okS_compile_stmt) >> simp[]
QED
