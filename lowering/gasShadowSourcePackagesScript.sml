Theory gasShadowSourcePackages
Ancestors
  gasShadowSourceMetadata gasShadowModuleDefs compileVyper gasShadow

Theorem gas_shadow_classify_fold:
  !tops exts ints fb ctor.
    FOLDR classify_function
      (MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) exts,
       MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) ints,
       OPTION_MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fb,
       OPTION_MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) ctor)
      (MAP gas_shadow_toplevel tops) =
    (\(es,is,fb,ct).
      (MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) es,
       MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) is,
       OPTION_MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fb,
       OPTION_MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) ct))
      (FOLDR classify_function (exts,ints,fb,ctor) tops)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FOLDR classify_function (exts,ints,fb,ctor) tops` >>
  PairCases_on `r` >>
  Cases_on `h` >> simp[gas_shadow_toplevel_def, classify_function_def] >>
  Cases_on `f` >> simp[classify_function_def] >> IF_CASES_TAC >> simp[]
QED

Theorem gas_shadow_classify_functions:
  !tops. classify_functions (MAP gas_shadow_toplevel tops) =
    (\(es,is,fb,ct).
      (MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) es,
       MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) is,
       OPTION_MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fb,
       OPTION_MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) ct))
      (classify_functions tops)
Proof
  gen_tac >>
  qspecl_then [`tops`,`[]`,`[]`,`NONE`,`NONE`] mp_tac gas_shadow_classify_fold >>
  simp[classify_functions_def]
QED

Theorem gas_shadow_package_external_fn:
  !tops tr keys m n r f a d t b.
  package_external_fn (MAP gas_shadow_toplevel tops) tr keys
    (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b) =
  gas_shadow_external_package (package_external_fn tops tr keys (m,n,r,f,a,d,t,b))
Proof
  simp[package_external_fn_def, gas_shadow_external_package_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem gas_shadow_package_internal_fn:
  !tops tr keys ctor imm m n r f a d t b.
  package_internal_fn (MAP gas_shadow_toplevel tops) tr keys ctor imm
    (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b) =
  gas_shadow_internal_package (package_internal_fn tops tr keys ctor imm (m,n,r,f,a,d,t,b))
Proof
  simp[package_internal_fn_def, gas_shadow_internal_package_def]
QED

Theorem gas_shadow_package_fallback_fn:
  !tops tr keys fb.
  package_fallback_fn (MAP gas_shadow_toplevel tops) tr keys
    (OPTION_MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fb) =
  OPTION_MAP gas_shadow_fallback_package (package_fallback_fn tops tr keys fb)
Proof
  rpt gen_tac >> Cases_on `fb` >> simp[package_fallback_fn_def] >>
  PairCases_on `x` >> simp[package_fallback_fn_def, gas_shadow_fallback_package_def]
QED

Theorem gas_shadow_set_external_package_target:
  !target p.
    set_external_package_target target (gas_shadow_external_package p) =
    gas_shadow_external_package (set_external_package_target target p)
Proof
  rpt gen_tac >> PairCases_on `p` >>
  simp[set_external_package_target_def, gas_shadow_external_package_def]
QED

Theorem gas_shadow_set_internal_package_target:
  !target p.
    set_internal_package_target target (gas_shadow_internal_package p) =
    gas_shadow_internal_package (set_internal_package_target target p)
Proof
  rpt gen_tac >> PairCases_on `p` >>
  simp[set_internal_package_target_def, gas_shadow_internal_package_def]
QED

Theorem gas_shadow_set_fallback_package_target:
  !target p.
    set_fallback_package_target target (OPTION_MAP gas_shadow_fallback_package p) =
    OPTION_MAP gas_shadow_fallback_package (set_fallback_package_target target p)
Proof
  rpt gen_tac >> Cases_on `p` >> simp[set_fallback_package_target_def] >>
  PairCases_on `x` >>
  simp[set_fallback_package_target_def, gas_shadow_fallback_package_def]
QED

Theorem gas_shadow_package_constructor:
  !tops trans keys mut nr rr name args defaults ret body.
  package_constructor (MAP gas_shadow_toplevel tops) trans keys
    (mut,nr,rr,name,args,MAP gas_shadow_expr defaults,ret,MAP gas_shadow_stmt body) =
  (let (ce,args,pay,nr,key,tr,body,ret) =
     package_constructor tops trans keys (mut,nr,rr,name,args,defaults,ret,body) in
   (gas_shadow_cenv ce,args,pay,nr,key,tr,MAP gas_shadow_stmt body,ret))
Proof
  simp[package_constructor_def]
QED

Theorem gas_shadow_set_constructor_package_target:
  !ce args pay nr key tr body ret target.
  set_constructor_package_target target
    (gas_shadow_cenv ce,args,pay,nr,key,tr,MAP gas_shadow_stmt body,ret) =
  (let (ce',args',pay',nr',key',tr',body',ret') =
     set_constructor_package_target target (ce,args,pay,nr,key,tr,body,ret) in
   (gas_shadow_cenv ce',args',pay',nr',key',tr',MAP gas_shadow_stmt body',ret'))
Proof
  simp[set_constructor_package_target_def]
QED

Theorem gas_shadow_build_selectors:
  !fs tenv.
    build_selectors tenv
      (MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fs) =
    build_selectors tenv fs
Proof
  Induct >> simp[build_selectors_def] >> rpt gen_tac >> PairCases_on `h` >>
  simp[build_selectors_def]
QED

Theorem gas_shadow_build_dense_entry_info:
  !exts sels.
    build_dense_entry_info sels (MAP gas_shadow_external_package exts) =
    build_dense_entry_info sels exts
Proof
  Induct >> Cases_on `sels` >> simp[build_dense_entry_info_def] >>
  rpt gen_tac >> PairCases_on `h` >> PairCases_on `h'` >>
  simp[gas_shadow_external_package_def, build_dense_entry_info_def]
QED

Theorem gas_shadow_map_package_external_fn:
  !fs tops tr keys target.
    MAP (set_external_package_target target o
         package_external_fn (MAP gas_shadow_toplevel tops) tr keys)
      (MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fs) =
    MAP gas_shadow_external_package
      (MAP (set_external_package_target target o package_external_fn tops tr keys) fs)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[gas_shadow_package_external_fn, gas_shadow_set_external_package_target]
QED

Theorem gas_shadow_map_package_internal_fn:
  !fs tops tr keys ctor imm target.
    MAP (set_internal_package_target target o
         package_internal_fn (MAP gas_shadow_toplevel tops) tr keys ctor imm)
      (MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fs) =
    MAP gas_shadow_internal_package
      (MAP (set_internal_package_target target o package_internal_fn tops tr keys ctor imm) fs)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[gas_shadow_package_internal_fn, gas_shadow_set_internal_package_target]
QED
