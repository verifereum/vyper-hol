(* Compiler-side cuts only: the code intervals do not assert reachability. *)
Theory bodyIntCallBufferCutsMods
Ancestors
  exprLowering exprLoweringProps context compileEnv emitHelper
  gasShadow gasShadowState gasShadowCompile gasShadowCompileBase gasShadowCompileContext
  gasShadowCompileConvert gasShadowCompileStmtHelpers gasShadowCompileCallSupport
  fragExec venomInst vyperAST pair list

Theorem buffer_cons_unroll[local]:
  compile_expr ce (expr_type e) e a = (vv,i) /\
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) i = (buf,b) /\
  unwrap_value ce vv b = (opn,u) /\
  (if is_word_type ty then emit_void MSTORE [buf.buf_operand;opn]
   else if (case ty of BaseT (BytesT (Dynamic _)) => T
                       | BaseT (StringT _) => T | _ => F) then
     (do compile_store_bytestring opn buf.buf_operand; return () od)
   else compile_store_memory ce opn buf.buf_operand ty (vv_type vv)) u = (x,w) /\
  compile_stage_intcall_args compile_expr ce es flags tys w = (rest,z) ==>
  compile_stage_intcall_args compile_expr ce (e::es) (F::flags) (ty::tys) a =
    (buf.buf_operand::rest,z)
Proof
  strip_tac >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def] >>
  once_rewrite_tac[comp_ignore_bind_def] >>
  simp[comp_bind_def, comp_return_def]
QED

Theorem buffer_cons_real[local]:
  compile_stage_intcall_args compile_expr ce (e::es) (F::flags) (ty::tys) a = (ops,z) ==>
  ?vv i buf b opn u x w rest.
    compile_expr ce (expr_type e) e a = (vv,i) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) i = (buf,b) /\
    unwrap_value ce vv b = (opn,u) /\
    (if is_word_type ty then emit_void MSTORE [buf.buf_operand;opn]
     else if (case ty of BaseT (BytesT (Dynamic _)) => T
                         | BaseT (StringT _) => T | _ => F) then
       (do compile_store_bytestring opn buf.buf_operand; return () od)
     else compile_store_memory ce opn buf.buf_operand ty (vv_type vv)) u = (x,w) /\
    compile_stage_intcall_args compile_expr ce es flags tys w = (rest,z) /\
    ops = buf.buf_operand::rest
Proof
  strip_tac >>
  Cases_on `compile_expr ce (expr_type e) e a` >>
  rename1 `compile_expr _ _ _ _ = (vv,i)` >>
  Cases_on `compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) i` >>
  rename1 `compile_alloc_buffer _ _ = (buf,b)` >>
  Cases_on `unwrap_value ce vv b` >>
  rename1 `unwrap_value _ _ _ = (opn,u)` >>
  qabbrev_tac `store = if is_word_type ty then emit_void MSTORE [buf.buf_operand;opn]
    else if (case ty of BaseT (BytesT (Dynamic _)) => T
                        | BaseT (StringT _) => T | _ => F) then
      (do compile_store_bytestring opn buf.buf_operand; return () od)
    else compile_store_memory ce opn buf.buf_operand ty (vv_type vv)` >>
  Cases_on `store u` >> rename1 `store u = (x,w)` >>
  Cases_on `compile_stage_intcall_args compile_expr ce es flags tys w` >>
  rename1 `compile_stage_intcall_args _ _ es flags tys w = (rest,z0)` >>
  unabbrev_all_tac >>
  drule_all_then assume_tac buffer_cons_unroll >>
  gvs[]
QED

Theorem buffer_shadow_result[local]:
  gas_shadow_compiles f g /\ gas_shadow_state a sa /\ f a = (v,b) ==>
  ?sb. g sa = (v,sb) /\ gas_shadow_state b sb
Proof
  simp[gas_shadow_compiles_def] >> strip_tac >>
  first_x_assum drule >> Cases_on `g sa` >> simp[]
QED

Theorem buffer_store_shadow[local]:
  store = (if is_word_type ty then emit_void MSTORE [dst;opn]
           else if (case ty of BaseT (BytesT (Dynamic _)) => T
                               | BaseT (StringT _) => T | _ => F) then
             (do compile_store_bytestring opn dst; return () od)
           else compile_store_memory ce opn dst ty sty) ==>
  gas_shadow_compiles store store
Proof
  disch_then SUBST1_TAC >> rpt IF_CASES_TAC >>
  simp[gas_shadow_compiles_ignore_bind, gas_shadow_compiles_store_bytestring,
       gas_shadow_compiles_store_memory, gas_shadow_compiles_return,
       gas_shadow_compiles_emit_void]
QED

Theorem buffer_store_mono[local]:
  (if is_word_type ty then emit_void MSTORE [dst;opn]
   else if (case ty of BaseT (BytesT (Dynamic _)) => T
                       | BaseT (StringT _) => T | _ => F) then
     (do compile_store_bytestring opn dst; return () od)
   else compile_store_memory ce opn dst ty sty) u = (x,w) ==>
  ci_mono u w
Proof
  rpt IF_CASES_TAC >> simp[] >> strip_tac
  >- (qspecl_then [`MSTORE`,`[dst;opn]`,`u`] mp_tac ci_mono_emit_void >> simp[])
  >- (qpat_x_assum `comp_ignore_bind _ _ _ = _` mp_tac >>
      simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      Cases_on `compile_store_bytestring opn dst u` >> simp[] >> strip_tac >>
      gvs[] >> qspecl_then [`opn`,`dst`,`u`] mp_tac ci_mono_compile_store_bytestring >> simp[])
  >> qspecl_then [`ce`,`opn`,`dst`,`ty`,`sty`,`u`] mp_tac ci_mono_compile_store_memory >> simp[]
QED

Theorem buffer_stage_shadow[local]:
  gas_shadow_compiles (compile_stage_intcall_args compile_expr ce es flags tys)
    (compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
       (MAP gas_shadow_expr es) flags tys)
Proof
  irule (SIMP_RULE std_ss []
    (Q.INST [`sh` |-> `T`] gas_shadow_compiles_stage_intcall_args_env)) >>
  simp[gas_shadow_compile_expr_env]
QED

Theorem buffer_cut_edges[local]:
  compile_expr cce ety e a = (vv,i) /\
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) i = (buf,b) /\
  unwrap_value ce vv b = (opn,u) /\
  (if is_word_type ty then emit_void MSTORE [buf.buf_operand;opn]
   else if (case ty of BaseT (BytesT (Dynamic _)) => T
                       | BaseT (StringT _) => T | _ => F) then
     (do compile_store_bytestring opn buf.buf_operand; return () od)
   else compile_store_memory ce opn buf.buf_operand ty (vv_type vv)) u = (x,w) /\
  compile_stage_intcall_args compile_expr cce es flags tys w = (rest,z) ==>
  ci_mono a i /\ ci_mono i b /\ ci_mono b u /\ ci_mono u w /\ ci_mono w z
Proof
  strip_tac >>
  conj_tac
  >- (qspecl_then [`cce`,`ety`,`e`,`a`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
  conj_tac
  >- (qspecl_then [`MAX 32 (type_memory_bytes ce ty)`,`i`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  conj_tac
  >- (qspecl_then [`ce`,`vv`,`b`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  conj_tac >- (drule buffer_store_mono >> simp[]) >>
  `ci_mono w (SND (compile_stage_intcall_args compile_expr cce es flags tys w))` by
    (irule ci_mono_compile_stage_intcall_args >> simp[compile_expr_ci_mono]) >>
  gvs[]
QED

Theorem buffer_code_slices[local]:
  ci_mono a i /\ ci_mono i b /\ ci_mono b u /\ ci_mono u w /\ ci_mono w z /\
  fn_has_code a z f ==>
  fn_has_code a i f /\ fn_has_code i b f /\ fn_has_code b u f /\
  fn_has_code u w f /\ fn_has_code w z f
Proof
  simp[ci_mono_def] >> strip_tac >>
  `cs_extends u z` by metis_tac[cs_extends_trans] >>
  `cs_extends b z` by metis_tac[cs_extends_trans] >>
  `cs_extends i z` by metis_tac[cs_extends_trans] >>
  `fn_has_code a i f /\ fn_has_code i z f` by
    (qspecl_then [`a`,`i`,`z`,`f`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code i b f /\ fn_has_code b z f` by
    (qspecl_then [`i`,`b`,`z`,`f`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code b u f /\ fn_has_code u z f` by
    (qspecl_then [`b`,`u`,`z`,`f`] mp_tac fn_has_code_split >> simp[]) >>
  qspecl_then [`u`,`w`,`z`,`f`] mp_tac fn_has_code_split >> simp[]
QED

Theorem intcall_stage_buffer_cuts_mods:
  compile_stage_intcall_args compile_expr ce (e::es) (F::flags) (ty::tys) a = (ops,z) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr (e::es)) (F::flags) (ty::tys) sa = (sops,sz) /\
  gas_shadow_state a sa /\ fn_has_code a z f /\ fn_has_code sa sz sf ==>
  ?vv i buf b opn u x w rest si sb su sw.
    compile_expr ce (expr_type e) e a = (vv,i) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sa = (vv,si) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) i = (buf,b) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) si = (buf,sb) /\
    unwrap_value ce vv b = (opn,u) /\ unwrap_value ce vv sb = (opn,su) /\
    (let store =
       if is_word_type ty then emit_void MSTORE [buf.buf_operand;opn]
       else if (case ty of BaseT (BytesT (Dynamic _)) => T
                           | BaseT (StringT _) => T | _ => F) then
         (do compile_store_bytestring opn buf.buf_operand; return () od)
       else compile_store_memory ce opn buf.buf_operand ty (vv_type vv) in
     store u = (x,w) /\ store su = (x,sw)) /\
    compile_stage_intcall_args compile_expr ce es flags tys w = (rest,z) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr es) flags tys sw = (rest,sz) /\
    ops = buf.buf_operand::rest /\ sops = buf.buf_operand::rest /\
    gas_shadow_state i si /\ gas_shadow_state b sb /\ gas_shadow_state u su /\
    gas_shadow_state w sw /\ gas_shadow_state z sz /\
    ci_mono a i /\ ci_mono i b /\ ci_mono b u /\ ci_mono u w /\ ci_mono w z /\
    ci_mono sa si /\ ci_mono si sb /\ ci_mono sb su /\ ci_mono su sw /\ ci_mono sw sz /\
    fn_has_code a i f /\ fn_has_code i b f /\ fn_has_code b u f /\
    fn_has_code u w f /\ fn_has_code w z f /\
    fn_has_code sa si sf /\ fn_has_code si sb sf /\ fn_has_code sb su sf /\
    fn_has_code su sw sf /\ fn_has_code sw sz sf
Proof
  strip_tac >>
  qpat_assum `compile_stage_intcall_args _ ce (e::es) _ _ a = _`
    (mp_then Any (qx_choosel_then [`vv`,`i`,`buf`,`b`,`opn`,`u`,`x`,`w`,`rest`]
                    strip_assume_tac) buffer_cons_real) >>
  qabbrev_tac `store = if is_word_type ty then emit_void MSTORE [buf.buf_operand;opn]
    else if (case ty of BaseT (BytesT (Dynamic _)) => T
                        | BaseT (StringT _) => T | _ => F) then
      (do compile_store_bytestring opn buf.buf_operand; return () od)
    else compile_store_memory ce opn buf.buf_operand ty (vv_type vv)` >>
  `?si. compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sa = (vv,si) /\
        gas_shadow_state i si` by
    (irule buffer_shadow_result >> irule_at Any gas_shadow_stmt_compile_expr_env >>
     qexists_tac `a` >> simp[]) >>
  `?sb. compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) si = (buf,sb) /\
        gas_shadow_state b sb` by
    (irule buffer_shadow_result >> irule_at Any gas_shadow_compiles_alloc_buffer >>
     qexists_tac `i` >> simp[]) >>
  `?su. unwrap_value ce vv sb = (opn,su) /\ gas_shadow_state u su` by
    (irule buffer_shadow_result >> irule_at Any gas_shadow_compiles_unwrap_value >>
     qexists_tac `b` >> simp[]) >>
  `gas_shadow_compiles store store` by
    (qpat_assum `Abbrev (store = _)`
       (mp_then Any ACCEPT_TAC buffer_store_shadow o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  `?sw. store su = (x,sw) /\ gas_shadow_state w sw` by
    (irule buffer_shadow_result >>
     qpat_assum `gas_shadow_compiles store store` (irule_at Any) >> qexists_tac `u` >> simp[]) >>
  `?sz0. compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
           (MAP gas_shadow_expr es) flags tys sw = (rest,sz0) /\ gas_shadow_state z sz0` by
    (irule buffer_shadow_result >> irule_at Any buffer_stage_shadow >> qexists_tac `w` >> simp[]) >>
  qpat_x_assum `gas_shadow_compiles store store` kall_tac >>
  unabbrev_all_tac >>
  `compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (gas_shadow_expr e::MAP gas_shadow_expr es) (F::flags) (ty::tys) sa =
      (buf.buf_operand::rest,sz0)` by
    (simp[Once compile_stage_intcall_args_def, comp_bind_def, gas_shadow_expr_type] >>
     once_rewrite_tac[comp_ignore_bind_def] >> simp[comp_bind_def, comp_return_def]) >>
  gvs[] >>
  qpat_assum `compile_expr _ _ e a = _`
    (mp_then (Pat `compile_expr _ _ _ _ = _`) (drule_all_then strip_assume_tac) buffer_cut_edges) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (mp_then (Pat `compile_expr _ _ _ _ = _`) (drule_all_then strip_assume_tac) buffer_cut_edges) >>
  qpat_assum `fn_has_code a z f`
    (mp_then Any (drule_all_then strip_assume_tac) buffer_code_slices) >>
  qpat_assum `fn_has_code sa _ sf`
    (mp_then Any (drule_all_then strip_assume_tac) buffer_code_slices) >>
  simp[]
QED
