(* Constructor-local boundaries for supported expression compilation. *)
Theory bodyIntCallExprBodyLabels
Ancestors
  bodyIntCallExprClosure bodyIntCallExprLabels bodyIntCallBuiltinLabels
  bodyIntCallContextLabels bodyIntCallLabelFrame bodyIntCallLabelReservations
  exprLowering compileEnv pred_set

Theorem compiler_block_tail_ifexp_body:
  (!ce t. compiler_block_tail (cfn ce t cond_e)) /\
  (!ce t. compiler_block_tail (cfn ce t then_e)) /\
  (!ce t. compiler_block_tail (cfn ce t else_e)) ==>
  compiler_block_tail
    (compile_expr_body cfn bfn tfn cenv ty (IfExp ann cond_e then_e else_e))
Proof
  strip_tac >> rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
       >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
           simp[compiler_block_tail_primitives, compiler_block_tail_lower_value]) >>
       gen_tac >> BETA_TAC) >>
  Cases_on `is_word_type (expr_type (IfExp ann cond_e then_e else_e))` >> simp[compiler_block_tail_def]
QED

Theorem compiler_label_hoare_ifexp_body:
  (!origin pending ce t.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t cond_e) (\r out. compiler_label_reservation origin pending out)) /\
  (!origin pending ce t.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t then_e) (\r out. compiler_label_reservation origin pending out)) /\
  (!origin pending ce t.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t else_e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_expr_body cfn bfn tfn cenv ty (IfExp ann cond_e then_e else_e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  ntac 2 (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
    >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
        simp[compiler_label_hoare_lower_value, compiler_label_hoare_context_primitives]) >>
    gen_tac >> BETA_TAC) >>
  ntac 3 (CONV_TAC (RATOR_CONV (RAND_CONV (HO_REWR_CONV compiler_pair_bind_eq))) >>
          CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
          irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC) >>
  gvs[] >>
  ntac 3
    (rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
      >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
          simp[compiler_label_hoare_context_primitives, compiler_label_hoare_lower_value]) >>
      gen_tac >> BETA_TAC) >>
     CONV_TAC (RATOR_CONV (RAND_CONV (HO_REWR_CONV compiler_pair_bind_eq))) >>
     CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
     ho_match_mp_tac compiler_label_hoare_new_block_bind >> conj_tac
     >- simp[] >> gen_tac >> BETA_TAC >> simp[]) >>
  Cases_on `is_word_type (expr_type (IfExp ann cond_e then_e else_e))` >>
  simp[compiler_label_hoare_def, DELETE_INSERT, DELETE_NON_ELEMENT_RWT]
QED

Theorem compiler_block_tail_attribute:
  compiler_block_tail (cfn cenv ty e) ==>
  compiler_block_tail (compile_attribute cfn cenv ann ty e fld)
Proof
  strip_tac >> simp[compile_attribute_def] >>
  ho_match_mp_tac compiler_block_tail_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_attribute:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn cenv ty e) (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_attribute cfn cenv ann ty e fld)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[compile_attribute_def] >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_mapping_helpers:
  compiler_block_tail (compile_mapping_subscript base_op key) /\
  compiler_block_tail (compile_keccak256_key key is32) /\
  compiler_block_tail (compile_tuple_subscript base_op off)
Proof
  Cases_on `is32` >>
  simp[compile_mapping_subscript_def, compile_keccak256_key_def,
       compile_tuple_subscript_def, comp_ignore_bind_def, compiler_block_tail_primitives] >>
  rpt conj_tac >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer] >>
       gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_mapping_helpers:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_mapping_subscript base_op key)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_keccak256_key key is32)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_tuple_subscript base_op off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `is32` >>
  simp[compile_mapping_subscript_def, compile_keccak256_key_def,
       compile_tuple_subscript_def, comp_ignore_bind_def,
       compiler_label_hoare_context_primitives] >>
  rpt conj_tac >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_storage_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_array_subscript:
  (!p. compiler_block_tail (loader p)) ==>
  compiler_block_tail
    (compile_array_subscript base_op idx dyn nitems scale sz signed loader)
Proof
  strip_tac >> simp[compile_array_subscript_def, comp_ignore_bind_def] >>
  Cases_on `dyn` >> Cases_on `signed` >> simp[] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_array_subscript:
  (!p. compiler_label_hoare (compiler_label_reservation origin pending)
    (loader p) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_array_subscript base_op idx dyn nitems scale sz signed loader)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[compile_array_subscript_def, comp_ignore_bind_def] >>
  Cases_on `dyn` >> Cases_on `signed` >> simp[] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_subscript:
  (!ce t. compiler_block_tail (cfn ce t be)) /\
  (!ce t. compiler_block_tail (cfn ce t ie)) ==>
  compiler_block_tail (compile_subscript cfn cenv ann ty be ie)
Proof
  strip_tac >> simp[compile_subscript_def] >>
  ho_match_mp_tac compiler_block_tail_bind >> conj_tac >- simp[] >>
  gen_tac >> Cases_on `place_type cenv be`
  >- (simp[] >>
      rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
        >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
            simp[compiler_block_tail_lower_value, compiler_block_tail_mapping_helpers,
                 compiler_block_tail_cond, compiler_block_tail_primitives]) >>
        gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]) >>
  rename1 `place_type cenv be = ValPT bt` >> Cases_on `bt` >> simp[] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
    >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
        simp[compiler_block_tail_lower_value, compiler_block_tail_mapping_helpers,
             compiler_block_tail_array_subscript, compiler_block_tail_primitives]) >>
    gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_subscript:
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t be) (\r out. compiler_label_reservation origin pending out)) /\
  (!ce t. compiler_label_hoare (compiler_label_reservation origin pending)
    (cfn ce t ie) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_subscript cfn cenv ann ty be ie)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[compile_subscript_def] >>
  ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac >- simp[] >>
  gen_tac >> Cases_on `place_type cenv be`
  >- (rename1 `place_type cenv be = MapPT kt vt` >>
      Cases_on `is_bytestring_type kt` >> simp[] >>
      rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
        >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
            simp[compiler_label_hoare_lower_value, compiler_label_hoare_mapping_helpers,
                 compiler_label_hoare_typed_primitives]) >>
        gen_tac >> BETA_TAC) >> simp[compiler_label_hoare_typed_primitives]) >>
  rename1 `place_type cenv be = ValPT bt` >> Cases_on `bt` >> simp[] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
    >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
        simp[compiler_label_hoare_lower_value, compiler_label_hoare_mapping_helpers,
             compiler_label_hoare_array_subscript, compiler_label_hoare_context_primitives,
             compiler_label_hoare_typed_primitives]) >>
    gen_tac >> BETA_TAC) >> simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_modular_names:
  compiler_block_tail (compile_addmod_names ce rt aty a bty b mty m) /\
  compiler_block_tail (compile_mulmod_names ce rt aty a bty b mty m) /\
  compiler_block_tail (compile_powmod256_names ce rt aty a bty b)
Proof
  rewrite_tac[lambdify compile_addmod_names_def,
    lambdify compile_mulmod_names_def, lambdify compile_powmod256_names_def] >>
  simp[] >> rpt conj_tac >>
  rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
    >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
        simp[compiler_block_tail_name_vv, compiler_block_tail_unwrap_value]) >>
    gen_tac >> BETA_TAC) >>
  irule compiler_block_tail_as_stack_val >> simp[compiler_block_tail_modular]
QED

Theorem compiler_label_hoare_modular_names:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_addmod_names ce rt aty a bty b mty m)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_mulmod_names ce rt aty a bty b mty m)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_powmod256_names ce rt aty a bty b)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[lambdify compile_addmod_names_def,
    lambdify compile_mulmod_names_def, lambdify compile_powmod256_names_def] >>
  simp[] >> rpt conj_tac >>
  rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
    >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
        simp[compiler_label_hoare_name_vv, compiler_label_hoare_unwrap_value]) >>
    gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_as_stack_val >> simp[compiler_label_hoare_modular]
QED

Theorem compiler_block_tail_dynarray_pop:
  compiler_block_tail (compile_dynarray_pop base_op ws sz load_opc store_opc)
Proof
  simp[compile_dynarray_pop_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_block_tail_bind >> conj_tac
    >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_dynarray_pop:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_dynarray_pop base_op ws sz load_opc store_opc)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_dynarray_pop_def, comp_ignore_bind_def] >>
  rpt (ho_match_mp_tac compiler_label_hoare_preserving_bind >> conj_tac
    >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
    gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_pop_body:
  compiler_block_tail (compile_expr_body cfn bfn tfn ce ty (Pop ann target))
Proof
  rewrite_tac[lambdify compile_expr_body_def] >>
  Cases_on `target` >> simp[] >>
  (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
   >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_dynarray_pop]) >>
   gen_tac >> BETA_TAC >> simp[compiler_block_tail_def])
QED

Theorem compiler_label_hoare_pop_body:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_expr_body cfn bfn tfn ce ty (Pop ann target))
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[lambdify compile_expr_body_def] >>
  Cases_on `target` >> simp[] >>
  (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
   >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
       simp[compiler_label_hoare_dynarray_pop]) >>
   gen_tac >> BETA_TAC >> simp[compiler_label_hoare_def])
QED


Theorem compile_call_send_action[local]:
  compile_call cfn cenv ret_ty ty (Send has_gas) args default_ret =
    (\st. case args of
       (addr_e :: val_e :: gas_es) =>
         if LENGTH gas_es = (if has_gas then 1 else 0) then
           let (addr_op, st1) = lower_value cfn cenv (BaseT AddressT) addr_e st in
           let (val_op, st2) = lower_value cfn cenv (BaseT (UintT 256)) val_e st1 in
           let (gas_op, st2') =
             (case gas_es of
                [gas_e] => lower_value cfn cenv (BaseT (UintT 256)) gas_e st2
              | _ => (Lit 0w, st2)) in
           let (success, st3) = emit_op CALL [gas_op; addr_op; val_op;
                                              Lit 0w; Lit 0w; Lit 0w; Lit 0w] st2' in
           let (_, st4) = emit_void ASSERT [success] st3 in
           (StackValue ret_ty (Lit 0w), st4)
         else let (_, st') = emit_inst INVALID [] [] st in
              (StackValue ret_ty (Lit 0w), st')
     | _ => let (_, st') = emit_inst INVALID [] [] st in
            (StackValue ret_ty (Lit 0w), st'))
Proof
  simp[FUN_EQ_THM, exprLoweringTheory.compile_call_def]
QED

Theorem compiler_block_tail_send:
  (!e ce t. MEM e args ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_call cfn ce rt ty (Send has_gas) args dflt)
Proof
  strip_tac >> rewrite_tac[compile_call_send_action] >>
  namedCases_on `args` ["", "addr rest"] >> simp[]
  >- (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
      >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_primitives]) >>
      gen_tac >> BETA_TAC >> simp[compiler_block_tail_def]) >>
  namedCases_on `rest` ["", "value gas_es"] >> simp[]
  >- (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
      >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_primitives]) >>
      gen_tac >> BETA_TAC >> simp[compiler_block_tail_def]) >>
  Cases_on `LENGTH gas_es = (if has_gas then 1 else 0)` >> simp[]
  >- (rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
       >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
           irule compiler_block_tail_lower_value >> gvs[]) >> gen_tac >> BETA_TAC) >>
      Cases_on `has_gas` >> gvs[listTheory.LENGTH_EQ_1] >>
      rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
        >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
            simp[compiler_block_tail_lower_value, compiler_block_tail_primitives]) >>
        gen_tac >> BETA_TAC) >> simp[compiler_block_tail_def]) >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >> simp[compiler_block_tail_def]
QED

Theorem compiler_label_hoare_send:
  (!e ce t. MEM e args ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_call cfn ce rt ty (Send has_gas) args dflt)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rewrite_tac[compile_call_send_action] >>
  namedCases_on `args` ["", "addr rest"] >> simp[]
  >- (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
      >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
          simp[compiler_label_hoare_context_primitives]) >>
      gen_tac >> BETA_TAC >> simp[compiler_label_hoare_def]) >>
  namedCases_on `rest` ["", "value gas_es"] >> simp[]
  >- (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
      >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
          simp[compiler_label_hoare_context_primitives]) >>
      gen_tac >> BETA_TAC >> simp[compiler_label_hoare_def]) >>
  Cases_on `LENGTH gas_es = (if has_gas then 1 else 0)` >> simp[]
  >- (ntac 2 (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
       >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
           irule compiler_label_hoare_lower_value >> gvs[]) >> gen_tac >> BETA_TAC) >>
      Cases_on `has_gas` >> gvs[listTheory.LENGTH_EQ_1] >>
      rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
        >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
            simp[compiler_label_hoare_lower_value, compiler_label_hoare_context_primitives,
                 compiler_label_hoare_typed_primitives]) >>
        gen_tac >> BETA_TAC) >> simp[compiler_label_hoare_def]) >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      simp[compiler_label_hoare_context_primitives]) >>
  gen_tac >> BETA_TAC >> simp[compiler_label_hoare_def]
QED
