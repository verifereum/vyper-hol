(* Constructor-local boundaries for supported expression compilation. *)
Theory bodyIntCallExprBodyLabels
Ancestors
  bodyIntCallExprClosure bodyIntCallExprLabels bodyIntCallBuiltinLabels
  bodyIntCallExternalLabels
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


Theorem compile_expr_body_builtin_nil[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi []) st =
  bfn ce (expr_type (Builtin ann bi [])) ty bi [] st
Proof
  Cases_on `bi` >> simp[compile_expr_body_def]
QED

Theorem compile_expr_body_builtin_single[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi [a]) st =
  bfn ce (expr_type (Builtin ann bi [a])) ty bi [a] st
Proof
  Cases_on `bi` >> simp[compile_expr_body_def] >> Cases_on `a` >> simp[]
QED

Theorem compile_expr_body_ordinary_builtin_two[local]:
  bi <> AddMod /\ bi <> MulMod /\ bi <> PowMod256 ==>
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi [a;b]) st =
  bfn ce (expr_type (Builtin ann bi [a;b])) ty bi [a;b] st
Proof
  strip_tac >> Cases_on `bi` >> gvs[] >>
  simp[compile_expr_body_def] >> Cases_on `a` >> simp[] >>
  Cases_on `b` >> simp[]
QED

Theorem compile_expr_body_ordinary_builtin_three[local]:
  bi <> AddMod /\ bi <> MulMod /\ bi <> PowMod256 ==>
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi [a;b;c]) st =
  bfn ce (expr_type (Builtin ann bi [a;b;c])) ty bi [a;b;c] st
Proof
  strip_tac >> Cases_on `bi` >> gvs[] >>
  simp[compile_expr_body_def] >> Cases_on `a` >> simp[] >>
  Cases_on `b` >> simp[] >> Cases_on `c` >> simp[]
QED

Theorem compile_expr_body_builtin_long[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi (a::b::c::d::rest)) st =
  bfn ce (expr_type (Builtin ann bi (a::b::c::d::rest))) ty bi (a::b::c::d::rest) st
Proof
  Cases_on `bi` >> simp[compile_expr_body_def] >>
  Cases_on `a` >> simp[] >>
  Cases_on `b` >> simp[] >> Cases_on `c` >> simp[]
QED

Theorem compile_expr_body_ordinary_builtin[local]:
  bi <> AddMod /\ bi <> MulMod /\ bi <> PowMod256 ==>
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi args) =
  bfn ce (expr_type (Builtin ann bi args)) ty bi args
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `args` >- simp[compile_expr_body_builtin_nil] >>
  rename1 `a::rest` >>
  Cases_on `rest` >- simp[compile_expr_body_builtin_single] >>
  rename1 `a::b::rest` >>
  Cases_on `rest` >- simp[compile_expr_body_ordinary_builtin_two] >>
  rename1 `a::b::c::rest` >>
  Cases_on `rest` >- simp[compile_expr_body_ordinary_builtin_three] >>
  simp[compile_expr_body_builtin_long]
QED

Theorem compile_expr_body_mod_two[local]:
  bi = AddMod \/ bi = MulMod ==>
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi [a;b]) st =
  bfn ce (expr_type (Builtin ann bi [a;b])) ty bi [a;b] st
Proof
  strip_tac >> gvs[] >> Cases_on `a` >> simp[compile_expr_body_def] >>
  Cases_on `b` >> simp[]
QED

Theorem compile_expr_body_addmod_three[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann AddMod [a;b;c]) st =
  (case (a,b,c) of
     (Name aty an, Name bty bn, Name cty cn) =>
       compile_addmod_names ce (expr_type (Builtin ann AddMod [a;b;c]))
         aty an bty bn cty cn st
   | _ => bfn ce (expr_type (Builtin ann AddMod [a;b;c])) ty AddMod [a;b;c] st)
Proof
  Cases_on `a` >> simp[compile_expr_body_def] >>
  Cases_on `b` >> simp[] >> Cases_on `c` >> simp[]
QED

Theorem compile_expr_body_mulmod_three[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann MulMod [a;b;c]) st =
  (case (a,b,c) of
     (Name aty an, Name bty bn, Name cty cn) =>
       compile_mulmod_names ce (expr_type (Builtin ann MulMod [a;b;c]))
         aty an bty bn cty cn st
   | _ => bfn ce (expr_type (Builtin ann MulMod [a;b;c])) ty MulMod [a;b;c] st)
Proof
  Cases_on `a` >> simp[compile_expr_body_def] >>
  Cases_on `b` >> simp[] >> Cases_on `c` >> simp[]
QED

Theorem compile_expr_body_powmod_two[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann PowMod256 [a;b]) st =
  (case (a,b) of
     (Name aty an, Name bty bn) =>
       compile_powmod256_names ce (expr_type (Builtin ann PowMod256 [a;b]))
         aty an bty bn st
   | _ => bfn ce (expr_type (Builtin ann PowMod256 [a;b])) ty PowMod256 [a;b] st)
Proof
  Cases_on `a` >> simp[compile_expr_body_def] >> Cases_on `b` >> simp[]
QED

Theorem compile_expr_body_powmod_three[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann PowMod256 [a;b;c]) st =
  bfn ce (expr_type (Builtin ann PowMod256 [a;b;c])) ty PowMod256 [a;b;c] st
Proof
  Cases_on `a` >> simp[compile_expr_body_def] >>
  Cases_on `b` >> simp[] >> Cases_on `c` >> simp[]
QED

Theorem compile_expr_body_addmod_action[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann AddMod args) =
  (case args of
     [Name aty a; Name bty b; Name mty m] =>
       compile_addmod_names ce (expr_type (Builtin ann AddMod args)) aty a bty b mty m
   | _ => bfn ce (expr_type (Builtin ann AddMod args)) ty AddMod args)
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `args` >- simp[compile_expr_body_builtin_nil] >> rename1 `a::rest` >>
  Cases_on `rest` >- (Cases_on `a` >> simp[compile_expr_body_builtin_single]) >>
  rename1 `a::b::rest` >>
  Cases_on `rest` >- (Cases_on `a` >> Cases_on `b` >> simp[compile_expr_body_mod_two]) >>
  rename1 `a::b::c::rest` >> Cases_on `rest` >>
  Cases_on `a` >> simp[compile_expr_body_addmod_three, compile_expr_body_builtin_long] >>
  Cases_on `b` >> simp[] >> Cases_on `c` >> simp[]
QED

Theorem compile_expr_body_mulmod_action[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann MulMod args) =
  (case args of
     [Name aty a; Name bty b; Name mty m] =>
       compile_mulmod_names ce (expr_type (Builtin ann MulMod args)) aty a bty b mty m
   | _ => bfn ce (expr_type (Builtin ann MulMod args)) ty MulMod args)
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `args` >- simp[compile_expr_body_builtin_nil] >> rename1 `a::rest` >>
  Cases_on `rest` >- (Cases_on `a` >> simp[compile_expr_body_builtin_single]) >>
  rename1 `a::b::rest` >>
  Cases_on `rest` >- (Cases_on `a` >> Cases_on `b` >> simp[compile_expr_body_mod_two]) >>
  rename1 `a::b::c::rest` >> Cases_on `rest` >>
  Cases_on `a` >> simp[compile_expr_body_mulmod_three, compile_expr_body_builtin_long] >>
  Cases_on `b` >> simp[] >> Cases_on `c` >> simp[]
QED

Theorem compile_expr_body_powmod_action[local]:
  compile_expr_body cfn bfn tfn ce ty (Builtin ann PowMod256 args) =
  (case args of
     [Name aty a; Name bty b] =>
       compile_powmod256_names ce (expr_type (Builtin ann PowMod256 args)) aty a bty b
   | _ => bfn ce (expr_type (Builtin ann PowMod256 args)) ty PowMod256 args)
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `args` >- simp[compile_expr_body_builtin_nil] >> rename1 `a::rest` >>
  Cases_on `rest` >- (Cases_on `a` >> simp[compile_expr_body_builtin_single]) >>
  rename1 `a::b::rest` >> Cases_on `rest`
  >- (Cases_on `a` >> simp[compile_expr_body_powmod_two] >> Cases_on `b` >> simp[]) >>
  rename1 `a::b::c::rest` >> Cases_on `rest` >>
  Cases_on `a` >> simp[compile_expr_body_powmod_three, compile_expr_body_builtin_long] >>
  Cases_on `b` >> simp[]
QED

Theorem compile_expr_body_builtin_property[local]:
  P (bfn ce (expr_type (Builtin ann bi args)) ty bi args) /\
  (!rt aty a bty b mty m. P (compile_addmod_names ce rt aty a bty b mty m)) /\
  (!rt aty a bty b mty m. P (compile_mulmod_names ce rt aty a bty b mty m)) /\
  (!rt aty a bty b. P (compile_powmod256_names ce rt aty a bty b)) ==>
  P (compile_expr_body cfn bfn tfn ce ty (Builtin ann bi args))
Proof
  strip_tac >>
  Cases_on `bi = AddMod` >>
  Cases_on `bi = MulMod` >>
  Cases_on `bi = PowMod256` >>
  gvs[compile_expr_body_ordinary_builtin] >>
  rewrite_tac[compile_expr_body_addmod_action,
    compile_expr_body_mulmod_action, compile_expr_body_powmod_action] >>
  (Cases_on `args` >- gvs[] >> rename1 `a::rest` >>
   Cases_on `rest` >- (Cases_on `a` >> gvs[]) >> rename1 `a::b::rest` >>
   Cases_on `rest` >- (Cases_on `a` >> gvs[] >> Cases_on `b` >> gvs[]) >>
   rename1 `a::b::c::rest` >> Cases_on `rest` >>
   Cases_on `a` >> gvs[] >> Cases_on `b` >> gvs[] >> Cases_on `c` >> gvs[])
QED

Theorem compiler_block_tail_builtin_body:
  compiler_block_tail (bfn ce (expr_type (Builtin ann bi args)) ty bi args) ==>
  compiler_block_tail (compile_expr_body cfn bfn tfn ce ty (Builtin ann bi args))
Proof
  strip_tac >> irule compile_expr_body_builtin_property >>
  simp[compiler_block_tail_modular_names]
QED

Theorem compiler_label_hoare_builtin_body:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (bfn ce (expr_type (Builtin ann bi args)) ty bi args)
    (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_expr_body cfn bfn tfn ce ty (Builtin ann bi args))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`P` |-> `\action.
    compiler_label_hoare (compiler_label_reservation origin pending) action
      (\r out. compiler_label_reservation origin pending out)`]
    compile_expr_body_builtin_property)) >>
  simp[compiler_label_hoare_modular_names]
QED

Theorem compile_expr_body_type_builtin_action[local]:
  compile_expr_body cfn bfn tfn ce ty (TypeBuiltin ann tb rt args) =
  tfn ce (expr_type (TypeBuiltin ann tb rt args)) ty tb rt args
Proof
  simp[FUN_EQ_THM] >> gen_tac >> simp[compile_expr_body_def]
QED

Theorem compiler_block_tail_type_builtin_body:
  compiler_block_tail (tfn ce (expr_type (TypeBuiltin ann tb rt args)) ty tb rt args) ==>
  compiler_block_tail (compile_expr_body cfn bfn tfn ce ty (TypeBuiltin ann tb rt args))
Proof
  simp[compile_expr_body_type_builtin_action]
QED

Theorem compiler_label_hoare_type_builtin_body:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (tfn ce (expr_type (TypeBuiltin ann tb rt args)) ty tb rt args)
    (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_expr_body cfn bfn tfn ce ty (TypeBuiltin ann tb rt args))
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_expr_body_type_builtin_action]
QED

Theorem compiler_block_tail_toplevel_body:
  compiler_block_tail (compile_expr_body cfn bfn tfn ce ty (TopLevelName ann nsid))
Proof
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid`
  >- simp[compiler_block_tail_def, emitHelperTheory.emit_inst_def,
          comp_bind_def, fresh_id_def, emit_def] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[compiler_block_tail_def, emitHelperTheory.emit_inst_def,
       comp_bind_def, fresh_id_def, emit_def]
QED

Theorem supported_send_pure_args[local]:
  supported_effect_expr tops (Call ann (Send b) args dflt) ==>
  supported_pure_exprs tops args
Proof
  Cases_on `dflt` >> Cases_on `ann` >> Cases_on `b` >>
  namedCases_on `args` ["", "a rest"] >>
  gvs[supportedExprsTheory.supported_effect_expr_def] >>
  namedCases_on `rest` ["", "v more"] >>
  gvs[supportedExprsTheory.supported_effect_expr_def] >>
  namedCases_on `more` ["", "g tail"] >>
  gvs[supportedExprsTheory.supported_effect_expr_def,
      supportedExprsTheory.supported_pure_expr_def] >>
  Cases_on `tail` >>
  gvs[supportedExprsTheory.supported_effect_expr_def,
      supportedExprsTheory.supported_pure_expr_def]
QED

Theorem compiler_block_tail_supported_expr_body:
  (!ce ty child.
    expr_size child < expr_size e /\
    (supported_pure_expr tops child \/ supported_place_expr tops child \/
     supported_effect_expr tops child \/ supported_effect_place_expr tops child) /\
    ~expr_has_internal_call child ==> compiler_block_tail (cfn ce ty child)) /\
  (!ce ann ty bi args.
    list_size expr_size args < expr_size e /\
    (supported_pure_expr tops (Builtin ann bi args) \/
     supported_place_expr tops (Builtin ann bi args) \/
     supported_effect_expr tops (Builtin ann bi args) \/
     supported_effect_place_expr tops (Builtin ann bi args)) /\
    ~expr_has_internal_call (Builtin ann bi args) ==>
    compiler_block_tail (bfn ce ann ty bi args)) /\
  (!ce ann ty tb rt args.
    list_size expr_size args < expr_size e /\
    (supported_pure_expr tops (TypeBuiltin ann tb rt args) \/
     supported_place_expr tops (TypeBuiltin ann tb rt args) \/
     supported_effect_expr tops (TypeBuiltin ann tb rt args) \/
     supported_effect_place_expr tops (TypeBuiltin ann tb rt args)) /\
    ~expr_has_internal_call (TypeBuiltin ann tb rt args) ==>
    compiler_block_tail (tfn ce ann ty tb rt args)) /\
  (supported_pure_expr tops e \/ supported_place_expr tops e \/
   supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
  ~expr_has_internal_call e ==>
  compiler_block_tail
    (compile_expr_body (expr_child_callback (expr_size e) cfn)
      (builtin_child_callback (expr_size e) bfn)
      (type_child_callback (expr_size e) tfn) ce ty e)
Proof
  Cases_on `e` >> disch_then (map_every assume_tac o CONJUNCTS)
  >~ [`Builtin ann bi args`] >- (
    irule compiler_block_tail_builtin_body >>
    simp[builtin_child_callback_property, vyperASTTheory.expr_size_def] >>
    first_x_assum irule >> simp[vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >> metis_tac[])
  >~ [`TypeBuiltin ann tb rt args`] >- (
    irule compiler_block_tail_type_builtin_body >>
    simp[type_child_callback_property, vyperASTTheory.expr_size_def] >>
    first_x_assum irule >> simp[vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >> metis_tac[])
  >~ [`Name ann id`] >- (
    rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_name_vv)
  >~ [`Literal ann lit`] >- (
    rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_literal_vv])
  >~ [`Subscript _ _ _`] >- (
    rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
    drule_all supported_closure_subscript >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_subscript >>
    simp[expr_child_callback_property, vyperASTTheory.expr_size_def] >>
    rpt strip_tac >> first_x_assum irule >>
    simp[vyperASTTheory.expr_size_def] >> metis_tac[])
  >~ [`Attribute _ _ _`] >- (
    rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
    drule_all supported_closure_attribute >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_attribute >>
    simp[expr_child_callback_property, vyperASTTheory.expr_size_def] >>
    first_x_assum irule >> simp[vyperASTTheory.expr_size_def])
  >~ [`IfExp ann cond_e then_e else_e`] >- (
    irule compiler_block_tail_ifexp_body >>
    gvs[supportedExprsTheory.supported_pure_expr_def,
      supportedExprsTheory.supported_effect_expr_def,
      supportedExprTraverseTheory.expr_has_internal_call_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.expr_internal_call_root_def] >>
    simp[expr_child_callback_property, vyperASTTheory.expr_size_def] >>
    rpt strip_tac >> first_x_assum irule >>
    simp[vyperASTTheory.expr_size_def] >> metis_tac[])
  >~ [`Pop _ _`] >- simp[compiler_block_tail_pop_body]
  >~ [`FlagMember _ _ _`] >- (
    gvs[supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def])
  >~ [`TopLevelName _ _`] >- simp[compiler_block_tail_toplevel_body]
  >~ [`StructLit _ _ _`] >- suspend "struct"
  >~ [`Call _ _ _ _`] >- suspend "call"
QED

Resume compiler_block_tail_supported_expr_body[struct]:
  rename1 `StructLit ann nsid fields` >>
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_alloc_buffer]) >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_struct_lit >>
      simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
      drule exprCallBoundsTheory.expr_struct_field_bound >>
      disch_then (qspecl_then [`nsid`,`ann`] assume_tac) >>
      fs[vyperASTTheory.expr_size_def, expr_child_callback_property] >>
      first_x_assum irule >> simp[] >>
      gvs[supportedExprsTheory.supported_pure_expr_def,
          supportedExprsTheory.supported_effect_expr_def,
          supportedExprsTheory.supported_pure_fields_every, listTheory.EVERY_MEM] >>
      `supported_pure_expr tops p_2` by
        (first_x_assum (qspec_then `(p_1,p_2)` mp_tac) >> simp[]) >>
      metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call]) >>
  gen_tac >> BETA_TAC >> simp[compiler_block_tail_def]
QED

Resume compiler_block_tail_supported_expr_body[call]:
  rename1 `Call ann target args dflt` >>
  Cases_on `dflt` >> Cases_on `target` >>
  gvs[supportedExprsTheory.supported_effect_expr_def,
      supportedExprsTheory.supported_pure_expr_def,
      supportedExprTraverseTheory.expr_has_internal_call_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.expr_internal_call_root_def]
  >~ [`ExtCall _ _ _ _`] >- suspend "external"
  >~ [`Send _`] >- suspend "send"
QED

Resume compiler_block_tail_supported_expr_body[external]:
  rename1 `ExtCall static skip sig opts` >> PairCases_on `sig` >>
  gvs[supportedExprsTheory.supported_effect_expr_def] >>
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_extcall >>
  rpt strip_tac >>
  drule exprCallBoundsTheory.expr_call_arg_bound >>
  disch_then (qspecl_then [`ExtCall static skip (sig0,sig1,sig2) opts`,`NONE`,`ann`] assume_tac) >>
  fs[vyperASTTheory.expr_size_def, expr_child_callback_property] >>
  first_x_assum irule >> simp[] >>
  fs[supportedExprsTheory.supported_pure_exprs_every, listTheory.EVERY_MEM] >>
  `supported_pure_expr tops e` by metis_tac[] >>
  drule supportedExprTraverseTheory.supported_pure_no_internal_call >>
  simp[supportedExprTraverseTheory.expr_has_internal_call_def]
QED

Resume compiler_block_tail_supported_expr_body[send]:
  drule supported_send_pure_args >> strip_tac >>
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_send >>
  rpt strip_tac >> drule exprCallBoundsTheory.expr_call_arg_bound >>
  disch_then (qspecl_then [`Send b`,`NONE`,`ann`] assume_tac) >>
  fs[vyperASTTheory.expr_size_def, expr_child_callback_property] >>
  first_x_assum irule >> simp[] >>
  fs[supportedExprsTheory.supported_pure_exprs_every, listTheory.EVERY_MEM] >>
  `supported_pure_expr tops e` by metis_tac[] >>
  drule supportedExprTraverseTheory.supported_pure_no_internal_call >>
  simp[supportedExprTraverseTheory.expr_has_internal_call_def]
QED

Finalise compiler_block_tail_supported_expr_body

Theorem compiler_label_hoare_toplevel_body:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_expr_body cfn bfn tfn ce ty (TopLevelName ann nsid))
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid`
  >- (simp[] >> ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
      >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
          simp[compiler_label_hoare_context_primitives]) >>
      gen_tac >> BETA_TAC >> simp[compiler_label_hoare_def]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
       >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
           simp[compiler_label_hoare_context_primitives]) >>
       gen_tac >> BETA_TAC) >> simp[compiler_label_hoare_def]
QED

Theorem expr_child_callback_eq[local]:
  expr_size e < n ==> expr_child_callback n f ce ty e = f ce ty e
Proof
  simp[FUN_EQ_THM, exprCallBoundsTheory.expr_child_callback_def]
QED

Theorem builtin_child_callback_eq[local]:
  list_size expr_size args < n ==>
  builtin_child_callback n f ce ann ty bi args = f ce ann ty bi args
Proof
  simp[FUN_EQ_THM, exprCallBoundsTheory.builtin_child_callback_def]
QED

Theorem type_child_callback_eq[local]:
  list_size expr_size args < n ==>
  type_child_callback n f ce ann ty tb rt args = f ce ann ty tb rt args
Proof
  simp[FUN_EQ_THM, exprCallBoundsTheory.type_child_callback_def]
QED

Theorem compiler_label_hoare_supported_expr_body:
  (!ce ty child. expr_size child < expr_size e /\
    (supported_pure_expr tops child \/ supported_place_expr tops child \/
     supported_effect_expr tops child \/ supported_effect_place_expr tops child) /\
    ~expr_has_internal_call child ==>
    !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce ty child) (\r out. compiler_label_reservation origin pending out)) /\
  (!ce ann ty bi args. list_size expr_size args < expr_size e /\
    (supported_pure_expr tops (Builtin ann bi args) \/
     supported_place_expr tops (Builtin ann bi args) \/
     supported_effect_expr tops (Builtin ann bi args) \/
     supported_effect_place_expr tops (Builtin ann bi args)) /\
    ~expr_has_internal_call (Builtin ann bi args) ==>
    !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
      (bfn ce ann ty bi args) (\r out. compiler_label_reservation origin pending out)) /\
  (!ce ann ty tb rt args. list_size expr_size args < expr_size e /\
    (supported_pure_expr tops (TypeBuiltin ann tb rt args) \/
     supported_place_expr tops (TypeBuiltin ann tb rt args) \/
     supported_effect_expr tops (TypeBuiltin ann tb rt args) \/
     supported_effect_place_expr tops (TypeBuiltin ann tb rt args)) /\
    ~expr_has_internal_call (TypeBuiltin ann tb rt args) ==>
    !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
      (tfn ce ann ty tb rt args) (\r out. compiler_label_reservation origin pending out)) /\
  (supported_pure_expr tops e \/ supported_place_expr tops e \/
   supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
  ~expr_has_internal_call e ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_expr_body (expr_child_callback (expr_size e) cfn)
      (builtin_child_callback (expr_size e) bfn)
      (type_child_callback (expr_size e) tfn) ce ty e)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `e` >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac
  >~ [`Builtin ann bi args`] >- (
    irule compiler_label_hoare_builtin_body >>
    simp[builtin_child_callback_eq, vyperASTTheory.expr_size_def] >>
    first_x_assum irule >> simp[vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >> metis_tac[])
  >~ [`TypeBuiltin ann tb rt args`] >- (
    irule compiler_label_hoare_type_builtin_body >>
    simp[type_child_callback_eq, vyperASTTheory.expr_size_def] >>
    first_x_assum irule >> simp[vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >> metis_tac[])
  >~ [`Name ann id`] >- (
    rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
    CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
    irule compiler_label_hoare_name_vv)
  >~ [`Literal ann lit`] >- (
    rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
    CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
    simp[compiler_label_hoare_literal_vv])
  >~ [`Subscript _ _ _`] >- suspend "subscript_h"
  >~ [`Attribute _ _ _`] >- suspend "attribute_h"
  >~ [`IfExp _ _ _ _`] >- suspend "ifexp_h"
  >~ [`Pop _ _`] >- simp[compiler_label_hoare_pop_body]
  >~ [`FlagMember _ _ _`] >- (
    gvs[supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def])
  >~ [`TopLevelName _ _`] >- simp[compiler_label_hoare_toplevel_body]
  >~ [`StructLit _ _ _`] >- suspend "struct_h"
  >~ [`Call _ _ _ _`] >- suspend "call_h"
QED

Resume compiler_label_hoare_supported_expr_body[subscript_h]:
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  drule_all supported_closure_subscript >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  irule compiler_label_hoare_subscript >>
  simp[expr_child_callback_eq, vyperASTTheory.expr_size_def] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[vyperASTTheory.expr_size_def] >> metis_tac[]
QED

Resume compiler_label_hoare_supported_expr_body[attribute_h]:
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  drule_all supported_closure_attribute >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  irule compiler_label_hoare_attribute >>
  simp[expr_child_callback_eq, vyperASTTheory.expr_size_def] >>
  first_x_assum irule >> simp[vyperASTTheory.expr_size_def]
QED

Resume compiler_label_hoare_supported_expr_body[ifexp_h]:
  irule compiler_label_hoare_ifexp_body >>
  gvs[supportedExprsTheory.supported_pure_expr_def,
      supportedExprsTheory.supported_effect_expr_def,
      supportedExprTraverseTheory.expr_has_internal_call_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.expr_internal_call_root_def] >>
  simp[expr_child_callback_eq, vyperASTTheory.expr_size_def] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[vyperASTTheory.expr_size_def] >> metis_tac[]
QED

Resume compiler_label_hoare_supported_expr_body[struct_h]:
  rename1 `StructLit ann nsid fields` >>
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      simp[compiler_label_hoare_alloc_buffer]) >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
      irule compiler_label_hoare_struct_lit >>
      simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
      drule exprCallBoundsTheory.expr_struct_field_bound >>
      disch_then (qspecl_then [`nsid`,`ann`] assume_tac) >>
      fs[vyperASTTheory.expr_size_def, expr_child_callback_eq] >>
      first_x_assum irule >> simp[] >>
      gvs[supportedExprsTheory.supported_pure_expr_def,
          supportedExprsTheory.supported_effect_expr_def,
          supportedExprsTheory.supported_pure_fields_every, listTheory.EVERY_MEM] >>
      `supported_pure_expr tops p_2` by
        (first_x_assum (qspec_then `(p_1,p_2)` mp_tac) >> simp[]) >>
      metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call]) >>
  gen_tac >> BETA_TAC >> simp[compiler_label_hoare_def]
QED

Resume compiler_label_hoare_supported_expr_body[call_h]:
  rename1 `Call ann target args dflt` >>
  Cases_on `dflt` >> Cases_on `target` >>
  gvs[supportedExprsTheory.supported_effect_expr_def,
      supportedExprsTheory.supported_pure_expr_def,
      supportedExprTraverseTheory.expr_has_internal_call_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.expr_internal_call_root_def]
  >~ [`ExtCall _ _ _ _`] >- suspend "external_h"
  >~ [`Send _`] >- suspend "send_h"
QED

Resume compiler_label_hoare_supported_expr_body[external_h]:
  rename1 `ExtCall static skip sig opts` >> PairCases_on `sig` >>
  gvs[supportedExprsTheory.supported_effect_expr_def] >>
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  irule compiler_label_hoare_extcall >> rpt strip_tac >>
  drule exprCallBoundsTheory.expr_call_arg_bound >>
  disch_then (qspecl_then [`ExtCall static skip (sig0,sig1,sig2) opts`,`NONE`,`ann`] assume_tac) >>
  fs[vyperASTTheory.expr_size_def, expr_child_callback_eq] >>
  first_x_assum irule >> simp[] >>
  fs[supportedExprsTheory.supported_pure_exprs_every, listTheory.EVERY_MEM] >>
  `supported_pure_expr tops e` by metis_tac[] >>
  drule supportedExprTraverseTheory.supported_pure_no_internal_call >>
  simp[supportedExprTraverseTheory.expr_has_internal_call_def]
QED

Resume compiler_label_hoare_supported_expr_body[send_h]:
  drule supported_send_pure_args >> strip_tac >>
  rewrite_tac[lambdify compile_expr_body_def] >> simp[] >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  irule compiler_label_hoare_send >> rpt strip_tac >>
  drule exprCallBoundsTheory.expr_call_arg_bound >>
  disch_then (qspecl_then [`Send b`,`NONE`,`ann`] assume_tac) >>
  fs[vyperASTTheory.expr_size_def, expr_child_callback_eq] >>
  first_x_assum irule >> simp[] >>
  fs[supportedExprsTheory.supported_pure_exprs_every, listTheory.EVERY_MEM] >>
  `supported_pure_expr tops e` by metis_tac[] >>
  drule supportedExprTraverseTheory.supported_pure_no_internal_call >>
  simp[supportedExprTraverseTheory.expr_has_internal_call_def]
QED

Finalise compiler_label_hoare_supported_expr_body
