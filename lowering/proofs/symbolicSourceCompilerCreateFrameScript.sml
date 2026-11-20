Theory symbolicSourceCompilerCreateFrame
Ancestors symbolicSourceCompilerFrame exprLowering compileEnv rich_list

val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind]];

fun frame_tac goal =
  (simp[comp_ignore_bind_def, pairTheory.FORALL_PROD] >>
   rpt (match_mp_tac symbolic_frame_bind >> conj_tac
     >- (simp[] >> frame_tac) >> gen_tac >> BETA_TAC) >> simp[]) goal

Theorem symbolic_frame_create_ctor_args:
  (!copy vv. symbolic_frame R (compile_snapshot_vv cenv copy vv)) /\
  (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
  symbolic_frame R (compile_create_ctor_args cfn cenv es)
Proof
  Induct_on `es` >> simp[compile_create_ctor_args_def] >>
  rpt strip_tac >>
  match_mp_tac symbolic_frame_bind >> conj_tac
  >- (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  gen_tac >> BETA_TAC >>
  match_mp_tac symbolic_frame_bind >> simp[] >> gen_tac >> BETA_TAC >>
  match_mp_tac symbolic_frame_bind >> simp[] >> first_x_assum irule >>
  metis_tac[]
QED

Theorem symbolic_frame_lower_value:
  symbolic_frame R (cfn cenv ty e) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) ==>
  symbolic_frame R (lower_value cfn cenv ty e)
Proof
  simp[lower_value_def]
QED

Theorem symbolic_frame_create_salt:
  (!e. salt = SOME e ==> symbolic_frame R (cfn cenv (expr_type e) e)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) ==>
  symbolic_frame R (compile_create_salt cfn cenv salt)
Proof
  Cases_on `salt` >> simp[compile_create_salt_def, symbolic_frame_lower_value]
QED

Theorem symbolic_frame_create_blueprint_args:
  (!opc ops. symbolic_frame R (emit_op opc ops)) /\
  symbolic_frame R (emit_inst INVALID [] []) /\
  (!copy vv. symbolic_frame R (compile_snapshot_vv cenv copy vv)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!dst rows. symbolic_frame R (compile_abi_encode_values_to_buf cenv dst rows)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
  symbolic_frame R (compile_create_blueprint_args cfn cenv raw later_es es)
Proof
  strip_tac >>
  `symbolic_frame R (compile_create_ctor_args cfn cenv es)` by
    (irule symbolic_frame_create_ctor_args >> simp[]) >>
  Cases_on `raw`
  >- (namedCases_on `es` ["", "arg remaining"] >>
      simp[compile_create_blueprint_args_def, comp_ignore_bind_def] >>
      Cases_on `remaining` >>
      gvs[compile_create_blueprint_args_def, comp_ignore_bind_def] >> frame_tac) >>
  rw[compile_create_blueprint_args_def] >> frame_tac
QED

Theorem symbolic_frame_create_snapshot:
  (!opc ops. symbolic_frame R (emit_op opc ops)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!p d n loc. symbolic_frame R (compile_slot_to_memory p d n loc)) /\
  (!b a p d n off. symbolic_frame R (compile_imm_copy_to_memory b a p d n off)) /\
  (!d s n. symbolic_frame R (compile_copy_memory_dynamic d s n)) ==>
  symbolic_frame R (compile_create_snapshot cenv vv ty)
Proof
  strip_tac >> simp[compile_create_snapshot_def, comp_ignore_bind_def] >>
  match_mp_tac symbolic_frame_bind >> simp[] >> gen_tac >>
  Cases_on `vv_location vv` >> simp[] >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> simp[]
QED

Theorem symbolic_frame_raw_create:
  (!opc ops. symbolic_frame R (emit_op opc ops)) /\
  symbolic_frame R (cfn cenv (expr_type bytecode) bytecode) /\
  symbolic_frame R (lower_value cfn cenv (expr_type value) value) /\
  (!vv ty. symbolic_frame R (compile_create_snapshot cenv vv ty)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!d s n. symbolic_frame R (compile_copy_memory_dynamic d s n)) /\
  symbolic_frame R (compile_create_ctor_args cfn cenv es) /\
  (!dst rows. symbolic_frame R (compile_abi_encode_values_to_buf cenv dst rows)) /\
  symbolic_frame R (compile_create_salt cfn cenv salt) /\
  (!p n v s b. symbolic_frame R (compile_create_dispatch p n v s b)) ==>
  symbolic_frame R (compile_raw_create cfn cenv bytecode value es salt rof)
Proof
  strip_tac >> simp[compile_raw_create_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac symbolic_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> frame_tac) >>
  simp[pairTheory.FORALL_PROD] >> frame_tac
QED

Theorem symbolic_frame_blueprint_offset[local]:
  symbolic_frame R (lower_value cfn cenv (expr_type e) e) ==>
  symbolic_frame R
    (case origin_fold_value e of
       Literal _ (IntL i) => comp_return (Lit (i2w i))
     | _ => lower_value cfn cenv (expr_type e) e)
Proof
  strip_tac >> Cases_on `origin_fold_value e` >> simp[] >>
  rename1 `origin_fold_value e = Literal ty literal` >>
  Cases_on `literal` >> simp[]
QED

Theorem symbolic_frame_create_call:
  symbolic_frame R (emit_inst INVALID [] []) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v. symbolic_frame R (compile_create_proxy_buf v)) /\
  (!p n v s b. symbolic_frame R (compile_create_dispatch p n v s b)) /\
  (!v w s b. symbolic_frame R (compile_create_copy v w s b)) /\
  (!is_lit v off. symbolic_frame R (compile_create_blueprint_check is_lit v off)) /\
  (!v w s off n p len b.
     symbolic_frame R (compile_create_blueprint_append v w s off n p len b)) /\
  (!es raw later_es. (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
     symbolic_frame R (compile_create_blueprint_args cfn cenv raw later_es es)) /\
  (!bytecode value es salt b.
     symbolic_frame R (cfn cenv (expr_type bytecode) bytecode) /\
     symbolic_frame R (cfn cenv (expr_type value) value) /\
     (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) /\
     (!e. salt = SOME e ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
     symbolic_frame R (compile_raw_create cfn cenv bytecode value es salt b)) /\
  (!e. MEM e args ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
  symbolic_frame R (compile_create_call cfn cenv ck has_salt rof args)
Proof
  strip_tac >> namedCases_on `args` ["", "target remaining"] >>
  simp[compile_create_call_def, comp_ignore_bind_def] >>
  namedCases_on `remaining` ["", "value rest"] >>
  simp[compile_create_call_def, comp_ignore_bind_def] >>
  Cases_on `ck` >> Cases_on `has_salt` >>
  namedCases_on `rest` ["", "head rest_tail"] >>
  gvs[compile_create_call_def, comp_ignore_bind_def, symbolic_frame_lower_value,
      symbolic_frame_create_salt, symbolic_frame_blueprint_offset] >>
  TRY (rename1 `symbolic_frame R (if SUC (LENGTH rest_tail) < 2 then _ else _)` >>
       Cases_on `rest_tail` >> gvs[]) >>
  rpt (FIRST [
    match_mp_tac symbolic_frame_bind >> conj_tac,
    gen_tac >> BETA_TAC,
    CHANGED_TAC (simp[symbolic_frame_lower_value, symbolic_frame_create_salt,
                      symbolic_frame_blueprint_offset, pairTheory.ELIM_UNCURRY])]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[rich_listTheory.MEM_FRONT, rich_listTheory.MEM_LAST, listTheory.MEM]
QED
