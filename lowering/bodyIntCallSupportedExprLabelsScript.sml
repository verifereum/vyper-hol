(* Structural compiler contracts on the supported expression closure. *)
Theory bodyIntCallSupportedExprLabels
Ancestors
  bodyIntCallExprBodyLabels bodyIntCallTypeBuiltinLabels bodyIntCallExprClosure
  bodyIntCallBuiltinLabels
  exprLowering supportedExprs supportedExprTraverse exprCallBounds

Theorem compile_expr_action[local]:
  compile_expr ce ty e =
    compile_expr_body (expr_child_callback (expr_size e) compile_expr)
      (builtin_child_callback (expr_size e) compile_builtin_dispatch)
      (type_child_callback (expr_size e) compile_type_builtin_dispatch) ce ty e
Proof
  simp[FUN_EQ_THM] >> gen_tac >> rewrite_tac[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem compile_builtin_dispatch_action[local]:
  compile_builtin_dispatch ce ann ty bi args =
    compile_builtin_dispatch_body
      (expr_child_callback (list_size expr_size args) compile_expr) ce ann ty bi args
Proof
  simp[FUN_EQ_THM] >> gen_tac >> rewrite_tac[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem compile_type_builtin_dispatch_action[local]:
  compile_type_builtin_dispatch ce ann ty tb rt args =
    compile_type_builtin_dispatch_body
      (expr_child_callback (list_size expr_size args) compile_expr) ce ann ty tb rt args
Proof
  simp[FUN_EQ_THM] >> gen_tac >> rewrite_tac[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem compiler_block_tail_supported_mutual:
  (!ce ty e (st:compile_state) tops.
    (supported_pure_expr tops e \/ supported_place_expr tops e \/
     supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
    ~expr_has_internal_call e ==> compiler_block_tail (compile_expr ce ty e)) /\
  (!ce ann ty bi args (st:compile_state) tops.
    supported_builtin_form tops ann bi args /\ supported_pure_exprs tops args ==>
    compiler_block_tail (compile_builtin_dispatch ce ann ty bi args)) /\
  (!ce ann ty tb rt args (st:compile_state) tops.
    supported_type_builtin_form tops ann tb rt args /\ supported_pure_exprs tops args ==>
    compiler_block_tail (compile_type_builtin_dispatch ce ann ty tb rt args))
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume compiler_block_tail_supported_mutual[expr]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[compile_expr_action] >>
  irule compiler_block_tail_supported_expr_body >> simp[] >> qexists_tac `tops` >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  gvs[supportedExprsTheory.supported_pure_expr_def,
      supportedExprsTheory.supported_effect_expr_def] >> metis_tac[]
QED

Resume compiler_block_tail_supported_mutual[builtin]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  rewrite_tac[compile_builtin_dispatch_action] >>
  irule compiler_block_tail_supported_builtin_source >>
  reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
  rpt strip_tac >> drule expr_list_member_bound >> strip_tac >>
  `!ce t. expr_child_callback (list_size expr_size args) compile_expr ce t e =
     compile_expr ce t e` by simp[FUN_EQ_THM, expr_child_callback_def] >>
  simp[] >> first_x_assum irule >>
  fs[supported_pure_exprs_every] >>
  drule_all supported_closure_pure_member >> metis_tac[]
QED

Resume compiler_block_tail_supported_mutual[type_builtin]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  rewrite_tac[compile_type_builtin_dispatch_action] >>
  irule compiler_block_tail_supported_type_builtin >>
  reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
  rpt strip_tac >> drule expr_list_member_bound >> strip_tac >>
  `!ce t. expr_child_callback (list_size expr_size args) compile_expr ce t e =
     compile_expr ce t e` by simp[FUN_EQ_THM, expr_child_callback_def] >>
  simp[] >> first_x_assum irule >>
  fs[supported_pure_exprs_every] >>
  drule_all supported_closure_pure_member >> metis_tac[]
QED

Finalise compiler_block_tail_supported_mutual

Theorem compiler_label_hoare_supported_mutual:
  (!ce ty e (st:compile_state) tops.
    (supported_pure_expr tops e \/ supported_place_expr tops e \/
     supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
    ~expr_has_internal_call e ==>
    !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_expr ce ty e) (\r out. compiler_label_reservation origin pending out)) /\
  (!ce ann ty bi args (st:compile_state) tops.
    supported_builtin_form tops ann bi args /\ supported_pure_exprs tops args ==>
    !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_builtin_dispatch ce ann ty bi args)
      (\r out. compiler_label_reservation origin pending out)) /\
  (!ce ann ty tb rt args (st:compile_state) tops.
    supported_type_builtin_form tops ann tb rt args /\ supported_pure_exprs tops args ==>
    !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_type_builtin_dispatch ce ann ty tb rt args)
      (\r out. compiler_label_reservation origin pending out))
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume compiler_label_hoare_supported_mutual[expr]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  rewrite_tac[compile_expr_action] >>
  irule compiler_label_hoare_supported_expr_body >> simp[] >> qexists_tac `tops` >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  gvs[supportedExprsTheory.supported_pure_expr_def,
      supportedExprsTheory.supported_effect_expr_def] >> metis_tac[]
QED

Resume compiler_label_hoare_supported_mutual[builtin]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> rpt gen_tac >>
  rewrite_tac[compile_builtin_dispatch_action] >>
  irule compiler_label_hoare_supported_builtin_source >>
  reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
  rpt strip_tac >> drule expr_list_member_bound >> strip_tac >>
  `!ce t. expr_child_callback (list_size expr_size args) compile_expr ce t e =
     compile_expr ce t e` by simp[FUN_EQ_THM, expr_child_callback_def] >>
  simp[] >> first_x_assum irule >>
  fs[supported_pure_exprs_every] >>
  drule_all supported_closure_pure_member >> metis_tac[]
QED

Resume compiler_label_hoare_supported_mutual[type_builtin]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> rpt gen_tac >>
  rewrite_tac[compile_type_builtin_dispatch_action] >>
  irule compiler_label_hoare_supported_type_builtin >>
  reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
  rpt strip_tac >> drule expr_list_member_bound >> strip_tac >>
  `!ce t. expr_child_callback (list_size expr_size args) compile_expr ce t e =
     compile_expr ce t e` by simp[FUN_EQ_THM, expr_child_callback_def] >>
  simp[] >> first_x_assum irule >>
  fs[supported_pure_exprs_every] >>
  drule_all supported_closure_pure_member >> metis_tac[]
QED

Finalise compiler_label_hoare_supported_mutual

Theorem compiler_block_tail_supported_expr:
  (supported_pure_expr tops e \/ supported_place_expr tops e \/
   supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
  ~expr_has_internal_call e ==> compiler_block_tail (compile_expr ce ty e)
Proof
  metis_tac[cj 1 compiler_block_tail_supported_mutual]
QED

Theorem compiler_block_tail_supported_builtin_dispatch:
  supported_builtin_form tops ann bi args /\ supported_pure_exprs tops args ==>
  compiler_block_tail (compile_builtin_dispatch ce ann ty bi args)
Proof
  metis_tac[cj 2 compiler_block_tail_supported_mutual]
QED

Theorem compiler_block_tail_supported_type_builtin_dispatch:
  supported_type_builtin_form tops ann tb rt args /\ supported_pure_exprs tops args ==>
  compiler_block_tail (compile_type_builtin_dispatch ce ann ty tb rt args)
Proof
  metis_tac[cj 3 compiler_block_tail_supported_mutual]
QED

Theorem compiler_label_hoare_supported_expr:
  (supported_pure_expr tops e \/ supported_place_expr tops e \/
   supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
  ~expr_has_internal_call e ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_expr ce ty e) (\r out. compiler_label_reservation origin pending out)
Proof
  metis_tac[cj 1 compiler_label_hoare_supported_mutual]
QED

Theorem compiler_label_hoare_supported_builtin_dispatch:
  supported_builtin_form tops ann bi args /\ supported_pure_exprs tops args ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_builtin_dispatch ce ann ty bi args)
    (\r out. compiler_label_reservation origin pending out)
Proof
  metis_tac[cj 2 compiler_label_hoare_supported_mutual]
QED

Theorem compiler_label_hoare_supported_type_builtin_dispatch:
  supported_type_builtin_form tops ann tb rt args /\ supported_pure_exprs tops args ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_type_builtin_dispatch ce ann ty tb rt args)
    (\r out. compiler_label_reservation origin pending out)
Proof
  metis_tac[cj 3 compiler_label_hoare_supported_mutual]
QED
