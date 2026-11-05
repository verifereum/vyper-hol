(* Legacy unrestricted Pop assertions. These are not production dependencies:
   arbitrary expression callbacks need not preserve compiler state. *)
Theory bodyIntCallExprBodyLabels
Ancestors
  bodyIntCallExprBodySoundLabels

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
