Theory runtimeSymSrcOpenPlaces
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  exprLowering compileEnv context list supportedExprs supportedExprTraverse
  finite_map venomInst loweringShapeDefs stackPlanTypes

Theorem runtime_sym_target_base:
  !target ce. runtime_sym_env ce ==>
  ~is_label_operand (compile_target_base ce target)
Proof
  gen_tac >> measureInduct_on `vyperAST$base_assignment_target_size target` >>
  Cases_on `target` >> simp[compile_target_base_def, vyperASTTheory.expr_size_def] >> rpt strip_tac
  >- (Cases_on `FLOOKUP ce.ce_vars s` >> gvs[is_label_operand_def] >>
      Cases_on `x` >> gvs[is_label_operand_def] >>
      drule_all runtime_sym_env_local >> simp[runtime_sym_loc_def]) >>
  Cases_on `FLOOKUP ce.ce_module_vars p` >> gvs[is_label_operand_def] >>
  Cases_on `x` >> gvs[is_label_operand_def]
QED

Theorem runtime_sym_attribute:
  runtime_sym_attribute_clause tops
Proof
  rewrite_tac[runtime_sym_attribute_clause_def] >>
  map_every qx_gen_tac [`cfn`,`ce`,`rt`,`ty`,`base_e`,`fld`,`s`,`v`,`s'`] >>
  strip_tac >>
  `supported_expr tops base_e \/ supported_place_expr tops base_e \/
   supported_effect_place_expr tops base_e` by
    (gvs[supported_expr_def, supported_pure_expr_def,
         supported_effect_expr_def]) >>
  `~supported_expr_exists is_self_code base_e` by
    gvs[supported_expr_exists_def] >>
  qpat_x_assum `compile_attribute _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_attribute_def, comp_bind_def] >>
  Cases_on `cfn ce ty base_e s` >> simp[] >>
  pairarg_tac >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  rewrite_tac[runtime_sym_expr_contract_def] >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule runtime_sym_value_operand >> strip_tac >>
  drule_at (Pos last) runtime_sym_emit_op >> simp[is_label_operand_def] >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED


Theorem runtime_sym_bind_safe:
  (!x t. f s = (x,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ P x) /\
  (!x t y u. EVERY runtime_sym_inst (state_insts t) /\ P x /\
     g x t = (y,u) ==> EVERY runtime_sym_inst (state_insts u) /\ Q y) /\
  comp_bind f g s = (z,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ Q z
Proof
  Cases_on `f s` >> simp[comp_bind_def] >> metis_tac[]
QED

Theorem runtime_sym_optional_hash:
  (!op b s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand op /\ compile_keccak256_key op b s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) ==>
  !b op s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand op /\
     (if b then compile_keccak256_key op F else comp_return op) s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  strip_tac >> Cases_on `b` >> simp[NoAsms, comp_return_def] >>
  metis_tac[]
QED

Theorem runtime_sym_map_sequence:
  (!op b s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand op /\ compile_keccak256_key op b s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) /\
  (!bop key s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand bop /\ ~is_label_operand key /\
     compile_mapping_subscript bop key s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) /\
  (!op t. key_comp s = (op,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ ~is_label_operand op) /\
  ~is_label_operand bop /\
  comp_bind key_comp (\key.
    comp_bind (if hash then compile_keccak256_key key F else comp_return key)
      (\hashed. comp_bind (compile_mapping_subscript bop hashed)
        (\slot. comp_return (LocatedValue rt (mk_ptr slot loc))))) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> Cases_on `key_comp s` >>
  `EVERY runtime_sym_inst (state_insts r) /\ ~is_label_operand q` by metis_tac[] >>
  Cases_on `(if hash then compile_keccak256_key q F else comp_return q) r` >>
  rename1 `(if hash then compile_keccak256_key q F else comp_return q) r = (hop,hs)` >>
  `EVERY runtime_sym_inst (state_insts hs) /\ ~is_label_operand hop` by
    (irule runtime_sym_optional_hash >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`hash`,`q`,`r`] >> asm_rewrite_tac[]) >>
  Cases_on `compile_mapping_subscript bop hop hs` >>
  rename1 `compile_mapping_subscript bop hop hs = (slot,ss)` >>
  `EVERY runtime_sym_inst (state_insts ss) /\ ~is_label_operand slot` by metis_tac[] >>
  qpat_x_assum `!op b s out s'. _` kall_tac >>
  qpat_x_assum `!bop key s out s'. _` kall_tac >>
  gvs[comp_bind_def, comp_return_def, runtime_sym_value_def, mk_ptr_def]
QED

Theorem runtime_sym_locate_sequence:
  (!op t. comp s = (op,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ ~is_label_operand op) /\
  comp_bind comp (\op. comp_return (LocatedValue rt (mk_ptr op loc))) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `comp s` >> simp[comp_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> simp[runtime_sym_value_def, mk_ptr_def]
QED

Theorem runtime_sym_operand_sequence:
  (!op t. comp s = (op,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ ~is_label_operand op) /\
  (!op t out u. EVERY runtime_sym_inst (state_insts t) /\
     ~is_label_operand op /\ next op t = (out,u) ==>
     EVERY runtime_sym_inst (state_insts u) /\ ~is_label_operand out) /\
  comp_bind comp next s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  Cases_on `comp s` >> simp[comp_bind_def] >> metis_tac[]
QED

Theorem runtime_sym_subscript_children:
  (supported_expr tops (Subscript rt be key) \/
   supported_place_expr tops (Subscript rt be key) \/
   supported_effect_place_expr tops (Subscript rt be key)) /\
  ~supported_expr_exists is_self_code (Subscript rt be key) ==>
  (supported_expr tops be \/ supported_place_expr tops be \/
   supported_effect_place_expr tops be) /\
  (supported_expr tops key \/ supported_place_expr tops key \/
   supported_effect_place_expr tops key) /\
  ~supported_expr_exists is_self_code be /\
  ~supported_expr_exists is_self_code key
Proof
  simp[supported_expr_def, supported_pure_expr_def,
       supported_effect_expr_def, supported_expr_exists_def] >> metis_tac[]
QED

Theorem runtime_sym_subscript:
  runtime_sym_lower_value_clause tops /\
  (!op b s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand op /\ compile_keccak256_key op b s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) /\
  (!bop key s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand bop /\ ~is_label_operand key /\
     compile_mapping_subscript bop key s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) /\
  (!bop off s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand bop /\ compile_tuple_subscript bop off s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) /\
  (!ce loc bop idx dyn count ws sz signed s out s'.
     runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand bop /\ ~is_label_operand idx /\
     compile_array_subscript bop idx dyn count ws sz signed
       (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) ==>
  runtime_sym_subscript_clause tops
Proof
  strip_tac >> rewrite_tac[runtime_sym_subscript_clause_def] >>
  map_every qx_gen_tac [`cfn`,`ce`,`rt`,`ty`,`be`,`key`,`s`,`v`,`s'`] >> strip_tac >>
  `((supported_expr tops be \/ supported_place_expr tops be \/
     supported_effect_place_expr tops be) /\
    (supported_expr tops key \/ supported_place_expr tops key \/
     supported_effect_place_expr tops key)) /\
    ~supported_expr_exists is_self_code be /\
    ~supported_expr_exists is_self_code key` by
    metis_tac[runtime_sym_subscript_children] >>
  Cases_on `cfn ce ty be s` >>
  `EVERY runtime_sym_inst (state_insts r) /\ runtime_sym_value q` by
    (qpat_x_assum `!t. _` (qspec_then `ty` strip_assume_tac) >>
     qpat_x_assum `runtime_sym_expr_contract _ _ _ _ be` mp_tac >>
     rewrite_tac[runtime_sym_expr_contract_def] >>
     disch_then (qspecl_then [`s`,`q`,`r`] mp_tac) >>
     asm_rewrite_tac[]) >>
  drule runtime_sym_value_operand >> strip_tac >>
  qpat_x_assum `compile_subscript _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `cfn ce ty be s = _`
    (fn th => simp[NoAsms, compile_subscript_def, comp_bind_def, th]) >>
  `!kt op t. lower_value cfn ce kt key r = (op,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ ~is_label_operand op` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `runtime_sym_lower_value_clause tops` mp_tac >>
     rewrite_tac[runtime_sym_lower_value_clause_def] >>
     disch_then irule >> qexistsl [`ce`,`cfn`,`key`,`r`,`kt`] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  pop_assum (mk_asm "key_safe") >>
  (Cases_on `place_type ce be` >> simp[NoAsms]
   >- (strip_tac >> irule runtime_sym_map_sequence >>
       conj_tac >- asm_rewrite_tac[] >>
       conj_tac >- asm_rewrite_tac[] >>
       goal_assum (drule_at (Pos last)) >> asm_rewrite_tac[] >>
       asm "key_safe" (qspec_then `expr_type key` MATCH_ACCEPT_TAC)) >>
   Cases_on `t` >> simp[NoAsms] >>
   CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC HO_REWR_CONV (GSYM comp_bind_assoc))) >> strip_tac >>
   irule runtime_sym_locate_sequence >>
   goal_assum (drule_at (Pos last)) >>
   rpt gen_tac >> strip_tac
   >>~- ([`place_type ce be = ValPT (TupleT _)`], metis_tac[])
   >>~- ([`place_type ce be = ValPT (StructT _)`], metis_tac[]) >>
   irule runtime_sym_operand_sequence >>
   goal_assum (drule_at (Pos last)) >>
   (conj_tac >- (simp[NoAsms] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!ce loc bop idx dyn count ws sz signed s out s'. _`
       (drule_at (Pos last)) >> asm_rewrite_tac[]) >>
   rpt gen_tac >> strip_tac >> asm "key_safe" irule >> qexists_tac `ty` >> asm_rewrite_tac[]))
QED
