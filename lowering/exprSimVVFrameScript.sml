(* Value judgments across variable-only target state updates. *)
Theory exprSimVVFrame
Ancestors
  context
  exprLowering
  exprSimProps exprSimDefs loweringPosts freshWrites exprLoweringProps
  compileEnv venomState venomExecSemantics valueEncoding
  vyperState vyperValue words list finite_map



Theorem storage_holds_inst_idx[local]:
  storage_holds cx tr t tv w es (s with vs_inst_idx := n) <=>
  storage_holds cx tr t tv w es s
Proof
  simp[storage_holds_def, venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def]
QED

Theorem vv_post_inst_idx[simp]:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv (s with vs_inst_idx := n) <=>
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s
Proof
  Cases_on `vv` >>
  simp[vv_post_def, stmt_state_rel_inst_idx, vv_holds_def, vv_at_def, vv_own_def,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def, lookup_var_def, local_region_def,
       storage_holds_inst_idx, immutable_holds_def]
QED

Theorem literal_operand_frame:
  !op sa s t.
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s
Proof
  rpt strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
       (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  Cases_on `op` >> simp[eval_operand_def]
QED

Theorem vv_holds_vars_frame:
  vv_holds cenv cx ty tv vv es s /\ t.vs_memory = s.vs_memory /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s ==>
  vv_holds cenv cx ty tv vv es t
Proof
  Cases_on `vv` >>
  simp[vv_holds_def, vv_operand_def, expr_val_rel_def, storage_holds_def] >>
  rpt strip_tac >> gvs[] >> BasicProvers.every_case_tac >> gvs[] >>
  metis_tac[immutable_holds_memory_cong]
QED

Theorem vv_at_vars_frame:
  vv_at cenv cx ty sa sm es tv vv s /\
  t.vs_allocas = s.vs_allocas /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
    local_region cenv es.scopes t n b sz) /\
  (!n b sz. local_region cenv es.scopes t n b sz ==>
    local_region cenv es.scopes s n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_at cenv cx ty sa sn es tv vv t
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_operand_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
        rpt strip_tac >>
        `local_region cenv es.scopes s n lb lsz` by metis_tac[] >>
        qpat_x_assum `!n lb lsz. local_region _ _ s _ _ _ ==> b + sz <= lb \/ _` drule >> simp[])
  >>~- ([`local_region cenv es.scopes s n b sz`],
        disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[])
  >> metis_tac[]
QED

Theorem vv_own_vars_frame:
  vv_own cenv cx ty sa sm es tv vv s /\
  t.vs_allocas = s.vs_allocas /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes t n b sz ==>
    local_region cenv es.scopes s n b sz) /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_own cenv cx ty sa sn es tv vv t
Proof
  Cases_on `vv` >>
  simp[vv_own_def, vv_operand_def, expr_val_own_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
        rpt strip_tac >>
        `local_region cenv es.scopes s n lb lsz` by metis_tac[] >>
        qpat_x_assum `!n lb lsz. local_region _ _ s _ _ _ ==> b + sz <= lb \/ _` drule >> simp[])
  >> metis_tac[]
QED

Theorem vv_post_vars_frame:
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  (t with vs_vars := s.vs_vars) = s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  local_ptrs_reserved cenv sa /\ sm.cs_next_id <= sn.cs_next_id /\
  stmt_state_rel ctx func cenv cx es' t ==>
  vv_post ctx func cenv cx e es sa sn s0 es' tv vv t
Proof
  strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with vs_vars := _ = s`
      (mp_tac o AP_TERM ``\z. (z.vs_memory,z.vs_allocas)``) >> simp[]) >>
  `contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    (qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
     simp[contract_storage_def, contract_transient_def]) >>
  qpat_x_assum `vv_post ctx _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv es' t` by
    (drule_all vv_holds_vars_frame >> simp[]) >>
  `vv_at cenv cx (post_value_type cenv e) sa sn es' tv vv t` by
    (irule vv_at_vars_frame >> qexistsl_tac [`s`, `sm`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> irule local_region_frame_fwd >>
         qexistsl_tac [`s`, `sa`, `es'.scopes`] >> asm_rewrite_tac[]) >>
     rpt strip_tac >> irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `es'.scopes`, `t`] >> asm_rewrite_tac[]) >>
  `post_value_type cenv e <> expr_type e ==>
   vv_own cenv cx (post_value_type cenv e) sa sn es' tv vv t` by
    (strip_tac >> irule vv_own_vars_frame >> qexistsl_tac [`s`, `sm`] >>
     simp[] >> rpt strip_tac >> irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `es'.scopes`, `t`] >> asm_rewrite_tac[]) >>
  `locals_kept cenv es es' s0 t` by
    (irule locals_kept_mem_tail >> qexists_tac `s` >> asm_rewrite_tac[]) >>
  `vv_storage_live cx vv es' s ==> vv_storage_live cx vv es' t` by
    (Cases_on `vv` >> fs[contextTheory.vv_operand_def]) >>
  pure_rewrite_tac[vv_post_def] >> asm_rewrite_tac[] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem vv_post_update_var:
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_id <= sn.cs_next_id /\ ~not_fresh_at sm x /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) ==>
  vv_post ctx func cenv cx e es sa sn s0 es' tv vv (update_var x w s)
Proof
  strip_tac >>
  `!z. not_fresh_at sm z ==> z <> x` by metis_tac[] >>
  `!z. not_fresh_at sa z ==> z <> x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (vv_operand vv) (update_var x w s) =
   eval_operand (vv_operand vv) s` by
    (irule literal_operand_frame >>
     reverse conj_tac >- simp[update_var_def] >>
     qexists_tac `sm` >>
     simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `stmt_state_rel ctx func cenv cx es' (update_var x w s)` by
    (irule exprLoweringPropsTheory.stmt_state_rel_update_var >>
     gvs[vv_post_def, not_local_ptr_def, local_ptrs_reserved_def] >>
     metis_tac[]) >>
  irule vv_post_vars_frame >> asm_rewrite_tac[] >>
  qexistsl_tac [`s`, `sm`] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
