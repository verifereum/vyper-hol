(* Memory-checked zero-gas execution of the fitting bytestring copy suffix. *)
Theory bodyIfExpBytesCopy
Ancestors
  exprSimMemUnwrap bodyCopyMemory valueCopy bodyIfExpArmMemory

Theorem ifexp_bytes_copy_no_gas[local]:
  compile_store_bytestring src dst sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  rpt strip_tac >>
  gvs[contextTheory.compile_store_bytestring_def,
      contextTheory.compile_bytestring_copy_len_def,
      emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
      compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def,
      exprLoweringPropsTheory.emitted_insts_def, listTheory.DROP_APPEND1] >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem ifexp_bytes_copy_path_mem:
  compile_store_bytestring src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  mem_word_at (w2n a) s.vs_memory = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n a + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n b + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
    q.vs_memory = (mcopy (w2n b) (w2n a) (32 + 32 * word_size len) s).vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func q /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  rpt strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. dst = Var x ==> not_fresh_at sa x)` by metis_tac[] >>
  drule_all store_bytestring_run_exact >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_store_bytestring_body_mem_ok >>
     fs[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    metis_tac[ifexp_bytes_copy_no_gas] >>
  drule_all straight_path_mem >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[venomStateTheory.lookup_var_def] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
  simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]
QED

Theorem ifexp_copy_post_transport:
  (q with <|vs_vars := m.vs_vars; vs_inst_idx := m.vs_inst_idx|>) = m /\
  (!x. not_fresh_at cut x ==> lookup_var x q = lookup_var x m) /\
  local_ptrs_reserved cenv cut /\ origin.cs_next_var <= cut.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at cut x) /\
  expr_post ctx func cenv cx e es origin sb s0 ee v op m /\
  vv_store_bound cx (expr_type e) lt ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) m ==>
  expr_post ctx func cenv cx e es origin sb s0 ee v op q /\
  vv_store_bound cx (expr_type e) lt ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) q
Proof
  strip_tac >>
  `q = (m with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>)` by
    (qpat_x_assum `q with <|vs_vars := _; vs_inst_idx := _|> = m`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `q.vs_labels = m.vs_labels` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = m`
       (mp_tac o AP_TERM ``\s. s.vs_labels``) >> simp[]) >>
  `eval_operand op q = eval_operand op m` by
    (Cases_on `op` >> fs[venomStateTheory.eval_operand_def]) >>
  `stmt_state_rel ctx func cenv cx ee (m with vs_vars := q.vs_vars)` by
    (irule exprSimPropsTheory.stmt_state_rel_vars_frame >>
     fs[loweringPostsTheory.expr_post_def] >> rpt strip_tac >>
     fs[compileEnvTheory.local_ptrs_reserved_def,
        venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  suspend "post"
QED

Resume ifexp_copy_post_transport[post]:
  `q.vs_memory = m.vs_memory /\ q.vs_allocas = m.vs_allocas /\
   q.vs_alloca_next = m.vs_alloca_next` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = m`
       (mp_tac o AP_TERM ``\s. (s.vs_memory,s.vs_allocas,s.vs_alloca_next)``) >>
     simp[]) >>
  `!n b sz. local_region cenv ee.scopes q n b sz <=>
             local_region cenv ee.scopes m n b sz` by
    (rpt gen_tac >>
     fs[compileEnvTheory.local_region_def, compileEnvTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `(q with vs_inst_idx := m.vs_inst_idx) = (m with vs_vars := q.vs_vars)` by
    (qpat_x_assum `q with <|vs_vars := _; vs_inst_idx := _|> = m`
       (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
  `stmt_state_rel ctx func cenv cx ee q` by
    metis_tac[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  `post_value_type cenv e <> expr_type e ==>
   expr_val_own cenv cx (post_value_type cenv e) origin sb ee v op q` by
    (strip_tac >>
     `expr_val_own cenv cx (post_value_type cenv e) origin sb ee v op m` by
       (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ m` mp_tac >>
        simp[loweringPostsTheory.expr_post_def]) >>
     pop_assum mp_tac >>
     qpat_assum `eval_operand op q = _` (fn th1 =>
       qpat_assum `q.vs_allocas = _` (fn th2 =>
         qpat_assum `!n b sz. local_region _ _ q _ _ _ <=> _` (fn th3 =>
           rewrite_tac[loweringPostsTheory.expr_val_own_def, th1, th2, th3])))) >>
  reverse conj_tac
  >- (fs[exprSimMemDefsTheory.vv_store_bound_def, contextTheory.mk_ptr_def]) >>
  fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
     loweringPostsTheory.expr_val_at_def, loweringPostsTheory.locals_kept_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at cut x` by
        (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `origin` >> simp[]) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
        irule >> conj_tac >- (first_assum ACCEPT_TAC) >>
      qexists_tac `aid` >> simp[]) >>
  rpt strip_tac >> qpat_x_assum `!n b sz off len. _` irule >> metis_tac[]
QED

Finalise ifexp_copy_post_transport
