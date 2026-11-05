(* Memory-safe account-read suffixes. *)
Theory bodyMemBiAccFrag
Ancestors
  bodyUnopFragMemory exprSimUnopProps fragExec bodyMemEmitOpFrame bodyDeclMemoryCounted bodyDeclMemoryCore
  exprSimAccounts allocaFootprint instMemFrontier memSafeRun fragGasPathMem
  stmtSimProps emitHelperProps freshWrites exprOperandVar exprLoweringProps
  fragGasMode compileEnv venomExecSemantics venomExecProofs venomInst venomState
  list finite_map exprSimUnop exprUnopSimDefs accountsRelProps
  valueEncodingProofs vyperInterpreter vyperTypeInvariants vyperTypeBytesCrypto
  vfmState integer_word words byte builtinSimple vyperTypeSystem
  valueEncoding exprSimDefs vyperContext

(* Account-read counterpart of bodyMemEmitOpFrame.emit_op_word_path_frame_mem. *)
Theorem emit_acc_path_frame_mem:
  !opc args sa op sb w s0 ctx func cenv cx es.
    emit_op opc args sa = (op,sb) /\
    (opc = BALANCE \/ opc = EXTCODESIZE \/ opc = EXTCODEHASH) /\
    step_inst_base
      (mk_inst sa.cs_next_id opc args [STRING #"%" (toString sa.cs_next_var)])
      s0 = OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s0) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    alloca_history func s0 ==>
    ?t. gas_marked_path T ctx func s0 0 (OK t) /\
      eval_operand op t = SOME w /\
      stmt_state_rel ctx func cenv cx es t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      local_ptrs_reserved cenv sb /\ alloca_history func t /\
      (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
      t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
      sa.cs_next_var <= sb.cs_next_var /\
      (?out. op = Var out /\ not_fresh_at sb out) /\
      t = (update_var (STRING #"%" (toString sa.cs_next_var)) w s0
        with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc` by
    simp[is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    (drule emit_op_mem_ok >> disch_then irule >>
     simp[below_frontier_no_ranges, mk_inst_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `run_inst_seq (emitted_insts sa sb) s0 = OK (update_var out w s0)` by
    gvs[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx func s0 0
     (OK (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~(update_var out w s0).vs_halted /\
   (update_var out w s0).vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `alloca_history func
     (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s0`, `sa`] >> simp[mk_inst_def, is_terminator_def]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (update_var out w s0)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  qexists_tac `update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, eval_operand_def] >>
  gvs[update_var_def] >>
  simp[Abbr `out`, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem unop_frag_mem_read_then:
  !ctx func cenv cx opc g w1 r t v w es0.
    (opc = BALANCE \/ opc = EXTCODESIZE \/ opc = EXTCODEHASH) /\
    is_word_type t /\ (!c. straight_fresh (g c)) /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          w = typed_val_to_w256 tv v) /\
    (!x ss n out.
       eval_operand x ss = SOME w1 /\ stmt_state_rel ctx func cenv cx es0 ss ==>
       step_inst_base (mk_inst n opc [x] [out]) ss =
         OK (update_var out r ss)) /\
    (!c sa sb op ss.
       g c sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       eval_operand c ss = SOME r ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
             eval_operand op ss' = SOME w) ==>
    unop_frag_mem ctx func cenv cx (\x. comp_bind (emit_op opc [x]) g) w1 t
      (INL v) es0
Proof
  rpt gen_tac >> strip_tac >>
  `unop_frag_mem ctx func cenv cx g r t (INL v) es0` by
    (irule unop_frag_mem_straight >> simp[] >> strip_tac >>
     qexists_tac `w` >> simp[] >> metis_tac[]) >>
  simp[unop_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >> simp[comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op _ [x] sa = (c, s1)` >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
    metis_tac[straight_fresh_cs_extends] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `?u. gas_marked_path T ctx func s0 0 (OK u) /\
      eval_operand c u = SOME r /\
      stmt_state_rel ctx func cenv cx es0 u /\
      ~u.vs_halted /\ u.vs_current_bb = s1.cs_current_bb /\
      u.vs_inst_idx = LENGTH s1.cs_current_insts /\
      local_ptrs_reserved cenv s1 /\ alloca_history func u /\
      (!rp. not_fresh_at sa rp ==> lookup_var rp u = lookup_var rp s0) /\
      u.vs_allocas = s0.vs_allocas /\ u.vs_alloca_next = s0.vs_alloca_next /\
      (?out. c = Var out /\ not_fresh_at s1 out) /\
      u.vs_memory = s0.vs_memory` by
    (drule emit_acc_path_frame_mem >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     disch_then (qspec_then `r` mp_tac) >> simp[] >>
     (impl_tac >- (qpat_x_assum `!x ss n out. _ ==> step_inst_base _ _ = _` mp_tac >> simp[] >>
                  disch_then irule >> simp[])) >>
     strip_tac >>
     qexists_tac `update_var (STRING #"%" (toString sa.cs_next_var)) r s0
                    with vs_inst_idx := LENGTH s1.cs_current_insts` >>
     gvs[update_var_def, eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `unop_frag_mem _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[unop_frag_mem_def] >>
  disch_then (qspecl_then [`s1`, `sb`, `c`, `op`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
    metis_tac[not_fresh_at_mono] >>
  (qexists_tac `OK s` >> conj_tac
   >- (`gas_marked_path T ctx func s0 (0 + 0) (OK s)` suffices_by simp[] >>
       irule gas_marked_path_then >> qexists_tac `u` >> gvs[]) >>
   simp[] >> rpt strip_tac >>
   qpat_x_assum `!z w. not_fresh_at s1 z /\ _ ==> _` irule >>
   simp[])
QED

Theorem unop_frag_mem_read:
  !ctx func cenv cx opc w1 r t v es0.
    (opc = BALANCE \/ opc = EXTCODESIZE \/ opc = EXTCODEHASH) /\
    is_word_type t /\
    (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
          r = typed_val_to_w256 tv v) /\
    (!x ss n out.
       eval_operand x ss = SOME w1 /\ stmt_state_rel ctx func cenv cx es0 ss ==>
       step_inst_base (mk_inst n opc [x] [out]) ss =
         OK (update_var out r ss)) ==>
    unop_frag_mem ctx func cenv cx (\x. emit_op opc [x]) w1 t (INL v) es0
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[GSYM comp_bind_comp_return] >>
  irule unop_frag_mem_read_then >> simp[straight_fresh_return] >>
  qexists_tac `r` >>
  simp[comp_return_def, emitted_insts_refl, run_inst_seq_def] >>
  qexists_tac `r` >> simp[]
QED

Theorem compile_acc_frag_mem:
  !ctx func cenv cx item bs es0.
    item <> Code /\ LENGTH bs = 20 /\ accounts_well_typed es0.accounts ==>
    unop_frag_mem ctx func cenv cx
      (\x. case item of
             Balance => emit_op BALANCE [x]
           | Codesize => emit_op EXTCODESIZE [x]
           | Codehash => emit_op EXTCODEHASH [x]
           | IsContract =>
               comp_bind (emit_op EXTCODESIZE [x])
                 (\c. emit_op GT [c; Lit 0w])
           | Address => comp_return x
           | Code => comp_return x)
      (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
      (account_item_type item)
      (unop_result cx (account_item_type item) (Acc item) [BaseT AddressT]
         (BytesV bs) es0) es0
Proof
  rpt strip_tac >>
  simp[unop_result_def, evaluate_builtin_def] >>
  qabbrev_tac `a = lookup_account (word_of_bytes_be bs) es0.accounts` >>
  `a.balance < 2 ** 256 /\ LENGTH a.code <= 24576` by
    gvs[Abbr `a`, accounts_well_typed_def, account_well_typed_def] >>
  drule address_word_w2w >> strip_tac >>
  Cases_on `item` >> gvs[]
  >~ [`comp_return`]
  >- (irule unop_frag_mem_straight >>
      simp[account_item_type_def, vyperValueTheory.evaluate_type_def,
           evaluate_account_op_def, is_word_type_def, straight_fresh_return,
           comp_return_def, emitted_insts_refl, run_inst_seq_def, expr_res_ok_def])
  >~ [`comp_bind`]
  >- (irule unop_frag_mem_read_then >>
      simp[account_item_type_def, vyperValueTheory.evaluate_type_def,
           evaluate_account_op_def, is_word_type_def, is_terminator_def,
           typed_val_to_w256_def, val_to_w256_def, straight_fresh_emit_op,
           fresh_write_op_def] >>
      qexists_tac `n2w (LENGTH a.code)` >>
      rpt strip_tac
      >~ [`step_inst_base`]
      >- (`!addr. (lookup_account addr ss.vs_accounts).code =
                  (lookup_account addr es0.accounts).code` by
            (fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
             metis_tac[accounts_agree_lookup]) >>
          gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
              typed_val_to_w256_def, Abbr `a`]) >>
      drule emit_op_GT_correct >>
      disch_then (qspecl_then [`n2w (LENGTH a.code)`, `0w`, `ss`] mp_tac) >>
      impl_tac >- gvs[eval_operand_def] >>
      strip_tac >> gvs[] >>
      `LENGTH a.code < dimword (:256)` by fs[dimword_def] >>
      Cases_on `a.code` >> gvs[bool_to_word_def]) >>
  irule unop_frag_mem_read >>
  simp[account_item_type_def, vyperValueTheory.evaluate_type_def,
       evaluate_account_op_def, is_word_type_def, is_terminator_def] >>
  rpt strip_tac >>
  `!addr. (lookup_account addr ss.vs_accounts).balance =
          (lookup_account addr es0.accounts).balance /\
          (lookup_account addr ss.vs_accounts).code =
          (lookup_account addr es0.accounts).code /\
          (lookup_account addr ss.vs_accounts).nonce =
          (lookup_account addr es0.accounts).nonce` by
    (fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
     metis_tac[accounts_agree_lookup]) >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, Abbr `a`] >>
  simp[typed_val_to_w256_def, val_to_w256_def, i2w_def] >>
  rw[PAD_RIGHT, LENGTH_Keccak_256_w64, word_of_bytes_be_def,
     word_of_bytes_replicate_zero] >>
  gvs[vfmStateTheory.account_empty_def]
QED
