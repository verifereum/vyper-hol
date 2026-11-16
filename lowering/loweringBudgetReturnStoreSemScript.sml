(* Exact sequential semantics at every prefix of the return-word stores. *)
Theory loweringBudgetReturnStoreSem
Ancestors
  intCallResult exprLowering exprLoweringProps emitHelper emitHelperProps
  compileEnv freshWrites fragExec immutableMemoryFrame loweringStateRelDefs
  venomExecSemantics venomExecProofs venomInst venomState valueEncodingDefs
  list rich_list arithmetic

Theorem store_multi_results_code_shape:
  !ops buf_op off sa sb.
    store_multi_results buf_op ops off sa = ((),sb) ==>
    LENGTH (emitted_insts sa sb) = 2 * LENGTH ops /\
    EVERY (\i. MEM i.inst_opcode [ADD; MSTORE]) (emitted_insts sa sb)
Proof
  Induct
  >- simp[store_multi_results_def, comp_return_def, emitted_insts_refl] >>
  rpt gen_tac >>
  simp_tac bool_ss [Once store_multi_results_def, LET_THM, comp_bind_def,
                    comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE [dst; h] mid = (u,post)` >> Cases_on `u` >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule store_multi_results_shape >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `emitted_insts mid sb = emitted_insts mid post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  fs[venomInstTheory.mk_inst_def]
QED

Theorem store_multi_results_take_sem[local]:
  !ops buf_op off sa sb s b ws n.
    store_multi_results buf_op ops off sa = ((),sb) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
    eval_operand buf_op s = SOME (n2w b) /\
    MAP (\op. eval_operand op s) ops = MAP SOME ws /\
    b + off + 32 * LENGTH ops < dimword (:256) /\
    n <= 2 * LENGTH ops ==>
    ?t. run_inst_seq (TAKE n (emitted_insts sa sb)) s = OK t /\
      (!i. i < n DIV 2 ==>
        mem_word_at (b + off + 32 * i) t.vs_memory = EL i ws) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= b + off \/ b + off + 32 * (n DIV 2) <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[store_multi_results_def, comp_return_def, emitted_insts_refl,
          run_inst_seq_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `n`
  >- simp[run_inst_seq_def] >>
  qpat_x_assum `store_multi_results _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once store_multi_results_def, LET_THM, comp_bind_def,
                    comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE [dst; h] mid = (u,post)` >> Cases_on `u` >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule store_multi_results_shape >> strip_tac >>
  `emitted_insts mid sb = emitted_insts mid post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  Cases_on `n'`
  >- suspend "odd_head" >>
  suspend "complete_head"
QED

Resume store_multi_results_take_sem[odd_head]:
  `step_inst_base (mk_inst sa.cs_next_id ADD [buf_op; Lit (n2w off)]
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
          ((n2w b:bytes32) + n2w off) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  simp[run_inst_seq_def, update_var_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  simp[lookup_var_def] >>
  first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Resume store_multi_results_take_sem[complete_head]:
  Cases_on `ws` >> gvs[] >>
  rename1 `MAP (\op. eval_operand op s) ops = MAP SOME rest` >>
  rename1 `eval_operand h s = SOME x` >>
  `store_multi_results buf_op [h] off sa = ((),post)` by
    simp[store_multi_results_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  drule store_multi_results_run >>
  disch_then (qspecl_then [`s`, `b`, `[x]`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  suspend "tail_input"
QED

Resume store_multi_results_take_sem[tail_input]:
  rename1 `run_inst_seq (emitted_insts sa post) s = OK head` >>
  `(!x. buf_op = Var x ==> not_fresh_at post x) /\
   (!x. MEM (Var x) ops ==> not_fresh_at post x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `eval_operand buf_op head = SOME (n2w b)` by
    metis_tac[store_result_operand_frame] >>
  `MAP (\op. eval_operand op head) ops = MAP SOME rest` by
    (qpat_x_assum `MAP _ ops = MAP SOME _` (SUBST1_TAC o SYM) >>
     irule MAP_CONG >> simp[] >> rpt strip_tac >>
     irule store_result_operand_frame >> simp[] >> qexists_tac `sa` >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `!buf_op off sa sb s b ws n. _` drule >>
  disch_then (qspecl_then [`head`, `b`, `rest`, `n`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  suspend "join_prefix"
QED

Resume store_multi_results_take_sem[join_prefix]:
  `SUC (SUC n) DIV 2 = SUC (n DIV 2)` by
    (`SUC (SUC n) = 2 + n` by decide_tac >>
     pop_assum SUBST1_TAC >> simp[ADD_DIV_RWT, ADD1]) >>
  `emitted_insts sa post = emitted_insts sa mid ++ emitted_insts mid post` by
    (qpat_x_assum `post.cs_current_insts = _ ++ emitted_insts sa post` kall_tac >>
     irule emitted_insts_append >> simp[]) >>
  qexists_tac `t` >>
  conj_tac
  >- (qpat_x_assum `run_inst_seq (emitted_insts sa post) s = OK head`
        (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  conj_tac
  >- (Cases >> simp[]
      >- (`mem_bytes_at (b + off) 32 t.vs_memory =
           mem_bytes_at (b + off) 32 head.vs_memory` by
            (first_assum irule >> simp[]) >>
          `mem_word_at (b + off) t.vs_memory =
           mem_word_at (b + off) head.vs_memory` by
            gvs[mem_word_at_def, mem_bytes_at_def] >>
          qpat_x_assum `!i. i < LENGTH [x] ==> _`
            (qspec_then `0` mp_tac) >> simp[]) >>
      strip_tac >>
      qpat_x_assum `!i. i < n DIV 2 ==> _` (qspec_then `n'` mp_tac) >>
      simp[MULT_SUC, ADD1]) >>
  conj_tac >- fs[venom_state_component_equality] >>
  conj_tac
  >- (rpt strip_tac >> rename1 `not_fresh_at sa y` >>
      `not_fresh_at post y` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule EQ_TRANS >> qexists_tac `mem_bytes_at a len head.vs_memory` >>
  conj_tac >> first_assum irule >> simp[MULT_SUC] >> decide_tac
QED

Finalise store_multi_results_take_sem

Theorem store_multi_results_take_run:
  !ops buf_op off sa sb s b ws n.
    store_multi_results buf_op ops off sa = ((),sb) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
    eval_operand buf_op s = SOME (n2w b) /\
    MAP (\op. eval_operand op s) ops = MAP SOME ws /\
    b + off + 32 * LENGTH ops < dimword (:256) /\
    n <= 2 * LENGTH ops ==>
    LENGTH (emitted_insts sa sb) = 2 * LENGTH ops /\
    EVERY (\i. MEM i.inst_opcode [ADD; MSTORE]) (emitted_insts sa sb) /\
    ?t. run_inst_seq (TAKE n (emitted_insts sa sb)) s = OK t /\
      (!i. i < n DIV 2 ==>
        mem_word_at (b + off + 32 * i) t.vs_memory = EL i ws) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= b + off \/ b + off + 32 * (n DIV 2) <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all store_multi_results_take_sem >>
  drule store_multi_results_code_shape >> simp[]
QED
