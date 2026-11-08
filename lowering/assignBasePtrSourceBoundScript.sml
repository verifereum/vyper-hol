(* A bounded test of the exported expression-post interface, not of execution. *)
Theory assignBasePtrSourceBound
Ancestors bodyPtrDefs loweringPosts exprLoweringProps compileEnv exprLowering
  valueEncoding venomState ptrDiscipline words finite_map vyperTyping vyperValue valueEncodingProofs exprSimProps vyperAST vyperState vyperContext accountsRelProps
  fcgDefs relation venomMemDefs pred_set venomInst list

(* Identity framing isolates the substantive placement and state relation
   obligations; no execution claim is made here. *)
Theorem assign_base_ptr_identity_post:
  !ctx func cenv cx e es sa sb s v op.
    stmt_state_rel ctx func cenv cx es s /\
    post_value_type cenv e = expr_type e /\
    expr_val_rel cx (expr_type e) v op s /\
    expr_val_at cenv cx (expr_type e) sa sb es v op s ==>
    expr_post ctx func cenv cx e es sa sb s es v op s
Proof
  simp[expr_post_def, locals_kept_def]
QED

Theorem assign_base_ptr_empty_bytes_placement:
  !cenv cx es sa sb s.
    lookup_var "p" s = SOME (n2w (dimword(:256)-64)) /\
    FLOOKUP s.vs_allocas 0 = SOME (dimword(:256)-64,32) /\
    sa.cs_next_id = 0 /\ sb.cs_next_id = 1 /\
    (!n b sz. ~local_region cenv es.scopes s n b sz) ==>
    expr_val_at cenv cx (BaseT (BytesT (Dynamic 64))) sa sb es
      (BytesV []) (Var "p") s
Proof
  rpt strip_tac >>
  simp[expr_val_at_def, evaluate_type_def, is_word_type_def,
       val_wf_def, val_footprint_def, eval_operand_def] >>
  EVAL_TAC
QED

Theorem assign_base_ptr_clean_memory_word:
  !mem mem' a.
    mem_agree_outside {} mem mem' ==>
    mem_word_at a mem' = mem_word_at a mem
Proof
  rpt strip_tac >> fs[mem_agree_outside_def] >>
  `mem_bytes_at a 32 mem' = mem_bytes_at a 32 mem` by
    (irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >>
     rpt strip_tac >>
     first_x_assum (qspec_then `a + x` mp_tac) >>
     disch_then (mp_tac o Q.AP_TERM `EL 0`) >>
     simp[EL_mem_bytes_at]) >>
  gvs[mem_word_at_def, mem_bytes_at_def]
QED

Theorem assign_base_ptr_empty_bytes_value:
  !cx s G.
    lookup_var "p" s = SOME (n2w (dimword(:256)-64)) /\
    mem_word_at (dimword(:256)-64) s.vs_memory = 0w /\
    FLOOKUP G "p" = SOME (dimword(:256)-64,96) ==>
    ptr_val_ok cx (BaseT (BytesT (Dynamic 64))) (BytesV [])
      (Var "p") G entry_taint s
Proof
  rpt strip_tac >>
  simp[ptr_val_ok_def, is_word_type_def, ptr_mem_ok_def, op_taint_def, entry_taint_def,
       evaluate_type_def, eval_operand_def, val_footprint_def,
       val_store_size_def, w2n_n2w, dimword_def] >>
  rpt strip_tac
  >- (drule assign_base_ptr_clean_memory_word >>
      disch_then (qspec_then `dimword(:256)-64` mp_tac) >>
      simp[val_in_memory_def, mem_bytes_at_def, dimword_def]) >>
  EVAL_TAC
QED

(* Conditional diagnostic only: the existence of this entire state relation
   at the indicated address remains to be checked. *)
Theorem assign_base_ptr_source_bound_conditional:
  !ctx func cenv cx es s.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_var "p" s = SOME (n2w (dimword(:256)-64)) /\
    mem_word_at (dimword(:256)-64) s.vs_memory = 0w /\
    FLOOKUP s.vs_allocas 0 = SOME (dimword(:256)-64,32) /\
    (!n b sz. ~local_region cenv es.scopes s n b sz) ==>
    ?e sa sb G tn v op w off tv.
      expr_post ctx func cenv cx e es sa sb s es v op s /\
      ptr_val_ok cx (expr_type e) v op G tn s /\
      ptr_buf_ok cenv e op G s /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) /\ eval_operand op s = SOME w /\
      off < type_memory_bytes cenv (lowered_value_type cenv e) /\
      ~(w2n w + off < dimword(:256))
Proof
  rpt strip_tac >>
  qexistsl [`Name (BaseT (BytesT (Dynamic 64))) "x"`,
            `ARB with cs_next_id := 0`, `ARB with cs_next_id := 1`,
            `FEMPTY |+ ("p",(dimword(:256)-64,96))`, `entry_taint`,
            `BytesV []`, `Var "p"`, `n2w (dimword(:256)-64)`, `64`,
            `BaseTV (BytesT (Dynamic 64))`] >>
  conj_tac
  >- (irule assign_base_ptr_identity_post >> simp[expr_type_def] >>
      conj_tac >- gvs[expr_val_rel_def, eval_operand_def, evaluate_type_def,
                       is_word_type_def, val_in_memory_def, mem_bytes_at_def,
                       w2n_n2w, dimword_def] >>
      irule assign_base_ptr_empty_bytes_placement >> simp[]) >>
  conj_tac
  >- (simp[expr_type_def] >> irule assign_base_ptr_empty_bytes_value >> simp[FLOOKUP_UPDATE]) >>
  simp[ptr_buf_ok_def, eval_operand_def, expr_type_def, evaluate_type_def,
       is_word_type_def, lowered_value_type_def, type_memory_bytes_def,
       type_memory_size_def, w2n_n2w, dimword_def, FLOOKUP_UPDATE] >> EVAL_TAC
QED


(* Field interface: ordinary source matching is independent of allocation
   bookkeeping when there are no locals or module declarations. *)
Theorem assign_base_ptr_empty_state_rel:
  !func cenv cx es s.
    cenv.ce_vars = FEMPTY /\ cenv.ce_module_vars = FEMPTY /\
    cx.sources = [] /\ es.scopes = [] /\
    es.logs = [] /\ s.vs_logs = [] /\
    es.requests = [] /\ s.vs_requests = [] /\
    es.pending_deletions = [] /\ s.vs_pending_deletions = [] /\
    es.outcomes = SOME s.vs_outcomes /\
    s.vs_accounts = es.accounts /\ s.vs_transient = es.tStorage /\
    call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx /\
    ~s.vs_call_ctx.cc_static /\ ~cx.txn.is_static ==>
    state_rel func cenv cx es s
Proof
  rpt strip_tac >>
  simp[state_rel_def, local_ptrs_rel_def, local_region_def,
       lookup_scopes_def, storage_vars_rel_def, transient_vars_rel_def,
       immutables_rel_def, logs_rel_def, accounts_rel_def,
       get_module_code_def] >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by gvs[call_ctx_rel_def] >>
  `accounts_rel cx es s` by simp[accounts_rel_def] >>
  drule_all accounts_rel_storage_transient >> simp[]
QED

Theorem assign_base_ptr_call_context_exists:
  !tx. tx_env_ok tx ==>
    ?cc tc bc. call_ctx_rel tx cc tc bc /\ ~cc.cc_static
Proof
  rpt strip_tac >>
  qexistsl [`ARB with <| cc_caller := tx.sender; cc_address := tx.target;
              cc_callvalue := n2w tx.value; cc_calldata := tx.calldata;
              cc_static := F |>`,
    `ARB with <| tc_origin := tx.origin; tc_gasprice := n2w tx.gas_price;
              tc_chainid := n2w tx.chain_id; tc_blobhashes := tx.blob_hashes |>`,
    `ARB with <| bc_coinbase := tx.coinbase; bc_timestamp := n2w tx.time_stamp;
              bc_number := n2w tx.block_number; bc_prevrandao := n2w tx.prev_randao;
              bc_gaslimit := n2w tx.gas_limit; bc_basefee := n2w tx.base_fee;
              bc_blobbasefee := n2w tx.blob_base_fee;
              bc_blockhash := (\n. if n < tx.block_number /\
                  tx.block_number - 256 <= n /\
                  tx.block_number - n - 1 < LENGTH tx.block_hashes
                then EL (tx.block_number - n - 1) tx.block_hashes else 0w) |>`] >>
  simp[call_ctx_rel_def]
QED

Theorem assign_base_ptr_ordinary_state_exists:
  !func mem vars allocas frontier.
    ?cenv cx es s.
      state_rel func cenv cx es s /\
      ~cenv.ce_is_ctor /\ cenv.ce_imm_alloca = NONE /\ es.scopes = [] /\
      s.vs_memory = mem /\ s.vs_vars = vars /\
      s.vs_allocas = allocas /\ s.vs_alloca_next = frontier
Proof
  rpt gen_tac >>
  qabbrev_tac `tx = ARB with <|is_static := F; block_number := 1;
                              block_hashes := [0w]|>` >>
  `tx_env_ok tx` by (simp[Abbr `tx`, tx_env_ok_def] >> EVAL_TAC) >>
  drule assign_base_ptr_call_context_exists >>
  disch_then (qx_choose_then `cc` (qx_choose_then `tc`
    (qx_choose_then `bc` strip_assume_tac))) >>
  qexistsl [`ARB with <|ce_vars := FEMPTY; ce_module_vars := FEMPTY;
                       ce_is_ctor := F; ce_imm_alloca := NONE|>`,
    `ARB with <|sources := []; txn := tx|>`,
    `ARB with <|scopes := []; logs := []; requests := [];
                pending_deletions := []; outcomes := SOME []|>`,
    `ARB with <|vs_memory := mem; vs_vars := vars; vs_allocas := allocas;
                vs_alloca_next := frontier; vs_accounts := (ARB:evaluation_state).accounts;
                vs_transient := (ARB:evaluation_state).tStorage; vs_logs := []; vs_requests := [];
                vs_pending_deletions := []; vs_outcomes := [];
                vs_call_ctx := cc; vs_tx_ctx := tc; vs_block_ctx := bc|>`] >>
  simp[] >> irule assign_base_ptr_empty_state_rel >>
  gvs[Abbr `tx`, call_ctx_rel_def]
QED

Theorem assign_base_ptr_empty_calls:
  !ctx. EVERY (\f. f.fn_blocks = []) ctx.ctx_functions ==>
    !a b. ~TC (fn_directly_calls ctx) a b
Proof
  gen_tac >> strip_tac >>
  `!a b. ~fn_directly_calls ctx a b` by
    (simp[fn_directly_calls_def] >> rpt strip_tac >>
     drule lookup_function_MEM >> strip_tac >>
     fs[EVERY_MEM] >> res_tac >>
     gvs[fn_insts_def, fn_insts_blocks_def]) >>
  simp[Once TC_CASES1]
QED

Theorem assign_base_ptr_empty_room:
  !func ctx s.
    func.fn_blocks = [] /\ ctx.ctx_functions = [func] /\
    s.vs_alloca_next < dimword(:256) ==>
    alloca_room ctx func s /\ fmp_room ctx func s
Proof
  rpt strip_tac >>
  `!a b. ~TC (fn_directly_calls ctx) a b` by
    (irule assign_base_ptr_empty_calls >> simp[]) >>
  simp[alloca_room_def, fmp_room_def, pending_alloca_size_def,
       fn_insts_def, fn_insts_blocks_def, lookup_function_def, FIND_thm]
QED

Theorem assign_base_ptr_empty_stmt_state:
  !ctx func cenv cx es s.
    state_rel func cenv cx es s /\
    func.fn_blocks = [] /\ ctx.ctx_functions = [func] /\
    ~cenv.ce_is_ctor /\ cenv.ce_imm_alloca = NONE /\
    s.vs_allocas = FEMPTY |+ (0,(dimword(:256)-64,32)) /\
    s.vs_alloca_next = dimword(:256)-32 ==>
    stmt_state_rel ctx func cenv cx es s
Proof
  rpt strip_tac >>
  `alloca_room ctx func s /\ fmp_room ctx func s` by
    (irule assign_base_ptr_empty_room >> simp[dimword_def]) >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_base_zero_def,
       fn_insts_def, fn_insts_blocks_def] >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       FLOOKUP_UPDATE, dimword_def] >> rpt strip_tac >> gvs[]
QED

Theorem assign_base_ptr_source_bound_state_exists:
  ?ctx func cenv cx es s.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_var "p" s = SOME (n2w (dimword(:256)-64)) /\
    mem_word_at (dimword(:256)-64) s.vs_memory = 0w /\
    FLOOKUP s.vs_allocas 0 = SOME (dimword(:256)-64,32) /\
    (!n b sz. ~local_region cenv es.scopes s n b sz)
Proof
  qabbrev_tac `func = (ARB:ir_function) with fn_blocks := []` >>
  qspecl_then [`func`, `[]`, `FEMPTY |+ ("p",n2w (dimword(:256)-64))`,
    `FEMPTY |+ (0,(dimword(:256)-64,32))`, `dimword(:256)-32`]
    strip_assume_tac assign_base_ptr_ordinary_state_exists >>
  qexistsl [`ARB with ctx_functions := [func]`, `func`, `cenv`, `cx`, `es`, `s`] >>
  conj_tac
  >- (irule assign_base_ptr_empty_stmt_state >> simp[Abbr `func`]) >>
  simp[lookup_var_def, FLOOKUP_UPDATE, local_region_def, lookup_scopes_def,
       mem_word_at_def, mem_bytes_at_def, dimword_def] >> EVAL_TAC >> simp[]
QED

(* The full exported expression post does not entail whole-buffer no-wrap.
   This remains an interface counterexample, not a statement execution. *)
Theorem assign_base_ptr_source_bound_counterexample:
  ?ctx func cenv cx es s e sa sb G tn v op w off tv.
    expr_post ctx func cenv cx e es sa sb s es v op s /\
    ptr_val_ok cx (expr_type e) v op G tn s /\
    ptr_buf_ok cenv e op G s /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ eval_operand op s = SOME w /\
    off < type_memory_bytes cenv (lowered_value_type cenv e) /\
    ~(w2n w + off < dimword(:256))
Proof
  strip_assume_tac assign_base_ptr_source_bound_state_exists >>
  drule_all assign_base_ptr_source_bound_conditional >>
  metis_tac[]
QED
