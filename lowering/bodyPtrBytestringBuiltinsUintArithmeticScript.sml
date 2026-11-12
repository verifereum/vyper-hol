Theory bodyPtrBytestringBuiltinsUintArithmetic
Ancestors
  bodyPtrBytestringBuiltinsAllocation fragGasSeqPtr typedCopyPtr
  bodyPtrDefs ptrSafeRun venomInst venomState venomExecSemantics
  ptrDiscipline finite_map words codegenRel contextCodegenRel

(* SUB retains the first operand's allocation, not merely its remaining
   forward coverage.  The allocation base is therefore explicit below. *)
Theorem pointer_sub_counted_edge:
  !D ctx func PG G tn s bb id root out a i delta.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id SUB [Var root; delta] [out]) /\
    lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
    eval_operand delta s = SOME (n2w i) /\ op_taint tn delta = {} ==>
    gas_path_ptr_edge D 0 ctx func PG G tn s 0
      (step_prov PG G (mk_inst id SUB [Var root; delta] [out])
        (update_var out (a - n2w i) s))
      (step_taint (mk_inst id SUB [Var root; delta] [out]) s
        (update_var out (a - n2w i) s) tn)
      (OK ((update_var out (a - n2w i) s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id SUB [Var root; delta] [out]) s =
    OK (update_var out (a - n2w i) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors,
       instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[GSYM mk_inst_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem pointer_sub_covers:
  !PG G tn s id root out b k total i width delta.
    lookup_var root s = SOME (n2w (b+k)) /\
    FLOOKUP G root = SOME (b,total) /\ op_taint tn (Var root) = {} /\
    eval_operand delta s = SOME (n2w i) /\ op_taint tn delta = {} /\
    i <= k /\ k <= total /\ k-i+width <= total /\
    b+total < dimword(:256) ==>
    ptr_covers
      (step_prov PG G (mk_inst id SUB [Var root; delta] [out])
        (update_var out (n2w (b+k) - n2w i) s))
      (step_taint (mk_inst id SUB [Var root; delta] [out]) s
        (update_var out (n2w (b+k) - n2w i) s) tn)
      out ((update_var out (n2w (b+k) - n2w i) s) with
        vs_inst_idx := SUC s.vs_inst_idx) width
Proof
  rpt strip_tac >>
  simp[ptr_covers_def, copy_len_binop_ghost_frame] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE, lookup_var_def,
       update_var_def] >>
  conj_tac >-
    simp[step_taint_def, set_var_taint_def, op_taint_def, out_taint_def,
         imm_taint_def, adopt_reset_def, FLOOKUP_UPDATE, eval_operand_def] >>
  `i <= b+k /\ b+k < dimword(:256) /\ b+k-i < dimword(:256)` by decide_tac >>
  simp[GSYM n2w_sub, w2n_n2w] >> decide_tac
QED

Theorem pointer_sub_ghost_frame:
  !PG G tn s id root delta out w.
    (step_taint (mk_inst id SUB [Var root;delta] [out]) s
      (update_var out w s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id SUB [Var root;delta] [out]) s
      (update_var out w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id SUB [Var root;delta] [out]) s
      (update_var out w s) tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id SUB [Var root;delta] [out]) s
      (update_var out w s) tn).t_imm = tn.t_imm /\
    op_taint (step_taint (mk_inst id SUB [Var root;delta] [out]) s
      (update_var out w s) tn) (Var out) = {} /\
    (!q. q <> out ==>
      lookup_var q ((update_var out w s) with vs_inst_idx := j) = lookup_var q s /\
      FLOOKUP (step_prov PG G (mk_inst id SUB [Var root;delta] [out])
        (update_var out w s)) q = FLOOKUP G q /\
      op_taint (step_taint (mk_inst id SUB [Var root;delta] [out]) s
        (update_var out w s) tn) (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, set_var_taint_def, op_taint_def, out_taint_def,
       mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def,
       mk_inst_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def] >>
  Cases_on `eval_operand (Var root) s` >> simp[] >> rpt strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  Cases_on `first_prov G [Var root;delta]` >>
  simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

(* These bounds validate both the decimal suffix and the initial-zero
   branch without requiring the allocation's padding to be initialized. *)
Theorem uint2str_sub_word:
  !b n i total.
    i <= n /\ n <= total /\ b+total < dimword(:256) ==>
    (n2w (b+n) - n2w i : bytes32) = n2w (b+n-i)
Proof
  rpt strip_tac >> simp[GSYM n2w_sub]
QED

Theorem uint2str_sub_buffer_bounds:
  !n i buf_size.
    i <= n ==> n-i+buf_size <= buf_size+n
Proof
  decide_tac
QED

Theorem uint2str_sub_result_covers:
  !PG G tn s id root out b n buf_size i delta.
    lookup_var root s = SOME (n2w (b+n)) /\
    FLOOKUP G root = SOME (b,buf_size+n) /\ op_taint tn (Var root) = {} /\
    eval_operand delta s = SOME (n2w i) /\ op_taint tn delta = {} /\
    i <= n /\ b+(buf_size+n) < dimword(:256) ==>
    ptr_covers
      (step_prov PG G (mk_inst id SUB [Var root;delta] [out])
        (update_var out (n2w (b+n-i)) s))
      (step_taint (mk_inst id SUB [Var root;delta] [out]) s
        (update_var out (n2w (b+n-i)) s) tn)
      out ((update_var out (n2w (b+n-i)) s) with
        vs_inst_idx := SUC s.vs_inst_idx) buf_size
Proof
  rpt strip_tac >>
  `n2w (b+n-i) = (n2w (b+n) - n2w i : bytes32)` by
    simp[GSYM n2w_sub] >>
  pop_assum SUBST1_TAC >>
  irule pointer_sub_covers >> simp[] >>
  qexists_tac `buf_size+n` >> simp[]
QED

(* Both callers use the same general result boundary. *)
Theorem uint2str_zero_sub_covers[local]:
  !PG G tn s id root out b n buf_size.
    lookup_var root s = SOME (n2w (b+n)) /\
    FLOOKUP G root = SOME (b,buf_size+n) /\ op_taint tn (Var root) = {} /\
    1 <= n /\ b+(buf_size+n) < dimword(:256) ==>
    ptr_covers
      (step_prov PG G (mk_inst id SUB [Var root;Lit 1w] [out])
        (update_var out (n2w (b+n-1)) s))
      (step_taint (mk_inst id SUB [Var root;Lit 1w] [out]) s
        (update_var out (n2w (b+n-1)) s) tn)
      out ((update_var out (n2w (b+n-1)) s) with
        vs_inst_idx := SUC s.vs_inst_idx) buf_size
Proof
  rpt strip_tac >> irule uint2str_sub_result_covers >>
  simp[eval_operand_def, op_taint_def]
QED

Theorem uint2str_suffix_sub_covers[local]:
  !PG G tn s id root out counter b n buf_size str.
    lookup_var root s = SOME (n2w (b+n)) /\
    lookup_var counter s = SOME (n2w (LENGTH (str:char list))) /\
    FLOOKUP G root = SOME (b,buf_size+n) /\
    op_taint tn (Var root) = {} /\ op_taint tn (Var counter) = {} /\
    LENGTH str <= n /\ b+(buf_size+n) < dimword(:256) ==>
    ptr_covers
      (step_prov PG G (mk_inst id SUB [Var root;Var counter] [out])
        (update_var out (n2w (b+n-LENGTH str)) s))
      (step_taint (mk_inst id SUB [Var root;Var counter] [out]) s
        (update_var out (n2w (b+n-LENGTH str)) s) tn)
      out ((update_var out (n2w (b+n-LENGTH str)) s) with
        vs_inst_idx := SUC s.vs_inst_idx) buf_size
Proof
  rpt strip_tac >> irule uint2str_sub_result_covers >>
  simp[eval_operand_def]
QED
