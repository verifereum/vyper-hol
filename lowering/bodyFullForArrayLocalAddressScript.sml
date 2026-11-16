(* Concrete local-array address execution. The endpoint and ghosts do not
   depend on either the dead mask or the finite horizon. *)
Theory bodyFullForArrayLocalAddress
Ancestors typedCopyLoopHeaderPtr typedCopyPtr fragGasSeqPtr exprLoweringProps instSeqPtrLo
  assignBasePtrOffset bodyPtrDefs arithmetic vyperAST words finite_map venomExecSemantics venomState
  venomInst ptrDiscipline ptrSafeRun

Theorem local_address_arith_step[local]:
  (opc = MUL \/ opc = ADD) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [a;b] [out]) s /\
  step_inst_base (mk_inst id opc [a;b] [out]) s =
    OK (update_var out (if opc = MUL then x*y else x+y) s) /\
  step_prov PG G (mk_inst id opc [a;b] [out])
    (update_var out (if opc = MUL then x*y else x+y) s) =
    set_prov G [out] (if opc = MUL then NONE else first_prov G [a;b]) /\
  step_taint (mk_inst id opc [a;b] [out]) s
    (update_var out (if opc = MUL then x*y else x+y) s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst_base (mk_inst id opc [a;b] [out]) s =
    OK (update_var out (if opc = MUL then x*y else x+y) s)` by
    (gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]) >>
  conj_tac
  >- (Cases_on `opc = MUL` >> gvs[]
      >- (irule typed_copy_loop_test_check >> simp[update_var_def] >>
          metis_tac[]) >>
      irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  simp[] >>
  `new_site_bytes s (update_var out (if opc = MUL then x*y else x+y) s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, out_taint_def]
QED

Theorem local_address_add_ghost[local]:
  step_prov PG G (mk_inst id ADD [left;right] [out]) (update_var out w s) =
    set_prov G [out] (first_prov G [left;right]) /\
  step_taint (mk_inst id ADD [left;right] [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, out_taint_def] >>
  Cases_on `eval_operand left s` >> simp[]
QED

Theorem for_array_local_address_checked_full:
  !bd bytes k idx ap ov tov ep j3 joff j4 wa az tv v s G tn lo ctx func PG
    code header.
  code = [mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov]] ++
    (case bd of Fixed n => [] | Dynamic n =>
       [mk_inst joff ADD [Lit 32w;Var ov] [tov]]) ++
    [mk_inst j4 ADD [Var ap;(case bd of Fixed n => Var ov |
                                             Dynamic n => Var tov)] [ep]] /\
  header = (case bd of Fixed n => 0 | Dynamic n => 32) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var ap s = SOME wa /\
  FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
  ptr_covers G tn ap s az /\ ALL_DISTINCT [idx;ov;ep] /\
  ap <> ov /\ ap <> ep /\
  (bd = Dynamic (bound_length bd) ==>
     ALL_DISTINCT [idx;ov;tov;ep] /\ ap <> tov) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  w2n wa + az < dimword (:256) /\ header + k * bytes + bytes <= az /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n wa + header + k * bytes) mem) ==>
  ?sf Gf tf.
    run_inst_seq code s = OK sf /\
    (!D. inst_seq_ptr D lo ctx func PG G tn code s Gf tf) /\
    lookup_var ep sf = SOME (wa + n2w (header + k * bytes)) /\
    FLOOKUP Gf ep = FLOOKUP G ap /\ op_taint tf (Var ep) = {} /\
    ptr_covers Gf tf ep sf bytes /\
    (!mem. mem_agree_outside tf.t_mem sf.vs_memory mem ==>
      val_in_memory tv v (w2n (wa + n2w (header + k * bytes))) mem) /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_current_bb = s.vs_current_bb /\ sf.vs_halted = s.vs_halted /\
    sf.vs_requests = s.vs_requests /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_immutables = s.vs_immutables /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. ~MEM x (case bd of Fixed n => [ov;ep] | Dynamic n => [ov;tov;ep]) ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `op_taint tn (Var ap) = {}` by fs[ptr_covers_def] >>
  `w2n wa + (header + k * bytes) < dimword (:256)` by decide_tac >>
  `header + k * bytes < dimword (:256)` by decide_tac >>
  `w2n (wa + n2w (header + k * bytes)) = w2n wa + header + k * bytes` by
    simp[w2n_add_2, w2n_n2w, LESS_MOD] >>
  `!D. ptr_inst_ok D 0 0 ctx func G tn
       (mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov]) s` by
    (gen_tac >> irule (cj 1 local_address_arith_step) >>
     fs[eval_operand_def, op_taint_def]) >>
  `step_inst_base (mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov]) s =
       OK (update_var ov (n2w (k * bytes)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         eval_operand_def, word_mul_n2w] >>
  `step_prov PG G (mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov])
       (update_var ov (n2w (k * bytes)) s) = DRESTRICT G (COMPL {ov}) /\
   step_taint (mk_inst j3 MUL [Var idx;Lit (n2w bytes)] [ov]) s
       (update_var ov (n2w (k * bytes)) s) tn =
       (tn with t_var := tn.t_var |+ (ov,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >>
     fs[update_var_def, op_taint_def, DISJ_IMP_THM, FORALL_AND_THM]) >>
  Cases_on `bd` >> gvs[]
  >- suspend "fixed"
  >> suspend "dynamic"
QED

Resume for_array_local_address_checked_full[fixed]:
  qexistsl [
        `update_var ep (wa + n2w (k * bytes))
           (update_var ov (n2w (k * bytes)) s)`,
        `set_prov (DRESTRICT G (COMPL {ov})) [ep] (FLOOKUP G ap)`,
        `tn with t_var := (tn.t_var |+ (ov,{})) |+ (ep,{})`] >>
      conj_tac
      >- fs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
              exec_pure2_def, eval_operand_def, update_var_def, lookup_var_def,
              FLOOKUP_UPDATE, word_mul_n2w, MULT_COMM] >>
      conj_tac
      >- (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
          qexists_tac `D` >>
          simp[inst_seq_ptr_def, MULT_COMM] >>
          conj_tac
          >- (irule ptr_inst_ok_copy_len_binop >>
              fs[op_taint_def, FLOOKUP_UPDATE]) >>
          fs[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
             eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
          simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def,
               step_taint_def, set_var_taint_def, out_taint_def, mem_taint_def,
               step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
               written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
               range_bytes_def, new_site_bytes_def, FLOOKUP_DRESTRICT,
               taint_component_equality, FLOOKUP_DEF,
               pred_setTheory.EXTENSION, SF CONJ_ss] >>
          simp[GSYM FLOOKUP_DEF, eval_operand_def, lookup_var_def,
               FLOOKUP_UPDATE] >>
          Cases_on `FLOOKUP G ap` >> simp[]) >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
           set_prov_def, FLOOKUP_DRESTRICT, op_taint_def, MULT_COMM] >>
      gvs[ptr_covers_def] >>
      simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
           op_taint_def, SF CONJ_ss] >> decide_tac
QED

Resume for_array_local_address_checked_full[dynamic]:
  qexistsl [
    `update_var ep (wa + n2w (32 + k * bytes))
       (update_var tov (n2w (32 + k * bytes))
         (update_var ov (n2w (k * bytes)) s))`,
    `set_prov (DRESTRICT (DRESTRICT G (COMPL {ov})) (COMPL {tov}))
       [ep] (FLOOKUP G ap)`,
    `tn with t_var := ((tn.t_var |+ (ov,{})) |+ (tov,{})) |+ (ep,{})`] >>
  conj_tac
  >- fs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
        exec_pure2_def, eval_operand_def, update_var_def, lookup_var_def,
        FLOOKUP_UPDATE, word_mul_n2w, MULT_COMM, word_add_n2w, ADD_COMM] >>
  conj_tac
  >- (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
      qexists_tac `D` >> simp[inst_seq_ptr_def, MULT_COMM] >>
      conj_tac
      >- (irule ptr_inst_ok_copy_len_binop >>
          fs[op_taint_def, FLOOKUP_UPDATE]) >>
      `step_inst_base (mk_inst joff ADD [Lit 32w;Var ov] [tov])
          (update_var ov (n2w (k*bytes)) s with vs_inst_idx := SUC s.vs_inst_idx) =
        OK (update_var tov (n2w (32+k*bytes))
          (update_var ov (n2w (k*bytes)) s with vs_inst_idx := SUC s.vs_inst_idx))` by
        simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
             eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
             word_add_n2w] >>
      fs[MULT_COMM] >>
      simp[local_address_add_ghost, first_prov_def, op_prov_def,
           FLOOKUP_DRESTRICT, set_prov_def] >>
      conj_tac
      >- (irule ptr_inst_ok_copy_len_binop >>
          fs[op_taint_def, FLOOKUP_UPDATE]) >>
      `step_inst_base (mk_inst j4 ADD [Var ap;Var tov] [ep])
         (update_var tov (n2w (bytes*k+32))
           (update_var ov (n2w (bytes*k)) s with vs_inst_idx := SUC s.vs_inst_idx)
          with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
       OK (update_var ep (wa + n2w (bytes*k+32))
         (update_var tov (n2w (bytes*k+32))
           (update_var ov (n2w (bytes*k)) s with vs_inst_idx := SUC s.vs_inst_idx)
          with vs_inst_idx := SUC (SUC s.vs_inst_idx)))` by
        fs[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      simp[local_address_add_ghost, first_prov_def, op_prov_def,
           FLOOKUP_DRESTRICT, set_prov_def] >>
      Cases_on `FLOOKUP G ap` >> simp[]) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       set_prov_def, FLOOKUP_DRESTRICT, op_taint_def, MULT_COMM, ADD_COMM] >>
  gvs[ptr_covers_def] >>
  simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def, SF CONJ_ss, ADD_COMM] >> decide_tac
QED

Finalise for_array_local_address_checked_full
