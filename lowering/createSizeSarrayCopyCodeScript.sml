(* Branch confinement for the static-array typed memory copy. *)
Theory createSizeSarrayCopyCode
Ancestors
  createSizeCutOpens createSizeCutCode context emitHelper compileEnv pair

Theorem create_sarray_loop:
  (!s. create_cut_code {} s (SND (test s))) /\
  (!s. create_cut_code {} s (SND (loop_body s))) ==>
  !h b x a. create_cut_code {} a
    (SND ((do emit_inst JMP [Label h] [];
              new_block h;
              cond <- test;
              emit_inst JNZ [cond; Label x; Label b] [];
              new_block b;
              loop_body;
              emit_inst JMP [Label h] [];
              _ <- new_block x;
              return ()
           od) a))
Proof
  rpt strip_tac >>
  Cases_on `emit_inst JMP [Label h] [] a` >>
  rename1 `emit_inst JMP [Label h] [] a = (_,a1)` >>
  Cases_on `new_block h a1` >> rename1 `new_block h a1 = (_,a2)` >>
  Cases_on `test a2` >> rename1 `test a2 = (cond,a3)` >>
  Cases_on `emit_inst JNZ [cond; Label x; Label b] [] a3` >>
  rename1 `emit_inst JNZ _ [] a3 = (_,a4)` >>
  Cases_on `new_block b a4` >> rename1 `new_block b a4 = (_,a5)` >>
  Cases_on `loop_body a5` >> rename1 `loop_body a5 = (_,a6)` >>
  Cases_on `emit_inst JMP [Label h] [] a6` >>
  rename1 `emit_inst JMP _ [] a6 = (_,a7)` >>
  Cases_on `new_block x a7` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  fs[oneTheory.one] >>
  `create_cut_code {} a2 a3` by
    (qpat_x_assum `!s. create_cut_code _ s (SND (test s))`
       (qspec_then `a2` mp_tac) >> simp[]) >>
  `create_cut_code {} a5 a6` by
    (qpat_x_assum `!s. create_cut_code _ s (SND (loop_body s))`
       (qspec_then `a5` mp_tac) >> simp[]) >>
  qpat_x_assum `!s. create_cut_code _ s (SND (test s))` kall_tac >>
  qpat_x_assum `!s. create_cut_code _ s (SND (loop_body s))` kall_tac >>
  metis_tac[create_cut_opaque_loop]
QED

fun sarray_cut_steps () =
  rpt (FIRST [CHANGED_TAC (simp[create_cut_code_emit_inst,
                                  create_cut_code_emit_void,
                                  create_cut_code_emit_op,
                                  create_cut_targets_def]),
              irule create_cut_code_bind, irule create_cut_code_ignore_bind,
              conj_tac]);

Theorem create_sarray_copy_case:
  (!d s a. create_cut_code {} a
       (SND (compile_store_memory_typed ce d dt s st a))) ==>
  !a. create_cut_code {} a
       (SND (compile_copy_sarray_typed ce dst dt src st n a))
Proof
  rpt strip_tac >> simp[Once contextTheory.compile_store_memory_typed_def] >>
  IF_CASES_TAC
  >- (Cases_on `n * type_memory_bytes ce st` >>
      simp[compile_copy_memory_def] >> sarray_cut_steps ()) >>
  qpat_x_assum `~(_ /\ _)` kall_tac >>
  ntac 4 (irule create_cut_code_bind >> simp[]) >>
  qmatch_goalsub_abbrev_tac `Var ctr` >>
  irule create_cut_code_ignore_bind >>
  conj_tac >- sarray_cut_steps () >>
  rename1 `Abbrev (ctr = FST (fresh_var _))` >>
  `!s. create_cut_code {} s
     (SND ((do lt <- emit_op LT [Var ctr; Lit (n2w n)];
               emit_op ISZERO [lt]
            od) s))` by (gen_tac >> sarray_cut_steps ()) >>
  `!s. create_cut_code {} s
     (SND ((do src_off <- emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes ce st))];
               dst_off <- emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes ce dt))];
               src_elem <- emit_op ADD [src; src_off];
               dst_elem <- emit_op ADD [dst; dst_off];
               compile_store_memory_typed ce dst_elem dt src_elem st;
               new_ctr <- emit_op ADD [Var ctr; Lit 1w];
               emit_inst ASSIGN [new_ctr] [ctr]
            od) s))` by (gen_tac >> sarray_cut_steps ()) >>
  drule_all create_sarray_loop >> simp[comp_ignore_bind_def, comp_bind_assoc]
QED
