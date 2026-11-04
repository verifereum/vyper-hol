(* Semantic copy steps.  Source slot arithmetic is modular. *)
Theory bodyIntCallCopyContent
Ancestors
  bodyIntCallCopyProbe exprSimStorageCopy valueEncodingProps exprLoweringProps
  emitHelperProps venomExecSemantics venomState venomInst

Theorem copy_load_exact:
  !opc src a id out s.
    (opc = SLOAD \/ opc = TLOAD) /\ eval_operand src s = SOME a ==>
    step_inst_base (mk_inst id opc [src] [out]) s =
      OK (update_var out (if opc = SLOAD then sload a s else tload a s) s)
Proof
  rpt strip_tac >> gvs[]
  >- (irule step_SLOAD >> simp[]) >>
  rw[step_inst_base_def, exec_read1_def]
QED

Theorem copy_slot_exact:
  !opc src dst a b id out s.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!x. dst = Var x ==> x <> out) ==>
    run_inst_seq
      [mk_inst id opc [src] [out];
       mk_inst (id+1) MSTORE [dst; Var out] []] s =
    OK (mstore (w2n b) (if opc = SLOAD then sload a s else tload a s)
          (update_var out (if opc = SLOAD then sload a s else tload a s) s))
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id opc [src] [out]) s =
    OK (update_var out (if opc = SLOAD then sload a s else tload a s) s)` by
    (irule copy_load_exact >> simp[]) >>
  qmatch_goalsub_abbrev_tac `mstore (w2n b) loaded t` >>
  `eval_operand dst t = SOME b` by
    (Cases_on `dst` >> gvs[Abbr `t`, eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [dst; Var out] []) t =
    OK (mstore (w2n b) loaded t)` by
    (irule step_MSTORE >> simp[Abbr `t`, eval_operand_def, lookup_var_update_var]) >>
  gvs[run_inst_seq_def, Abbr `t`, Abbr `loaded`]
QED

Theorem copy_slot_content_frame:
  !opc src dst a b id out s.
    (opc = SLOAD \/ opc = TLOAD) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!x. dst = Var x ==> x <> out) ==>
    ?t. run_inst_seq
          [mk_inst id opc [src] [out];
           mk_inst (id+1) MSTORE [dst; Var out] []] s = OK t /\
        mem_word_at (w2n b) t.vs_memory =
          (if opc = SLOAD then sload a s else tload a s) /\
        (!off len. off + len <= w2n b \/ w2n b + 32 <= off ==>
          mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
        (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
        t with <|vs_memory := s.vs_memory; vs_vars := s.vs_vars|> = s
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qexists_tac `mstore (w2n b)
    (if opc = SLOAD then sload a s else tload a s)
    (update_var out (if opc = SLOAD then sload a s else tload a s) s)` >>
  conj_tac >- (irule copy_slot_exact >> metis_tac[]) >>
  simp[mstore_mem_word_at_same] >>
  conj_tac
  >- (rpt strip_tac >> irule EQ_TRANS >>
      irule_at Any mstore_mem_bytes_at_disjoint >> simp[] >>
      simp[update_var_def]) >>
  simp[mstore_def, write_memory_with_expansion_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED
