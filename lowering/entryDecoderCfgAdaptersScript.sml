Theory entryDecoderCfgAdapters
Ancestors
  entryDecoderCfgRules abiEncoder compileEnv emitHelper venomInst pred_set context
Libs
  monadsyntax

Theorem entry_cfg_preserves_bind:
  entry_cfg_preserves f /\ (!x. entry_cfg_preserves (g x)) ==>
  entry_cfg_preserves (comp_bind f g)
Proof
  strip_tac >> rewrite_tac[entry_cfg_preserves_def] >> rpt strip_tac >>
  Cases_on `f st` >> gvs[comp_bind_def] >>
  drule_all entry_cfg_preserves_apply >>
  disch_then (qx_choose_then `BF` strip_assume_tac) >>
  `entry_cfg_preserves (g q)` by simp[] >>
  drule_all entry_cfg_preserves_apply >>
  disch_then (qx_choose_then `BG` strip_assume_tac) >>
  qexists_tac `BG` >> simp[] >> metis_tac[SUBSET_TRANS]
QED

Theorem entry_cfg_preserves_return:
  entry_cfg_preserves (return x)
Proof
  simp[entry_cfg_preserves_def, comp_return_def] >> metis_tac[SUBSET_REFL]
QED

Theorem entry_cfg_preserves_fresh_var:
  entry_cfg_preserves fresh_var
Proof
  rw[entry_cfg_preserves_def] >> qexists_tac `B` >>
  simp[] >> metis_tac[entry_cfg_cert_fresh_var]
QED

Theorem entry_cfg_preserves_fresh_id:
  entry_cfg_preserves fresh_id
Proof
  rw[entry_cfg_preserves_def] >> qexists_tac `B` >>
  simp[] >> metis_tac[entry_cfg_cert_fresh_id]
QED

Theorem entry_cfg_preserves_emit:
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode ==> entry_cfg_preserves (emit inst)
Proof
  strip_tac >> rw[entry_cfg_preserves_def] >>
  qexists_tac `B` >> simp[] >>
  metis_tac[entry_cfg_cert_emit_straight]
QED

Theorem entry_cfg_preserves_emit_inst:
  opc <> PHI /\ opc <> INVOKE /\ ~is_terminator opc ==>
  entry_cfg_preserves (emit_inst opc ops outs)
Proof
  strip_tac >> rewrite_tac[emit_inst_def] >>
  irule entry_cfg_preserves_bind >> simp[entry_cfg_preserves_fresh_id] >>
  gen_tac >> irule entry_cfg_preserves_emit >> simp[mk_inst_def]
QED

Theorem entry_cfg_preserves_emit_void:
  opc <> PHI /\ opc <> INVOKE /\ ~is_terminator opc ==>
  entry_cfg_preserves (emit_void opc ops)
Proof
  simp[emit_void_def, GSYM emit_inst_def, entry_cfg_preserves_emit_inst]
QED

Theorem entry_cfg_preserves_emit_op:
  opc <> PHI /\ opc <> INVOKE /\ ~is_terminator opc ==>
  entry_cfg_preserves (emit_op opc ops)
Proof
  strip_tac >> rewrite_tac[emit_op_def] >>
  irule entry_cfg_preserves_bind >> simp[entry_cfg_preserves_fresh_id] >>
  gen_tac >> irule entry_cfg_preserves_bind >>
  simp[entry_cfg_preserves_fresh_var] >> gen_tac >>
  irule entry_cfg_preserves_ignore_bind >>
  simp[entry_cfg_preserves_return] >>
  irule entry_cfg_preserves_emit >> simp[mk_inst_def]
QED

Theorem entry_cfg_preserves_clamp_basetype:
  entry_cfg_preserves (compile_abi_clamp_basetype val_op info)
Proof
  Cases_on `info` >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def] >>
  rpt IF_CASES_TAC >>
  simp[entry_cfg_preserves_bind, entry_cfg_preserves_ignore_bind,
       entry_cfg_preserves_return, entry_cfg_preserves_emit_op,
       entry_cfg_preserves_emit_void, is_terminator_def]
QED

Theorem entry_cfg_preserves_decode_static:
  (!v. entry_cfg_preserves (clamp v)) ==>
  entry_cfg_preserves (compile_abi_decode_static src dst CALLDATALOAD clamp)
Proof
  simp[compile_abi_decode_static_def, entry_cfg_preserves_bind,
       entry_cfg_preserves_ignore_bind, entry_cfg_preserves_emit_op,
       entry_cfg_preserves_emit_void, is_terminator_def]
QED

Theorem entry_cfg_preserves_alloc_buffer:
  entry_cfg_preserves (compile_alloc_buffer sz)
Proof
  simp[compile_alloc_buffer_def, entry_cfg_preserves_bind,
       entry_cfg_preserves_emit_op, entry_cfg_preserves_return,
       is_terminator_def]
QED

Theorem entry_cfg_preserves_getelemptr_abi:
  entry_cfg_preserves
    (compile_getelemptr_abi src is_dyn offset CALLDATALOAD hi)
Proof
  Cases_on `is_dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, entry_cfg_preserves_bind,
       entry_cfg_preserves_ignore_bind, entry_cfg_preserves_emit_op,
       entry_cfg_preserves_emit_void, entry_cfg_preserves_return,
       is_terminator_def] >>
  ntac 3 (irule entry_cfg_preserves_bind >>
    reverse conj_tac >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
    gen_tac >> BETA_TAC) >>
  simp[entry_cfg_preserves_bind, entry_cfg_preserves_ignore_bind,
       entry_cfg_preserves_emit_op, entry_cfg_preserves_emit_void,
       entry_cfg_preserves_return, is_terminator_def]
QED

Theorem entry_cfg_preserves_dyn_elem_ptr:
  entry_cfg_preserves
    (compile_abi_decode_dyn_elem_ptr CALLDATALOAD elem_src src hi sz)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, entry_cfg_preserves_bind,
       entry_cfg_preserves_ignore_bind, entry_cfg_preserves_emit_op,
       entry_cfg_preserves_emit_void, entry_cfg_preserves_return,
       is_terminator_def] >>
  ntac 2 (irule entry_cfg_preserves_bind >>
    reverse conj_tac >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
    gen_tac >> BETA_TAC) >>
  irule entry_cfg_preserves_ignore_bind >>
  reverse conj_tac >- simp[entry_cfg_preserves_return] >>
  ntac 2 (irule entry_cfg_preserves_bind >>
    reverse conj_tac >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
    gen_tac >> BETA_TAC) >>
  simp[entry_cfg_preserves_bind, entry_cfg_preserves_ignore_bind,
       entry_cfg_preserves_emit_op, entry_cfg_preserves_emit_void,
       entry_cfg_preserves_return, is_terminator_def] >>
  irule entry_cfg_preserves_ignore_bind >>
  reverse conj_tac >-
    simp[entry_cfg_preserves_bind, entry_cfg_preserves_emit_op,
         entry_cfg_preserves_emit_void, is_terminator_def] >>
  simp[entry_cfg_preserves_emit_void, is_terminator_def]
QED

Theorem entry_cfg_cert_emit_inst_jmp:
  entry_cfg_cert start st B P F /\ lbl IN B UNION P /\
  emit_inst JMP [Label lbl] [] st = ((),st') ==>
  entry_cfg_cert start st' B P T
Proof
  simp[emit_inst_def, GSYM emit_void_def] >>
  metis_tac[entry_cfg_cert_jmp, IN_UNION]
QED

Theorem entry_cfg_cert_emit_inst_jnz:
  entry_cfg_cert start st B P F /\ yes IN B UNION P /\ no IN B UNION P /\
  emit_inst JNZ [cond; Label yes; Label no] [] st = ((),st') ==>
  entry_cfg_cert start st' B P T
Proof
  simp[emit_inst_def, GSYM emit_void_def] >>
  metis_tac[entry_cfg_cert_jnz, IN_UNION]
QED

Theorem entry_cfg_preserves_loop:
  entry_cfg_preserves header /\ entry_cfg_preserves prefix /\
  (!x. entry_cfg_preserves (nested x)) /\
  (!x. entry_cfg_preserves (update x)) ==>
  entry_cfg_preserves
    (comp_bind (fresh_label hdr_suffix) (\hdr.
     comp_bind (fresh_label body_suffix) (\body_lbl.
     comp_bind (fresh_label exit_suffix) (\exit.
     comp_ignore_bind (emit_inst JMP [Label hdr] [])
     (comp_ignore_bind (new_block hdr)
     (comp_bind header (\cond.
     comp_ignore_bind (emit_inst JNZ [cond; Label exit; Label body_lbl] [])
     (comp_ignore_bind (new_block body_lbl)
     (comp_bind prefix (\x.
     comp_ignore_bind (nested x)
     (comp_ignore_bind (update x)
     (comp_ignore_bind (emit_inst JMP [Label hdr] [])
     (comp_ignore_bind (new_block exit) (return ()))))))))))))))
Proof
  strip_tac >> rewrite_tac[entry_cfg_preserves_def] >> rpt strip_tac >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def,
      emit_inst_def, GSYM emit_void_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `entry_cfg_preserves (nested x)` by simp[] >>
  `entry_cfg_preserves (update x)` by simp[] >>
  drule_all entry_cfg_loop_skeleton >> metis_tac[]
QED

Theorem entry_cfg_preserves_decode_dyn_loop:
  (!d s. entry_cfg_preserves
    (compile_abi_decode_to_buf d s CALLDATALOAD hi info)) ==>
  entry_cfg_preserves
    (compile_abi_decode_dyn_loop dst src CALLDATALOAD hi info asz msz ip cnt)
Proof
  strip_tac >>
  qabbrev_tac `header = do i <- emit_op MLOAD [ip];
    n <- emit_op CALLDATALOAD [src]; c <- emit_op LT [i;n];
    emit_op ISZERO [c] od` >>
  qabbrev_tac `prefix = do i <- emit_op MLOAD [ip];
    sd <- emit_op ADD [src; Lit 32w];
    so <- emit_op MUL [i; Lit (n2w asz)]; es <- emit_op ADD [sd;so];
    a <- (if dec_info_needs_offset info then
      compile_abi_decode_dyn_elem_ptr CALLDATALOAD es sd hi asz else return es);
    dd <- emit_op ADD [dst; Lit 32w];
    doff <- emit_op MUL [i; Lit (n2w msz)]; ed <- emit_op ADD [dd;doff];
    return ((ed,a),i) od` >>
  qabbrev_tac `nested = \(x:(operand # operand) # operand). compile_abi_decode_to_buf
    (FST (FST x)) (SND (FST x)) CALLDATALOAD hi info` >>
  qabbrev_tac `update = \(x:(operand # operand) # operand). do ni <- emit_op ADD [SND x; Lit 1w];
    emit_void MSTORE [ip;ni] od` >>
  qabbrev_tac `cfgloop = do h <- fresh_label "dec_dyn_hdr";
    b <- fresh_label "dec_dyn_body"; e <- fresh_label "dec_dyn_exit";
    emit_inst JMP [Label h] []; new_block h; c <- header;
    emit_inst JNZ [c;Label e;Label b] []; new_block b; x <- prefix;
    nested x; update x; emit_inst JMP [Label h] []; new_block e; return () od` >>
  `entry_cfg_preserves cfgloop` suffices_by
    (disch_tac >>
     `cfgloop = compile_abi_decode_dyn_loop dst src CALLDATALOAD hi info asz msz ip cnt`
       by (pop_assum kall_tac >>
           simp[Abbr `cfgloop`, Abbr `header`, Abbr `prefix`, Abbr `nested`,
                Abbr `update`, Once (cj 7 compile_abi_decode_to_buf_def),
                comp_ignore_bind_def, comp_bind_assoc] >>
           simp[FUN_EQ_THM, comp_bind_def, comp_return_def]) >> gvs[]) >>
  simp[Abbr `cfgloop`] >> irule entry_cfg_preserves_loop >>
  simp[Abbr `nested`, Abbr `update`, entry_cfg_preserves_bind,
       entry_cfg_preserves_emit_op, entry_cfg_preserves_emit_void,
       is_terminator_def] >> conj_tac
  >- (simp[Abbr `prefix`] >>
      ntac 4 (irule entry_cfg_preserves_bind >> reverse conj_tac
        >- simp[entry_cfg_preserves_emit_op, is_terminator_def] >>
        gen_tac >> BETA_TAC) >>
      irule entry_cfg_preserves_bind >> reverse conj_tac
      >- (Cases_on `dec_info_needs_offset info` >>
          simp[entry_cfg_preserves_dyn_elem_ptr, entry_cfg_preserves_return]) >>
      gen_tac >> simp[entry_cfg_preserves_bind, entry_cfg_preserves_emit_op,
                     entry_cfg_preserves_return, is_terminator_def]) >>
  simp[Abbr `header`, entry_cfg_preserves_bind,
       entry_cfg_preserves_emit_op, is_terminator_def]
QED
