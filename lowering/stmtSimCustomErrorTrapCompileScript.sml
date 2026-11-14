Theory stmtSimCustomErrorTrapCompile
Ancestors
  stmtSimCustomErrorTrap abiEncoder abiEncoderAppend compileEnv emitHelper
  context venomInst list

Definition ce_compile_commutes_def:
  ce_compile_commutes (f:'a compiler) <=>
    !s x t. f s = (x,t) ==> f (ce_trap_cs s) = (x,ce_trap_cs t)
End

Theorem ce_compile_return:
  ce_compile_commutes (comp_return x)
Proof
  simp[ce_compile_commutes_def, comp_return_def]
QED

Theorem ce_compile_bind:
  ce_compile_commutes f /\ (!x. ce_compile_commutes (g x)) ==>
  ce_compile_commutes (comp_bind f g)
Proof
  rw[ce_compile_commutes_def, comp_bind_def] >>
  Cases_on `f s` >> gvs[] >>
  `f (ce_trap_cs s) = (q,ce_trap_cs r)` by metis_tac[] >>
  simp[] >> metis_tac[]
QED

Theorem ce_compile_ignore_bind:
  ce_compile_commutes f /\ ce_compile_commutes g ==>
  ce_compile_commutes (comp_ignore_bind f g)
Proof
  simp[comp_ignore_bind_def, ce_compile_bind]
QED

Theorem ce_compile_prims[local]:
  ce_compile_commutes fresh_var /\
  ce_compile_commutes (fresh_label suffix) /\
  ce_compile_commutes fresh_id /\
  ce_compile_commutes (new_block lbl)
Proof
  simp[ce_compile_commutes_def, fresh_var_def, fresh_label_def,
       fresh_id_def, new_block_def, ce_trap_cs_def, ce_trap_block_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ce_compile_emit[local]:
  ce_trap_inst i = i ==> ce_compile_commutes (emit i)
Proof
  simp[ce_compile_commutes_def, emit_def, ce_trap_cs_def, MAP_APPEND] >>
  rpt strip_tac >> gvs[]
QED

Theorem ce_compile_emit_helpers:
  opc <> GAS /\ opc <> INVOKE ==>
  ce_compile_commutes (emit_op opc ops) /\
  ce_compile_commutes (emit_void opc ops) /\
  ce_compile_commutes (emit_inst opc ops outs)
Proof
  strip_tac >>
  simp[emit_op_def, emit_void_def, emit_inst_def] >>
  rpt conj_tac >>
  irule ce_compile_bind >> simp[ce_compile_prims] >> gen_tac
  >- (irule ce_compile_bind >> simp[ce_compile_prims] >> gen_tac >>
      irule ce_compile_ignore_bind >> simp[ce_compile_return] >>
      irule ce_compile_emit >> simp[ce_trap_inst_def, mk_inst_def])
  >> irule ce_compile_emit >> simp[ce_trap_inst_def, mk_inst_def]
QED

Theorem ce_compile_alloc_buffer:
  !sz. ce_compile_commutes (compile_alloc_buffer sz)
Proof
  gen_tac >> rewrite_tac[compile_alloc_buffer_def] >>
  irule ce_compile_bind >> simp[ce_compile_emit_helpers, ce_compile_return]
QED

val ce_compile_simps =
  [ce_compile_return, ce_compile_prims, ce_compile_emit_helpers,
   ce_compile_alloc_buffer, LET_THM];

fun ce_compile_tac extra g =
  (asm_simp_tac (srw_ss()) (extra @ ce_compile_simps) >>
   (fn goal =>
     let
       val code = rand (snd goal)
       val head = fst (strip_comb code)
       val name = if is_const head then fst (dest_const head) else ""
     in
       if name = "comp_bind" then
         (ho_match_mp_tac ce_compile_bind >> conj_tac
           >- ce_compile_tac extra >> rpt gen_tac >> ce_compile_tac extra) goal
       else if name = "comp_ignore_bind" then
         (ho_match_mp_tac ce_compile_ignore_bind >> conj_tac >>
          ce_compile_tac extra) goal
       else if boolSyntax.is_cond code then
         (IF_CASES_TAC >> gvs[] >> ce_compile_tac extra) goal
       else
         first_x_assum (fn th => irule (SRULE[] th) >> simp[]) goal
     end)) g;

Theorem ce_compile_static[local]:
  ce_compile_commutes (compile_abi_encode_static dst src)
Proof
  rewrite_tac[compile_abi_encode_static_def] >> ce_compile_tac []
QED

Theorem ce_compile_static_info[local]:
  !dst src ei. ce_compile_commutes (compile_abi_encode_static_info dst src ei)
Proof
  rpt gen_tac >> Cases_on `ei` >>
  rewrite_tac[compile_abi_encode_static_info_def] >>
  ce_compile_tac [ce_compile_static]
QED

Theorem ce_compile_static_loop[local]:
  ce_compile_commutes (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ce_compile_tac [ce_compile_static_info]
QED

Theorem ce_compile_encoder_mutual:
  (!dst src ei dyn off ptr. ce_compile_commutes (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. ce_compile_commutes (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr. ce_compile_commutes (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len. ce_compile_commutes (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  ONCE_REWRITE_TAC [compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  ce_compile_tac [ce_compile_static, ce_compile_static_loop]
QED

Theorem ce_trap_compile_abi_encode_to_buf:
  compile_abi_encode_to_buf dst src ei st = (out,en) ==>
  compile_abi_encode_to_buf dst src ei (ce_trap_cs st) = (out,ce_trap_cs en)
Proof
  metis_tac[cj 2 ce_compile_encoder_mutual, ce_compile_commutes_def]
QED
