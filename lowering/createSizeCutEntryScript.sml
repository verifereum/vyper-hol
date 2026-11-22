(* PHI entry at the open targets of actions preceding CREATE dispatch. *)
Theory createSizeCutEntry
Ancestors
  entryReachBodyFirstEmissionExpr entryReachBodyFirstEmissionExprSupport
  entryReachBodyFirstEmissionSupport compilerFirstEmission blockPrefixEquiv
  externalEntryShape exprLoweringProps exprLowering builtinCreate context
  fragExec compileEnv emitHelper venomExecSemantics venomInst list rich_list

(* The emitting arm deliberately concerns only the first new instruction in
   the original block.  Later blocks may contain expression-join PHIs. *)
Definition create_cut_first_def:
  create_cut_first a b <=>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
        lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\
        i.inst_opcode <> PHI))
End

Theorem create_cut_first_refl[simp]:
  create_cut_first a a
Proof
  simp[create_cut_first_def, cs_extends_refl]
QED

Theorem create_cut_first_trans[local]:
  create_cut_first a b /\ create_cut_first b c ==> create_cut_first a c
Proof
  rewrite_tac[create_cut_first_def] >> strip_tac >> irule first_emission_trans >>
  qexists_tac `b` >> simp[]
QED

(* cuts lists the intermediate compiler states, not execution states. *)
Theorem create_cut_first_chain[local]:
  !cuts m sc. LIST_REL create_cut_first (m::cuts) (cuts ++ [sc]) ==>
              create_cut_first m sc
Proof
  Induct >- simp[] >>
  rpt gen_tac >> rewrite_tac[APPEND, LIST_REL_def] >> strip_tac >>
  irule create_cut_first_trans >> qexists_tac `h` >> simp[]
QED

Theorem create_pre_dispatch_phi_bound:
  LIST_REL create_cut_first (m::cuts) (cuts ++ [sc]) /\
  cs_extends sc sb /\ fn_has_code m sb fn /\
  lookup_block sc.cs_current_bb fn.fn_blocks = SOME dispatch_bb /\
  get_instruction dispatch_bb (LENGTH sc.cs_current_insts) = SOME dispatch /\
  MEM dispatch.inst_opcode [CREATE; CREATE2] /\
  lookup_block m.cs_current_bb fn.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions <= LENGTH m.cs_current_insts
Proof
  strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE[create_cut_first_def]) create_cut_first_chain
  >- (irule phi_prefix_length_non_phi >>
      gvs[get_instruction_def, AllCaseEqs()]) >>
  `fn_has_code m sc fn` by metis_tac[fn_has_code_split] >>
  qpat_x_assum `!f. fn_has_code m sc f ==> _` (qspec_then `fn` mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  irule phi_prefix_length_non_phi >> gvs[EL_APPEND_EQN]
QED

(* Primitive and callback actions used in the production run layout. *)
Theorem create_cut_first_actions:
  (!a b x y. comp_return x a = (y,b) ==> create_cut_first a b) /\
  (!opc ops a x b. opc <> PHI /\ emit_op opc ops a = (x,b) ==> create_cut_first a b) /\
  (!opc ops a x b. opc <> PHI /\ emit_void opc ops a = (x,b) ==> create_cut_first a b) /\
  (!opc ops outs a x b. opc <> PHI /\ emit_inst opc ops outs a = (x,b) ==>
                      create_cut_first a b) /\
  (!ce ty e a x b. compile_expr ce ty e a = (x,b) ==> create_cut_first a b) /\
  (!ce ty e a x b. lower_value compile_expr ce ty e a = (x,b) ==> create_cut_first a b) /\
  (!ce vv a x b. unwrap_value ce vv a = (x,b) ==> create_cut_first a b) /\
  (!ce copy vv a x b. compile_snapshot_vv ce copy vv a = (x,b) ==> create_cut_first a b) /\
  (!n a x b. compile_alloc_buffer n a = (x,b) ==> create_cut_first a b) /\
  (!sz a x b. compile_alloc_dynamic sz a = (x,b) ==> create_cut_first a b) /\
  (!dst src sz a x b. compile_copy_memory_dynamic dst src sz a = (x,b) ==>
                      create_cut_first a b) /\
  (!is_lit target off a x b. compile_create_blueprint_check is_lit target off a = (x,b) ==>
                             create_cut_first a b)
Proof
  rewrite_tac[create_cut_first_def, compile_alloc_dynamic_def, compile_copy_memory_dynamic_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST [drule first_emission_return,
         drule_all (cj 3 first_emission_emit_helpers),
         drule_all (cj 2 first_emission_emit_helpers),
         drule_all (cj 1 first_emission_emit_helpers),
         drule (cj 1 first_emission_compile_expr),
         drule (MATCH_MP first_emission_lower_value
                 (SPECL [``ce:compile_env``, ``ty:type``, ``e:expr``]
                   (cj 1 first_emission_compile_expr))),
         drule first_emission_unwrap_value,
         drule first_emission_snapshot_vv,
         drule first_emission_alloc_buffer,
         drule ctor_create_blueprint_check_first_emission_strong,
         drule_at Any (cj 3 first_emission_emit_helpers),
         drule_at Any (cj 2 first_emission_emit_helpers)] >> simp[]
QED

(* Three preparations have an allocation as their first action.  Their
   memory-copy/encoding tails need only extend the compiler state. *)
Theorem create_cut_first_alloc[local]:
  (!buf. cs_appends (k buf)) ==>
  !a x b. comp_bind (compile_alloc_buffer n) k a = (x,b) ==> create_cut_first a b
Proof
  strip_tac >> rewrite_tac[create_cut_first_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >>
  conj_tac >- metis_tac[first_emission_alloc_buffer] >>
  fs[cs_appends_def]
QED

Theorem create_cut_first_preparation:
  (!a x b. compile_create_proxy_buf target a = (x,b) ==> create_cut_first a b) /\
  (!a y b. compile_create_snapshot ce vv ty a = (y,b) ==> create_cut_first a b) /\
  (!a z b. compile_abi_encode_values_to_buf ce dst rows a = (z,b) ==> create_cut_first a b)
Proof
  rewrite_tac[compile_create_proxy_buf_def, compile_create_snapshot_def,
              compile_abi_encode_values_to_buf_def] >> simp_tac bool_ss [LET_THM] >>
  rpt conj_tac >> ho_match_mp_tac create_cut_first_alloc >> gen_tac
  >- (rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
           conj_tac >> rpt gen_tac >> BETA_TAC >>
           simp[cs_appends_emit_helpers, cs_appends_return]))
  >- (irule cs_appends_ignore_bind >> simp[cs_appends_return] >>
      Cases_on `vv_location vv` >> simp[] >>
      TRY (rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> simp[]) >>
      simp[contextTheory.compile_slot_to_memory_def] >>
      rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >> conj_tac >>
           rpt gen_tac >> BETA_TAC >> simp[cs_appends_emit_helpers, cs_appends_return]) >>
      simp[compile_copy_memory_dynamic_def, cs_appends_emit_helpers] >>
      rw[cs_appends_def] >>
      metis_tac[compile_word_copy_loop_labels, compile_imm_copy_to_memory_labels,
                pairTheory.SND]) >>
  irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers] >>
  irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers, cs_appends_def] >>
  metis_tac[ci_mono_compile_abi_encode_value_rows, ci_mono_def, pairTheory.SND]
QED
