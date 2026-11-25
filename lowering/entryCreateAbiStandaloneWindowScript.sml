(* The standalone payload restores the saved representation before running
   the joint encoder.  Both laws supply their semantic posts and their scope
   on one endpoint and one pair of ghosts. *)
Theory entryCreateAbiStandaloneWindow
Ancestors
  entryCreatePathScope entryCreateFocusSpec bodyFullAbiEncodeNonwordWindow
  abiEncoderWindowJoint abiEncoderWindowPhase bodyFullExtCallDirectState
  gasSummaryCompose vyperABI vyperTypeSystem exprLowering compileEnv
  context finite_map contractABI fragGasOriginPtr venomState venomInst
  abiEncoderWindowContract abiEncoderProps fragGasOriginPtrLoop list pred_set
  entryCreateEffectFocus createSizeCutCode exprSimAbiEncodeSiteResources
  entryCreateAbiRestoreScope entryCreateAbiPackagingSuffix entryCreatePosSnapshotCode
  entryCreateStructLitExitFetch exprSimAbiEncodeObliviousCode compileExprAllocaFresh
  bodyFullIfExpReach bodyFullUnwrapSlotBand bodyFullAbiEncodeArgs venomExecProofs
  entryCreateIntervalLayout createSizeLocationCode createSizeEncodeCoreCode
  exprLoweringProps fragExec pair

Theorem abi_standalone_payload_split:
  ~is_word_type ty /\
  compile_abi_encode_payload ce T [saved] [ty] dst ready = (len,body_end) ==>
  ?src unwrap_end.
    unwrap_value ce saved ready = (src,unwrap_end) /\
    compile_abi_encode_to_buf dst src
      (type_to_abi_enc_info ce.ce_struct_fields ce ty) unwrap_end = (len,body_end)
Proof
  Cases_on `unwrap_value ce saved ready` >>
  gvs[compile_abi_encode_payload_def,comp_bind_def] >> metis_tac[]
QED

Theorem abi_standalone_payload_from_window_laws:
  unwrap_value ce saved ready = (src,unwrap_end) /\
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info ce.ce_struct_fields ce ty) unwrap_end = (len,body_end) /\
  ready.cs_next_id <= unwrap_end.cs_next_id /\
  unwrap_end.cs_next_id <= body_end.cs_next_id /\
  (!bb i. lookup_block body_end.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH body_end.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids ready unwrap_end) /\
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent ce.ce_struct_fields E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!ty' v'. evaluate_type E0 ty' = SOME v' ==>
     type_memory_bytes ce ty' = type_memory_size v') /\
  value_has_type tv v /\ vyper_to_abi E ty v = SOME av /\
  bytes = enc (vyper_to_abi_type E ty) av /\
  (* The saved-row restore law, at its installed unwrap site. *)
  (!src' cut. unwrap_value ce saved ready = (src',cut) ==>
    ?z Gz tz addr.
      RestorePost src' cut z Gz tz /\
      eval_operand src' z = SOME (n2w addr) /\
      (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
         val_in_memory tv v addr mem) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (pre,Gpre,tnpre) [] (OK z,Gz,tz)) /\
      create_operand_full_scope ready cut explicit ctx func pre [] (OK z)) /\
  (* Apply the joint law only at that restore's actual successor. *)
  (!z Gz tz addr ct rv.
    RestorePost src unwrap_end z Gz tz /\
    eval_operand src z = SOME (n2w addr) /\ enc ct rv = bytes /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
       abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
         ct rv addr (val_footprint tv v) mem) ==>
    ?q Gq tq.
      window_strong_result ctx func unwrap_end body_end len ct rv dest z q /\
      abi_encode_exec_frame func z q /\
      EncodePost z Gz tz q Gq tq /\
      op_taint tq len = {} /\
      (!x. len = Var x ==> not_fresh_at body_end x) /\
      (!j. dest <= j /\ j < dest + LENGTH (enc ct rv) ==> j NOTIN tq.t_mem) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (z,Gz,tz) [] (OK q,Gq,tq)) /\
      create_operand_full_scope unwrap_end body_end explicit ctx func z [] (OK q)) ==>
  ?z Gz tz addr ct rv q Gq tq.
    RestorePost src unwrap_end z Gz tz /\
    eval_operand src z = SOME (n2w addr) /\ enc ct rv = bytes /\
    window_strong_result ctx func unwrap_end body_end len ct rv dest z q /\
    window_phase ctx func unwrap_end body_end
      (window_alloca_sites func (frag_ids unwrap_end body_end))
      [(dest,LENGTH bytes)] z q /\
    abi_encode_exec_frame func z q /\ EncodePost z Gz tz q Gq tq /\
    mem_bytes_at dest (LENGTH bytes) q.vs_memory = bytes /\
    eval_operand len q = SOME (n2w (LENGTH bytes)) /\ op_taint tq len = {} /\
    (!x. len = Var x ==> not_fresh_at body_end x) /\
    (!j. dest <= j /\ j < dest + LENGTH bytes ==> j NOTIN tq.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (pre,Gpre,tnpre) [] (OK q,Gq,tq)) /\
    create_operand_full_scope ready body_end explicit ctx func pre [] (OK q)
Proof
  strip_tac >>
  qpat_x_assum `!src' cut. unwrap_value _ _ _ = (src',cut) ==> _`
    (drule_then strip_assume_tac) >>
  drule_all abi_encode_uniform_translated_footprint_window >> strip_tac >>
  `enc ct rv = bytes` by metis_tac[] >>
  qpat_x_assum `!z Gz tz addr ct rv. _ ==> _`
    (qspecl_then [`z`,`Gz`,`tz`,`addr`,`ct`,`rv`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  drule window_phase_strong_result >> strip_tac >>
  drule window_strong_result_public >> strip_tac >>
  drule abi_encoder_window_result_output >> strip_tac >>
  `bytes = enc ct rv` by metis_tac[] >>
  qpat_x_assum `bytes = enc (vyper_to_abi_type E ty) av` kall_tac >>
  qpat_x_assum `enc ct rv = enc (vyper_to_abi_type E ty) av` kall_tac >>
  qpat_x_assum `enc ct rv = bytes` kall_tac >>
  qpat_x_assum `bytes = enc ct rv` SUBST_ALL_TAC >>
  qexistsl_tac [`z`,`Gz`,`tz`,`addr`,`ct`,`rv`,`q`,`Gq`,`tq`] >>
  simp[] >> conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gz`,`z`,`tz`] >> simp[]) >>
  irule (SIMP_RULE bool_ss [APPEND] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
    create_operand_full_scope_prepend)) >>
  qexistsl_tac [`unwrap_end`,`z`] >> simp[]
QED

(* This static composition applies before either physical phase has run.
   The two inventories are compilation laws, not successful-run premises. *)
Theorem abi_standalone_payload_inventory_from_phases:
  ~is_word_type ty /\
  compile_abi_encode_payload ce T [saved] [ty] dst ready = (len,body_end) /\
  (!src cut i. unwrap_value ce saved ready = (src,cut) /\
      MEM i (fn_insts func) /\ i.inst_id IN frag_ids ready cut ==>
      ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]) /\
  (!src cut i.
      compile_abi_encode_to_buf dst src
        (type_to_abi_enc_info ce.ce_struct_fields ce ty) cut = (len,body_end) /\
      MEM i (fn_insts func) /\ i.inst_id IN frag_ids cut body_end ==>
      ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]) ==>
  !i. MEM i (fn_insts func) /\ i.inst_id IN frag_ids ready body_end ==>
      ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]
Proof
  strip_tac >> drule_all abi_standalone_payload_split >> strip_tac >>
  rpt strip_tac >>
  Cases_on `i.inst_id < unwrap_end.cs_next_id`
  >- (`i.inst_id IN frag_ids ready unwrap_end` by fs[frag_ids_def] >>
      metis_tac[]) >>
  `i.inst_id IN frag_ids unwrap_end body_end` by fs[frag_ids_def] >>
  metis_tac[]
QED

Theorem abi_standalone_payload_cut_from_inventory:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} ready body_end /\ fn_has_code ready body_end func /\
  (!i. MEM i (fn_insts func) /\ i.inst_id IN frag_ids ready body_end ==>
       ~MEM i.inst_opcode [CREATE;CREATE2;INVOKE]) ==>
  create_operand_cut ready body_end explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> irule create_effect_suffix_cut >>
  simp[EVERY_MEM] >> conj_tac
  >- (rpt strip_tac >> fs[create_cut_code_def] >>
      metis_tac[abi_encode_frag_code_members]) >>
  qexists_tac `ce` >> simp[]
QED

Theorem abi_standalone_installed_restore[local]:
  unwrap_value ce saved ready = (src,cut) /\
  create_layout ready cut /\ fn_has_code ready cut func /\
  fn_inst_ids_distinct func /\ body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  ~is_word_type (lowered_value_type ce e) ==>
  abi_packaging_restore_law (abi_packaging_segment explicit ctx func)
    ctx func explicit PG lo ce cx st0 DF d front ready cut e saved src
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!bb j. lookup_block cut.cs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb (LENGTH cut.cs_current_insts) = SOME j ==>
           j.inst_id NOTIN frag_ids ready cut` by
    (mp_tac (Q.INST [`a` |-> `ready`, `b` |-> `cut`, `f` |-> `func`]
        installed_covered_exit_fetch) >>
     impl_tac
     >- (asm_rewrite_tac[] >> conj_tac
         >- (mp_tac (Q.INST [`ce` |-> `ce`, `vv` |-> `saved`] admin_unwrap_code_action) >>
             simp[code_action_def, code_step_def] >> disch_then drule >> simp[]) >>
         metis_tac[unwrap_value_added_id]) >>
     disch_then ACCEPT_TAC) >>
  `unwrap_exit_phi_free func cut` by
    (simp[unwrap_exit_phi_free_def] >> metis_tac[body_inv_no_phi, lookup_block_MEM]) >>
  pure_rewrite_tac[abi_packaging_restore_law_def] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`su` |-> `ready`, `sb` |-> `cut`] abi_standalone_restore_scoped) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]]) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >>
  asm_rewrite_tac[abi_packaging_segment_def, create_operand_at_def]
QED

Theorem abi_standalone_installed_payload_phases:
  ~is_word_type (lowered_value_type ce e) /\
  compile_abi_encode_payload ce T [saved] [lowered_value_type ce e] dst ready =
    (len,body_end) /\
  cs_extends st ready /\ cs_extends body_end fin_cs /\
  create_layout st fin_cs /\ fn_has_code st fin_cs func /\
  fn_inst_ids_distinct func /\ body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  (!src cut. compile_abi_encode_to_buf dst src
       (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e)) cut =
       (len,body_end) ==>
     abi_packaging_window_law (abi_packaging_segment explicit ctx func)
       ctx func explicit PG lo cut body_end dst src
       (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e)) len) ==>
  abi_packaging_payload_phases (abi_packaging_segment explicit ctx func) RowSide
    ctx func explicit PG lo ce cx st0 DF d T [lowered_value_type ce e] [e] [saved]
    k N st ready dst len body_end
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_standalone_payload_split >>
  disch_then (qx_choosel_then [`src`,`cut`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `cs_extends ready cut /\ cs_extends cut body_end` by
    metis_tac[ci_mono_def,ci_mono_unwrap_value,cj 2 ci_mono_compile_abi_encode,SND] >>
  `cs_extends cut fin_cs /\ cs_extends st cut` by metis_tac[cs_extends_trans] >>
  `create_layout ready cut` by metis_tac[create_layout_subinterval] >>
  `fn_has_code ready cut func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  simp[abi_packaging_payload_phases_def] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- metis_tac[create_unwrap_cut_code,SND]
  >- metis_tac[create_encode_to_buf_cut_code,SND]
  >- (irule abi_standalone_installed_restore >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
  qpat_assum `!src cut. compile_abi_encode_to_buf _ src _ cut = _ ==> _`
    (qspecl_then [`src`,`cut`] mp_tac) >> asm_rewrite_tac[]
QED
