(* Extra temporary bindings are bounded by an initial environment. This permits
   loop re-entry while retaining a final freshness bound and all defined inputs. *)
Theory abiDecoderVarExtend
Ancestors
  execEquivParamDefs venomState compileEnv finite_map pred_set

Definition abi_decoder_var_map_def:
  abi_decoder_var_map extras small large <=>
    small SUBMAP large /\ large SUBMAP (FUNION small extras)
End

Definition abi_decoder_vars_extend_def:
  abi_decoder_vars_extend extras s t <=>
    vsr_frame s = vsr_frame t /\ abi_decoder_var_map extras s.vs_vars t.vs_vars
End

Theorem abi_decoder_var_map_refl[simp]:
  abi_decoder_var_map extras vars vars
Proof
  simp[abi_decoder_var_map_def, SUBMAP_FUNION_ID]
QED

Theorem abi_decoder_submap_update[local]:
  small SUBMAP large ==> small |+ (x,v) SUBMAP large |+ (x,v)
Proof
  strip_tac >> irule SUBMAP_mono_FUPDATE >>
  pure_rewrite_tac [GSYM SUBMAP_DOMSUB_gen] >>
  irule SUBMAP_TRANS >> qexists_tac `small` >> simp[]
QED

Theorem abi_decoder_var_map_update:
  abi_decoder_var_map extras small large ==>
  abi_decoder_var_map extras (small |+ (x,v)) (large |+ (x,v))
Proof
  rw[abi_decoder_var_map_def, FUNION_FUPDATE_1] >>
  irule abi_decoder_submap_update >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_var_map_lookup:
  abi_decoder_var_map extras small large /\ FLOOKUP small x = SOME v ==>
  FLOOKUP large x = SOME v
Proof
  rw[abi_decoder_var_map_def] >> drule_all FLOOKUP_SUBMAP >> simp[]
QED

Theorem abi_decoder_frame_labels[local]:
  (vsr_frame s = vsr_frame t ==> s.vs_labels = t.vs_labels) /\
  (vsr_term_frame s = vsr_term_frame t ==> s.vs_labels = t.vs_labels)
Proof
  conj_tac >> strip_tac >>
  first_x_assum (mp_tac o AP_TERM ``\s:venom_state. s.vs_labels``) >>
  simp[vsr_frame_def, vsr_term_frame_def]
QED

Theorem abi_decoder_frame_weaken[local]:
  vsr_frame s = vsr_frame t ==> vsr_term_frame s = vsr_term_frame t
Proof
  strip_tac >> first_x_assum
    (ACCEPT_TAC o SIMP_RULE bool_ss [vsr_frame_idempotent] o AP_TERM ``vsr_term_frame``)
QED

Theorem abi_decoder_operand_agreement[local]:
  s.vs_labels = t.vs_labels /\
  (!x. op = Var x ==> lookup_var x s = lookup_var x t) ==>
  eval_operand op s = eval_operand op t
Proof
  Cases_on `op` >> simp[eval_operand_def]
QED

Theorem abi_decoder_vars_extend_refl[simp]:
  abi_decoder_vars_extend extras s s
Proof
  simp[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_decoder_vars_extend_update:
  abi_decoder_vars_extend extras s t ==>
  abi_decoder_vars_extend extras (update_var x v s) (update_var x v t)
Proof
  rw[abi_decoder_vars_extend_def, update_var_def,
     Excl "vsr_complete_mask_equality"] >>
  irule abi_decoder_var_map_update >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_vars_extend_valid:
  valid_state_rel (abi_decoder_vars_extend extras)
    (\s t. vsr_term_frame s = vsr_term_frame t)
Proof
  rw[valid_state_rel_def, abi_decoder_vars_extend_def, update_var_def,
     Excl "vsr_complete_mask_equality"] >>
  metis_tac[abi_decoder_var_map_update, abi_decoder_operand_agreement,
            abi_decoder_frame_labels, abi_decoder_frame_weaken]
QED

Theorem abi_decoder_vars_extend_eval:
  abi_decoder_vars_extend extras s t /\ eval_operand op s = SOME v ==>
  eval_operand op t = SOME v
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by
    (fs[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"] >>
     drule (cj 1 abi_decoder_frame_labels) >> simp[]) >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def] >>
  irule abi_decoder_var_map_lookup >>
  qexistsl_tac [`extras`, `s.vs_vars`] >>
  fs[abi_decoder_vars_extend_def, Excl "vsr_complete_mask_equality"]
QED

Theorem abi_decoder_vars_extend_restore:
  abi_decoder_vars_extend extras s t ==> (t with vs_vars := s.vs_vars) = s
Proof
  simp_tac bool_ss [abi_decoder_vars_extend_def] >> strip_tac >>
  qpat_x_assum `vsr_frame s = vsr_frame t`
    (mp_tac o AP_TERM ``\u:venom_state. u with vs_vars := s.vs_vars``) >>
  simp[vsr_frame_def] >> metis_tac[]
QED

Theorem abi_decoder_vars_extend_observations:
  abi_decoder_vars_extend extras s t ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\ t.vs_labels = s.vs_labels /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule abi_decoder_vars_extend_restore >>
  disch_then (mp_tac o AP_TERM ``\u:venom_state.
    (u.vs_memory,u.vs_call_ctx,u.vs_data_section,u.vs_labels,u.vs_allocas,u.vs_alloca_next)``) >>
  simp[]
QED

Theorem abi_decoder_vars_extend_fresh:
  abi_decoder_vars_extend extras s t /\ fresh_vars_wrt st s /\
  (!n. st.cs_next_var <= n ==> STRING #"%" (toString n) NOTIN FDOM extras) ==>
  fresh_vars_wrt st t
Proof
  pure_rewrite_tac [abi_decoder_vars_extend_def, abi_decoder_var_map_def,
    fresh_vars_wrt_def] >> rpt strip_tac >>
  qpat_assum `t.vs_vars SUBMAP _`
    (assume_tac o MATCH_MP SUBMAP_FDOM_SUBSET) >>
  fs[SUBSET_DEF, FDOM_FUNION, arithmeticTheory.GREATER_EQ,
     Excl "vsr_complete_mask_equality"] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VAR_EXTEND_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI variable extension not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderVarExtend");
