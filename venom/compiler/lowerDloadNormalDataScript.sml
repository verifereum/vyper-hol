Theory lowerDloadNormalData
Ancestors
  lowerDloadParameterEnvelope lowerDloadCopyCertificate lowerDloadCoverageInvariant
  lowerDloadSharedState o1PassContract ptrDiscipline venomState finite_map pred_set list

(* Normal-boundary data only. Source annotations, configured positions and
   saved control correspondence remain outside this conjunction. *)
Definition ld_normal_data_def:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f <=>
  ld_frame_data V U E L H AP BP AG BH tn un s t /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz < dimword(:256) /\ bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  ld_alloc_account keys d A s t /\
  d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\ ld_stack_bound t.vs_alloca_next gstk /\
  lo <= f /\ allocas_from f t /\ f <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  ((CS.ctx_entry = SOME fn.fn_name /\ AP = [] /\ BP = [] /\
      entry_fn_no_params fn) \/
   (LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
    LENGTH s.vs_params = LENGTH t.vs_params /\
    (!q. q < LENGTH s.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s.vs_params) (EL q t.vs_params)))) /\
  s.vs_gas_readings = t.vs_gas_readings /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==> s.vs_transient a = t.vs_transient a)
End

Theorem ld_normal_data_frame:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  ld_frame_data V U E L H AP BP AG BH tn un s t
Proof
  simp[ld_normal_data_def]
QED

Theorem ld_normal_data_memory:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t)
Proof
  simp[ld_normal_data_def]
QED

Theorem ld_normal_data_geometry:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz < dimword(:256) /\ bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  ld_alloc_account keys d A s t /\
  d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\ ld_stack_bound t.vs_alloca_next gstk /\
  lo <= f /\ allocas_from f t /\ f <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz))
Proof
  simp[ld_normal_data_def] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem ld_normal_data_masks:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm
Proof
  simp[ld_normal_data_def] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem ld_normal_data_envelope:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  ((CS.ctx_entry = SOME fn.fn_name /\ AP = [] /\ BP = [] /\
      entry_fn_no_params fn) \/
   (LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
    LENGTH s.vs_params = LENGTH t.vs_params /\
    (!q. q < LENGTH s.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s.vs_params) (EL q t.vs_params))))
Proof
  simp[ld_normal_data_def]
QED

Theorem ld_normal_data_companions:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  s.vs_gas_readings = t.vs_gas_readings /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==> s.vs_transient a = t.vs_transient a)
Proof
  simp[ld_normal_data_def] >> strip_tac >> asm_rewrite_tac[]
QED

(* Assembly is the introduction direction of the defining conjunction; unlike
   a second certificate predicate it introduces no competing clause inventory. *)
Theorem ld_normal_data_assemble:
  ld_frame_data V U E L H AP BP AG BH tn un s t /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz < dimword(:256) /\ bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  ld_alloc_account keys d A s t /\
  d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\ ld_stack_bound t.vs_alloca_next gstk /\
  lo <= f /\ allocas_from f t /\ f <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  ((CS.ctx_entry = SOME fn.fn_name /\ AP = [] /\ BP = [] /\
      entry_fn_no_params fn) \/
   (LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
    LENGTH s.vs_params = LENGTH t.vs_params /\
    (!q. q < LENGTH s.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s.vs_params) (EL q t.vs_params)))) /\
  s.vs_gas_readings = t.vs_gas_readings /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==> s.vs_transient a = t.vs_transient a) ==>
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f
Proof
  rewrite_tac[ld_normal_data_def]
QED

Theorem ld_normal_data_unchanged:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  s' = s /\ t' = t /\ AG' = AG /\ BH' = BH /\ tn' = tn /\ un' = un ==>
  ld_normal_data CS fn V U lo E L H AP BP AG' BH' tn' un' s' t'
    astk live keys d A suspended gstk f
Proof
  strip_tac >> gvs[]
QED
