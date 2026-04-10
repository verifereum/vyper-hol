Theory evalCompiler
Ancestors compileVyper
Libs finite_mapLib computeLib wordsLib

val () = the_compset := add_finite_map_compset(!the_compset)

val () = Globals.max_print_depth := 20

val result = EVAL ``compile_vyper [] I Linear``

(*
EVAL ``
let tops = [];
    pipeline = I;
    dispatch_strategy = Linear;
       tenv = type_env tops;
       sft = make_struct_fields_map tops;
       sft_fn = get_struct_fields sft;
       immutables_len = compute_immutables_len sft_fn tops;
       nkey_map = assign_nkeys tops 0;
       use_trans = F;
       (ext_fns,int_fns,fb_fn,ctor_fn) = classify_functions tops;
       selectors = build_selectors tenv ext_fns;
       external_fns =
         MAP (package_external_fn tops use_trans nkey_map) ext_fns;
       runtime_int_fns =
         MAP (package_internal_fn tops use_trans nkey_map F) int_fns;
       fallback_fn = package_fallback_fn tops use_trans nkey_map fb_fn;
       entry_label = "__entry";
       method_ids = MAP FST selectors;
       entry_info = build_dense_entry_info selectors external_fns;
       (bucket_count,fn_meta_bytes,dense_buckets) =
         case dispatch_strategy of
           Linear => (0,0,[])
         | Sparse =>
           (let
              (nb,_10) = generate_sparse_jumptable_buckets method_ids
            in
              (nb,0,[]))
         | Dense =>
           (let
              min_cds_values =
                MAP (λ(_0,_1,_2,min_cds,_3,_4,_5,_6,_7,_8,_9). min_cds)
                  external_fns;
              fn_mb = compute_fn_metadata_bytes min_cds_values
            in
              case generate_dense_jumptable_info method_ids of
                NONE => (1,fn_mb,[])
              | SOME (nb,buckets) => (nb,fn_mb,buckets));
       (runtime_ctx,runtime_data) =
         run_lowering selectors external_fns runtime_int_fns fallback_fn
           dispatch_strategy bucket_count fn_meta_bytes dense_buckets
           entry_info entry_label;
       runtime_ctx' = pipeline runtime_ctx;
       codegen_result = codegen runtime_ctx' FEMPTY runtime_data;
       runtime_bytecode = THE codegen_result;
       has_constructor = IS_SOME ctor_fn;
            deploy_int_fns =
              MAP (package_internal_fn tops use_trans nkey_map T) int_fns;
            (ctor_cenv,ctor_args,ctor_payable,ctor_nr,ctor_nkey,ctor_trans,
               ctor_body,ctor_ret) =
              case ctor_fn of
                NONE => (ARB,[],F,F,0,F,[],NoneT)
              | SOME cf => package_constructor tops use_trans nkey_map cf;
            (deploy_ctx,deploy_data_base) =
              run_deploy_lowering has_constructor (LENGTH runtime_bytecode)
                immutables_len ctor_args 0 deploy_int_fns ctor_cenv ctor_body
                ctor_payable ctor_nr ctor_nkey ctor_trans "__deploy";
            deploy_ctx' = pipeline deploy_ctx;
            deploy_data =
              deploy_data_base ⧺
              [<|ds_label := "runtime_begin";
                 ds_items := [DataBytes runtime_bytecode]|>];
            codegen_deploy_result = codegen deploy_ctx' FEMPTY deploy_data;
       (*
            | SOME deploy_bytecode => SOME (deploy_bytecode,runtime_bytecode)))
       ctx = runtime_ctx';
       fn_eom_map = FEMPTY;
       data_seg = runtime_data;
       plan_result = generate_context_plan ctx fn_eom_map;
       plan = THE plan_result;
       reduced_plan = TAKE 2 plan;
       code_asm = execute_plan reduced_plan;
       *)
in
(("deploy_ctx'", deploy_ctx'),
 ("deploy_data", deploy_data))
``
*)
