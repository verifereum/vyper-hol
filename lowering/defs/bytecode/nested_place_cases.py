"""External prerequisites for the checked-in TASK witness sources.

Sources live in nested-places/sources; preparation never regenerates them.
"""
CONDITIONAL = {
    's20_nested_map_read_key_order':'#542', 's23_nested_map_read_call_inner_key':'#542',
    'm10_imm_nested_array':'#563', 'tup_nested_subscript':'#571',
    'p57_int_struct_local_return':'#545', 'f32_for_storage_struct_field_arr':'#559',
    'f38_for_storage_struct_field_arr_set':'#559', 'g2_a_dyn_nested':'#559 and #560',
    'g3_st_dyn_field':'#559', 's16_storage_map_of_dynarray_elem':'#559',
}
