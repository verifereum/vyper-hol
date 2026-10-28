"""Literal behaviours for the complete supplied nested-place source matrix."""

DEFERRED = {
    'p57_int_struct_local_return': '#545: internal struct returns',
    'm10_imm_nested_array': '#563: immutable aggregates',
    'f32_for_storage_struct_field_arr': '#559: storage array iteration',
    'f38_for_storage_struct_field_arr_set': '#559: storage array iteration',
    'g2_a_dyn_nested': '#559/#560: nested Append and copy',
    'g3_st_dyn_field': '#559: attribute Append',
    's16_storage_map_of_dynarray_elem': '#559: subscript Append',
}

INITIAL_STORAGE = {
    'storage_struct_second_field': {0: 13, 1: 17},
    'g3_st_read_second_only': {0: 13, 1: 17},
    'g3_st_copy_to_mem': {0: 13, 1: 17},
    'g6_aug_field_second': {0: 13, 1: 3},
    'g3_st_in_expr': {0: 2, 1: 7},
    'g6_tuple_from_storage': {0: 13, 1: 17, 2: 19},
    'g7_coll_field_storage_rd': {0: 17, 1: 29},
    'f32_for_storage_struct_field_arr': {0: 7, 1: 1, 2: 2, 3: 3},
    'g7_struct_bytes_field_read': {
        1: 40,
        2: int.from_bytes(bytes(range(32)), 'big'),
        3: int.from_bytes(bytes(range(32, 40)).ljust(32, b'\0'), 'big'),
    },
}

RETURN_TYPES = {
    'g6_tuple_from_storage': ['uint256', 'uint256'],
    'st_array_field': ['(uint256,uint256[2])'],
    'g3_st_string_field': ['string'],
    'g7_struct_bytes_field_read': ['bytes'],
}

def known_dependency_failure(stem, error, stage):
    """Classify only the retained dependency failures, including their stage."""
    if stem in ('m10_imm_nested_array', 'p57_int_struct_local_return'):
        return (stage == 'NONE' and isinstance(error, KeyError)
                and f'actual/{stem}.hex' in str(error))
    if stage != 'PARITY_DEFECT' or not isinstance(error, ValueError):
        return False
    expected_errors = {
        'f32_for_storage_struct_field_arr': 'return 0, expected 6',
        'f38_for_storage_struct_field_arr_set': 'return 0, expected 14',
        'g2_a_dyn_nested': "b''",
        'g3_st_dyn_field': "b''",
        's16_storage_map_of_dynarray_elem': "b''",
    }
    return stem in expected_errors and str(error) == expected_errors[stem]

def full_cases(base, mapping, keccak):
    address = '0x' + '00' * 19 + '01'
    other = '0x' + '00' * 19 + '02'
    word = bytes(range(32))
    string_word = int.from_bytes(b'ab'.ljust(32, b'\0'), 'big')
    extra = [
        ('arr_2d_subscript', 'f(uint256[2][3],uint256,uint256)',
         ['uint256[2][3]', 'uint256', 'uint256'], [[[1,2],[3,4],[5,6]],2,1],6,{},{}),
        ('b06_struct_arr_field_elem','f(uint256,uint256)',['uint256']*2,[1,9],9,{},{}),
        ('f32_for_storage_struct_field_arr','f()',[],[],6,{0:7,1:1,2:2,3:3},{}),
        ('f38_for_storage_struct_field_arr_set','f()',[],[],14,{0:7,1:9,2:2,3:3},{}),
        ('g2_a_dyn_nested','f(uint256)',['uint256'],[9],9,{0:1,1:2,2:9,3:9},{}),
        ('g2_a_dyn_struct','f(uint256)',['uint256'],[9],9,{0:1,1:1,2:9},{}),
        ('g2_a_nested_fixed','f(uint256,uint256,uint256)',['uint256']*3,[2,1,9],9,{5:9},{}),
        ('g2_a_struct_fixed','f(uint256,uint256)',['uint256']*2,[1,9],9,{3:9},{}),
        ('g3_st_array_field','f(uint256,uint256)',['uint256']*2,[2,9],9,{3:9},{}),
        ('g3_st_copy_to_mem','f()',[],[],17,{0:13,1:17},{}),
        ('g3_st_dyn_field','f(uint256)',['uint256'],[9],9,{1:1,2:9},{}),
        ('g3_st_in_expr','f(uint256)',['uint256'],[5],9,{0:2,1:7},{}),
        ('g3_st_nested','f(uint256)',['uint256'],[9],9,{2:9},{}),
        ('g3_st_read_first_ref','f(uint256)',['uint256'],[9],9,{0:9},{}),
        ('g3_st_read_second','f(uint256)',['uint256'],[9],9,{1:9},{}),
        ('g3_st_read_second_only','f()',[],[],17,{0:13,1:17},{}),
        ('g3_st_string_field','f(string)',['string'],['ab'],'ab',{1:2,2:string_word},{}),
        ('g3_st_subword','f(address)',['address'],[address],1,{0:3,1:1},{}),
        ('g3_st_three_third','f(bytes32)',['bytes32'],[word],int.from_bytes(word,'big'),
         {2:int.from_bytes(word,'big')},{}),
        ('g4_t_array','f(uint256,uint256)',['uint256']*2,[2,9],9,{}, {2:9}),
        ('g4_t_dynarray','f(uint256)',['uint256'],[9],9,{}, {0:0,1:9}),
        ('g4_t_hashmap','f(uint256,uint256)',['uint256']*2,[1,9],9,{}, {mapping(0,1):9}),
        ('g4_t_struct','f(uint256)',['uint256'],[9],9,{}, {1:9}),
        ('g4_t_u8','f(uint8)',['uint8'],[9],9,{}, {0:9}),
        ('g5_hm_nested','f(address,address,uint256)',['address','address','uint256'],
         [address,other,9],9,{mapping(mapping(0,1),2):9},{}),
        ('g5_hm_nested_aug','f(address,address,uint256)',['address','address','uint256'],
         [address,other,3],None,{mapping(mapping(0,1),2):6},{}),
        ('g5_hm_val_array','f(uint256,uint256,uint256)',['uint256']*3,[1,2,9],9,
         {mapping(0,1)+2:9},{}),
        ('g5_hm_val_struct','f(uint256,uint256)',['uint256']*2,[1,9],9,{mapping(0,1)+1:9},{}),
        ('g5_hm_val_u8','f(uint256,uint8)',['uint256','uint8'],[1,9],9,{mapping(0,1):9},{}),
        ('g6_aug_field_second','f(uint256)',['uint256'],[4],13,{0:13,1:12},{}),
        ('g6_aug_hm','f(uint256)',['uint256'],[1],1,{mapping(0,1):1},{}),
        ('g6_tuple_from_storage','f()',[],[],(19,17),{0:13,1:17,2:19},{}),
        ('g7_aug_transient_arr','f(uint256)',['uint256'],[1],1,{}, {1:1}),
        ('g7_coll_field_storage','f(uint256)',['uint256'],[9],9,{1:9},{}),
        ('g7_coll_field_storage_rd','f()',[],[],17,{0:17,1:29,2:7},{}),
        ('g7_coll_memfield_storage','f(uint256)',['uint256'],[9],9,{},{}),
        ('g7_struct_bytes_field_read','f()',[],[],bytes(range(40)),INITIAL_STORAGE['g7_struct_bytes_field_read'],{}),
        ('m10_imm_nested_array','get(uint256)',['uint256'],[1],4,{},{}),
        ('p57_int_struct_local_return','foo(uint256)',['uint256'],[9],7,{},{}),
        ('s03_storage_nested_map_assign','f(address,uint256,uint256)',['address','uint256','uint256'],
         [address,2,9],None,{mapping(mapping(0,1),2):9},{}),
        ('s16_storage_map_of_dynarray_elem','f(uint256,uint256)',['uint256']*2,[1,9],None,
         {mapping(0,1):1,mapping(0,1)+1:9},{}),
        ('s18_storage_map_int128_key_aug','f(int128,uint256)',['int128','uint256'],[-1,9],None,
         {mapping(0,2**256-1):9},{}),
        ('s23_nested_map_read_call_inner_key','f()',[],[],0,{1:1},{}),
        ('s24_nested_map_read_call_outer_key','f()',[],[],0,{1:1},{}),
        ('st_array_field','f((uint256,uint256[2]))',['(uint256,uint256[2])'],
         [(7,[8,9])],(7,(8,9)),{},{}),
        ('st_nested_attr_q','f((uint256,(uint256,uint256)))',['(uint256,(uint256,uint256))'],
         [(7,(8,9))],9,{},{}),
        ('tup_nested_subscript','f(uint256)',['uint256'],[9],11,{},{}),
        ('x05_struct_field_named_like_storage','f(uint256)',['uint256'],[9],10,{0:0},{}),
        ('x07_local_named_like_storage_array','f(uint256)',['uint256'],[1],6,{0:0},{}),
    ]
    result = [((row[0],row[1],row[2],row[3],17,{0:13,1:17},row[6])
               if row[0] == 'storage_struct_second_field' else row) for row in base] + extra
    if len({row[0] for row in result}) != len(result):
        raise ValueError('duplicate full-matrix behaviour case')
    return result
