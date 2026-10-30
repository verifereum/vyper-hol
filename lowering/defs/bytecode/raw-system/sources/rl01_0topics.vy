# raw_log with no topics and literal data
@external
def foo():
    raw_log([], b"\x01\x02")
