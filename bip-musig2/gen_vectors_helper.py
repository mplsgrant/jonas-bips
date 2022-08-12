from reference import *

def gen_key_agg_vectors():
    print("key_agg_vectors.json: Intermediate tweaking result is point at infinity")
    sk = bytes.fromhex("7FB9E0E687ADA1EEBF7ECFE2F21E73EBDB51A7D450948DFE8D76D7F2D1007671")
    pk = keygen(sk)
    keygen_ctx = key_agg([pk])
    aggpoint, _, _ = keygen_ctx
    aggsk = key_agg_coeff([pk], pk)*int_from_bytes(sk) % n
    t = n - aggsk
    assert point_add(point_mul(G, t), aggpoint) == None
    is_xonly = False
    tweak = bytes_from_int(t)
    assert_raises(ValueError, lambda: apply_tweak(keygen_ctx, tweak, is_xonly), lambda e: True)
    print("  pubkey:", pk.hex().upper())
    print("  tweak: ", tweak.hex().upper())

gen_key_agg_vectors()
