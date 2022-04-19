from collections import namedtuple
from typing import Any, List, Optional, Tuple
import hashlib
import secrets
import time

#
# The following helper functions were copied from the BIP-340 reference implementation:
# https://github.com/bitcoin/bips/blob/master/bip-0340/reference.py
#

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

# Points are tuples of X and Y coordinates and the point at infinity is
# represented by the None keyword.
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798, 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

Point = Tuple[int, int]

# This implementation can be sped up by storing the midstate after hashing
# tag_hash instead of rehashing it all the time.
def tagged_hash(tag: str, msg: bytes) -> bytes:
    tag_hash = hashlib.sha256(tag.encode()).digest()
    return hashlib.sha256(tag_hash + tag_hash + msg).digest()

def is_infinite(P: Optional[Point]) -> bool:
    return P is None

def x(P: Point) -> int:
    assert not is_infinite(P)
    return P[0]

def y(P: Point) -> int:
    assert not is_infinite(P)
    return P[1]

def point_add(P1: Optional[Point], P2: Optional[Point]) -> Optional[Point]:
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    if (x(P1) == x(P2)) and (y(P1) != y(P2)):
        return None
    if P1 == P2:
        lam = (3 * x(P1) * x(P1) * pow(2 * y(P1), p - 2, p)) % p
    else:
        lam = ((y(P2) - y(P1)) * pow(x(P2) - x(P1), p - 2, p)) % p
    x3 = (lam * lam - x(P1) - x(P2)) % p
    return (x3, (lam * (x(P1) - x3) - y(P1)) % p)

def point_mul(P: Optional[Point], n: int) -> Optional[Point]:
    R = None
    for i in range(256):
        if (n >> i) & 1:
            R = point_add(R, P)
        P = point_add(P, P)
    return R

def bytes_from_int(x: int) -> bytes:
    return x.to_bytes(32, byteorder="big")

def bytes_from_point(P: Point) -> bytes:
    return bytes_from_int(x(P))

def lift_x(b: bytes) -> Optional[Point]:
    x = int_from_bytes(b)
    if x >= p:
        return None
    y_sq = (pow(x, 3, p) + 7) % p
    y = pow(y_sq, (p + 1) // 4, p)
    if pow(y, 2, p) != y_sq:
        return None
    return (x, y if y & 1 == 0 else p-y)

def int_from_bytes(b: bytes) -> int:
    return int.from_bytes(b, byteorder="big")

def has_even_y(P: Point) -> bool:
    assert not is_infinite(P)
    return y(P) % 2 == 0

def schnorr_verify(msg: bytes, pubkey: bytes, sig: bytes) -> bool:
    if len(msg) != 32:
        raise ValueError('The message must be a 32-byte array.')
    if len(pubkey) != 32:
        raise ValueError('The public key must be a 32-byte array.')
    if len(sig) != 64:
        raise ValueError('The signature must be a 64-byte array.')
    P = lift_x(pubkey)
    r = int_from_bytes(sig[0:32])
    s = int_from_bytes(sig[32:64])
    if (P is None) or (r >= p) or (s >= n):
        return False
    e = int_from_bytes(tagged_hash("BIP0340/challenge", sig[0:32] + pubkey + msg)) % n
    R = point_add(point_mul(G, s), point_mul(P, n - e))
    if (R is None) or (not has_even_y(R)) or (x(R) != r):
        return False
    return True

#
# End of helper functions copied from BIP-340 reference implementation.
#

# There are two types of exceptions that can be raised by this implementation:
#   - ValueError for indicating that an input doesn't conform to some function
#     precondition (e.g. an input array is the wrong length, a serialized
#     representation doesn't have the correct format).
#   - InvalidContributionError for indicating that a signer (or the
#     aggregator) is misbehaving in the protocol.
#
# Assertions are used to (1) satisfy the type-checking system, and (2) check for
# inconvenient events that can't happen except with negligible probability (e.g.
# output of a hash function is 0) and can't be manually triggered by any
# signer.

# This exception is raised if a party (signer or nonce aggregator) sends invalid
# values. Actual implementations should not crash when receiving invalid
# contributions. Instead, they should hold the offending party accountable.
class InvalidContributionError(Exception):
    def __init__(self, signer, contrib):
        self.signer = signer
        # contrib is one of "pubkey", "pubnonce", "aggnonce", or "psig".
        self.contrib = contrib

infinity = None

def cbytes(P: Point) -> bytes:
    a = b'\x02' if has_even_y(P) else b'\x03'
    return a + bytes_from_point(P)

def point_negate(P: Optional[Point]) -> Optional[Point]:
    if P is None:
        return P
    return (x(P), p - y(P))

def cpoint(x: bytes) -> Point:
    P = lift_x(x[1:33])
    if P is None:
        raise ValueError('x is not a valid compressed point.')
    if x[0] == 2:
        return P
    elif x[0] == 3:
        P = point_negate(P)
        assert P is not None
        return P
    else:
        raise ValueError('x is not a valid compressed point.')

def key_agg(pubkeys: List[bytes], tweaks: List[bytes], is_xonly: List[bool]) -> bytes:
    Q, _, _ = key_agg_internal(pubkeys, tweaks, is_xonly)
    return bytes_from_point(Q)

def key_agg_internal(pubkeys: List[bytes], tweaks: List[bytes], is_xonly: List[bool]) -> Tuple[Point, int, int]:
    pk2 = get_second_key(pubkeys)
    u = len(pubkeys)
    Q = infinity
    for i in range(u):
        P_i = lift_x(pubkeys[i])
        if P_i is None:
            raise InvalidContributionError(i, "pubkey")
        a_i = key_agg_coeff_internal(pubkeys, pubkeys[i], pk2)
        Q = point_add(Q, point_mul(P_i, a_i))
    # Q is not the point at infinity except with negligible probability.
    assert(Q is not None)
    gacc = 1
    tacc = 0
    v = len(tweaks)
    for i in range(v):
        Q, gacc, tacc = apply_tweak(Q, gacc, tacc, tweaks[i], is_xonly[i])
    return Q, gacc, tacc

def hash_keys(pubkeys: List[bytes]) -> bytes:
    return tagged_hash('KeyAgg list', b''.join(pubkeys))

def get_second_key(pubkeys: List[bytes]) -> bytes:
    u = len(pubkeys)
    for j in range(1, u):
        if pubkeys[j] != pubkeys[0]:
            return pubkeys[j]
    return bytes_from_int(0)

def key_agg_coeff(pubkeys: List[bytes], pk_: bytes) -> int:
    pk2 = get_second_key(pubkeys)
    return key_agg_coeff_internal(pubkeys, pk_, pk2)

def key_agg_coeff_internal(pubkeys: List[bytes], pk_: bytes, pk2: bytes) -> int:
    L = hash_keys(pubkeys)
    if pk_ == pk2:
        return 1
    return int_from_bytes(tagged_hash('KeyAgg coefficient', L + pk_)) % n

def apply_tweak(Q: Point, gacc: int, tacc: int, tweak_i: bytes, is_xonly_i: bool) -> Tuple[Point, int, int]:
    if len(tweak_i) != 32:
        raise ValueError('The tweak must be a 32-byte array.')
    if is_xonly_i and not has_even_y(Q):
        g = n - 1
    else:
        g = 1
    t_i = int_from_bytes(tweak_i)
    if t_i >= n:
        raise ValueError('The tweak must be less than n.')
    Q_i = point_add(point_mul(Q, g), point_mul(G, t_i))
    if Q_i is None:
        raise ValueError('The result of tweaking cannot be infinity.')
    gacc_i = g * gacc % n
    tacc_i = (t_i + g * tacc) % n
    return Q_i, gacc_i, tacc_i

def bytes_xor(a: bytes, b: bytes) -> bytes:
    return bytes(x ^ y for x, y in zip(a, b))

def nonce_hash(rand: bytes, aggpk: bytes, i: int, msg: bytes, extra_in: bytes) -> int:
    buf = b''
    buf += rand
    buf += len(aggpk).to_bytes(1, 'big')
    buf += aggpk
    buf += len(msg).to_bytes(1, 'big')
    buf += msg
    buf += len(extra_in).to_bytes(4, 'big')
    buf += extra_in
    buf += i.to_bytes(1, 'big')
    return int_from_bytes(tagged_hash('MuSig/nonce', buf))

def nonce_gen_internal(rand_: bytes, sk: bytes, aggpk: bytes, msg: bytes, extra_in: bytes) -> Tuple[bytes, bytes]:
    if len(sk) > 0:
        rand = bytes_xor(sk, tagged_hash('MuSig/aux', rand_))
    else:
        rand = rand_
    k_1 = nonce_hash(rand, aggpk, 0, msg, extra_in)
    k_2 = nonce_hash(rand, aggpk, 1, msg, extra_in)
    # k_1 == 0 or k_2 == 0 cannot occur except with negligible probability.
    assert k_1 != 0
    assert k_2 != 0
    R_1_ = point_mul(G, k_1)
    R_2_ = point_mul(G, k_2)
    assert R_1_ is not None
    assert R_2_ is not None
    pubnonce = cbytes(R_1_) + cbytes(R_2_)
    secnonce = bytes_from_int(k_1) + bytes_from_int(k_2)
    return secnonce, pubnonce

def nonce_gen(sk: bytes, aggpk: bytes, msg: bytes, extra_in: bytes) -> Tuple[bytes, bytes]:
    if len(sk) not in (0, 32):
        raise ValueError('The optional byte array sk must have length 0 or 32.')
    if len(aggpk) not in (0, 32):
        raise ValueError('The optional byte array aggpk must have length 0 or 32.')
    if len(msg) not in (0, 32):
        raise ValueError('The optional byte array msg must have length 0 or 32.')
    rand_ = secrets.token_bytes(32)
    return nonce_gen_internal(rand_, sk, aggpk, msg, extra_in)

def nonce_agg(pubnonces: List[bytes]) -> bytes:
    u = len(pubnonces)
    aggnonce = b''
    for i in (1, 2):
        R_i_ = infinity
        for j in range(u):
            try:
                R_ij = cpoint(pubnonces[j][(i-1)*33:i*33])
            except ValueError:
                raise InvalidContributionError(j, "pubnonce")
            R_i_ = point_add(R_i_, R_ij)
        R_i = R_i_ if not is_infinite(R_i_) else G
        assert R_i is not None
        aggnonce += cbytes(R_i)
    return aggnonce

SessionContext = namedtuple('SessionContext', ['aggnonce', 'pubkeys', 'tweaks', 'is_xonly', 'msg'])

def get_session_values(session_ctx: SessionContext) -> Tuple[Point, int, int, int, Point, int]:
    (aggnonce, pubkeys, tweaks, is_xonly, msg) = session_ctx
    Q, gacc_v, tacc_v = key_agg_internal(pubkeys, tweaks, is_xonly)
    b = int_from_bytes(tagged_hash('MuSig/noncecoef', aggnonce + bytes_from_point(Q) + msg)) % n
    try:
        R_1 = cpoint(aggnonce[0:33])
        R_2 = cpoint(aggnonce[33:66])
    except ValueError:
        # Nonce aggregator sent invalid nonces
        raise InvalidContributionError(None, "aggnonce")
    R = point_add(R_1, point_mul(R_2, b))
    # The aggregate public nonce cannot be infinity except with negligible probability.
    assert R is not None
    e = int_from_bytes(tagged_hash('BIP0340/challenge', bytes_from_point(R) + bytes_from_point(Q) + msg)) % n
    return (Q, gacc_v, tacc_v, b, R, e)

def get_session_key_agg_coeff(session_ctx: SessionContext, P: Point) -> int:
    (_, pubkeys, _, _, _) = session_ctx
    return key_agg_coeff(pubkeys, bytes_from_point(P))

# Callers should overwrite secnonce with zeros after calling sign.
def sign(secnonce: bytes, sk: bytes, session_ctx: SessionContext) -> bytes:
    (Q, gacc_v, _, b, R, e) = get_session_values(session_ctx)
    k_1_ = int_from_bytes(secnonce[0:32])
    k_2_ = int_from_bytes(secnonce[32:64])
    if not 0 < k_1_ < n:
        raise ValueError('first secnonce value is out of range.')
    if not 0 < k_2_ < n:
        raise ValueError('second secnonce value is out of range.')
    k_1 = k_1_ if has_even_y(R) else n - k_1_
    k_2 = k_2_ if has_even_y(R) else n - k_2_
    d_ = int_from_bytes(sk)
    if not 0 < d_ < n:
        raise ValueError('secret key value is out of range.')
    P = point_mul(G, d_)
    assert P is not None
    a = get_session_key_agg_coeff(session_ctx, P)
    gp = 1 if has_even_y(P) else n - 1
    g_v = 1 if has_even_y(Q) else n - 1
    d = g_v * gacc_v * gp * d_ % n
    s = (k_1 + b * k_2 + e * a * d) % n
    psig = bytes_from_int(s)
    R_1_ = point_mul(G, k_1_)
    R_2_ = point_mul(G, k_2_)
    assert R_1_ is not None
    assert R_2_ is not None
    pubnonce = cbytes(R_1_) + cbytes(R_2_)
    # Optional correctness check. The result of signing should pass signature verification.
    assert partial_sig_verify_internal(psig, pubnonce, bytes_from_point(P), session_ctx)
    return psig

def partial_sig_verify(psig: bytes, pubnonces: List[bytes], pubkeys: List[bytes], tweaks: List[bytes], is_xonly: List[bool], msg: bytes, i: int) -> bool:
    aggnonce = nonce_agg(pubnonces)
    session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
    return partial_sig_verify_internal(psig, pubnonces[i], pubkeys[i], session_ctx)

def partial_sig_verify_internal(psig: bytes, pubnonce: bytes, pk_: bytes, session_ctx: SessionContext) -> bool:
    (Q, gacc_v, _, b, R, e) = get_session_values(session_ctx)
    s = int_from_bytes(psig)
    if s >= n:
        return False
    R_1_ = cpoint(pubnonce[0:33])
    R_2_ = cpoint(pubnonce[33:66])
    R__ = point_add(R_1_, point_mul(R_2_, b))
    R_ = R__ if has_even_y(R) else point_negate(R__)
    g_v = 1 if has_even_y(Q) else n - 1
    g_ = g_v * gacc_v % n
    P = point_mul(lift_x(pk_), g_)
    if P is None:
        return False
    a = get_session_key_agg_coeff(session_ctx, P)
    return point_mul(G, s) == point_add(R_, point_mul(P, e * a % n))

def partial_sig_agg(psigs: List[bytes], session_ctx: SessionContext) -> Optional[bytes]:
    (Q, _, tacc_v, _, R, e) = get_session_values(session_ctx)
    s = 0
    u = len(psigs)
    for i in range(u):
        s_i = int_from_bytes(psigs[i])
        if s_i >= n:
            return None
        s = (s + s_i) % n
    g_v = 1 if has_even_y(Q) else n - 1
    s = (s + e * g_v * tacc_v) % n
    return bytes_from_point(R) + bytes_from_int(s)
#
# The following code is only used for testing.
# Test vectors were copied from libsecp256k1-zkp's MuSig test file.
# See `musig_test_vectors_keyagg` and `musig_test_vectors_sign` in
# https://github.com/ElementsProject/secp256k1-zkp/blob/master/src/modules/musig/tests_impl.h
#
def fromhex_all(l):
    return [bytes.fromhex(l_i) for l_i in l]

# Check that calling `try_fn` raises a `exception`. If `exception` is raised,
# examine it with `except_fn`.
def assertRaises(exception, try_fn, except_fn):
    try:
        try_fn()
        raise RuntimeError("Exception was _not_ raised in a test where it was required.")
    except exception as e:
        assert(except_fn(e))

def test_key_agg_vectors():
    X = fromhex_all([
        'F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9',
        'DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659',
        '3590A94E768F8E1815C2F24B4D80A8E3149316C3518CE7B7AD338368D038CA66',
    ])

    expected = fromhex_all([
        'E5830140512195D74C8307E39637CBE5FB730EBEAB80EC514CF88A877CEEEE0B',
        'D70CD69A2647F7390973DF48CBFA2CCC407B8B2D60B08C5F1641185C7998A290',
        '81A8B093912C9E481408D09776CEFB48AEB8B65481B6BAAFB3C5810106717BEB',
        '2EB18851887E7BDC5E830E89B19DDBC28078F1FA88AAD0AD01CA06FE4F80210B',
    ])

    # Vector 1
    assert key_agg([X[0], X[1], X[2]], [], []) == expected[0]
    # Vector 2
    assert key_agg([X[2], X[1], X[0]], [], []) == expected[1]
    # Vector 3
    assert key_agg([X[0], X[0], X[0]], [], []) == expected[2]
    # Vector 4
    assert key_agg([X[0], X[0], X[1], X[1]], [], []) == expected[3]
    # Vector 5: Invalid public key
    invalid_pk = bytes.fromhex('0000000000000000000000000000000000000000000000000000000000000005')
    assertRaises(InvalidContributionError,
                 lambda: key_agg([X[0], invalid_pk], [], []),
                 lambda e: e.signer == 1 and e.contrib == "pubkey")
    # Vector 6: Public key exceeds field size
    invalid_pk = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30')
    assertRaises(InvalidContributionError,
                 lambda: key_agg([X[0], invalid_pk], [], []),
                 lambda e: e.signer == 1 and e.contrib == "pubkey")
    # Vector 7: Tweak is out of range
    invalid_tweak = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141')
    assertRaises(ValueError,
                 lambda: key_agg([X[0], X[1]], [invalid_tweak], [True]),
                 lambda e: str(e) == 'The tweak must be less than n.')
    # Vector 8: Intermediate tweaking result is point at infinity
    G_ = bytes_from_point(G)
    coeff = bytes_from_int(n - key_agg_coeff([G_], G_))
    assertRaises(ValueError,
                 lambda: key_agg([G_], [coeff], [False]),
                 lambda e: str(e) == 'The result of tweaking cannot be infinity.')

def test_nonce_gen_vectors():
    def fill(i):
        return i.to_bytes(1, byteorder='big') * 32
    rand_ = fill(0)
    msg = fill(1)
    sk = fill(2)
    aggpk = fill(3)
    extra_in = fill(4)

    expected = fromhex_all([
        '149378B996F012F70C1016C29AE0A9B1D86AAD557CCD29178A24479756205DFD' +
        '6285697E57E8578FCFDE6FE7FA4B6CA8E3A5AECAB4FB92F84B7F9DF8DDEF4DB8',
        '6613EA4A36A50F34990EAF73612EAA28636ED01325793456C04D8D89DB49372B' +
        '54E9DB34D09CBD394DB3FE3CCFFBCA6ED016F3AC877938613095893F54FA70DF',
        '7B3B5A002356471AF0E961DE2549C121BD0D48ABCEEDC6E034BDDF86AD3E0A18' +
        '7ECEE674CEF7364B0BC4BEEFB8B66CAD89F98DE2F8C5A5EAD5D1D1E4BD7D04CD'
    ])

    assert nonce_gen_internal(rand_, sk, aggpk, msg, extra_in)[0] == expected[0]
    assert nonce_gen_internal(rand_, sk, aggpk, b'', extra_in)[0] == expected[1]
    assert nonce_gen_internal(rand_, b'', b'', b'', b'')[0] == expected[2]

def test_nonce_agg_vectors():
    pnonce = fromhex_all([
        '020151C80F435648DF67A22B749CD798CE54E0321D034B92B709B567D60A42E666' +
        '03BA47FBC1834437B3212E89A84D8425E7BF12E0245D98262268EBDCB385D50641',
        '03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A6' +
        '0248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B833',
    ])
    expected = fromhex_all([
        '035FE1873B4F2967F52FEA4A06AD5A8ECCBE9D0FD73068012C894E2E87CCB5804B' +
        '024725377345BDE0E9C33AF3C43C0A29A9249F2F2956FA8CFEB55C8573D0262DC8'
    ])

    # Vector 1
    assert nonce_agg([pnonce[0], pnonce[1]]) == expected[0]
    # Vector 2: Public nonce from signer 1 is invalid due wrong tag, 0x04, in
    # the first half
    invalid_pnonce = bytes.fromhex(
        '04FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A6' +
        '0248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B833')
    assertRaises(InvalidContributionError,
                 lambda: nonce_agg([pnonce[0], invalid_pnonce]),
                 lambda e: e.signer == 1 and e.contrib == "pubnonce")
    # Vector 3: Public nonce from signer 0 is invalid because the second half
    # does not correspond to an X coordinate
    invalid_pnonce = bytes.fromhex(
        '03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A6' +
        '0248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B831')
    assertRaises(InvalidContributionError,
                 lambda: nonce_agg([invalid_pnonce, pnonce[1]]),
                 lambda e: e.signer == 0 and e.contrib == "pubnonce")
    # Vector 4: Public nonce from signer 0 is invalid because second half
    # exceeds field size
    invalid_pnonce = bytes.fromhex(
        '03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A6' +
        '02FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30')
    assertRaises(InvalidContributionError,
                 lambda: nonce_agg([invalid_pnonce, pnonce[1]]),
                 lambda e: e.signer == 0 and e.contrib == "pubnonce")
    # Vector 5: Sum of second points encoded in the nonces would be point at
    # infinity, therefore set sum to base point G
    neg_G = point_mul(G, n - 1)
    assert nonce_agg([pnonce[0][0:33] + cbytes(G), pnonce[1][0:33] + cbytes(neg_G)]) == expected[0][0:33] + cbytes(G)

def test_sign_verify_vectors():
    X = fromhex_all([
        'F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9',
        'DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659',
    ])

    secnonce = bytes.fromhex(
        '508B81A611F100A6B2B6B29656590898AF488BCF2E1F55CF22E5CFB84421FE61' +
        'FA27FD49B1D50085B481285E1CA205D55C82CC1B31FF5CD54A489829355901F7')

    # The public nonce corresponding to secnonce is at index 0
    pnonce = fromhex_all([
        '0337C87821AFD50A8644D820A8F3E02E499C931865C2360FB43D0A0D20DAFE07EA' +
        '0287BF891D2A6DEAEBADC909352AA9405D1428C15F4B75F04DAE642A95C2548480',
        '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798' +
        '0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798',
        '032DE2662628C90B03F5E720284EB52FF7D71F4284F627B68A853D78C78E1FFE93' +
        '03E4C5524E83FFE1493B9077CF1CA6BEB2090C93D930321071AD40B2F44E599046'
    ])

    aggnonce = bytes.fromhex(
        '028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '037496A3CC86926D452CAFCFD55D25972CA1675D549310DE296BFF42F72EEEA8C9')

    sk  = bytes.fromhex('7FB9E0E687ADA1EEBF7ECFE2F21E73EBDB51A7D450948DFE8D76D7F2D1007671')
    msg = bytes.fromhex('F95466D086770E689964664219266FE5ED215C92AE20BAB5C9D79ADDDDF3C0CF')

    expected = fromhex_all([
        '68537CC5234E505BD14061F8DA9E90C220A181855FD8BDB7F127BB12403B4D3B',
        '2DF67BFFF18E3DE797E13C6475C963048138DAEC5CB20A357CECA7C8424295EA',
        '0D5B651E6DE34A29A12DE7A8B4183B4AE6A7F7FBE15CDCAFA4A3D1BCAABC7517',
    ])

    pk = bytes_from_point(point_mul(G, int_from_bytes(sk)))

    # Vector 1
    session_ctx = SessionContext(aggnonce, [pk, X[0], X[1]], [], [], msg)
    assert sign(secnonce, sk, session_ctx) == expected[0]
    # WARNING: An actual implementation should clear the secnonce after use,
    # e.g. by setting secnonce = bytes(64) after usage. Reusing the secnonce, as
    # we do here for testing purposes, can leak the secret key.

    # Vector 2
    session_ctx = SessionContext(aggnonce, [X[0], pk, X[1]], [], [], msg)
    assert sign(secnonce, sk, session_ctx) == expected[1]

    # Vector 3
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], [], [], msg)
    assert sign(secnonce, sk, session_ctx) == expected[2]

    # Vector 4: Signer 2 provided an invalid public key
    invalid_pk = bytes.fromhex('0000000000000000000000000000000000000000000000000000000000000007')
    session_ctx = SessionContext(aggnonce, [X[0], pk, invalid_pk], [], [], msg)
    assertRaises(InvalidContributionError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: e.signer == 2 and e.contrib == "pubkey")

    # Vector 5: Aggregate nonce is invalid due wrong tag, 0x04, in the first
    # half
    invalid_aggnonce = bytes.fromhex(
        '048465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '037496A3CC86926D452CAFCFD55D25972CA1675D549310DE296BFF42F72EEEA8C9')
    session_ctx = SessionContext(invalid_aggnonce, [X[0], X[1], pk], [], [], msg)
    assertRaises(InvalidContributionError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: e.signer == None and e.contrib == "aggnonce")
    # Vector 6: Aggregate nonce is invalid because the second half does not
    # correspond to an X coordinate
    invalid_aggnonce = bytes.fromhex(
        '028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '020000000000000000000000000000000000000000000000000000000000000009')
    session_ctx = SessionContext(invalid_aggnonce, [X[0], X[1], pk], [], [], msg)
    assertRaises(InvalidContributionError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: e.signer == None and e.contrib == "aggnonce")
    # Vector 7: Aggregate nonce is invalid because second half exceeds field
    # size
    invalid_aggnonce = bytes.fromhex(
        '028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '02FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30')
    session_ctx = SessionContext(invalid_aggnonce, [X[0], X[1], pk], [], [], msg)
    assertRaises(InvalidContributionError,
                 lambda: sign(secnonce, sk, session_ctx),
                 lambda e: e.signer == None and e.contrib == "aggnonce")

    # Verification test vectors
    # Vector 8
    assert partial_sig_verify(expected[0], pnonce, [pk, X[0], X[1]], [], [], msg, 0)
    # Vector 9
    assert partial_sig_verify(expected[1], [pnonce[1], pnonce[0], pnonce[2]], [X[0], pk, X[1]], [], [], msg, 1)
    # Vector 10
    assert partial_sig_verify(expected[2], [pnonce[1], pnonce[2], pnonce[0]], [X[0], X[1], pk], [], [], msg, 2)

    # Vector 11: Wrong signature (which is equal to the negation of valid signature expected[0])
    wrong_sig = bytes.fromhex('97AC833ADCB1AFA42EBF9E0725616F3C9A0D5B614F6FE283CEAAA37A8FFAF406')
    assert not partial_sig_verify(wrong_sig, pnonce, [pk, X[0], X[1]], [], [], msg, 0)
    # Vector 12: Wrong signer
    assert not partial_sig_verify(expected[0], pnonce, [pk, X[0], X[1]], [], [], msg, 1)
    # Vector 13: Signature exceeds group size
    wrong_sig = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141')
    assert not partial_sig_verify(wrong_sig, pnonce, [pk, X[0], X[1]], [], [], msg, 0)
    # Vector 14: Invalid pubnonce
    invalid_pubnonce = bytes.fromhex('020000000000000000000000000000000000000000000000000000000000000009')
    assertRaises(InvalidContributionError,
                 lambda: partial_sig_verify(expected[0], [invalid_pubnonce, pnonce[1], pnonce[2]], [pk, X[0], X[1]], [], [], msg, 0),
                 lambda e: e.signer == 0 and e.contrib == "pubnonce")
    # Vector 15: Invalid public key
    assertRaises(InvalidContributionError,
                 lambda: partial_sig_verify(expected[0], pnonce, [invalid_pk, X[0], X[1]], [], [], msg, 0),
                 lambda e: e.signer == 0 and e.contrib == "pubkey")

def test_tweak_vectors():
    X = fromhex_all([
        'F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9',
        'DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659',
    ])

    secnonce = bytes.fromhex(
        '508B81A611F100A6B2B6B29656590898AF488BCF2E1F55CF22E5CFB84421FE61' +
        'FA27FD49B1D50085B481285E1CA205D55C82CC1B31FF5CD54A489829355901F7')

    aggnonce = bytes.fromhex(
        '028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61' +
        '037496A3CC86926D452CAFCFD55D25972CA1675D549310DE296BFF42F72EEEA8C9')

    sk  = bytes.fromhex('7FB9E0E687ADA1EEBF7ECFE2F21E73EBDB51A7D450948DFE8D76D7F2D1007671')
    msg = bytes.fromhex('F95466D086770E689964664219266FE5ED215C92AE20BAB5C9D79ADDDDF3C0CF')

    tweaks = fromhex_all([
        'E8F791FF9225A2AF0102AFFF4A9A723D9612A682A25EBE79802B263CDFCD83BB',
        'AE2EA797CC0FE72AC5B97B97F3C6957D7E4199A167A58EB08BCAFFDA70AC0455',
        'F52ECBC565B3D8BEA2DFD5B75A4F457E54369809322E4120831626F290FA87E0',
        '1969AD73CC177FA0B4FCED6DF1F7BF9907E665FDE9BA196A74FED0A3CF5AEF9D',
    ])

    expected = fromhex_all([
        '5E24C7496B565DEBC3B9639E6F1304A21597F9603D3AB05B4913641775E1375B',
        '78408DDCAB4813D1394C97D493EF1084195C1D4B52E63ECD7BC5991644E44DDD',
        'C3A829A81480E36EC3AB052964509A94EBF34210403D16B226A6F16EC85B7357',
        '8C4473C6A382BD3C4AD7BE59818DA5ED7CF8CEC4BC21996CFDA08BB4316B8BC7',
    ])

    pk = bytes_from_point(point_mul(G, int_from_bytes(sk)))

    # A single x-only tweak
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], tweaks[:1], [True], msg)
    assert sign(secnonce, sk, session_ctx) == expected[0]
    # WARNING: An actual implementation should clear the secnonce after use,
    # e.g. by setting secnonce = bytes(64) after usage. Reusing the secnonce, as
    # we do here for testing purposes, can leak the secret key.

    # A single ordinary tweak
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], tweaks[:1], [False], msg)
    assert sign(secnonce, sk, session_ctx) == expected[1]

    # An ordinary tweak followed by an x-only tweak
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], tweaks[:2], [False, True], msg)
    assert sign(secnonce, sk, session_ctx) == expected[2]

    # Four tweaks: x-only, ordinary, x-only, ordinary
    session_ctx = SessionContext(aggnonce, [X[0], X[1], pk], tweaks[:4], [True, False, True, False], msg)
    assert sign(secnonce, sk, session_ctx) == expected[3]

def test_sign_and_verify_random(iters):
    for i in range(iters):
        sk_1 = secrets.token_bytes(32)
        sk_2 = secrets.token_bytes(32)
        pk_1 = bytes_from_point(point_mul(G, int_from_bytes(sk_1)))
        pk_2 = bytes_from_point(point_mul(G, int_from_bytes(sk_2)))
        pubkeys = [pk_1, pk_2]

        # In this example, the message and aggregate pubkey are known
        # before nonce generation, so they can be passed into the nonce
        # generation function as a defense-in-depth measure to protect
        # against nonce reuse.
        #
        # If these values are not known when nonce_gen is called, empty
        # byte arrays can be passed in for the corresponding arguments
        # instead.
        msg = secrets.token_bytes(32)
        v = secrets.randbelow(4)
        tweaks = [secrets.token_bytes(32) for _ in range(v)]
        is_xonly = [secrets.choice([False, True]) for _ in range(v)]
        aggpk = key_agg(pubkeys, tweaks, is_xonly)

        # Use a non-repeating counter for extra_in
        secnonce_1, pubnonce_1 = nonce_gen(sk_1, aggpk, msg, i.to_bytes(4, 'big'))

        # Use a clock for extra_in
        t = time.clock_gettime_ns(time.CLOCK_MONOTONIC)
        secnonce_2, pubnonce_2 = nonce_gen(sk_2, aggpk, msg, t.to_bytes(8, 'big'))

        pubnonces = [pubnonce_1, pubnonce_2]
        aggnonce = nonce_agg(pubnonces)

        session_ctx = SessionContext(aggnonce, pubkeys, tweaks, is_xonly, msg)
        psig_1 = sign(secnonce_1, sk_1, session_ctx)
        # Clear the secnonce after use
        secnonce_1 = bytes(64)
        assert partial_sig_verify(psig_1, pubnonces, pubkeys, tweaks, is_xonly, msg, 0)

        # Wrong signer index
        assert not partial_sig_verify(psig_1, pubnonces, pubkeys, tweaks, is_xonly, msg, 1)

        # Wrong message
        assert not partial_sig_verify(psig_1, pubnonces, pubkeys, tweaks, is_xonly, secrets.token_bytes(32), 0)

        psig_2 = sign(secnonce_2, sk_2, session_ctx)
        # Clear the secnonce after use
        secnonce_2 = bytes(64)
        assert partial_sig_verify(psig_2, pubnonces, pubkeys, tweaks, is_xonly, msg, 1)

        sig = partial_sig_agg([psig_1, psig_2], session_ctx)
        assert schnorr_verify(msg, aggpk, sig)

if __name__ == '__main__':
    test_key_agg_vectors()
    test_nonce_gen_vectors()
    test_nonce_agg_vectors()
    test_sign_verify_vectors()
    test_tweak_vectors()
    test_sign_and_verify_random(4)
