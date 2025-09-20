// arrays.dfy


module Arrays {
  predicate EqualsExcept<T(==)>(lhs: seq<T>, rhs: seq<T>, address: nat, length: nat)
    requires address + length <= |lhs|
    decreases lhs, rhs, address, length
  {
    |lhs| == |rhs| &&
    lhs[..address] == rhs[..address] &&
    lhs[address + length..] == rhs[address + length..]
  }

  function SliceAndPad<T>(mem: seq<T>, address: nat, len: nat, padding: T): (result: seq<T>)
    ensures |result| == len
    decreases mem, address, len
  {
    var n: int := address + len;
    if n <= |mem| then
      mem[address .. n]
    else if address < |mem| then
      mem[address..] + seq(n - |mem|, (i: int) => padding)
    else
      seq(len, (i: int) => padding)
  }

  opaque function Copy<T>(src: seq<T>, dst: seq<T>, start: nat): (result: seq<T>)
    requires start + |src| <= |dst|
    ensures |result| == |dst|
    ensures src == result[start .. start + |src|]
    ensures EqualsExcept(dst, result, start, |src|)
    decreases src, dst, start
  {
    var end: int := start + |src|;
    seq(|dst|, (i: int) requires i >= 0 && i < 0 => if i >= start && i < end then src[i - start] else dst[i])
  }

  import opened Int

  type Array<T> = arr: seq<T>
    | |arr| < TWO_256
}

module Int {
  const TWO_1: int := 2
  const TWO_2: int := 4
  const TWO_3: int := 8
  const TWO_4: int := 16
  const TWO_5: int := 32
  const TWO_6: int := 64
  const TWO_7: int := 128
  const TWO_8: int := 256
  const TWO_15: int := 32768
  const TWO_16: int := 65536
  const TWO_24: int := 16777216
  const TWO_31: int := 2147483648
  const TWO_32: int := 4294967296
  const TWO_40: int := 1099511627776
  const TWO_48: int := 281474976710656
  const TWO_56: int := 72057594037927936
  const TWO_63: int := 9223372036854775808
  const TWO_64: int := 18446744073709551616
  const TWO_72: int := 4722366482869645213696
  const TWO_80: int := 1208925819614629174706176
  const TWO_88: int := 309485009821345068724781056
  const TWO_96: int := 79228162514264337593543950336
  const TWO_104: int := 20282409603651670423947251286016
  const TWO_112: int := 5192296858534827628530496329220096
  const TWO_120: int := 1329227995784915872903807060280344576
  const TWO_127: int := 170141183460469231731687303715884105728
  const TWO_128: int := 340282366920938463463374607431768211456
  const TWO_136: int := 87112285931760246646623899502532662132736
  const TWO_144: int := 22300745198530623141535718272648361505980416
  const TWO_152: int := 5708990770823839524233143877797980545530986496
  const TWO_160: int := 1461501637330902918203684832716283019655932542976
  const TWO_168: int := 374144419156711147060143317175368453031918731001856
  const TWO_176: int := 95780971304118053647396689196894323976171195136475136
  const TWO_184: int := 24519928653854221733733552434404946937899825954937634816
  const TWO_192: int := 6277101735386680763835789423207666416102355444464034512896
  const TWO_200: int := 1606938044258990275541962092341162602522202993782792835301376
  const TWO_208: int := 411376139330301510538742295639337626245683966408394965837152256
  const TWO_216: int := 105312291668557186697918027683670432318895095400549111254310977536
  const TWO_224: int := 26959946667150639794667015087019630673637144422540572481103610249216
  const TWO_232: int := 6901746346790563787434755862277025452451108972170386555162524223799296
  const TWO_240: int := 1766847064778384329583297500742918515827483896875618958121606201292619776
  const TWO_248: int := 452312848583266388373324160190187140051835877600158453279131187530910662656
  const TWO_255: int := 57896044618658097711785492504343953926634992332820282019728792003956564819968
  const TWO_256: int := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  const MIN_I8: int := -TWO_7
  const MAX_I8: int := TWO_7 - 1
  const MIN_I16: int := -TWO_15
  const MAX_I16: int := TWO_15 - 1
  const MIN_I32: int := -TWO_31
  const MAX_I32: int := TWO_31 - 1
  const MIN_I64: int := -TWO_63
  const MAX_I64: int := TWO_63 - 1
  const MIN_I128: int := -TWO_127
  const MAX_I128: int := TWO_127 - 1
  const MIN_I256: int := -TWO_255
  const MAX_I256: int := TWO_255 - 1
  const MAX_U1: int := TWO_1 - 1
  const MAX_U2: int := TWO_2 - 1
  const MAX_U3: int := TWO_3 - 1
  const MAX_U4: int := TWO_4 - 1
  const MAX_U5: int := TWO_5 - 1
  const MAX_U6: int := TWO_6 - 1
  const MAX_U7: int := TWO_7 - 1
  const MAX_U8: int := TWO_8 - 1
  const MAX_U16: int := TWO_16 - 1
  const MAX_U24: int := TWO_24 - 1
  const MAX_U32: int := TWO_32 - 1
  const MAX_U40: int := TWO_40 - 1
  const MAX_U48: int := TWO_48 - 1
  const MAX_U56: int := TWO_56 - 1
  const MAX_U64: int := TWO_64 - 1
  const MAX_U72: int := TWO_72 - 1
  const MAX_U80: int := TWO_80 - 1
  const MAX_U88: int := TWO_88 - 1
  const MAX_U96: int := TWO_96 - 1
  const MAX_U104: int := TWO_104 - 1
  const MAX_U112: int := TWO_112 - 1
  const MAX_U120: int := TWO_120 - 1
  const MAX_U128: int := TWO_128 - 1
  const MAX_U136: int := TWO_136 - 1
  const MAX_U144: int := TWO_144 - 1
  const MAX_U152: int := TWO_152 - 1
  const MAX_U160: int := TWO_160 - 1
  const MAX_U168: int := TWO_168 - 1
  const MAX_U176: int := TWO_176 - 1
  const MAX_U184: int := TWO_184 - 1
  const MAX_U192: int := TWO_192 - 1
  const MAX_U200: int := TWO_200 - 1
  const MAX_U208: int := TWO_208 - 1
  const MAX_U216: int := TWO_216 - 1
  const MAX_U224: int := TWO_224 - 1
  const MAX_U232: int := TWO_232 - 1
  const MAX_U240: int := TWO_240 - 1
  const MAX_U248: int := TWO_248 - 1
  const MAX_U256: int := TWO_256 - 1

  function Abs(x: int): nat
    decreases x
  {
    if x >= 0 then
      x
    else
      -x
  }

  function Max(i1: int, i2: int): int
    decreases i1, i2
  {
    if i1 >= i2 then
      i1
    else
      i2
  }

  function Min(i1: int, i2: int): int
    decreases i1, i2
  {
    if i1 < i2 then
      i1
    else
      i2
  }

  function RoundUp(i: int, r: nat): int
    requires r > 0
    decreases i, r
  {
    if i % r == 0 then
      i
    else
      i / r * r + r
  }

  function MaxUnsignedN(n: nat): (r: nat)
    requires 1 <= n <= 32
    decreases n
  {
    match n
    case 1 =>
      MAX_U8
    case 2 =>
      MAX_U16
    case 3 =>
      MAX_U24
    case 4 =>
      MAX_U32
    case 5 =>
      MAX_U40
    case 6 =>
      MAX_U48
    case 7 =>
      MAX_U56
    case 8 =>
      MAX_U64
    case 9 =>
      MAX_U72
    case 10 =>
      MAX_U80
    case 11 =>
      MAX_U88
    case 12 =>
      MAX_U96
    case 13 =>
      MAX_U104
    case 14 =>
      MAX_U112
    case 15 =>
      MAX_U120
    case 16 =>
      MAX_U128
    case 17 =>
      MAX_U136
    case 18 =>
      MAX_U144
    case 19 =>
      MAX_U152
    case 20 =>
      MAX_U160
    case 21 =>
      MAX_U168
    case 22 =>
      MAX_U176
    case 23 =>
      MAX_U184
    case 24 =>
      MAX_U192
    case 25 =>
      MAX_U200
    case 26 =>
      MAX_U208
    case 27 =>
      MAX_U216
    case 28 =>
      MAX_U224
    case 29 =>
      MAX_U232
    case 30 =>
      MAX_U240
    case 31 =>
      MAX_U248
    case 32 =>
      MAX_U256
    case _ /* _v0 */ =>
      MathUtils.Pow(2, n) - 1
  }

  function Div(lhs: int, rhs: int): int
    requires rhs != 0
    decreases lhs, rhs
  {
    if lhs >= 0 then
      lhs / rhs
    else
      -(-lhs / rhs)
  }

  function Rem(lhs: int, rhs: int): int
    requires rhs != 0
    decreases lhs, rhs
  {
    if lhs >= 0 then
      lhs % rhs
    else
      var d: int := -(-lhs / rhs); lhs - d * rhs
  }

  function {:tailrecursion true} ToBytes(v: nat): (r: seq<u8>)
    ensures |r| > 0
    decreases v
  {
    var byte: u8 := (v % 256) as u8;
    var w: nat := v / 256;
    if w == 0 then
      [byte]
    else
      ToBytes(w) + [byte]
  }

  function FromBytes(bytes: seq<u8>): (r: nat)
    decreases bytes
  {
    if |bytes| == 0 then
      0
    else
      var last: int := |bytes| - 1; var byte: nat := bytes[last] as nat; var msw: nat := FromBytes(bytes[..last]); msw * 256 + byte
  } by method {
    r := 0;
    for i: int := 0 to |bytes|
      invariant r == FromBytes(bytes[..i])
    {
      var ith := bytes[i] as nat;
      r := r * 256 + ith;
      LemmaFromBytes(bytes, i);
    }
    assert bytes[..|bytes|] == bytes;
    return r;
  }

  lemma LemmaFromBytes(bytes: seq<u8>, i: nat)
    requires 0 <= i < |bytes|
    ensures FromBytes(bytes[..i + 1]) == FromBytes(bytes[..i]) * 256 + bytes[i] as nat
    decreases bytes, i
  {
    if i != 0 {
      ghost var cons := bytes[..i + 1];
      ghost var tail := bytes[..i];
      ghost var head := bytes[i];
      assert cons == tail + [head];
    }
  }

  lemma /*{:_inductionTrigger ToBytes(v)}*/ /*{:_induction v}*/ LemmaFromToBytes(v: nat)
    ensures FromBytes(ToBytes(v)) == v
    decreases v
  {
  }

  lemma {:verify false} /*{:_inductionTrigger FromBytes(bytes)}*/ /*{:_inductionTrigger bytes[0]}*/ /*{:_inductionTrigger |bytes|}*/ /*{:_induction bytes}*/ LemmaToFromBytes(bytes: seq<u8>)
    requires |bytes| > 0 && (|bytes| == 1 || bytes[0] != 0)
    ensures ToBytes(FromBytes(bytes)) == bytes
    decreases bytes
  {
    ghost var n := |bytes| - 1;
    if |bytes| > 1 {
      ghost var tail := bytes[..n];
      LemmaToFromBytes(tail);
    } else {
      assert ToBytes(FromBytes(bytes)) == bytes;
    }
  }

  lemma /*{:_inductionTrigger ToBytes(m), ToBytes(n)}*/ /*{:_induction n, m}*/ LemmaLengthToBytes(n: nat, m: nat)
    requires n <= m
    ensures |ToBytes(n)| <= |ToBytes(m)|
    decreases n, m
  {
  }

  lemma /*{:_inductionTrigger |bytes|, |ToBytes(n)|}*/ /*{:_inductionTrigger ToBytes(n), FromBytes(bytes)}*/ /*{:_induction n, bytes}*/ LemmaLengthFromBytes(n: nat, bytes: seq<u8>)
    requires n == FromBytes(bytes)
    ensures bytes == [] || |ToBytes(n)| <= |bytes|
    decreases n, bytes
  {
    if |bytes| == 1 {
      assert |ToBytes(n)| == 1;
    } else if |bytes| > 1 {
      ghost var last := |bytes| - 1;
      ghost var tail := bytes[..last];
      LemmaLengthFromBytes(n / 256, tail);
    }
  }

  import opened Optional

  import MathUtils

  newtype {:nativeType "sbyte"} i8 = i: int
    | MIN_I8 <= i <= MAX_I8

  newtype {:nativeType "short"} i16 = i: int
    | MIN_I16 <= i <= MAX_I16

  newtype {:nativeType "int"} i32 = i: int
    | MIN_I32 <= i <= MAX_I32

  newtype {:nativeType "long"} i64 = i: int
    | MIN_I64 <= i <= MAX_I64

  newtype i128 = i: int
    | MIN_I128 <= i <= MAX_I128

  newtype i256 = i: int
    | MIN_I256 <= i <= MAX_I256

  newtype {:nativeType "byte"} u1 = i: int
    | 0 <= i <= MAX_U1

  newtype {:nativeType "byte"} u2 = i: int
    | 0 <= i <= MAX_U2

  newtype {:nativeType "byte"} u3 = i: int
    | 0 <= i <= MAX_U3

  newtype {:nativeType "byte"} u4 = i: int
    | 0 <= i <= MAX_U4

  newtype {:nativeType "byte"} u5 = i: int
    | 0 <= i <= MAX_U5

  newtype {:nativeType "byte"} u6 = i: int
    | 0 <= i <= MAX_U6

  newtype {:nativeType "byte"} u7 = i: int
    | 0 <= i <= MAX_U7

  newtype {:nativeType "byte"} u8 = i: int
    | 0 <= i <= MAX_U8

  newtype {:nativeType "ushort"} u16 = i: int
    | 0 <= i <= MAX_U16

  newtype {:nativeType "uint"} u24 = i: int
    | 0 <= i <= MAX_U24

  newtype {:nativeType "uint"} u32 = i: int
    | 0 <= i <= MAX_U32

  newtype {:nativeType "ulong"} u40 = i: int
    | 0 <= i <= MAX_U40

  newtype {:nativeType "ulong"} u48 = i: int
    | 0 <= i <= MAX_U48

  newtype {:nativeType "ulong"} u56 = i: int
    | 0 <= i <= MAX_U56

  newtype {:nativeType "ulong"} u64 = i: int
    | 0 <= i <= MAX_U64

  newtype u128 = i: int
    | 0 <= i <= MAX_U128

  newtype u160 = i: int
    | 0 <= i <= MAX_U160

  newtype u256 = i: int
    | 0 <= i <= MAX_U256
}

module U8 {
  function Log2(v: u8): (r: nat)
    ensures r < 8
    decreases v
  {
    if v <= 15 then
      if v <= 3 then
        if v <= 1 then
          0
        else
          1
      else if v <= 7 then
        2
      else
        3
    else if v <= 63 then
      if v <= 31 then
        4
      else
        5
    else if v <= 127 then
      6
    else
      7
  }

  import opened Int
}

module U16 {
  function NthUint8(v: u16, k: nat): u8
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_8 as u16) as u8
    else
      (v % TWO_8 as u16) as u8
  }

  function Log2(v: u16): (r: nat)
    ensures r < 16
    decreases v
  {
    var low: u8 := (v % TWO_8 as u16) as u8;
    var high: u8 := (v / TWO_8 as u16) as u8;
    if high != 0 then
      U8.Log2(high) + 8
    else
      U8.Log2(low)
  }

  function Log256(v: u16): (r: nat)
    ensures r <= 1
    decreases v
  {
    var low: u8 := (v % TWO_8 as u16) as u8;
    var high: u8 := (v / TWO_8 as u16) as u8;
    if high != 0 then
      1
    else
      0
  }

  function ToBytes(v: u16): (r: seq<u8>)
    ensures |r| == 2
    decreases v
  {
    var low: u8 := (v % TWO_8 as u16) as u8;
    var high: u8 := (v / TWO_8 as u16) as u8;
    [high, low]
  }

  function Read(bytes: seq<u8>, address: nat): u16
    requires address + 1 < |bytes|
    decreases bytes, address
  {
    var b1: u16 := bytes[address] as u16;
    var b2: u16 := bytes[address + 1] as u16;
    b1 * TWO_8 as u16 + b2
  }

  import opened Int

  import U8
}

module U32 {
  function NthUint16(v: u32, k: nat): u16
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_16 as u32) as u16
    else
      (v % TWO_16 as u32) as u16
  }

  function Log2(v: u32): (r: nat)
    ensures r < 32
    decreases v
  {
    var low: u16 := (v % TWO_16 as u32) as u16;
    var high: u16 := (v / TWO_16 as u32) as u16;
    if high != 0 then
      U16.Log2(high) + 16
    else
      U16.Log2(low)
  }

  function Log256(v: u32): (r: nat)
    ensures r <= 3
    decreases v
  {
    var low: u16 := (v % TWO_16 as u32) as u16;
    var high: u16 := (v / TWO_16 as u32) as u16;
    if high != 0 then
      U16.Log256(high) + 2
    else
      U16.Log256(low)
  }

  function ToBytes(v: u32): (r: seq<u8>)
    ensures |r| == 4
    decreases v
  {
    var low: u16 := (v % TWO_16 as u32) as u16;
    var high: u16 := (v / TWO_16 as u32) as u16;
    U16.ToBytes(high) + U16.ToBytes(low)
  }

  function Read(bytes: seq<u8>, address: nat): u32
    requires address + 3 < |bytes|
    decreases bytes, address
  {
    var b1: u32 := U16.Read(bytes, address) as u32;
    var b2: u32 := U16.Read(bytes, address + 2) as u32;
    b1 * TWO_16 as u32 + b2
  }

  import U16

  import opened Int
}

module U64 {
  function NthUint32(v: u64, k: nat): u32
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_32 as u64) as u32
    else
      (v % TWO_32 as u64) as u32
  }

  function Log2(v: u64): (r: nat)
    ensures r < 64
    decreases v
  {
    var low: u32 := (v % TWO_32 as u64) as u32;
    var high: u32 := (v / TWO_32 as u64) as u32;
    if high != 0 then
      U32.Log2(high) + 32
    else
      U32.Log2(low)
  }

  function Log256(v: u64): (r: nat)
    ensures r <= 7
    decreases v
  {
    var low: u32 := (v % TWO_32 as u64) as u32;
    var high: u32 := (v / TWO_32 as u64) as u32;
    if high != 0 then
      U32.Log256(high) + 4
    else
      U32.Log256(low)
  }

  function ToBytes(v: u64): (r: seq<u8>)
    ensures |r| == 8
    decreases v
  {
    var low: u32 := (v % TWO_32 as u64) as u32;
    var high: u32 := (v / TWO_32 as u64) as u32;
    U32.ToBytes(high) + U32.ToBytes(low)
  }

  function Read(bytes: seq<u8>, address: nat): u64
    requires address + 7 < |bytes|
    decreases bytes, address
  {
    var b1: u64 := U32.Read(bytes, address) as u64;
    var b2: u64 := U32.Read(bytes, address + 4) as u64;
    b1 * TWO_32 as u64 + b2
  }

  import U32

  import opened Int
}

module U128 {
  function NthUint64(v: u128, k: nat): u64
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_64 as u128) as u64
    else
      (v % TWO_64 as u128) as u64
  }

  function Log2(v: u128): (r: nat)
    ensures r < 128
    decreases v
  {
    var low: u64 := (v % TWO_64 as u128) as u64;
    var high: u64 := (v / TWO_64 as u128) as u64;
    if high != 0 then
      U64.Log2(high) + 64
    else
      U64.Log2(low)
  }

  function Log256(v: u128): (r: nat)
    ensures r <= 15
    decreases v
  {
    var low: u64 := (v % TWO_64 as u128) as u64;
    var high: u64 := (v / TWO_64 as u128) as u64;
    if high != 0 then
      U64.Log256(high) + 8
    else
      U64.Log256(low)
  }

  function ToBytes(v: u128): (r: seq<u8>)
    ensures |r| == 16
    decreases v
  {
    var low: u64 := (v % TWO_64 as u128) as u64;
    var high: u64 := (v / TWO_64 as u128) as u64;
    U64.ToBytes(high) + U64.ToBytes(low)
  }

  function Read(bytes: seq<u8>, address: nat): u128
    requires address + 15 < |bytes|
    decreases bytes, address
  {
    var b1: u128 := U64.Read(bytes, address) as u128;
    var b2: u128 := U64.Read(bytes, address + 8) as u128;
    b1 * TWO_64 as u128 + b2
  }

  import U64

  import opened Int
}

module U256 {
  lemma {:axiom} as_bv256_as_u256(v: bv256)
    ensures v as nat < TWO_256
    decreases v

  function Shl(lhs: u256, rhs: u256): u256
    decreases lhs, rhs
  {
    if rhs >= 256 then
      0
    else
      var p: nat := MathUtils.Pow(2, rhs as nat); var n: int := lhs as nat * p; (n % TWO_256) as u256
  }

  function Shr(lhs: u256, rhs: u256): u256
    decreases lhs, rhs
  {
    if rhs >= 256 then
      0
    else
      var p: nat := MathUtils.Pow(2, rhs as nat); var n: int := lhs as nat / p; n as u256
  }

  function Log2(v: u256): (r: nat)
    ensures r < 256
    decreases v
  {
    var low: u128 := (v % TWO_128 as u256) as u128;
    var high: u128 := (v / TWO_128 as u256) as u128;
    if high != 0 then
      U128.Log2(high) + 128
    else
      U128.Log2(low)
  }

  function Log256(v: u256): (r: nat)
    ensures r <= 31
    decreases v
  {
    var low: u128 := (v % TWO_128 as u256) as u128;
    var high: u128 := (v / TWO_128 as u256) as u128;
    if high != 0 then
      U128.Log256(high) + 16
    else
      U128.Log256(low)
  }

  function NthUint128(v: u256, k: nat): u128
    requires k < 2
    decreases v, k
  {
    if k == 0 then
      (v / TWO_128 as u256) as u128
    else
      (v % TWO_128 as u256) as u128
  }

  function NthUint8(v: u256, k: nat): u8
    requires k < 32
    decreases v, k
  {
    var w128: u128 := NthUint128(v, k / 16);
    var w64: u64 := U128.NthUint64(w128, k % 16 / 8);
    var w32: u32 := U64.NthUint32(w64, k % 8 / 4);
    var w16: u16 := U32.NthUint16(w32, k % 4 / 2);
    U16.NthUint8(w16, k % 2)
  }

  function Read(bytes: seq<u8>, address: nat): u256
    requires address + 31 < |bytes|
    decreases bytes, address
  {
    var b1: u256 := U128.Read(bytes, address) as u256;
    var b2: u256 := U128.Read(bytes, address + 16) as u256;
    b1 * TWO_128 as u256 + b2
  }

  function ToBytes(v: u256): (r: seq<u8>)
    ensures |r| == 32
    decreases v
  {
    var low: u128 := (v % TWO_128 as u256) as u128;
    var high: u128 := (v / TWO_128 as u256) as u128;
    U128.ToBytes(high) + U128.ToBytes(low)
  }

  function SignExtend(v: u256, k: nat): u256
    decreases v, k
  {
    if k >= 31 then
      v
    else
      var ith: int := 31 - k; var byte: u8 := NthUint8(v, ith); var signs: seq<u8> := if byte >= 128 then seq(31 - k, (i: int) => 255) else seq(31 - k, (i: int) => 0); var bytes: seq<u8> := ToBytes(v)[ith..]; assert |signs + bytes| == 32; Read(signs + bytes, 0)
  }

  import opened Int

  import U8

  import U16

  import U32

  import U64

  import U128
}

module I256 {
  function Div(lhs: i256, rhs: i256): i256
    requires rhs != 0
    requires rhs != -1 || lhs != -TWO_255 as i256
    decreases lhs, rhs
  {
    Int.Div(lhs as int, rhs as int) as i256
  }

  function Rem(lhs: i256, rhs: i256): i256
    requires rhs != 0
    decreases lhs, rhs
  {
    Int.Rem(lhs as int, rhs as int) as i256
  }

  function Sar(lhs: i256, rhs: u256): i256
    decreases lhs, rhs
  {
    if rhs == 0 then
      lhs
    else if rhs < 256 then
      assert 0 < rhs < 256;
      var r: nat := MathUtils.Pow(2, rhs as nat);
      (lhs as int / r as int) as i256
    else if lhs < 0 then
      -1
    else
      0
  }

  import U256

  import Word

  import opened Int
}

module Word {
  function asI256(w: u256): i256
    decreases w
  {
    if w > MAX_I256 as u256 then
      var v: int := 1 + MAX_U256 - w as int;
      -v as i256
    else
      w as i256
  }

  function fromI256(w: Int.i256): u256
    decreases w
  {
    if w < 0 then
      var v: int := 1 + MAX_U256 + w as int;
      v as u256
    else
      w as u256
  }

  import opened Int
}

module Optional {
  datatype Option<T> = Some(v: T) | None {
    function Unwrap(): T
      requires this.Some?
      decreases this
    {
      this.v
    }

    function UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case none =>
        default
    }
  }
}

module MathUtils {
  function Abs(x: int): nat
    decreases x
  {
    if x >= 0 then
      x
    else
      -x
  }

  function Pow(n: nat, k: nat): (r: nat)
    ensures n > 0 ==> r > 0
    decreases n, k
  {
    if k == 0 then
      1
    else if k == 1 then
      n
    else
      var p: int := k / 2; var np: nat := Pow(n, p); if p * 2 == k then np * np else np * np * n
  }

  lemma /*{:_inductionTrigger Pow(2, k)}*/ /*{:_induction k}*/ lemma_pow2(k: nat)
    ensures Pow(2, k) > 0
    decreases k
  {
    if k == 0 {
      assert Pow(2, k) == 1;
    } else if k == 1 {
      assert Pow(2, k) == 2;
    } else {
      lemma_pow2(k / 2);
    }
  }

  function ModPow(n: nat, k: nat, m: nat): (r: nat)
    requires m > 0
    ensures r < m
    ensures n > 0 ==> r >= 0
    decreases k
  {
    var nm: int := n % m;
    if k == 0 || m == 1 then
      1 % m
    else if k == 1 then
      nm
    else
      var np: nat := ModPow(nm, k / 2, m); var np2: int := np * np % m; if k % 2 == 0 then np2 else np2 * nm % m
  }

  function GcdExtended(a: nat, b: nat): (r: (nat, int, int))
    ensures b > 0 ==> r.0 > 0
    ensures a * r.1 + b * r.2 == r.0
    decreases a, b
  {
    if a == 0 then
      (b, 0, 1)
    else
      var (g: nat, x: int, y: int) := GcdExtended(b % a, a); (g, y - b / a * x, x)
  }

  function Inverse(a: nat, n: nat): (r: Option<nat>)
    requires a < n
    ensures r != None ==> r.Unwrap() < n
    decreases a, n
  {
    var (gcd: nat, x: int, y: int) := GcdExtended(a, n);
    assume {:axiom} Abs(x) < n;
    if gcd > 1 then
      None
    else if x >= 0 then
      Some(x)
    else
      Some(x + n)
  }

  predicate IsPrime(n: nat)
    decreases n
  {
    n > 1 &&
    forall a: int {:trigger GcdExtended(a, n)} :: 
      1 <= a < n ==>
        GcdExtended(a, n).0 == 1
  }

  lemma PrimeFieldsHaveInverse(a: nat, n: nat)
    requires IsPrime(n)
    requires 1 <= a < n
    ensures Inverse(a, n) != None
    decreases a, n
  {
    assert GcdExtended(a, n).0 == 1;
  }

  import opened Optional
}
